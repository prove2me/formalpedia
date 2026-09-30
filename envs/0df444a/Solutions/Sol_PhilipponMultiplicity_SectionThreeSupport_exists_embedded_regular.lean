-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.exists_embedded_regular
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:41:33.536761+00:00
-- url     : https://prove2.me/submissions/e913b90b-3c33-49d9-9c9f-47a83bf2bace

import Theorems.Thm_Ideal_exists_mem_forall_not_mem_of_forall_not_le
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

-- Reused from Solutions/PhilipponDimensionSlice.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComponentSelection

theorem finite_iInf_le_prime {R ι : Type*} [CommRing R] [Finite ι]
    (A : ι → Ideal R) (q : Ideal R) (hq : q.IsPrime) :
    (⨅ i, A i) ≤ q ↔ ∃ i, A i ≤ q := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Finset.mem_univ, true_and] using
    (hq.inf_le' (s := Finset.univ) (f := A))

end PhilipponMultiplicity.ComponentSelection

end

-- Reused from Solutions/PhilipponEmbeddedAvoidance.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.ComponentSelection

/-- Avoiding the radicals of primary factors gives an actual regular
element in the quotient by their intersection. -/
theorem regular_quotient_iInf {R ι : Type*} [CommRing R]
    (Q : ι → Ideal R) (s : ι → Prop) (hQ : ∀ i, (Q i).IsPrimary)
    (x : R) (hx : ∀ i, s i → x ∉ (Q i).radical) :
    IsRegular (Ideal.Quotient.mk (⨅ i, if s i then Q i else ⊤) x) := by
  classical
  let A : Ideal R := ⨅ i, if s i then Q i else ⊤
  apply (Commute.isRegular_iff (fun y => mul_comm _ y)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change r ∈ A
  have hxr : x * r ∈ A := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  simp only [A, Submodule.mem_iInf] at hxr ⊢
  intro i
  split_ifs with hi
  · have hmem : x * r ∈ Q i := by simpa only [if_pos hi] using hxr i
    exact ((Ideal.isPrimary_iff.mp (hQ i)).2 (mul_comm x r ▸ hmem)).resolve_right (hx i hi)
  · trivial

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.SectionThreeSupport
open ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Fact D: one element removes all embedded components and is a
non-zero-divisor on the entire isolated intersection. -/
theorem exists_embedded_regular (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) :
    ∃ Q ∈ D.embeddedIntersection,
      IsRegular (Ideal.Quotient.mk D.isolatedIntersection Q) := by
  classical
  let S : Finset (Ideal M.CoordinateRing) :=
    (Finset.univ.filter D.IsIsolated).image (fun i => (D.component i).radical)
  have hS : ∀ p ∈ S, p.IsPrime := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Ideal.isPrime_radical (D.primary i)
  have havoid : ∀ p ∈ S, ¬ D.embeddedIntersection ≤ p := by
    intro p hp hle
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    have his : D.IsIsolated i := (Finset.mem_filter.mp hi).2
    have hpprime := Ideal.isPrime_radical (D.primary i)
    obtain ⟨j, hj⟩ := (finite_iInf_le_prime _ _ hpprime).mp hle
    split_ifs at hj with hjemb
    · have hrad : (D.component j).radical ≤ (D.component i).radical :=
        hpprime.radical_le_iff.mpr hj
      have hIj : I ≤ D.component j := D.intersection_eq.le.trans (iInf_le _ j)
      have hback := his.2 ⟨Ideal.isPrime_radical (D.primary j),
        hIj.trans Ideal.le_radical⟩ hrad
      have hji : j = i := D.radicals_injective (le_antisymm hrad hback)
      exact hjemb (hji ▸ his)
    · exact hpprime.ne_top (top_unique hj)
  obtain ⟨Q, hQ, havoidQ⟩ :=
    Ideal.exists_mem_forall_not_mem_of_forall_not_le D.embeddedIntersection S hS havoid
  refine ⟨Q, hQ, ?_⟩
  apply regular_quotient_iInf D.component D.IsIsolated D.primary Q
  intro i hi
  apply havoidQ _
  exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) :
    ∃ Q ∈ D.embeddedIntersection,
      IsRegular (Ideal.Quotient.mk D.isolatedIntersection Q) := by
  exact PhilipponMultiplicity.SectionThreeSupport.exists_embedded_regular M I D
