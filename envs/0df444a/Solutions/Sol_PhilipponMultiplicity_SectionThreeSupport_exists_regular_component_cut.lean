-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.exists_regular_component_cut
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:44:50.243861+00:00
-- url     : https://prove2.me/submissions/8ae13b16-0579-4fe0-ac43-4920056fdba9

import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_bounded_homogeneous_avoiding
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_component_partition_primes
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

-- Reused from Solutions/PhilipponRegularComponentCut.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
variable {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K)

/-- The cut used in the descending induction: it lies in the original equation
ideal, has exact multidegree D, and is regular on the selected discarded components. -/
theorem exists_regular_component_cut {ι : Type*} [Finite ι]
    (I₀ J : Ideal M.CoordinateRing) (hI₀J : I₀ ≤ J)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (hJI : J ≤ I₀ ⊔ Ideal.span (Set.range P))
    (q : ι → Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
    (hrel : ∀ i, Hilbert.IsRelevant K M.factorCount M.ambientDimension (q i).1.asIdeal)
    (hdiscard : ∀ i, (q i).1.asIdeal ∉ associatedPrimes M.CoordinateRing
      (M.CoordinateRing ⧸ (I₀ ⊔ Ideal.span (Set.range P)))) :
    ∃ f : M.CoordinateRing, f ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous f D ∧
      (∀ i, f ∉ (q i).1.asIdeal) ∧
      IsRegular (Ideal.Quotient.mk
        (⨅ i, Hilbert.primaryComponent K M.factorCount M.ambientDimension J (q i).1) f) := by
  have hb := (component_partition_primes M J (I₀ ⊔ Ideal.span (Set.range P)) hJI).2
  obtain ⟨f, hf, hhom, hout⟩ := exists_bounded_homogeneous_avoiding M I₀ m P D hP
    (fun i => (q i).1.asIdeal) (fun i => (q i).1.isPrime) hrel
    (fun i => hI₀J.trans (q i).2.1.2)
    (fun i => hb _ (q i).2 (hdiscard i))
  refine ⟨f, hf, hhom, hout, ?_⟩
  classical
  apply (Commute.isRegular_iff (fun y => mul_comm _ y)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hfr : f * r ∈ (⨅ i, Hilbert.primaryComponent K M.factorCount M.ambientDimension J (q i).1) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    exact hz
  simp only [Submodule.mem_iInf] at hfr ⊢
  intro i
  have hprimary := Hilbert.primaryComponent_isPrimary K M.factorCount M.ambientDimension J
    (q i).1 (q i).2
  have hnot : f ∉ (Hilbert.primaryComponent K M.factorCount M.ambientDimension J (q i).1).radical := by
    rw [Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J (q i).1 (q i).2]
    exact hout i
  exact ((Ideal.isPrimary_iff.mp hprimary).2 (mul_comm f r ▸ hfr i)).resolve_right hnot

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K) {ι : Type*} [Finite ι]
    (I₀ J : Ideal M.CoordinateRing) (hI₀J : I₀ ≤ J)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (hJI : J ≤ I₀ ⊔ Ideal.span (Set.range P))
    (q : ι → Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
    (hrel : ∀ i, Hilbert.IsRelevant K M.factorCount M.ambientDimension (q i).1.asIdeal)
    (hdiscard : ∀ i, (q i).1.asIdeal ∉ associatedPrimes M.CoordinateRing
      (M.CoordinateRing ⧸ (I₀ ⊔ Ideal.span (Set.range P)))) :
    ∃ f : M.CoordinateRing, f ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous f D ∧
      (∀ i, f ∉ (q i).1.asIdeal) ∧
      IsRegular (Ideal.Quotient.mk
        (⨅ i, Hilbert.primaryComponent K M.factorCount M.ambientDimension J (q i).1) f) := by
  exact PhilipponMultiplicity.SectionThreeSupport.exists_regular_component_cut M I₀ J hI₀J m P D hP hJI q hrel hdiscard
