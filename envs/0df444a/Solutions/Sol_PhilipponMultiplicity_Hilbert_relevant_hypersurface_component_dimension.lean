-- Prove2me | solution 1 for PhilipponMultiplicity.Hilbert.relevant_hypersurface_component_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T00:58:08.811618+00:00
-- url     : https://prove2.me/submissions/40b515a3-5abd-4ab8-ae05-8b652ed75ad4

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_Ideal_height_map_quotient_eq_one_of_minimalPrimes
import Theorems.Thm_Algebra_FiniteType_prime_quotient_dimension_formula
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevantCore_krull_dimension
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i


end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_sup_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I ⊔ Ideal.span {P}) := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI f hf d
  have hPg : (Ideal.span {P}).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro f hf
    have heq : f = P := Set.mem_singleton_iff.mp hf
    subst f
    exact ⟨D, (M.degreePiece_iff P D).mpr hP⟩
  intro f hf d
  exact weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d


end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem relevantRadicalCore_eq_of_relevant_prime (p : Ideal M.CoordinateRing)
    (hp : p.IsPrime) (hr : IsRelevant K M.factorCount M.ambientDimension p) :
    relevantRadicalCore M p = p := by
  classical
  let : p.IsPrime := hp
  have hm : p.minimalPrimes = {p} := Ideal.minimalPrimes_eq_subsingleton_self
  let q₀ : MinimalComponent K M.factorCount M.ambientDimension p :=
    ⟨⟨p, hp⟩, by rw [hm]; exact Set.mem_singleton p⟩
  apply le_antisymm
  · exact (iInf_le_of_le q₀ (by simpa only [q₀, if_pos hr] using (le_refl p)))
  · apply le_iInf
    intro q
    have hq : q.1.asIdeal = p := by
      simpa only [hm, Set.mem_singleton_iff] using q.2
    simp only [hq, if_pos hr, le_refl]

/-- Convert the existing general Hilbert--Krull foundation to a relevant
homogeneous prime. The relevant core is proved equal to that prime. -/
theorem relevant_prime_krull_dimension (p : Ideal M.CoordinateRing)
    (hp : p.IsPrime) (hpH : IsMultihomogeneousIdeal M p)
    (hr : IsRelevant K M.factorCount M.ambientDimension p) :
    ringKrullDim (M.CoordinateRing ⧸ p) =
      ((idealDimension M p + M.factorCount : ℕ) : WithBot ℕ∞) := by
  have hn : IsNontrivialIdeal M p := by
    simpa only [IsNontrivialIdeal, IsRelevant, hp.radical] using hr
  have h := relevantCore_krull_dimension M p hpH hn
  rwa [relevantRadicalCore_eq_of_relevant_prime M p hp hr] at h

/-- Geometric hypersurface component dimension. This reduction imports two
explicit open foundations: affine altitude and Hilbert--Krull comparison. -/
theorem relevant_hypersurface_component_dimension (p : Ideal M.CoordinateRing)
    (hp : p.IsPrime) (hpH : IsMultihomogeneousIdeal M p)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hPp : P ∉ p)
    (q : Ideal M.CoordinateRing) (hq : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes)
    (hqr : IsRelevant K M.factorCount M.ambientDimension q) :
    idealDimension M q + 1 = idealDimension M p := by
  let : p.IsPrime := hp
  let : q.IsPrime := hq.isPrime
  have hpq : p ≤ q := le_sup_left.trans hq.le
  have hpr : IsRelevant K M.factorCount M.ambientDimension p := fun h => hqr (h.trans hpq)
  have hqh := minimalPrime_homogeneous M _ q (homogeneous_sup_span M p hpH P D hP) hq
  have hmap : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hpq)
  have hheight := Ideal.height_map_quotient_eq_one_of_minimalPrimes p q hp P hPp hq
  have hd := Algebra.FiniteType.prime_quotient_dimension_formula K
    (M.CoordinateRing ⧸ p) (q.map (Ideal.Quotient.mk p)) hmap
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq), hheight] at hd
  rw [relevant_prime_krull_dimension M p hp hpH hpr,
    relevant_prime_krull_dimension M q hq.isPrime hqh hqr] at hd
  have hn : idealDimension M q + M.factorCount + 1 =
      idealDimension M p + M.factorCount := by exact_mod_cast hd
  omega

end PhilipponMultiplicity.Hilbert

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(p : Ideal M.CoordinateRing)
    (hp : p.IsPrime) (hpH : IsMultihomogeneousIdeal M p)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hPp : P ∉ p)
    (q : Ideal M.CoordinateRing) (hq : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes)
    (hqr : IsRelevant K M.factorCount M.ambientDimension q) :
    idealDimension M q + 1 = idealDimension M p := by
  exact PhilipponMultiplicity.Hilbert.relevant_hypersurface_component_dimension M p hp hpH P D hP hPp q hq hqr
