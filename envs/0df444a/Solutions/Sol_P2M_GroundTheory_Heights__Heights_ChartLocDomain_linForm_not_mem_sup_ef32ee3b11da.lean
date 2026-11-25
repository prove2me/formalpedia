-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_not_mem_sup_ef32ee3b11da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:52.162126+00:00
-- url     : https://prove2.me/submissions/c8b99aa6-ebd1-46ad-997e-a9f2f17113b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_aeval_mul_of_isHomogeneous_4651ac7a1fe2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_isHomogeneous_618f3987ba84

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLocDomain
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartLocDomain
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) F)} (hI : IsProjPrime I) {t u : Fin n → F}
    (ht : linForm t ∉ I) (hu : linForm u ∉ I) : linForm u ∉ I ⊔ Ideal.span {linForm t - 1} := by
  have := hI.isPrime
  set a : MvPolynomial (Fin n) F ⧸ I := Ideal.Quotient.mk I (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ I) A).comp (Ideal.Quotient.mkₐ F I)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    rw [← comp_aeval_apply]; simp
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {d : ℕ}, g.IsHomogeneous d → ψ g = v ^ d * φ g :=
    fun hg => by rw [← hφ]; exact aeval_mul_of_isHomogeneous hg _ _
  have hle : I ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) ?_
    · rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [hhom (homogeneousComponent_isHomogeneous d g)]
      have : φ (homogeneousComponent d g) = 0 := by
        simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hI.isHomog g hg d)]
      rw [this, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
        hhom (linForm_isHomogeneous t), pow_one]
      have : φ (linForm t) = algebraMap _ A a := rfl
      rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  intro hmem
  have h0 : ψ (linForm u) = 0 := hle hmem
  rw [hhom (linForm_isHomogeneous u), pow_one] at h0
  have h1 : algebraMap _ A (Ideal.Quotient.mk I (linForm u)) = 0 :=
    calc algebraMap _ A (Ideal.Quotient.mk I (linForm u))
        = algebraMap _ A a * (v * φ (linForm u)) := by
          rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]; rfl
      _ = 0 := by rw [h0, mul_zero]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ I) A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  exact hu (Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h1.trans (map_zero _).symm)))
end GroundTheory.Heights₂.Heights.ChartLocDomain
