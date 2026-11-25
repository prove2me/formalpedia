-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDehomog_proof_43d0929de030
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:05.741802+00:00
-- url     : https://prove2.me/submissions/2a3446ab-3239-4da7-a209-a7217588b586

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
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
namespace GroundTheory.Heights₂.Heights
namespace ChartDehomog
theorem _root_.solution : ChartDehomog.Statement := by
  intro F _ n W t G d hW hH ht hG hmem
  set a : MvPolynomial (Fin n) F ⧸ W := Ideal.Quotient.mk W (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) A).comp (Ideal.Quotient.mkₐ F W)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    rw [← comp_aeval_apply]; simp
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {k : ℕ}, g.IsHomogeneous k → ψ g = v ^ k * φ g :=
    fun hg => by rw [← hφ]; exact ChartLocDomain.aeval_mul_of_isHomogeneous hg _ _
  have hle : W ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) ?_
    · rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hhom (homogeneousComponent_isHomogeneous k g)]
      have : φ (homogeneousComponent k g) = 0 := by
        simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hH g hg k)]
      rw [this, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
        hhom (ChartLocDomain.linForm_isHomogeneous t), pow_one]
      have : φ (linForm t) = algebraMap _ A a := rfl
      rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  have h0 : ψ G = 0 := hle hmem
  rw [hhom hG] at h0
  have h1 : algebraMap _ A (Ideal.Quotient.mk W G) = 0 :=
    calc algebraMap _ A (Ideal.Quotient.mk W G)
        = (algebraMap _ A a * v) ^ d * φ G := by
          rw [IsLocalization.Away.mul_invSelf, one_pow, one_mul]; rfl
      _ = algebraMap _ A a ^ d * (v ^ d * φ G) := by ring
      _ = 0 := by rw [h0, mul_zero]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ W) A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h1.trans (map_zero _).symm))
end ChartDehomog
end GroundTheory.Heights₂.Heights
