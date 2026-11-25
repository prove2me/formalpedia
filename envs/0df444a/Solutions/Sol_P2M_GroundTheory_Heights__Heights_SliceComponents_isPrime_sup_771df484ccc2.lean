-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceComponents_isPrime_sup_771df484ccc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:37.998146+00:00
-- url     : https://prove2.me/submissions/b4ee4bcd-722c-4fcd-aa2f-43345d0342ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHomogenise_exists_homogeneous_sub_mem_span_2f27af3c3435
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
open GroundTheory.Heights₂.Heights.SliceComponents
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceComponents
theorem _root_.solution {W : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F} (hW : W.IsPrime)
    (hH : IsHomogIdeal W) (ht : linForm t ∉ W) : (W ⊔ Ideal.span {linForm t - 1}).IsPrime := by
  set a : MvPolynomial (Fin n) F ⧸ W := Ideal.Quotient.mk W (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors ha
  have : IsDomain A := IsLocalization.isDomain_localization hM
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
  have hv : IsUnit v := IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf a)
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ W) A) := IsLocalization.injective A hM
  suffices e : RingHom.ker ψ = W ⊔ Ideal.span {linForm t - 1} by rw [← e]; exact RingHom.ker_isPrime _
  refine le_antisymm (fun g hg => ?_) hle
  obtain ⟨G, D, hG, hGg⟩ :=
    ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) g (ChartLocDomain.linForm_isHomogeneous t)
  have h1 := hle (Ideal.mem_sup_right hGg)
  rw [RingHom.mem_ker, map_sub, (RingHom.mem_ker).mp hg, sub_zero, hhom hG] at h1
  have h2 : algebraMap _ A (Ideal.Quotient.mk W G) = 0 := (hv.pow D).mul_right_eq_zero.mp h1
  have hGW : G ∈ W := Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h2.trans (map_zero _).symm))
  rw [show g = G - (G - g) by ring]
  exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)
end GroundTheory.Heights₂.Heights.SliceComponents
