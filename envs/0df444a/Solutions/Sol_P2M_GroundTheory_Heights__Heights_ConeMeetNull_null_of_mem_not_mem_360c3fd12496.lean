-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMeetNull_null_of_mem_not_mem_360c3fd12496
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:39.193404+00:00
-- url     : https://prove2.me/submissions/5293809b-a66d-4d61-8ba4-0549f1826058

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMeetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMeetNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_le_of_add_one_le_succ_12d2e29deaff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_quot_sup_add_one_le_814a859d861d
import Theorems.Thm_UpperTheory_Reformulated_B_Qn14_le_of_add_one_le_succ


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
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeMeetNull
theorem _root_.solution (hZ : ZeroLocusDimH.Statement) {n e : ℕ} (h : HermNorm n)
    (W W' : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime]
    (hW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (g : MvPolynomial (Fin n) ℂ) (hgW' : g ∈ W') (hgW : g ∉ W) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0 := by
  set J : Ideal (MvPolynomial (Fin n) ℂ) := W ⊔ Ideal.span {g} with hJ

  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (e : ℕ) :=
    ZeroLocusDimH.le_of_add_one_le_succ
      ((ZeroLocusDimH.ringKrullDim_quot_sup_add_one_le W g hgW).trans hW)

  let φ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.transpose h.mat).mulVecLin.comp (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hφ : ∀ y, φ y = h.pointOf y := fun _ => rfl
  have hinj : Function.Injective φ := by
    have hu : IsUnit (Matrix.transpose h.mat) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu).comp
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz φ).mp hinj

  have hsub : coneBall h W ∩ coneBall h W' ⊆ φ ⁻¹' {x | ∀ q ∈ J, eval x q = 0} := by
    rintro y ⟨⟨-, hyW⟩, ⟨-, hyW'⟩⟩
    have hle : J ≤ RingHom.ker (eval (h.pointOf y)) := by
      refine sup_le (fun q hq => (RingHom.mem_ker).2 (hyW q hq)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact hyW' g hgW'
    intro q hq
    rw [hφ]
    exact (RingHom.mem_ker).1 (hle hq)
  have hdimH : dimH (coneBall h W ∩ coneBall h W') ≤ 2 * (e : ENNReal) :=
    (dimH_mono hsub).trans ((hK.dimH_preimage_le _).trans (hZ n e J hdim))
  have hlt : dimH (coneBall h W ∩ coneBall h W') < (((2 * (e + 1) : ℕ) : NNReal) : ENNReal) := by
    refine hdimH.trans_lt ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : 2 * e < 2 * (e + 1))
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  exact hausdorffMeasure_of_dimH_lt hlt
end ConeMeetNull
end GroundTheory.Heights₂.Heights
