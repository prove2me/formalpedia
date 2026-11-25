-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.hess
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:35.268595+00:00
-- url     : https://prove2.me/submissions/b8624751-6822-4ce2-88e3-b5a6858ec334

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_PositivityTheory_ThKR_Mp_dRho_eval_zero
import Theorems.Thm_GlobalTheory_RealWeil_dRho_comm
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inl
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_dRho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution {s : Mat l} {H : Sch l} (hA : Ann s H) (j k : l) :
    ∑ a, upperParabolic s a j * (∂_{(EuclideanSpace.single a 1 : Eu l)} (∂_{(EuclideanSpace.single k 1 : Eu l)} H)) 0 =
      -(2 * π * I) * loQ s k j * H 0 := by
  have comm : ∀ w, dRho (Pi.single (.inl k) 1) (dRho w H) =
      dRho w (∂_{(EuclideanSpace.single k 1 : Eu l)} H) + (2 * π * I * sympl (Pi.single (.inl k) 1) w : ℂ) • H :=
    fun w => by
      have := congrArg (fun T : Sch l →L[ℂ] Sch l => T H) (dRho_comm (Pi.single (.inl k) 1) w)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply] at this
      rw [← dRho_single_inl, ← this]
      abel
  have hsy : ∀ w : l ⊕ l → ℝ, sympl (Pi.single (.inl k) 1) w = w (.inr k) := fun w => by
    simp [sympl, pPart, qPart, PiLp.inner_apply, Pi.single_apply]
  have hcol : ∀ b c, (s *ᵥ Pi.single b 1) c = s c b := fun b c => by
    simp [mulVec, dotProduct, Pi.single_apply]
  have e := congrArg (fun u : Sch l => dRho (Pi.single (.inl k) 1) u 0) (hA j)
  simp only [map_smul, SchwartzMap.smul_apply, smul_eq_mul, comm, SchwartzMap.add_apply, dRho_eval_zero, hsy,
    hcol] at e
  simp only [upperParabolic, loQ, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  linear_combination e
end PositivityTheory.ThKR.Mp
