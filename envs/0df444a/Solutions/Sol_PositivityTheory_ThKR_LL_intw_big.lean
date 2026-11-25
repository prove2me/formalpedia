-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.intw_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:53.561148+00:00
-- url     : https://prove2.me/submissions/601631b3-4832-4406-a9d6-65e84be0ac7d

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_smul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_intw_ph
import Theorems.Thm_PositivityTheory_ThKR_LL_intw_dil
import Theorems.Thm_PositivityTheory_ThKR_LL_intw_fou
import Theorems.Thm_PositivityTheory_ThKR_LL_intw_fouInv
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {A Ai B C D : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (h1 : ∀ x, A (Ai x) = x) (h2 : ∀ x, Ai (A x) = x)
    (hAC : ∀ y z, ⟪A y, C z⟫ = ⟪C y, A z⟫) (hBD : ∀ y z, ⟪B y, D z⟫ = ⟪D y, B z⟫)
    (hAD : ∀ y z, ⟪A y, D z⟫ - ⟪C y, B z⟫ = ⟪y, z⟫) (c : ℝ) (p q : Eu l) :
    Intw (big Ai B C c) p q (A p + B q) (C p + D q) := by
  have hS : ∀ x y, ⟪x, (C * Ai) y⟫ = ⟪y, (C * Ai) x⟫ := fun x y => by
    have := hAC (Ai x) (Ai y)
    rw [h1, h1] at this
    exact this.trans (real_inner_comm _ _)
  have hr : ∀ q x, ⟪D q - (C * Ai) (B q), x⟫ = ⟪q, Ai x⟫ := fun q x => by
    have := hAD (Ai x) q
    rw [h1] at this
    rw [inner_sub_left, real_inner_comm x, real_inner_comm x, hS, real_inner_comm (Ai x) q, ← this,
      real_inner_comm _ (B q)]
    rfl
  have hT : ∀ x y, ⟪x, (-(Ai * B)) y⟫ = ⟪y, (-(Ai * B)) x⟫ := fun x y => by
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, ContinuousLinearMap.mul_apply (f := Ai), ← hr,
      inner_sub_left]
    rw [← hBD, real_inner_comm (B x) (D y), real_inner_comm (B y), real_inner_comm (B x), hS]
  have e : C p + D q = D q - (C * Ai) (B q) + (C * Ai) (A p + B q) := by
    simp [h2, add_comm]
  rw [e]
  refine (intw_ph hS _ _).mul (((intw_dil h ?_ (hr q)).smul c).mul
    ((intw_fou _ _).mul ((intw_ph hT _ _).mul (intw_fouInv p q))))
  simp [h2, add_comm]
end PositivityTheory.ThKR.LL
