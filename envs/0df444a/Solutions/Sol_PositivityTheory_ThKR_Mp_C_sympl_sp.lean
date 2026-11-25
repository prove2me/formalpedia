-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.C.sympl_sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:56.132923+00:00
-- url     : https://prove2.me/submissions/51863319-f37f-4c18-afa2-2b53ab398789

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul
import Theorems.Thm_PositivityTheory_ThKF_E_sympl_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.C
namespace PositivityTheory.ThKR.Mp.C
theorem _root_.solution (s : Sp l) (w w' : l ⊕ l → ℝ) : sympl (s.1 *ᵥ w) (s.1 *ᵥ w') = sympl w w' := by
  have h2 : s.1ᵀ * (Matrix.J l ℝ * s.1) = Matrix.J l ℝ := by
    have := SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem s.2)
    rwa [transpose_transpose, Matrix.mul_assoc] at this
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]
end PositivityTheory.ThKR.Mp.C
