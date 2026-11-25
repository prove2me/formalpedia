-- Prove2me | solution 1 for QnYLeibnizW.hpart_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:00.920231+00:00
-- url     : https://prove2.me/submissions/b519c756-a7ae-4611-bc12-0a979add152c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule
import Theorems.Thm_QnYLeibnizW_hpart1_skew
import Theorems.Thm_QnYLeibnizW_hpart2_skew
import Theorems.Thm_QnYLeibnizW_hpart_kill
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open QnYLeibnizW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)}
namespace QnYLeibnizW
theorem _root_.solution (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
      inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := GBasic.Hpk_herm k r
  have hHH : Hpk k r * Hpk k r = 1 := GBasic.Hpk_sq k r
  have hs : ∀ a' : Fin r, a'.val < i.val → (esI k r a').val < i.val ∨ 2 * r + k < (esI k r a').val + i.val := by
    intro a' ha'
    right
    have := a'.isLt
    show 2 * r + k < 2 * r + k - a'.val + i.val
    omega
  have he : ∀ a' : Fin r, a'.val < i.val → (eI k r a').val < i.val ∨ 2 * r + k < (eI k r a').val + i.val :=
    fun a' ha' => Or.inl ha'
  constructor
  · unfold inLieLev
    exact ⟨hpart1_skew _ _ hH hHH, fun a' ha' => ⟨(hpart_kill a b _ (he a' ha')).1, (hpart_kill a b _ (hs a' ha')).1⟩⟩
  · unfold inLieLev
    exact ⟨hpart2_skew _ _ hH hHH, fun a' ha' => ⟨(hpart_kill a b _ (he a' ha')).2, (hpart_kill a b _ (hs a' ha')).2⟩⟩
end QnYLeibnizW
