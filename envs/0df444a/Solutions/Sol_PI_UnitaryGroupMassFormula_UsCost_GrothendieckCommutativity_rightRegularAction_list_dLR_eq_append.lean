-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.rightRegularAction_list_dLR_eq_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:15.989809+00:00
-- url     : https://prove2.me/submissions/62c71861-302b-49bd-95f5-64b93e1e9f42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_ckDw
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_len_wR
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_lie_wR
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_moveR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNACG
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNS
namespace PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
theorem _root_.solution {f : B.Mat k r → E} {m : ℕ} (hf : B.CkOn (m : ℕ∞) (B.GV k r) f) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.inLie k r X) (hv : ∀ X ∈ v, B.inLie k r X) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → u.length + v.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, B.Rw w (B.dLR u v f) g = B.dLR u (w ++ v) f g
  | [], _, _, _, _ => rfl
  | X :: w, hw, hm, g, hg => by
    have hX : B.inLie k r X := hw X (by simp)
    have hw' : ∀ Z ∈ w, B.inLie k r Z := fun Z hZ => hw Z (by simp [hZ])
    have hm' : u.length + v.length + w.length ≤ m := by simp at hm; omega
    have e1 : ∀ F : B.Mat k r → E, Formalism.REAL.RdV X F = Dx (false, X) F := fun F => by simp [Dx]
    show Formalism.REAL.RdV X (B.Rw w (B.dLR u v f)) g = B.dLR u (X :: (w ++ v)) f g
    rw [e1, Dx_congr (x := (false, X)) hX (solution hf u v hu hv w hw' hm') g hg]
    simp only [dLR_eq, Dw_append, Dw_wR]
    have hck : B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) (B.Rw (w ++ v) f) := by
      rw [← Dw_wR]
      refine ckDw (lie_wR ?_) hf ?_
      · intro Z hZ
        rcases List.mem_append.mp hZ with h | h
        · exact hw' Z h
        · exact hv Z h
      · rw [len_wR, List.length_append]; simp at hm; omega
    rw [moveR hX u hu hck g hg]
    rfl
end PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
