-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.moveR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:59.031037+00:00
-- url     : https://prove2.me/submissions/4e524021-8a51-45c2-92a0-38358eb4361c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_swap1
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_ckDw
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_len_wL
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_lie_wL
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


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
theorem _root_.solution {X : B.Mat k r} (hX : B.inLie k r X) : ∀ (u : List (B.Mat k r)), (∀ Y ∈ u, B.inLie k r Y) →
    ∀ {h : B.Mat k r → E}, B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) h →
    ∀ g ∈ B.GV k r, Dx (false, X) (Dw (wL u) h) g = Dw (wL u) (Dx (false, X) h) g
  | [], _, _, _, _, _ => rfl
  | Y :: u, hu, h, hh, g, hg => by
    have hY : B.inLie k r Y := hu Y (by simp)
    have hu' : ∀ Z ∈ u, B.inLie k r Z := fun Z hZ => hu Z (by simp [hZ])
    show Dx (false, X) (Dx (true, Y) (Dw (wL u) h)) g = Dx (true, Y) (Dw (wL u) (Dx (false, X) h)) g
    have h2 : B.CkOn ((2 : ℕ) : ℕ∞) (B.GV k r) (Dw (wL u) h) :=
      ckDw (lie_wL hu') hh (by rw [len_wL]; simp; omega)
    rw [swap1 hX hY (by exact_mod_cast h2) hg]
    have hh' : B.CkOn ((u.length + 1 : ℕ) : ℕ∞) (B.GV k r) h :=
      sCkOn_mono (by exact_mod_cast (by simp : u.length + 1 ≤ (Y :: u).length + 1)) hh
    exact Dx_congr (x := (true, Y)) hY (solution hX u hu' hh') g hg
end PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
