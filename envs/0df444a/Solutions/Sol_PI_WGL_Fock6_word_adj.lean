-- Prove2me | solution 1 for PI.WGL.Fock6.word_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:42.807804+00:00
-- url     : https://prove2.me/submissions/954b0ff0-2738-4c4f-84e1-cca835ac5451

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
import Theorems.Thm_PI_WGL_Fock6_applyWord_cons
import Theorems.Thm_PI_WGL_Fock6_applyWord_append
import Theorems.Thm_Formalism_GradedWeylDivisibility_applyWord_cons
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_adjC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
open PI.WGL.Fock6
namespace PI.WGL.Fock6
theorem _root_.solution {r n : ℕ} (w : List (Fin r × Fin r × ℕ)) :
    ∀ F G : MvPolynomial (Fin r × Fin n) ℂ,
      fockF (applyWord ℂ w F) G = fockF F (applyWord ℂ (transposeWord w) G) := by
  induction w with
  | nil => intro F G; rfl
  | cons x w ih =>
    intro F G
    rw [applyWord_cons, Formalism.GradedWeylDivisibility.lfockq_adjC, ih]
    congr 1
    unfold transposeWord
    rw [List.map_cons, List.reverse_cons, applyWord_append]
    rfl
end PI.WGL.Fock6
