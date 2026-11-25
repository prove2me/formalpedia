-- Prove2me | solution 1 for PIQnLT.qminorOp_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:38.83098+00:00
-- url     : https://prove2.me/submissions/e9241932-607e-4ab3-a194-ae7311ac9b69

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Theorems.Thm_PIQnLT_Top_lev
import Theorems.Thm_PIQnLT_foldr_ofFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (hL : LevHom)
include hL
namespace PIQnLT
theorem _root_.solution {t : ℕ} (a b : Fin t → Fin (2 * r' + k + 1)) (u : ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    qminorOp (Formalism.FourierDecayAlt.Q.EH k (i + r')) (levPos k i r' ∘ a) (levPos k i r' ∘ b) u F (ιLev k i r' x) =
      qminorOp (Formalism.FourierDecayAlt.Q.EH k r') a b u (fun y => F (ιLev k i r' y)) x := by
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have := foldr_ofFn (fun (G : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E) y =>
      G (ιLev k i r' y))
    (fun j : Fin t => Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k (i + r')) (u - ((j : ℕ) : ℂ)) (levPos k i r' (a (σ j))) (levPos k i r' (b j)))
    (fun j : Fin t => Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k r') (u - ((j : ℕ) : ℂ)) (a (σ j)) (b j))
    (fun j G => funext fun y => Top_lev hL _ _ _ G y) F
  exact congrFun this x
end PIQnLT
