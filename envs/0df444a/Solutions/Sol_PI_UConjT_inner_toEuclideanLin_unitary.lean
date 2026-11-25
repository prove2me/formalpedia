-- Prove2me | solution 1 for PI.UConjT.inner_toEuclideanLin_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:25.641262+00:00
-- url     : https://prove2.me/submissions/c000c915-ef19-4227-91a8-ac229b9f6932

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix
namespace PI.UConjT
theorem _root_.solution {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (hg : gᴴ * g = 1)
    (x y : EuclideanSpace ℂ (Fin m)) :
    inner ℂ (Matrix.toEuclideanLin g x) (Matrix.toEuclideanLin g y) = inner ℂ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec,
    dotProduct_comm]
end PI.UConjT
