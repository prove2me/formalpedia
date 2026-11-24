-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.actU_lf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:40.608162+00:00
-- url     : https://prove2.me/submissions/4d57b326-517c-415f-a8e6-ae99f8a33cb3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_X
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_lin_lf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KSplit
theorem _root_.solution (u M : Matrix (Fin m) (Fin m) ℂ) (b : Bool) (a : Fin m) (i : Fin n) :
    actU u (lf b M a i) = lf b (M * am b u) a i :=
  lin_lf (actU u).toLinearMap b _ M a i fun c => actU_X u c i b
end PositivityTheory.SiegelWeilFormula.KSplit
