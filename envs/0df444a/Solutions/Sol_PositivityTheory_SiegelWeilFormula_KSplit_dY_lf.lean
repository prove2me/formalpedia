-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.dY_lf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:45.786711+00:00
-- url     : https://prove2.me/submissions/4cb5413f-0114-44c8-add3-3e5c9ab9ac11

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_lin_lf
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_X

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
theorem _root_.solution (Y M : Matrix (Fin m) (Fin m) ℂ) (b : Bool) (a : Fin m) (i : Fin n) :
    dY Y (lf b M a i) = lf b (M * dm b Y) a i :=
  lin_lf (dY Y : Derivation ℂ (PX m n) (PX m n)).toLinearMap b _ M a i fun c => dY_X Y c i b
end PositivityTheory.SiegelWeilFormula.KSplit
