-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.liftMonomialDeterminantStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:59.641932+00:00
-- url     : https://prove2.me/submissions/a2a9b262-cdee-4c19-bef3-f5b38e01d8ed

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_det_valM_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : LiftMonomialDeterminantStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X D
  exact FrobeniusValuationMatrix.det_valM_ne hS.integers hS.p_lt D
end ReciprocityTheory.PGsh.Up
