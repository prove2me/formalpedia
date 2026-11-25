-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.u4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:43:57.858104+00:00
-- url     : https://prove2.me/submissions/a8d8eab4-eaab-45a7-9459-3057071842ff

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Theorems.Thm_ReciprocityTheory_PGsh_Up_claim_all
import Theorems.Thm_ReciprocityTheory_PGsh_Up_colengthCotangentBoundStatement_of_claim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : ColengthCotangentBoundStatement := by
  apply colengthCotangentBoundStatement_of_claim
  intro p _ C _ _ _ v R _ _ hv hvp N _ _ _ hN AA
  exact claim_all p C v R hv hvp (Fintype.card N) N rfl hN AA
end ReciprocityTheory.PGsh.Up
