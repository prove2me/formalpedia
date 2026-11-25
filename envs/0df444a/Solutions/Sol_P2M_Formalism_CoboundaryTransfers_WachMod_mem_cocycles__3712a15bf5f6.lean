-- Prove2me | solution 1 for P2M_Formalism_CoboundaryTransfers_WachMod_mem_cocycles__3712a15bf5f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:33.363434+00:00
-- url     : https://prove2.me/submissions/258c92de-8fe3-4c92-9683-0949ba11fbe9

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_mem_Z1_iff_cocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Formalism.CoboundaryTransfers.WachMod
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)
namespace Formalism.CoboundaryTransfers.WachMod
theorem _root_.solution (pr : D × D) : pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := W.mem_Z1_iff_cocycle pr.1 pr.2
end Formalism.CoboundaryTransfers.WachMod
