-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.transAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:52.852093+00:00
-- url     : https://prove2.me/submissions/c49a0dd9-6448-4b82-99f2-50fec4a1aa21

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAll
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (_h1 : TensorGl) (h2 : Trans) : TransAll := by
  intro n M _ _ ι _ _ E hE hC l hl ℓ hℓ hW P _ _ lab C _ col b co h1' h2' h3'
  exact TA.main h2 (Fintype.card P) n M ι E hE hC l hl ℓ hℓ hW P rfl lab C col b co h1' h2' h3'
end PositivityTheory.Rg.Cz
