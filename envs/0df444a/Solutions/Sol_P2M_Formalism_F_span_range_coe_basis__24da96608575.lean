-- Prove2me | solution 1 for P2M_Formalism_F_span_range_coe_basis__24da96608575
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:52.569167+00:00
-- url     : https://prove2.me/submissions/bcbc966b-5e59-462f-8009-954570cdce53

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution {E : Type*} [AddCommGroup E] (L : Submodule ℤ E) {ι : Type*}
    (b : Basis ι ℤ L) : span ℤ (Set.range (fun i => (b i : E))) = L := by
  have h1 : (Set.range fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp L.subtype b
  rw [h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
end Formalism.F
