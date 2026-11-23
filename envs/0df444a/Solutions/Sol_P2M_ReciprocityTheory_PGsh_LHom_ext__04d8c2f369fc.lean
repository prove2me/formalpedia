-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:20.906536+00:00
-- url     : https://prove2.me/submissions/5e3bbaee-94f8-434d-a896-0c8252cf8dcf

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace ReciprocityTheory.PGsh
namespace LHom
theorem _root_.solution {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (AlgHom.ext h)
end LHom
end ReciprocityTheory.PGsh
