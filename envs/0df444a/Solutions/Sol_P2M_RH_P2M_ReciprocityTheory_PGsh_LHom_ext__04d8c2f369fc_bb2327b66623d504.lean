-- Prove2me | solution 1 for P2M_RH_P2M_ReciprocityTheory_PGsh_LHom_ext__04d8c2f369fc_bb2327b66623d504
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:17.678795+00:00
-- url     : https://prove2.me/submissions/bc2c2a20-9c30-4d88-b649-48658eaf4162

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace ReciprocityTheory.PGsh
namespace LHom
theorem _root_.solution {R S : LAlg R₀} {f g : LHom R S} (h : ∀ a, f.1 a = g.1 a) : f = g :=
  Subtype.ext (AlgHom.ext h)
end LHom
end ReciprocityTheory.PGsh
