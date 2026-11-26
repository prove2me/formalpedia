-- Prove2me | solution 1 for P2M_TunnellMap_OrthogonalFrame_ext__c848da21134f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:26.460788+00:00
-- url     : https://prove2.me/submissions/46ef0a13-259b-415e-910d-38bf461cf87b

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
namespace OrthogonalFrame
theorem _root_.solution {p : Triple} {F G : OrthogonalFrame p}
    (h₁ : F.e₁ = G.e₁) (h₂ : F.e₂ = G.e₂) (h₃ : F.z = G.z) : F = G := by
  cases F; cases G; cases h₁; cases h₂; cases h₃; rfl
end OrthogonalFrame
end TunnellMap
