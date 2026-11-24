-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.reIx_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:25.8141+00:00
-- url     : https://prove2.me/submissions/65956fd3-6fca-484c-aed8-60a699dca8b3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution {P Q : Type} (e : P ≃ Q) (c : ℂ) (ξ : TV n M P) : reIx e (c • ξ) = c • reIx e ξ := rfl
end PositivityTheory.Rg.Cz.CtrX
