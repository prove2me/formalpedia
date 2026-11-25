-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_evalHom_apply_01d7b863b51a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:46.848643+00:00
-- url     : https://prove2.me/submissions/4fc97285-bc9f-47f0-86b0-89cee6b2e5e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
variable (Y : Scheme.{u}) (n : ℕ)
variable {Y}
namespace GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
theorem _root_.solution {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) (φ : M ⟶ N) :
    evalHom V x φ = (φ.app V).hom x := rfl
end GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
