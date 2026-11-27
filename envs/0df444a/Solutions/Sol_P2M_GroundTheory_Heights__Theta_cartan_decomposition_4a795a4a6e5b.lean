-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_cartan_decomposition_4a795a4a6e5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:12:12.407584+00:00
-- url     : https://prove2.me/submissions/9417033f-091a-4287-a296-86216a494ca1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {p q : ℕ}
local notation "𝔐" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "J" => indefJ p q
local notation "G" => indefiniteUnitaryGroup p q
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (g : G) :
    ∃! ks : maxCompact G × cartanPos p q,
      (((ks.1 : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) * ks.2.1 = ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) := by
  refine ⟨cartanHomeomorph.symm g, ?_, fun ks hks => ?_⟩
  · exact congrArg (fun x : G => ((x : GL (Fin p ⊕ Fin q) ℂ) : 𝔐))
      (cartanHomeomorph.apply_symm_apply g)
  · apply cartanHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (Units.ext hks)
end GroundTheory.Heights₂.Theta
