-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slt_ofCoords_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:44.907441+00:00
-- url     : https://prove2.me/submissions/33345d9f-7f1a-4a04-ae46-69e31fbd705d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    ofCoords k f x κ = f κ x := rfl
end ReciprocityTheory.ChartRestriction.DS
