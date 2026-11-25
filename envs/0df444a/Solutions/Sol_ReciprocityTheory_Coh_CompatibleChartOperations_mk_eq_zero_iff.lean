-- Prove2me | solution 1 for ReciprocityTheory.Coh.CompatibleChartOperations.mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:42.597226+00:00
-- url     : https://prove2.me/submissions/30d11198-859c-4d4b-85a2-efe959e7a461

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_ProdHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
open ReciprocityTheory.Coh.CompatibleChartOperations
variable {R : Type u} [CommRing R]
namespace ReciprocityTheory.Coh.CompatibleChartOperations
theorem _root_.solution {A : Cx R} {n : ℕ} (x : A.Z n) :
    (Submodule.Quotient.mk x : A.H n) = 0 ↔ x.1 ∈ A.B n := by
  rw [Submodule.Quotient.mk_eq_zero]; rfl
end ReciprocityTheory.Coh.CompatibleChartOperations
