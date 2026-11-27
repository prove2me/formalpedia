-- Prove2me | solution 1 for P2M_GlobalTheory_OnePoint_exists_eq_C_of_eval__eq_zero_f49c21f6d652
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:30.444522+00:00
-- url     : https://prove2.me/submissions/1ab7e613-e614-4cdb-8494-dcd553295460

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_algebraMap_laurentSeries
import Theorems.Thm_GlobalTheory_OnePoint_exists_eq_C_of_isAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution {x : K⸨X⸩} {p : Polynomial K} (hp : p ≠ 0)
    (hx : p.eval₂ (HahnSeries.C : K →+* K⸨X⸩) x = 0) : ∃ c : K, x = HahnSeries.C c :=
  exists_eq_C_of_isAlgebraic ⟨p, hp, by rwa [Polynomial.aeval_def, algebraMap_laurentSeries]⟩
end GlobalTheory.OnePoint
