-- Prove2me | solution 1 for PI.Dv.GLatHermW.star_map_cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:07.591377+00:00
-- url     : https://prove2.me/submissions/a1774d7d-0e96-40bc-a7dc-ad2c3c274542

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_StarMapTraceOfPowEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
import Theorems.Thm_PI_Dv_GLatHermW_star_map_trace_rep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLatHermW
theorem _root_.solution (σ : K →+* ℂ) (T : GoodSet K G) (g : G) :
    star (σ (cf T g)) = σ (cf T g⁻¹) := by
  unfold cf
  rw [map_sum, map_sum, star_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_mul, star_mul', star_map_trace_rep σ (T.tau s) g⁻¹, inv_inv]
  congr 1
  rw [map_div₀, map_natCast, map_natCast, star_div₀, star_natCast, star_natCast]
end PI.Dv.GLatHermW
