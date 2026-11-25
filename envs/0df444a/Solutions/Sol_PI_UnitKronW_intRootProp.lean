-- Prove2me | solution 1 for PI.UnitKronW.intRootProp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:04.084264+00:00
-- url     : https://prove2.me/submissions/8716bed9-c78b-42ca-ba0c-b4463c8391b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_IntRootProp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Polynomial
namespace PI.UnitKronW
theorem _root_.solution : IntRootProp := by
  intro E L _ _ _ p hp hc x hx
  have hcoef : ∀ n, (p.map (algebraMap E L)).coeff n ∈
      Set.range (algebraMap (integralClosure ℤ L) L) := by
    intro n
    rw [coeff_map]
    have hmem : algebraMap E L (p.coeff n) ∈ integralClosure ℤ L := by
      rw [mem_integralClosure_iff]
      exact (hc n).map (algebraMap E L).toIntAlgHom
    exact ⟨⟨algebraMap E L (p.coeff n), hmem⟩, rfl⟩
  obtain ⟨r, hr, -, hrm⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_coeff_lifts _).mpr hcoef) (hp.map (algebraMap E L))
  have hxS : IsIntegral (integralClosure ℤ L) x := by
    refine ⟨r, hrm, ?_⟩
    rw [← eval_map, hr]
    exact hx
  exact isIntegral_trans x hxS
end PI.UnitKronW
