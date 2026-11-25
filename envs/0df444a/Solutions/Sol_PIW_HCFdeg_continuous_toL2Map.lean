-- Prove2me | solution 1 for PIW.HCFdeg.continuous_toL2Map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:50.522176+00:00
-- url     : https://prove2.me/submissions/c1eed22e-0982-4f14-92f0-2c864f412408

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_ContinuousToL2Map
import Theorems.Thm_PIW_HCFdeg_toL2Map_apply_ae_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory Filter Topology
variable {X H : Type} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
namespace PIW.HCFdeg
theorem _root_.solution [CompleteSpace H] (c : H →ₗ[ℂ] (X → ℂ))
    (hcont : ∀ x, Continuous fun v => c v x) (hL : ∀ v, MemLp (c v) 2 μ) :
    Continuous (toL2Map c hL) := by
  refine LinearMap.continuous_of_seq_closed_graph (g := toL2Map c hL) ?_
  intro u v y hu hy
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, (toL2Map c hL (u n) : X → ℂ) x = c (u n) x :=
    ae_all_iff.2 fun n => toL2Map_apply_ae_eq c hL (u n)
  apply Lp.ext
  filter_upwards [hae, hall, toL2Map_apply_ae_eq c hL v] with x hx hxa hxv
  rw [hxv]
  have h2 : Tendsto (fun i => c (u (ns i)) x) atTop (𝓝 (c v x)) :=
    ((hcont x).tendsto v).comp (hu.comp hns.tendsto_atTop)
  refine tendsto_nhds_unique hx (h2.congr fun i => ?_)
  exact (hxa (ns i)).symm
end PIW.HCFdeg
