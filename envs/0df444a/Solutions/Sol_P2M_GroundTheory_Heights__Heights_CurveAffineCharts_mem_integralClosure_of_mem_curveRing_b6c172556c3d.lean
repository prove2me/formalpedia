-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integralClosure_of_mem_curveRing_b6c172556c3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:08:16.643311+00:00
-- url     : https://prove2.me/submissions/fec3095e-9a1a-42bd-b113-4ea1dc606ee9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integer_of_mem_chartRingZ_a503b6b08454
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.CurveAffineCharts
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
namespace GroundTheory.Heights₂.Heights.CurveAffineCharts
theorem _root_.solution [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1)
    {b : K'} (hb : b ∈ curveRing y) : b ∈ integralClosure ℤ K' := by
  obtain ⟨t0, ht0⟩ := exists_chart y hy
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' b ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' b hv
    rw [← hr]
    exact r.2
  intro v
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  exact mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _))
    (mem_curveRing.mp hb (fun _ => t) (fun _ => hyt))
end GroundTheory.Heights₂.Heights.CurveAffineCharts
