-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integer_of_mem_chartRingZ_a503b6b08454
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:09.159487+00:00
-- url     : https://prove2.me/submissions/87c40033-266d-4672-a9d8-411a15f2a244

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts

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
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.CurveAffineCharts
theorem _root_.solution [NumberField K'] (v : HeightOneSpectrum (𝓞 K')) (t : T)
    (ht : ∀ u, v.valuation K' (y ⟨(), u⟩) ≤ v.valuation K' (y ⟨(), t⟩)) {b : K'}
    (hb : b ∈ chartRingZ y (fun _ => t)) : b ∈ (v.valuation K').integer := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    rw [Valuation.mem_integer_iff, map_div₀]
    rcases eq_or_ne (v.valuation K' (y ⟨(), t⟩)) 0 with h0 | h0
    · simp [h0]
    · exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (ht u)
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz
end GroundTheory.Heights₂.Heights.CurveAffineCharts
