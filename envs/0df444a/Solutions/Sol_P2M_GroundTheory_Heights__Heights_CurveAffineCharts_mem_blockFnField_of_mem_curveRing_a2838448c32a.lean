-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_blockFnField_of_mem_curveRing_a2838448c32a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:46.63644+00:00
-- url     : https://prove2.me/submissions/72de4832-c5b5-4a86-a20a-cf9377a2cf99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14
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
    {b : K'} (hb : b ∈ curveRing y) : b ∈ blockFnField y := by
  obtain ⟨t, ht⟩ := exists_chart y hy
  have hbt := mem_curveRing.mp hb (fun _ => t) (fun _ => ht)
  clear hb
  induction hbt using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz
end GroundTheory.Heights₂.Heights.CurveAffineCharts
