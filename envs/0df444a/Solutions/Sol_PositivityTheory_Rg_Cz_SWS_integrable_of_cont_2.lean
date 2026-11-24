-- Prove2me | solution 2 for PositivityTheory.Rg.Cz.SWS.integrable_of_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:48.348272+00:00
-- url     : https://prove2.me/submissions/e25b9e88-73a7-4703-b9fb-ffeb8eb56f11

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
variable {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}
namespace PositivityTheory.Rg.Cz.SWS
theorem _root_.solution [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : MeasureTheory.Measure Γ)
    [MeasureTheory.IsFiniteMeasure μ] {f : Γ → ℂ} (hf : Continuous f) : MeasureTheory.Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
end PositivityTheory.Rg.Cz.SWS
