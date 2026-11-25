-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawBasic_volume_firstRow_mem_1fba3e2dc8f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:18:09.422459+00:00
-- url     : https://prove2.me/submissions/96f6a2af-0a4d-4504-b0dd-35220fc5b691

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawBasic

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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawBasic
namespace GroundTheory.Heights₂.Heights.SphereLawBasic
theorem _root_.solution (N : ℕ) (S : Submodule ℂ (Fin N → ℂ)) (hS : S ≠ ⊤) :
    volume {u : Fin 1 × Fin N → ℂ | firstRow N u ∈ S} = 0 := by
  let T : Submodule ℝ (Fin 1 × Fin N → ℂ) := (S.restrictScalars ℝ).comap (firstRow N)
  have hT : T ≠ ⊤ := by
    intro h
    apply hS
    rw [eq_top_iff]
    intro v _
    let u : Fin 1 × Fin N → ℂ := fun ij ↦ v ij.2
    have hu : u ∈ T := h ▸ Submodule.mem_top
    exact hu
  exact Measure.addHaar_submodule volume T hT
end GroundTheory.Heights₂.Heights.SphereLawBasic
