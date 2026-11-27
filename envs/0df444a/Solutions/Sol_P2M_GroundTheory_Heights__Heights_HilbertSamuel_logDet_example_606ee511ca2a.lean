-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_logDet_example_606ee511ca2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:18.028403+00:00
-- url     : https://prove2.me/submissions/df04f529-26fa-46b1-9eee-3493abdef173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt MeasureTheory Module Filter
  Topology Asymptotics Matrix
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution :
    (∀ t : ℝ, (diagonal fun _ : Fin 2 ↦ ((Real.exp t : ℝ) : ℂ)).PosDef) ∧
    ∀ (t : ℝ) (i j : Fin 2),
      HasDerivAt (fun s : ℝ ↦ diagonal (fun _ : Fin 2 ↦ ((Real.exp s : ℝ) : ℂ)) i j)
        (diagonal (fun _ : Fin 2 ↦ ((Real.exp t : ℝ) : ℂ)) i j) t := by
  refine ⟨fun t ↦ PosDef.diagonal fun _ ↦ Complex.zero_lt_real.mpr (Real.exp_pos t),
    fun t i j ↦ ?_⟩
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq]
    exact (Real.hasDerivAt_exp t).ofReal_comp
  · simp only [diagonal_apply_ne _ hij]
    exact hasDerivAt_const t 0
end GroundTheory.Heights₂.Heights.HilbertSamuel
