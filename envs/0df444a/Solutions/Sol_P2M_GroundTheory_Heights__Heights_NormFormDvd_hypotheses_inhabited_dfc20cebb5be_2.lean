-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_NormFormDvd_hypotheses_inhabited_dfc20cebb5be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:04:01.459826+00:00
-- url     : https://prove2.me/submissions/29155729-840a-46f0-ad0d-914ff8760e4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace NormFormDvd
theorem _root_.solution :
    Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => (1 : ℚ))) = ⊤ ∧
      ∑ m : Fin 1, (fun _ : Fin 1 => (1 : ℚ)) m • (fun _ : Fin 1 => (1 : ℚ)) m = 1 ∧
      (∑ m : Fin 1, X m * C ((fun _ : Fin 1 => (1 : ℚ)) m)) ∣
        map (algebraMap ℚ ℚ) (X 0 : MvPolynomial (Fin 1) ℚ) := by
  refine ⟨?_, by simp, by simp⟩
  rw [eq_top_iff]
  intro x _
  exact Subalgebra.algebraMap_mem (Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => (1 : ℚ)))) x
end NormFormDvd
end GroundTheory.Heights₂.Heights
