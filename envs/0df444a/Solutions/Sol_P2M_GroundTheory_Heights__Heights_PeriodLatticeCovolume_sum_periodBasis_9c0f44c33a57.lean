-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_sum_periodBasis_9c0f44c33a57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:28.883884+00:00
-- url     : https://prove2.me/submissions/2d736053-d168-4e71-9c27-29819a693f56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodLatticeCovolume

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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.PeriodLatticeCovolume
namespace GroundTheory.Heights₂.Heights.PeriodLatticeCovolume
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a n : Fin g → ℤ) :
    ∑ i, ((Fin.append a n i : ℤ) : ℂ) • periodBasis τ i = intVecC a + τ *ᵥ intVecC n := by
  rw [Fin.sum_univ_add]
  simp only [periodBasis, Fin.append_left, Fin.append_right]
  congr 1
  · ext l
    simp [intVecC, Finset.sum_apply, Pi.single_apply]
  · have hs : ∀ x, ((n x : ℤ) : ℂ) • (τ *ᵥ Pi.single x (1 : ℂ)) =
        τ *ᵥ (((n x : ℤ) : ℂ) • Pi.single x (1 : ℂ)) := fun x => (mulVec_smul _ _ _).symm
    simp only [hs]
    rw [← mulVec_sum]
    congr 1
    ext l
    simp [intVecC, Finset.sum_apply, Pi.single_apply]
end GroundTheory.Heights₂.Heights.PeriodLatticeCovolume
