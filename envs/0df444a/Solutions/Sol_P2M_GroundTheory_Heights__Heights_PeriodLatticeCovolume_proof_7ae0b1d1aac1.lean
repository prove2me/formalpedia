-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_proof_7ae0b1d1aac1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:25.517476+00:00
-- url     : https://prove2.me/submissions/8cd7217d-cfee-4c6d-bb01-6dba2a708dbc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodLatticeCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_hermPair_comb_de07ed4153bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_sum_periodBasis_9c0f44c33a57

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
open PeriodLatticeCovolume
namespace GroundTheory.Heights₂.Heights
namespace PeriodLatticeCovolume
theorem _root_.solution : PeriodLatticeCovolume.Statement := by
  intro g τ k v hv hind
  choose a n han using hv
  let N : Matrix (Fin (g + g)) (Fin k) ℤ := fun i j => Fin.append (a j) (n j) i
  have hN : ∀ j, v j = ∑ i, (N i j : ℂ) • periodBasis τ i := fun j => by
    rw [han j]
    exact (sum_periodBasis τ (a j) (n j)).symm
  refine ⟨N, hN, ?_, ?_⟩
  · intro c hc
    rw [Fintype.linearIndependent_iff] at hind
    funext j
    refine hind c ?_ j
    have : ∀ j, c j • v j = ∑ i, ((c j : ℂ) * (N i j : ℂ)) • periodBasis τ i := fun j => by
      rw [hN j, ← Int.cast_smul_eq_zsmul ℂ, Finset.smul_sum]
      simp only [smul_smul]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_smul]
    have hi := congrFun hc i
    simp only [mulVec, dotProduct, Pi.zero_apply] at hi
    have : ∑ j, (c j : ℂ) * (N i j : ℂ) = ((∑ j, N i j * c j : ℤ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this, hi]
    simp
  · unfold covolume
    congr 2
    ext j l
    rw [Matrix.of_apply, hN j, hN l]
    have h1 : ∀ j, ∑ i, (N i j : ℂ) • periodBasis τ i
        = ∑ i, (((N i j : ℝ)) : ℂ) • periodBasis τ i := fun j => by
      simp
    rw [h1 j, h1 l, hermPair_comb]
    simp only [intGram, mul_apply, transpose_apply, map_apply, periodGram, Matrix.of_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    ring
end PeriodLatticeCovolume
end GroundTheory.Heights₂.Heights
