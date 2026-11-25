-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_ball_ne_top_7f8ee292491b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:07.844166+00:00
-- url     : https://prove2.me/submissions/f2c4759d-9b46-47b0-8b84-3e3a8ccc1ee0

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_Formalism_REAL_injective_coeMatrix
import Theorems.Thm_Formalism_REAL_isClosed_pseudoUnitary
import Theorems.Thm_Formalism_REAL_isInducing_coeMatrix
import Theorems.Thm_Formalism_REAL_range_coeMatrix
import Theorems.Thm_UpperTheory_Reformulated_B_Qk27_isInducing_coeMatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : muG ε {a | hsG a ≤ rad n} ≠ ⊤ := by

  have hemb : Topology.IsClosedEmbedding (coeMatrixAlt ε) :=
    ⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, by rw [range_coeMatrix]; exact isClosed_pseudoUnitary ε⟩
  set K : Set (Matrix (Fin n) (Fin n) ℂ) := {M | hs M ≤ rad n} with hK
  have hKc : IsClosed K := by
    refine isClosed_le ?_ continuous_const
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact (((continuous_apply j).comp (continuous_apply i)).norm).pow 2
  have hKsub : K ⊆ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      Metric.closedBall (0 : ℂ) (Real.sqrt (rad n)) := by
    intro M hM i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    refine Real.le_sqrt_of_sq_le (le_trans ?_ hM)
    calc ‖M i j‖ ^ 2 ≤ ∑ j', ‖M i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖M i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖M i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖M i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  have hKcomp : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _).of_isClosed_subset
      hKc hKsub
  have hball : {a : UJ ε | hsG a ≤ rad n} = coeMatrixAlt ε ⁻¹' K := rfl
  rw [hball]
  unfold muG
  exact (hemb.isCompact_preimage hKcomp).measure_lt_top.ne
end Formalism.BasicNotions.Examples₂.CD
