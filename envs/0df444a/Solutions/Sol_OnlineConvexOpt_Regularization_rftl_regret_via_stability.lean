-- Prove2me | solution 1 for OnlineConvexOpt.Regularization.rftl_regret_via_stability
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:21:10.76879+00:00
-- url     : https://prove2.me/submissions/0dceae2b-3db7-4e67-afcc-f1250e5e9567

import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.Regularization

lemma aux_rftlrs_inner_le :
    (⨅ y ∈ (Set.univ : Set ℝ), ∑ t ∈ Finset.range 1, (fun (_ : ℕ) (z : ℝ) => Real.cos z) t y)
      ≤ -1 := by
  have hb : BddBelow (Set.range fun y : ℝ =>
      ⨅ (_ : y ∈ (Set.univ : Set ℝ)),
        ∑ t ∈ Finset.range 1, (fun (_ : ℕ) (z : ℝ) => Real.cos z) t y) := by
    refine ⟨-1, ?_⟩
    rintro _ ⟨y, rfl⟩
    simp only [Set.mem_univ, ciInf_pos, Finset.sum_range_one]
    exact Real.neg_one_le_cos y
  refine ciInf_le_of_le hb Real.pi ?_
  simp [Set.mem_univ, ciInf_pos, Real.cos_pi]

lemma aux_rftlrs_diam : RDiameterSq (fun _ : ℝ => (0 : ℝ)) Set.univ = 0 := by
  simp [RDiameterSq]

end OnlineConvexOpt.Regularization

open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (R : E → ℝ) (gradR : E → E) (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ)
    (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (hRbdd : BddAbove (Set.image2 (fun p q => R p - R q) K K)) (T : ℕ),
    RegretT K f x T ≤
      (∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ) + (1 / η) * RDiameterSq R K) := by
  intro h
  have hRun : IsRFTLRun (Set.univ : Set ℝ) (fun _ => 0) 1 (fun _ z => Real.cos z)
      (fun _ => 0) (fun _ => 0) := by
    refine ⟨⟨Set.mem_univ _, fun _ _ => le_rfl⟩, ?_, ?_⟩
    · intro t
      apply HasDerivAt.hasGradientAt'
      simpa using Real.hasDerivAt_cos 0
    · intro t
      refine ⟨Set.mem_univ _, fun y _ => ?_⟩
      simp
  have hbdd : BddAbove (Set.image2 (fun p q => (fun _ : ℝ => (0 : ℝ)) p - (fun _ : ℝ => (0 : ℝ)) q)
      (Set.univ : Set ℝ) Set.univ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, _, q, _, rfl⟩
    simp
  have key := h (E := ℝ) Set.univ (fun _ => 0) (fun _ => 0) 1 one_pos (fun _ z => Real.cos z)
    (fun _ => 0) (fun _ => 0) hRun hbdd 1
  rw [aux_rftlrs_diam] at key
  have hinf := aux_rftlrs_inner_le
  simp only [RegretT] at key
  simp only [Finset.sum_range_one, Real.cos_zero, sub_self, inner_zero_left, mul_zero,
    add_zero] at key hinf
  linarith
