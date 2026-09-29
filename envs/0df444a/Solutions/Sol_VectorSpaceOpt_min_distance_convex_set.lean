-- Prove2me | solution 1 for VectorSpaceOpt.min_distance_convex_set
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:34.303717+00:00
-- url     : https://prove2.me/submissions/92a3f824-076a-4274-9c20-87220d5de78e

import Mathlib
open scoped RealInnerProductSpace

section VSMAux
variable {Hh : Type*} [NormedAddCommGroup Hh] [InnerProductSpace ℝ Hh]

theorem vsm_best_iff_iInf (K : Set Hh) (x : Hh) {v : Hh} (hv : v ∈ K) :
    (∀ w ∈ K, ‖x - v‖ ≤ ‖x - w‖) ↔ ‖x - v‖ = ⨅ w : K, ‖x - w‖ := by
  haveI : Nonempty K := ⟨⟨v, hv⟩⟩
  have hbdd : BddBelow (Set.range fun w : K => ‖x - w‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  exact ⟨fun h => le_antisymm (le_ciInf fun w => h w w.2) (ciInf_le hbdd ⟨v, hv⟩),
    fun h w hw => h ▸ ciInf_le hbdd ⟨w, hw⟩⟩

theorem vsm_best_of_orth (M : Submodule ℝ Hh) (x v : Hh) (hv : v ∈ M)
    (h : ∀ m ∈ M, ⟪x - v, m⟫ = 0) : ∀ m ∈ M, ‖x - v‖ ≤ ‖x - m‖ := by
  intro m hm
  have hsq : ‖x - m‖ ^ 2 = ‖x - v‖ ^ 2 + ‖v - m‖ ^ 2 := by
    have hsplit : x - m = (x - v) + (v - m) := by abel
    rw [hsplit, norm_add_sq_real, h _ (M.sub_mem hv hm)]; ring
  nlinarith [norm_nonneg (x - v), norm_nonneg (x - m), sq_nonneg ‖v - m‖]

theorem vsm_orth_iff_best (M : Submodule ℝ Hh) (x v : Hh) (hv : v ∈ M) :
    (∀ m ∈ M, ‖x - v‖ ≤ ‖x - m‖) ↔ (∀ m ∈ M, ⟪x - v, m⟫ = 0) :=
  ⟨fun h => (Submodule.norm_eq_iInf_iff_real_inner_eq_zero M hv).1
      ((vsm_best_iff_iInf (M : Set Hh) x hv).1 h),
   vsm_best_of_orth M x v hv⟩

end VSMAux


theorem solution {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : Set H) (hK : Convex ℝ K) (hKc : IsClosed K) (hKne : K.Nonempty) (x : H) :
    (∃! k₀ : H, k₀ ∈ K ∧ ∀ k ∈ K, ‖x - k₀‖ ≤ ‖x - k‖) ∧
    (∀ k₀ ∈ K, (∀ k ∈ K, ‖x - k₀‖ ≤ ‖x - k‖) ↔ (∀ k ∈ K, ⟪x - k₀, k - k₀⟫ ≤ 0)) := by
  have hchar : ∀ k₀ ∈ K, ((∀ k ∈ K, ‖x - k₀‖ ≤ ‖x - k‖) ↔ (∀ k ∈ K, ⟪x - k₀, k - k₀⟫ ≤ 0)) :=
    fun k₀ hk₀ => (vsm_best_iff_iInf K x hk₀).trans (norm_eq_iInf_iff_real_inner_le_zero hK hk₀)
  refine ⟨?_, hchar⟩
  obtain ⟨v, hv, hvinf⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKc.isComplete hK x
  refine ⟨v, ⟨hv, (vsm_best_iff_iInf K x hv).2 hvinf⟩, ?_⟩
  rintro w ⟨hw, hwbest⟩
  have c1 : ⟪x - w, v - w⟫ ≤ (0:ℝ) := (hchar w hw).1 hwbest v hv
  have c2 : ⟪x - v, w - v⟫ ≤ (0:ℝ) :=
    (hchar v hv).1 ((vsm_best_iff_iInf K x hv).2 hvinf) w hw
  have hsplit : ⟪v - w, v - w⟫ = ⟪x - w, v - w⟫ - ⟪x - v, v - w⟫ := by
    rw [← inner_sub_left]; congr 1; abel
  have c2' : ⟪x - v, v - w⟫ = -⟪x - v, w - v⟫ := by
    rw [← inner_neg_right]; congr 1; abel
  have key : ⟪v - w, v - w⟫ ≤ (0:ℝ) := by rw [hsplit, c2']; linarith
  have hzero : ⟪v - w, v - w⟫ = (0:ℝ) := le_antisymm key real_inner_self_nonneg
  exact (sub_eq_zero.1 (inner_self_eq_zero.1 hzero)).symm
