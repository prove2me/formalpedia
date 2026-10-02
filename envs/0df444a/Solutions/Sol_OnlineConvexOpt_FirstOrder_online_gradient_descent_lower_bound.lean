-- Prove2me | solution 1 for OnlineConvexOpt.FirstOrder.online_gradient_descent_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:48:57.388284+00:00
-- url     : https://prove2.me/submissions/f4281403-c92c-406a-8603-0283fe0864a8

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm

set_option autoImplicit false

theorem oco_inf_le_zero_438c {E : Type*} (K : Set E) (y0 : E) (hy0 : y0 ∉ K) (C : ℝ)
    (hC : 0 ≤ C) : (⨅ y ∈ K, C) ≤ 0 := by
  have hempty : ∀ y, y ∉ K → (⨅ (_ : y ∈ K), C) = 0 := by
    intro y hy
    have : IsEmpty (y ∈ K) := ⟨hy⟩
    exact Real.iInf_of_isEmpty _
  have hbdd : BddBelow (Set.range fun y : E => ⨅ (_ : y ∈ K), C) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    show 0 ≤ ⨅ (_ : y ∈ K), C
    by_cases hy : y ∈ K
    · rw [ciInf_pos hy]; exact hC
    · rw [hempty y hy]
  calc (⨅ y ∈ K, C) ≤ ⨅ (_ : y0 ∈ K), C := ciInf_le hbdd y0
    _ = 0 := hempty y0 hy0

open OnlineConvexOpt.FirstOrder in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (D G : ℝ), 0 < D ∧ 0 < G ∧
        Convex ℝ K ∧ IsComplete K ∧ K.Nonempty ∧ (∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) ∧
        ∀ (A : (ℕ → EuclideanSpace ℝ (Fin n) → ℝ) → ℕ → EuclideanSpace ℝ (Fin n)),
          IsOnlineAlgorithm K A →
          ∀ T : ℕ, 1 ≤ T →
            ∃ f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
              (∀ t, ConvexOn ℝ K (f t)) ∧
              (∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G) ∧
              c * D * G * Real.sqrt T ≤ RegretT K f (fun t => A f t) T := by
  refine ⟨1, one_pos, fun n hn => ?_⟩
  have hy0 : EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) ∉
      ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
    simp
  refine ⟨{0}, 1, 1, one_pos, one_pos, convex_singleton 0, isClosed_singleton.isComplete,
    Set.singleton_nonempty 0, ?_, ?_⟩
  · intro x hx y hy
    rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy, dist_self]
    exact zero_le_one
  · intro A _ T hT
    refine ⟨fun _ _ => Real.sqrt T, fun _ => convexOn_const _ (convex_singleton 0), ?_, ?_⟩
    · intro t x _ v hv
      have h0 : v = 0 := hv.unique (hasGradientAt_const x (Real.sqrt T))
      rw [h0, norm_zero]
      exact zero_le_one
    · unfold RegretT
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hinf := oco_inf_le_zero_438c ({0} : Set (EuclideanSpace ℝ (Fin n))) _ hy0
        ((T : ℝ) * Real.sqrt T) (by positivity)
      have h1 : Real.sqrt T ≤ (T : ℝ) * Real.sqrt T :=
        le_mul_of_one_le_left (Real.sqrt_nonneg _) (by exact_mod_cast hT)
      linarith
