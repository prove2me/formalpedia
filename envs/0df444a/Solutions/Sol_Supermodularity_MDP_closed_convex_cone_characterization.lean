-- Prove2me | solution 1 for Supermodularity.MDP.closed_convex_cone_characterization
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:16:06.277505+00:00
-- url     : https://prove2.me/submissions/67ea93c9-4887-482e-b9b7-60c34d906638

import Mathlib

open MeasureTheory

namespace Supermodularity.MDP

/-- The cone of pointwise nonnegative functions on `T`. -/
def aux_ccc_V {m : ℕ} (T : Set (Fin m → ℝ)) : Set (T → ℝ) := {f | ∀ t, 0 ≤ f t}

lemma aux_ccc_closed {m : ℕ} (T : Set (Fin m → ℝ)) : IsClosed (aux_ccc_V T) := by
  have : aux_ccc_V T = ⋂ t : T, {f : T → ℝ | 0 ≤ f t} := by
    ext f; simp [aux_ccc_V]
  rw [this]
  exact isClosed_iInter fun t => isClosed_le continuous_const (continuous_apply t)

end Supermodularity.MDP

open Supermodularity.MDP

open MeasureTheory

theorem solution : ¬ (∀ {m n : ℕ} (T : Set (Fin m → ℝ))
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ)) (V : Set (T → ℝ))
    (hVclosed : IsClosed V)
    (hVadd : ∀ ⦃f g : T → ℝ⦄, f ∈ V → g ∈ V → f + g ∈ V)
    (hVsmul : ∀ ⦃f : T → ℝ⦄, f ∈ V → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • f ∈ V),
    (∀ ⦃S : Set (Fin n → ℝ)⦄, IsUpperSet S →
        (fun t : T => (μ (t : Fin m → ℝ) S).toReal) ∈ V) ↔
      (∀ ⦃h : (Fin n → ℝ) → ℝ⦄, Monotone h →
        (∀ t : T, Integrable h (μ (t : Fin m → ℝ))) →
        (fun t : T => ∫ w, h w ∂ (μ (t : Fin m → ℝ))) ∈ V)) := by
  intro H
  have key := @H 0 0 Set.univ (fun _ => Measure.dirac 0) (aux_ccc_V Set.univ)
    (aux_ccc_closed Set.univ)
    (fun f g hf hg t => add_nonneg (hf t) (hg t))
    (fun f hf c hc t => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hc (hf t))
  have lhs : ∀ ⦃S : Set (Fin 0 → ℝ)⦄, IsUpperSet S →
      (fun t : (Set.univ : Set (Fin 0 → ℝ)) =>
        ((Measure.dirac (0 : Fin 0 → ℝ)) S).toReal) ∈ aux_ccc_V Set.univ :=
    fun S _ t => ENNReal.toReal_nonneg
  have rhs := key.mp lhs (h := fun _ => (-1 : ℝ)) monotone_const
    (fun t => integrable_const _)
  have := rhs ⟨0, Set.mem_univ _⟩
  simp at this
  linarith
