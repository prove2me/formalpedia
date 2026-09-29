-- Prove2me | solution 1 for VectorSpaceOpt.classical_projection_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:11.753066+00:00
-- url     : https://prove2.me/submissions/e0a10ee4-d6be-4b48-9f12-e25261d5b310

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
    (M : Submodule ℝ H) (hM : IsClosed (M : Set H)) (x : H) :
    ∃! m₀ : H, m₀ ∈ M ∧ ∀ m ∈ M, ‖x - m₀‖ ≤ ‖x - m‖ := by
  have hcomp : IsComplete (M : Set H) := hM.isComplete
  obtain ⟨v, hv, hvinf⟩ := M.exists_norm_eq_iInf_of_complete_subspace hcomp x
  refine ⟨v, ⟨hv, (vsm_best_iff_iInf (M : Set H) x hv).2 hvinf⟩, ?_⟩
  rintro y ⟨hy, hybest⟩
  have o₁ := (vsm_orth_iff_best M x y hy).1 hybest
  have o₀ := (vsm_orth_iff_best M x v hv).1 ((vsm_best_iff_iInf (M : Set H) x hv).2 hvinf)
  have hd : v - y ∈ M := M.sub_mem hv hy
  have key : ⟪v - y, v - y⟫ = (0:ℝ) := by
    have : ⟪(x - y) - (x - v), v - y⟫ = (0:ℝ) := by
      rw [inner_sub_left, o₁ _ hd, o₀ _ hd]; ring
    simpa using this
  have : v - y = 0 := inner_self_eq_zero.1 key
  exact (sub_eq_zero.1 this).symm
