-- Prove2me | solution 1 for SolodovSvaiterVI.Alg21.mem_viSol_iff_residual_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:22:11.430904+00:00
-- url     : https://prove2.me/submissions/be414964-8729-4d2a-8dd4-c76db5fec312

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_residual
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
open scoped InnerProductSpace
open SolodovSvaiterVI.Alg21

private theorem projection_spec {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C)
    (x : EuclideanSpace ℝ (Fin n)) :
    projOnto C x ∈ C ∧ ∀ y ∈ C, ⟪x - projOnto C x, y - projOnto C x⟫_ℝ ≤ 0 := by
  letI : Nonempty C := hne.to_subtype
  have hb : BddBelow (Set.range (fun y : C => ‖x - y‖)) := ⟨0, by
    rintro _ ⟨y, rfl⟩
    exact norm_nonneg _⟩
  have he : ∃ p ∈ C, ∀ y ∈ C, ‖x - p‖ ≤ ‖x - y‖ := by
    obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv x
    refine ⟨p, hp, ?_⟩
    intro y hy
    rw [hmin]
    exact ciInf_le hb ⟨y, hy⟩
  have hp : projOnto C x ∈ C ∧ ∀ y ∈ C, ‖x - projOnto C x‖ ≤ ‖x - y‖ := by
    simpa only [projOnto, dif_pos he] using Classical.choose_spec he
  refine ⟨hp.1, (norm_eq_iInf_iff_real_inner_le_zero hcv hp.1).mp ?_⟩
  exact le_antisymm (le_ciInf (fun y => hp.2 y y.2))
    (ciInf_le hb ⟨_, hp.1⟩)

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCne : C.Nonempty) (hCc : IsClosed C)
    (hCcv : Convex ℝ C) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ viSol F C ↔ residual F C x = 0 := by
  obtain ⟨hp, hpi⟩ := projection_spec C hCne hCc hCcv (x - F x)
  constructor
  · intro hx
    obtain ⟨hx, hvi⟩ := hx
    have h1 := hpi x hx
    have h2 := hvi (projOnto C (x - F x)) hp
    have he : x - F x - projOnto C (x - F x) = residual F C x - F x := by
      unfold SolodovSvaiterVI.Alg21.residual
      abel
    rw [he] at h1
    change ⟪residual F C x - F x, residual F C x⟫_ℝ ≤ 0 at h1
    have he2 : projOnto C (x - F x) - x = -residual F C x := by
      unfold SolodovSvaiterVI.Alg21.residual
      abel
    rw [he2, inner_neg_right] at h2
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h1
    have hn : ‖residual F C x‖ = 0 := by nlinarith [norm_nonneg (residual F C x)]
    exact norm_eq_zero.mp hn
  · intro hx
    have he : projOnto C (x - F x) = x := (sub_eq_zero.mp hx).symm
    rw [he] at hp hpi
    refine ⟨hp, ?_⟩
    intro y hy
    have hi := hpi y hy
    have he2 : x - F x - x = -F x := by abel
    rw [he2, inner_neg_left] at hi
    linarith
