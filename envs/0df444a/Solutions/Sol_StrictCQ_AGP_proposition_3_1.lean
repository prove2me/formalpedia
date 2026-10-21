-- Prove2me | solution 1 for StrictCQ.AGP.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:54:14.624992+00:00
-- url     : https://prove2.me/submissions/70f286c7-f517-4a42-8e76-63414b90936d

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

set_option autoImplicit false
open Filter Topology InnerProductSpace
open StrictCQ.AGP

section ProjLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_le_of_min {S : Set E} (hcv : Convex ℝ S) {z p : E} (hp : p ∈ S)
    (hmin : ∀ w ∈ S, ‖z - p‖ ≤ ‖z - w‖) : ∀ w ∈ S, inner ℝ (z - p) (w - p) ≤ 0 := by
  have hb : BddBelow (Set.range fun w : S => ‖z - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have : ‖z - p‖ = ⨅ w : S, ‖z - (w : E)‖ := by
    have : Nonempty S := ⟨⟨p, hp⟩⟩
    apply le_antisymm
    · exact le_ciInf (fun w => hmin w w.2)
    · exact ciInf_le hb ⟨p, hp⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hcv hp).1 this

lemma min_of_inner_le {S : Set E} (hcv : Convex ℝ S) {z p : E} (hp : p ∈ S)
    (h : ∀ w ∈ S, inner ℝ (z - p) (w - p) ≤ 0) : ∀ w ∈ S, ‖z - p‖ ≤ ‖z - w‖ := by
  have hb : BddBelow (Set.range fun w : S => ‖z - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have := (norm_eq_iInf_iff_real_inner_le_zero hcv hp).2 h
  intro w hw
  rw [this]
  exact ciInf_le hb ⟨w, hw⟩

lemma proj_nonexp {S : Set E} (hcv : Convex ℝ S) {z z' y y' : E} (hy : y ∈ S) (hy' : y' ∈ S)
    (h1 : ∀ w ∈ S, ‖z - y‖ ≤ ‖z - w‖) (h2 : ∀ w ∈ S, ‖z' - y'‖ ≤ ‖z' - w‖) :
    ‖y - y'‖ ≤ ‖z - z'‖ := by
  have a1 := inner_le_of_min hcv hy h1 y' hy'
  have a2 := inner_le_of_min hcv hy' h2 y hy
  have key : ‖y - y'‖ ^ 2 ≤ inner ℝ (z - z') (y - y') := by
    have e1 : inner ℝ (z - y) (y' - y) = - inner ℝ (z - y) (y - y') := by
      rw [← inner_neg_right]; congr 1; abel
    have e2 : inner ℝ (z' - y') (y - y') = inner ℝ (z' - y') (y - y') := rfl
    have e3 : inner ℝ (z - z') (y - y') = inner ℝ (z - y) (y - y') - inner ℝ (z' - y') (y - y')
        + inner ℝ (y - y') (y - y') := by
      rw [← inner_sub_left, ← inner_add_left]; congr 1; abel
    rw [e3, real_inner_self_eq_norm_sq]
    linarith
  have key2 : inner ℝ (z - z') (y - y') ≤ ‖z - z'‖ * ‖y - y'‖ := real_inner_le_norm _ _
  by_cases h0 : ‖y - y'‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖y - y'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith
end ProjLib

theorem solution {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (hne : S.Nonempty)
    (hcl : IsClosed S) (hcv : Convex ℝ S) (x w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) :
    w ∈ normalCone S x ↔ IsProj S (x + w) x := by
  have e : x + w - x = w := by abel
  constructor
  · rintro ⟨_, h⟩
    refine ⟨hx, ?_⟩
    apply min_of_inner_le hcv hx
    intro z hz
    rw [e]; exact h z hz
  · rintro ⟨_, h⟩
    refine ⟨hx, ?_⟩
    intro z hz
    have := inner_le_of_min hcv hx h z hz
    rwa [e] at this
