-- Prove2me | solution 1 for ObsCostMDP.WellPosed.proposition_3_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:25:59.005015+00:00
-- url     : https://prove2.me/submissions/373ff195-7a0f-489e-ad21-404410c89d7e

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_Truncated

open ObsCostMDP.WellPosed in
theorem solution {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (Ft : TDriver N X A) (β : ℝ) (hFt : Property35 Ft β)
    (Q : Fin N → Matrix X X ℝ) (hQ : IsSubstochasticT Q)
    (c : A → X → ℝ) (pen : ℝ → ℝ) (hpen : IsPenalty pen) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (u v : Fin N → X → A → ℝ)
    (hsub : IsPenSubsolution Ft Q c pen ρ u) (hsup : IsPenSupersolution Ft Q c pen ρ v) :
    ∀ n l a, u n l a ≤ v n l a := by
  intro n l a
  by_contra hlt
  push_neg at hlt
  obtain ⟨⟨nb, lb, ab⟩, hmax⟩ :=
    Finite.exists_max (fun p : Fin N × X × A => u p.1 p.2.1 p.2.2 - v p.1 p.2.1 p.2.2)
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = u nb lb ab - v nb lb ab := ⟨_, rfl⟩
  have hm : ∀ n l a, u n l a - v n l a ≤ δ := fun n l a => hδdef ▸ hmax (n, l, a)
  have hδ : 0 < δ := lt_of_lt_of_le (sub_pos.mpr hlt) (hm n l a)
  have h35 := hFt.2 u v nb lb ab (fun n l a => hδdef ▸ hm n l a) (hδdef ▸ hδ.le)
  have hs := hsub nb lb ab
  have hv := hsup nb lb ab
  unfold penResidual at hs hv
  have hI : tInspection Q c u nb lb ≤ tInspection Q c v nb lb + δ := by
    unfold tInspection
    have hy : ∀ y, actMax (fun a => u 0 y a - c a y) ≤ actMax (fun a => v 0 y a - c a y) + δ := by
      intro y
      unfold actMax
      apply Finset.sup'_le
      intro a _
      have h1 := hm 0 y a
      have h2 : v 0 y a - c a y ≤
          Finset.univ.sup' Finset.univ_nonempty (fun a => v 0 y a - c a y) :=
        Finset.le_sup' (fun a => v 0 y a - c a y) (Finset.mem_univ a)
      linarith
    have hsum : ∑ y, Q nb lb y * δ ≤ δ := by
      rw [← Finset.sum_mul]
      have := (hQ nb).2 lb
      nlinarith
    calc ∑ y, Q nb lb y * actMax (fun a => u 0 y a - c a y)
        ≤ ∑ y, (Q nb lb y * actMax (fun a => v 0 y a - c a y) + Q nb lb y * δ) :=
          Finset.sum_le_sum fun y _ => by
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left (hy y) ((hQ nb).1 lb y)
      _ ≤ ∑ y, Q nb lb y * actMax (fun a => v 0 y a - c a y) + δ := by
          rw [Finset.sum_add_distrib]
          linarith
  have hp : pen (tInspection Q c u nb lb - u nb lb ab) ≤ pen (tInspection Q c v nb lb - v nb lb ab) :=
    hpen.2.1 (by linarith)
  have hρp := mul_le_mul_of_nonneg_left hp hρ
  have hβδ : 0 < β * δ := mul_pos hFt.1 hδ
  rw [← hδdef] at h35
  linarith
