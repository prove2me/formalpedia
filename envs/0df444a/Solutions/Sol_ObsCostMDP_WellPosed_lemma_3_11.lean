-- Prove2me | solution 1 for ObsCostMDP.WellPosed.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:11:27.376569+00:00
-- url     : https://prove2.me/submissions/d85906f2-4cdd-4de4-9e50-7297fa954a2d

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_Truncated

open ObsCostMDP.WellPosed in
theorem solution {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (Ft : TDriver N X A) (β : ℝ) (hFt : Property35 Ft β)
    (Q : Fin N → Matrix X X ℝ) (hQ : IsSubstochasticT Q)
    (c : A → X → ℝ) (hc : ∀ a l, 0 ≤ c a l) (pen : ℝ → ℝ) (hpen : IsPenalty pen)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (u : Fin N → X → A → ℝ) (hu : IsPenSolution Ft Q c pen ρ u)
    (K : ℝ) (hK : ∀ a n l, |Ft a (fun _ _ _ => 0) n l| ≤ K) :
    ∀ n l a, |u n l a| ≤ K / β := by
  intro n l a
  have hβ := hFt.1
  obtain ⟨pM, hpM⟩ := Finite.exists_max (fun p : Fin N × X × A => u p.1 p.2.1 p.2.2)
  obtain ⟨pm, hpm⟩ := Finite.exists_min (fun p : Fin N × X × A => u p.1 p.2.1 p.2.2)
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _)
    (hK (Classical.arbitrary A) 0 (Classical.arbitrary X))
  have hKb : 0 ≤ K / β := div_nonneg hK0 hβ.le
  have hpent : ∀ t ≤ 0, pen t = 0 := hpen.2.2.1
  have hpen0 : ∀ t, 0 ≤ pen t := by
    intro t
    rcases le_or_gt t 0 with h | h
    · rw [hpent t h]
    · exact (hpen.2.2.2 t h).le
  have hFeq : ∀ n l a, Ft a u n l = ρ * pen (tInspection Q c u n l - u n l a) := by
    intro n l a
    have := hu n l a
    unfold penResidual at this
    linarith
  have hup : u n l a ≤ K / β := by
    have hle : u n l a ≤ u pM.1 pM.2.1 pM.2.2 := hpM (n, l, a)
    rcases le_or_gt (u pM.1 pM.2.1 pM.2.2) 0 with h | h
    · linarith
    · have hP := hFt.2 u (fun _ _ _ => 0) pM.1 pM.2.1 pM.2.2
        (fun n' l' a' => by
          show u n' l' a' - 0 ≤ u pM.1 pM.2.1 pM.2.2 - 0
          linarith [hpM (n', l', a')])
        (by show (0:ℝ) ≤ u pM.1 pM.2.1 pM.2.2 - 0; linarith)
      have hins : tInspection Q c u pM.1 pM.2.1 ≤ u pM.1 pM.2.1 pM.2.2 := by
        unfold tInspection
        calc ∑ y, Q pM.1 pM.2.1 y * actMax (fun a => u 0 y a - c a y)
            ≤ ∑ y, Q pM.1 pM.2.1 y * u pM.1 pM.2.1 pM.2.2 := by
              refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_
                ((hQ pM.1).1 pM.2.1 y)
              refine Finset.sup'_le _ _ fun a' _ => ?_
              have h1 : u 0 y a' ≤ u pM.1 pM.2.1 pM.2.2 := hpM (0, y, a')
              have := hc a' y
              show u 0 y a' - c a' y ≤ u pM.1 pM.2.1 pM.2.2
              linarith
          _ = (∑ y, Q pM.1 pM.2.1 y) * u pM.1 pM.2.1 pM.2.2 := (Finset.sum_mul _ _ _).symm
          _ ≤ 1 * u pM.1 pM.2.1 pM.2.2 :=
              mul_le_mul_of_nonneg_right ((hQ pM.1).2 pM.2.1) h.le
          _ = u pM.1 pM.2.1 pM.2.2 := one_mul _
      rw [hFeq, hpent _ (by linarith), mul_zero] at hP
      have hk := (abs_le.mp (hK pM.2.2 pM.1 pM.2.1)).1
      rw [le_div_iff₀ hβ]
      have : β * (u pM.1 pM.2.1 pM.2.2 - 0) ≤ 0 - Ft pM.2.2 (fun _ _ _ => 0) pM.1 pM.2.1 := hP
      nlinarith
  have hlow : -u n l a ≤ K / β := by
    have hle : u pm.1 pm.2.1 pm.2.2 ≤ u n l a := hpm (n, l, a)
    rcases le_or_gt 0 (u pm.1 pm.2.1 pm.2.2) with h | h
    · linarith
    · have hP := hFt.2 (fun _ _ _ => 0) u pm.1 pm.2.1 pm.2.2
        (fun n' l' a' => by
          show 0 - u n' l' a' ≤ 0 - u pm.1 pm.2.1 pm.2.2
          linarith [hpm (n', l', a')])
        (by show (0:ℝ) ≤ 0 - u pm.1 pm.2.1 pm.2.2; linarith)
      rw [hFeq] at hP
      have hk := (abs_le.mp (hK pm.2.2 pm.1 pm.2.1)).2
      have hp0 := mul_nonneg hρ (hpen0 (tInspection Q c u pm.1 pm.2.1 - u pm.1 pm.2.1 pm.2.2))
      rw [le_div_iff₀ hβ]
      have : β * (0 - u pm.1 pm.2.1 pm.2.2) ≤ Ft pm.2.2 (fun _ _ _ => 0) pm.1 pm.2.1
          - ρ * pen (tInspection Q c u pm.1 pm.2.1 - u pm.1 pm.2.1 pm.2.2) := hP
      nlinarith
  exact abs_le.mpr ⟨by linarith, hup⟩
