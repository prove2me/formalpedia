-- Prove2me | solution 1 for ShrinkingUCB.boundary_terms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:37:22.786218+00:00
-- url     : https://prove2.me/submissions/a895ce12-c38e-4347-9030-30dae2dccb70

import Definitions.Def_ShrinkingUCB_ConfidenceBounds

open ShrinkingUCB in
theorem solution {d N : ℕ} (K T : ℕ) (I : LinearSemiBandit d N)
    (tb : TieBreak N) {α : ℝ} (hα : 0 ≤ α) (o : OutcomeTable N)
    (Sstar : Finset (Fin N)) (hS : Sstar.card = K) :
    (ConfidenceHolds I tb α K o T → ∑ i ∈ Sstar, LCB I tb α K o (T + 1) i ≤ K) ∧
    ∑ i ∈ Sstar, -LCB I tb α K o 1 i ≤ α * K := by
  refine ⟨fun hC => ?_, ?_⟩
  · calc ∑ i ∈ Sstar, LCB I tb α K o (T + 1) i ≤ ∑ i ∈ Sstar, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => le_trans
            (hC (T + 1) (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩) i).1 (I.mean_le_one i))
      _ = K := by rw [Finset.sum_const, hS]; simp
  · have hθ : theta I tb α K o 1 = 0 := by
      unfold theta
      simp [runState]
    have hA : innerA I tb α K o 1 0 = 1 := by
      unfold innerA
      simp [selections, runState]
    have hΔ : ∀ i, Delta I tb α K o 1 0 i ≤ 1 := by
      intro i
      unfold Delta
      rw [hA, inv_one, Matrix.one_mulVec]
      exact I.x_norm_le i
    calc ∑ i ∈ Sstar, -LCB I tb α K o 1 i ≤ ∑ i ∈ Sstar, α :=
          Finset.sum_le_sum (fun i _ => by
            unfold LCB
            rw [hθ, dotProduct_zero]
            nlinarith [mul_le_mul_of_nonneg_left (hΔ i) hα])
      _ = α * K := by rw [Finset.sum_const, hS, nsmul_eq_mul]; ring
