-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.own_report_transfers
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:27:49.747968+00:00
-- url     : https://prove2.me/submissions/6af2385d-cecd-448c-a195-9d72e878f581

import Definitions.Def_SecondBestTrade_HalfEfficiency_PaymentTransforms

open scoped BigOperators
open SecondBestTrade.HalfEfficiency

noncomputable section

private theorem totalPrior (N : Market) : ∑ v, prior N v = 1 := by
  classical
  simpa [prior, N.mass_sum] using (Fintype.prod_sum N.mass).symm

private theorem expectConst (N : Market) (c : ℝ) : expect N (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, totalPrior, one_mul]

private theorem expectSub (N : Market) (f g : Profile N → ℝ) :
    expect N (fun v => f v - g v) = expect N f - expect N g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

/-- Exchange one agent's two draws in a pair of independent profiles. -/
private def swapDraws (N : Market) (a : Agent N) : Profile N × Profile N ≃ Profile N × Profile N :=
  Function.Involutive.toPerm (fun vw => (overwrite N vw.1 a (vw.2 a), overwrite N vw.2 a (vw.1 a))) (by
    intro ⟨v,w⟩
    apply Prod.ext <;> funext b <;> by_cases h : b = a <;> subst_vars <;>
      simp_all [overwrite, Function.update_of_ne])

private theorem swapWeights (N : Market) (a : Agent N) (v w : Profile N) :
    prior N (overwrite N v a (w a)) * prior N (overwrite N w a (v a)) =
      prior N v * prior N w := by
  classical
  simp only [prior, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b _
  by_cases h : b = a
  · subst b
    simp [overwrite, mul_comm]
  · simp [overwrite, Function.update_of_ne h]

private theorem resample (N : Market) (a : Agent N) (g : Profile N → ℝ) :
    expect N (fun v => expect N (fun w => g (overwrite N w a (v a)))) = expect N g := by
  classical
  let F : Profile N × Profile N → ℝ := fun vw => prior N vw.1 * prior N vw.2 * g vw.2
  calc
    _ = ∑ vw : Profile N × Profile N, F (swapDraws N a vw) := by
      rw [Fintype.sum_prod_type]
      unfold expect
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      change prior N v * (prior N w * g (overwrite N w a (v a))) =
        prior N (overwrite N v a (w a)) * prior N (overwrite N w a (v a)) *
          g (overwrite N w a (v a))
      rw [swapWeights, mul_assoc]
    _ = ∑ vw, F vw := (swapDraws N a).sum_comp F
    _ = expect N g := by
      rw [Fintype.sum_prod_type]
      simp only [F, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, totalPrior, one_mul, expect]

theorem solution (N : Market) (m : SignedMechanism N) (_hx : feasible N m.q) :
    (∀ a t r, U N (ownReport N m) a t r = U N m a t r) ∧
    (∀ a, expect N ((ownReport N m).t a) = expect N (m.t a)) ∧
    (BIC N m → BIC N (ownReport N m)) ∧
    (IR N m → IR N (ownReport N m)) ∧
    (WBB N m → WBB N (ownReport N m)) := by
  classical
  have hu (a : Agent N) (t r : Ty N a) : U N (ownReport N m) a t r = U N m a t r := by
    simp only [U, expectSub, ownReport, ownPayment, overwrite, Function.update_self, expectConst]
  have hp (a : Agent N) : expect N ((ownReport N m).t a) = expect N (m.t a) :=
    resample N a (m.t a)
  refine ⟨hu, hp, fun h a t r => ?_, fun h a t => ?_, fun h => ?_⟩
  · simpa only [hu] using h a t r
  · simpa only [hu] using h a t
  · have interchange (T : Agent N → Profile N → ℝ) :
        expect N (fun v => ∑ a, T a v) = ∑ a, expect N (T a) := by
      unfold expect
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    simpa only [WBB, interchange, hp] using h
