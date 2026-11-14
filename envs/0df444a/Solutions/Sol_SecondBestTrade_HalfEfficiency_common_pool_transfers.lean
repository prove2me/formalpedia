-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.common_pool_transfers
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:27:51.133207+00:00
-- url     : https://prove2.me/submissions/ec28f5e2-91f6-401c-a2f8-c856f7f9ee09

import Definitions.Def_SecondBestTrade_HalfEfficiency_PaymentTransforms

open scoped BigOperators
open SecondBestTrade.HalfEfficiency

noncomputable section

set_option maxHeartbeats 2000000 in
private theorem expectMarginal (N : Market) (a : Agent N) (f : Ty N a → ℝ) :
    expect N (fun v => f (v a)) = ∑ t, N.mass a t * f t := by
  classical
  let q : ∀ b : Agent N, Ty N b → ℝ := Function.update (fun _ _ => 1) a f
  have prodVal (v : Profile N) : (∏ b, q b (v b)) = f (v a) := by
    calc
      _ = ∏ b, (if b = a then f (v a) else 1) := by
        apply Finset.prod_congr rfl
        intro b _
        by_cases h : b = a
        · subst b; simp [q]
        · simp [q, h]
      _ = _ := by simp
  calc
    _ = ∑ v : Profile N, ∏ b, N.mass b (v b) * q b (v b) := by
      simp only [expect, prior, Finset.prod_mul_distrib, prodVal]
    _ = ∏ b, ∑ t, N.mass b t * q b t := (Fintype.prod_sum (fun (b : Agent N) (t : Ty N b) => N.mass b t * q b t)).symm
    _ = ∏ b, (if b = a then ∑ t, N.mass a t * f t else 1) := by
      apply Finset.prod_congr rfl
      intro b _
      by_cases h : b = a
      · subst b; simp [q]
      · simp [q, h, N.mass_sum]
    _ = _ := by simp

private theorem expectSum (N : Market) {ι : Type} [Fintype ι] (g : ι → Profile N → ℝ) :
    expect N (fun v => ∑ i, g i v) = ∑ i, expect N (g i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

private theorem zeroWeights {ι : Type} [Fintype ι] {T : ι → Type} [∀ i, Fintype (T i)]
    (w p : ∀ i, T i → ℝ) (hw : ∀ i t, 0 < w i t) (hp : ∀ i t, 0 ≤ p i t)
    (h : ∑ i, ∑ t, w i t * p i t = 0) : ∀ i t, p i t = 0 := by
  intro i t
  have hn (j) (s) := mul_nonneg (hw j s).le (hp j s)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg (fun s _ => hn j s))).mp h i (Finset.mem_univ i)
  have hit := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hn i s)).mp hi t (Finset.mem_univ t)
  exact (mul_eq_zero.mp hit).resolve_left (hw i t).ne'

private theorem expectScaled (N : Market) (c d : ℝ) (g : Profile N → ℝ) :
    expect N (fun v => c * g v / d) = c * expect N g / d := by
  unfold expect
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem solution (N : Market) (p : ∀ a, Ty N a → ℝ)
    (hp : ∀ a t, 0 ≤ p a t)
    (hbalance : poolSize N p = ∑ j : Fin N.ns, ∑ t,
      N.mass (.inr j) t * p (.inr j) t) :
    ∃ q : Agent N → Profile N → ℝ, poolCorrect N p q ∧
      (0 < poolSize N p → q = poolTransfers N p) ∧
      (poolSize N p = 0 → (∀ a t, p a t = 0) ∧ q = fun _ _ => 0) := by
  classical
  by_cases hz : poolSize N p = 0
  · have hpz (a : Agent N) (t : Ty N a) : p a t = 0 := by
      cases a with
      | inl i => exact zeroWeights _ _ (fun i => N.mass_pos (.inl i)) (fun i => hp (.inl i)) hz i t
      | inr j => exact zeroWeights _ _ (fun j => N.mass_pos (.inr j)) (fun j => hp (.inr j)) (hbalance.symm.trans hz) j t
    refine ⟨fun _ _ => 0, ?_, fun h => (h.ne' hz).elim, fun _ => ⟨hpz, rfl⟩⟩
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro a r
    cases a <;> simp [expect, hpz]
  · have hpos : 0 < poolSize N p := lt_of_le_of_ne
        (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun t _ =>
           mul_nonneg (N.mass_pos _ _).le (hp _ _)))) (Ne.symm hz)
    have bnn (v : Profile N) : 0 ≤ buyerTotal N p v := Finset.sum_nonneg fun i _ => hp _ _
    have snn (v : Profile N) : 0 ≤ sellerTotal N p v := Finset.sum_nonneg fun j _ => hp _ _
    have eb : expect N (buyerTotal N p) = poolSize N p := by
      change expect N (fun v => ∑ i : Fin N.nb, p (.inl i) (v (.inl i))) = _
      rw [expectSum N (fun i v => p (.inl i) (v (.inl i)))]
      exact Finset.sum_congr rfl (fun i _ => expectMarginal N (.inl i) (p (.inl i)))
    have es : expect N (sellerTotal N p) = poolSize N p := by
      change expect N (fun v => ∑ j : Fin N.ns, p (.inr j) (v (.inr j))) = _
      rw [expectSum N (fun j v => p (.inr j) (v (.inr j))), hbalance]
      exact Finset.sum_congr rfl (fun j _ => expectMarginal N (.inr j) (p (.inr j)))
    refine ⟨poolTransfers N p, ?_, fun _ => rfl, fun h => (hz h).elim⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i v
      simpa [poolTransfers, hz] using div_nonneg (mul_nonneg (hp _ _) (snn v)) hpos.le
    · intro j v
      simpa [poolTransfers, hz] using div_nonneg (mul_nonneg (hp _ _) (bnn v)) hpos.le
    · intro v
      rw [Fintype.sum_sum_type]
      simp only [poolTransfers, if_neg hz, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib,
        ← Finset.sum_div, ← Finset.sum_mul]
      change buyerTotal N p v * sellerTotal N p v / _ + -(sellerTotal N p v * buyerTotal N p v / _) = 0
      ring
    · intro a r
      cases a with
      | inl i =>
        change expect N _ = p (.inl i) r
        have he (v : Profile N) : sellerTotal N p (overwrite N v (.inl i) r) = sellerTotal N p v := by
          simp [sellerTotal, overwrite, Function.update_of_ne]
        simp only [poolTransfers, if_neg hz, Sum.elim_inl, he]
        simp only [overwrite, Function.update_self]
        rw [expectScaled, es, mul_div_cancel_right₀ _ hz]
      | inr j =>
        change expect N _ = -p (.inr j) r
        have he (v : Profile N) : buyerTotal N p (overwrite N v (.inr j) r) = buyerTotal N p v := by
          simp [buyerTotal, overwrite, Function.update_of_ne]
        simp only [poolTransfers, if_neg hz, Sum.elim_inr, he]
        simp only [overwrite, Function.update_self, ← neg_div, ← neg_mul]
        rw [expectScaled, eb, mul_div_cancel_right₀ _ hz]
