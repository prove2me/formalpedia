-- Prove2me | solution 1 for RankOneBimatrix.BinSearch.strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:19:49.644991+00:00
-- url     : https://prove2.me/submissions/11e53185-7cf8-42b4-9ba2-40cf9840a4a5

import Theorems.Thm_MatousekLP_ZeroSum_minimax_theorem
import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm

open Matrix RankOneBimatrix.BinSearch

namespace R1BSSD

variable {m n : ℕ}

/-- Weak duality between `Pλ` and `Dλ`. -/
lemma weak (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ)
    {p : PPoint m n} {q : DPoint n} (hp : p ∈ PFeas A b lam) (hq : q ∈ DSet A) :
    DValue b lam q ≤ p.2.1 := by
  obtain ⟨⟨hx0, hx1⟩, hs, hc⟩ := hp
  obtain ⟨⟨hy0, hy1⟩, hD⟩ := hq
  have h1 : p.2.1 = ∑ j, q.1 j * p.2.1 := by rw [← Finset.sum_mul, hy1, one_mul]
  have h2 : ∑ j, q.1 j * (b j * lam - (Aᵀ *ᵥ p.1) j) ≤ ∑ j, q.1 j * p.2.1 :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by linarith [hc j, hs j]) (hy0 j)
  have h3 : ∑ j, q.1 j * (b j * lam - (Aᵀ *ᵥ p.1) j) =
      lam * (b ⬝ᵥ q.1) - p.1 ⬝ᵥ (A *ᵥ q.1) := by
    have e1 : ∑ j, q.1 j * (Aᵀ *ᵥ p.1) j = p.1 ⬝ᵥ (A *ᵥ q.1) := by
      rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]; rfl
    have e2 : ∑ j, q.1 j * (b j * lam) = lam * (b ⬝ᵥ q.1) := by
      simp only [dotProduct, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [← e1, ← e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h4 : p.1 ⬝ᵥ (A *ᵥ q.1) ≤ ∑ i, p.1 i * (-q.2) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hD i]) (hx0 i)
  have h5 : ∑ i, p.1 i * (-q.2) = -q.2 := by rw [← Finset.sum_mul, hx1, one_mul]
  unfold DValue
  linarith

/-- If a feasible primal point and a feasible dual point have equal objective values,
both are optimal. -/
lemma opt_of_eq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ)
    {p : PPoint m n} {q : DPoint n} (hp : p ∈ PFeas A b lam) (hq : q ∈ DSet A)
    (heq : p.2.1 = DValue b lam q) : p ∈ POpt A b lam ∧ q ∈ Yopt A b lam := by
  refine ⟨⟨hp, ⟨p, hp, rfl⟩, ?_⟩, ⟨hq, ⟨q, hq, rfl⟩, ?_⟩⟩
  · rintro _ ⟨p', hp', rfl⟩
    rw [heq]; exact weak A b lam hp' hq
  · rintro _ ⟨q', hq', rfl⟩
    rw [← heq]; exact weak A b lam hp hq'

end R1BSSD

open R1BSSD in
theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    ∃ p ∈ POpt A b lam, ∃ q ∈ Yopt A b lam, p.2.1 = DValue b lam q := by
  classical
  let M : Matrix (Fin m) (Fin n) ℝ := A - Matrix.of (fun _ j => lam * b j)
  obtain ⟨⟨xt, hxt⟩, ⟨yt, hyt⟩, hne, -⟩ := MatousekLP.ZeroSum.minimax_theorem hm hn M
  obtain ⟨⟨hxS, hxBR⟩, hyS, hyBR⟩ := hne xt yt hxt hyt
  have hpay : ∀ x y, x ∈ stdSimplex ℝ (Fin m) →
      MatousekLP.ZeroSum.payoff M x y = x ⬝ᵥ (A *ᵥ y) - lam * (b ⬝ᵥ y) := by
    intro x y hx
    have hc : (Matrix.of (fun (_ : Fin m) j => lam * b j)) *ᵥ y = fun _ => lam * (b ⬝ᵥ y) := by
      ext i
      simp only [mulVec, dotProduct, of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have : x ⬝ᵥ (fun (_ : Fin m) => lam * (b ⬝ᵥ y)) = lam * (b ⬝ᵥ y) := by
      simp only [dotProduct]; rw [← Finset.sum_mul, hx.2, one_mul]
    simp only [MatousekLP.ZeroSum.payoff, M, sub_mulVec, dotProduct_sub, hc, this]
  set w := xt ⬝ᵥ (A *ᵥ yt) with hw
  let q : DPoint n := (yt, -w)
  let v : ℝ := lam * (b ⬝ᵥ yt) - w
  let p : PPoint m n := (xt, v, fun j => (Aᵀ *ᵥ xt) j + v - b j * lam)
  have hq : q ∈ DSet A := by
    refine ⟨hyS, fun i => ?_⟩
    have h := hxBR (Pi.single i 1) (single_mem_stdSimplex ℝ i)
    rw [hpay _ _ (single_mem_stdSimplex ℝ i), hpay _ _ hxS, single_dotProduct, one_mul] at h
    show (A *ᵥ yt) i + -w ≤ 0
    linarith
  have hp : p ∈ PFeas A b lam := by
    refine ⟨hxS, fun j => ?_, fun j => by simp only [p]; ring⟩
    have h := hyBR (Pi.single j 1) (single_mem_stdSimplex ℝ j)
    rw [hpay _ _ hxS, hpay _ _ hxS, dotProduct_single, mul_one] at h
    have e : xt ⬝ᵥ (A *ᵥ Pi.single j 1) = (Aᵀ *ᵥ xt) j := by
      rw [dotProduct_mulVec, mulVec_transpose, dotProduct_single, mul_one]
    show 0 ≤ (Aᵀ *ᵥ xt) j + v - b j * lam
    simp only [v]
    linarith
  have heq : p.2.1 = DValue b lam q := by
    simp only [p, q, v, DValue]; ring
  obtain ⟨hpo, hqo⟩ := opt_of_eq A b lam hp hq heq
  exact ⟨p, hpo, q, hqo, heq⟩
