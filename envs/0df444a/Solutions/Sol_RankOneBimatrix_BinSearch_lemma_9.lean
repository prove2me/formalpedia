-- Prove2me | solution 1 for RankOneBimatrix.BinSearch.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:21:23.242204+00:00
-- url     : https://prove2.me/submissions/042021b0-ac7e-4d8a-9bbf-0af55f437536

import Theorems.Thm_RankOneBimatrix_BinSearch_strong_duality

open Matrix RankOneBimatrix.BinSearch

namespace R1BSL9

variable {m n : ℕ}

lemma rowIneq (A : Matrix (Fin m) (Fin n) ℝ) {x' : Fin m → ℝ} {q : DPoint n}
    (hx : x' ∈ Mixed m) (hq : q ∈ DSet A) : x' ⬝ᵥ (A *ᵥ q.1) ≤ -q.2 := by
  have h4 : x' ⬝ᵥ (A *ᵥ q.1) ≤ ∑ i, x' i * (-q.2) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hq.2 i]) (hx.1 i)
  have h5 : ∑ i, x' i * (-q.2) = -q.2 := by rw [← Finset.sum_mul, hx.2, one_mul]
  linarith

lemma colIneq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ)
    {p : PPoint m n} {y' : Fin n → ℝ} (hp : p ∈ PFeas A b lam) (hy : y' ∈ Mixed n) :
    lam * (b ⬝ᵥ y') - p.1 ⬝ᵥ (A *ᵥ y') ≤ p.2.1 := by
  obtain ⟨_, hs, hc⟩ := hp
  have h1 : p.2.1 = ∑ j, y' j * p.2.1 := by rw [← Finset.sum_mul, hy.2, one_mul]
  have h2 : ∑ j, y' j * (b j * lam - (Aᵀ *ᵥ p.1) j) ≤ ∑ j, y' j * p.2.1 :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by linarith [hc j, hs j]) (hy.1 j)
  have h3 : ∑ j, y' j * (b j * lam - (Aᵀ *ᵥ p.1) j) =
      lam * (b ⬝ᵥ y') - p.1 ⬝ᵥ (A *ᵥ y') := by
    have e1 : ∑ j, y' j * (Aᵀ *ᵥ p.1) j = p.1 ⬝ᵥ (A *ᵥ y') := by
      rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]; rfl
    have e2 : ∑ j, y' j * (b j * lam) = lam * (b ⬝ᵥ y') := by
      simp only [dotProduct, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [← e1, ← e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  linarith

lemma weak (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ)
    {p : PPoint m n} {q : DPoint n} (hp : p ∈ PFeas A b lam) (hq : q ∈ DSet A) :
    DValue b lam q ≤ p.2.1 := by
  have := colIneq A b lam hp hq.1
  have := rowIneq A hp.1 hq
  unfold DValue; linarith

lemma opt_of_eq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ)
    {p : PPoint m n} {q : DPoint n} (hp : p ∈ PFeas A b lam) (hq : q ∈ DSet A)
    (heq : p.2.1 = DValue b lam q) : p ∈ POpt A b lam ∧ q ∈ Yopt A b lam := by
  refine ⟨⟨hp, ⟨p, hp, rfl⟩, ?_⟩, ⟨hq, ⟨q, hq, rfl⟩, ?_⟩⟩
  · rintro _ ⟨p', hp', rfl⟩
    rw [heq]; exact weak A b lam hp' hq
  · rintro _ ⟨q', hq', rfl⟩
    rw [← heq]; exact weak A b lam hp hq'

lemma payB (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ)
    {x : Fin m → ℝ} (hx : x ∈ Mixed m) (y : Fin n → ℝ) :
    x ⬝ᵥ ((-A + onesLam lam b) *ᵥ y) = -(x ⬝ᵥ (A *ᵥ y)) + lam * (b ⬝ᵥ y) := by
  have hc : (onesLam lam b : Matrix (Fin m) (Fin n) ℝ) *ᵥ y = fun _ => lam * (b ⬝ᵥ y) := by
    ext i
    simp only [onesLam, mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have : x ⬝ᵥ (fun (_ : Fin m) => lam * (b ⬝ᵥ y)) = lam * (b ⬝ᵥ y) := by
    simp only [dotProduct]; rw [← Finset.sum_mul, hx.2, one_mul]
  rw [add_mulVec, dotProduct_add, hc, this, neg_mulVec, dotProduct_neg]

lemma payR (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    x ⬝ᵥ (rankOneB A a b *ᵥ y) = -(x ⬝ᵥ (A *ᵥ y)) + (x ⬝ᵥ a) * (b ⬝ᵥ y) := by
  have hc : (vecMulVec a b : Matrix (Fin m) (Fin n) ℝ) *ᵥ y = fun i => a i * (b ⬝ᵥ y) := by
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have : x ⬝ᵥ (fun i => a i * (b ⬝ᵥ y)) = (x ⬝ᵥ a) * (b ⬝ᵥ y) := by
    simp only [dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [rankOneB, add_mulVec, dotProduct_add, hc, this, neg_mulVec, dotProduct_neg]

end R1BSL9

open R1BSL9 in
theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (lam : ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (IsNE A (-A + onesLam lam b) x y ↔
      ∃ (t v : ℝ) (s : Fin n → ℝ),
        (y, t) ∈ Yopt A b lam ∧ (x, v, s) ∈ POpt A b lam ∧
        (∀ t' : ℝ, (y, t') ∈ Yopt A b lam → t' = t) ∧
        (∀ (v' : ℝ) (s' : Fin n → ℝ),
          (x, v', s') ∈ POpt A b lam → v' = v ∧ s' = s) ∧
        -t = x ⬝ᵥ (A *ᵥ y) ∧
        v = x ⬝ᵥ ((-A + onesLam lam b) *ᵥ y)) ∧
    (∀ (t v : ℝ) (s : Fin n → ℝ),
      (y, t) ∈ Yopt A b lam → (x, v, s) ∈ POpt A b lam →
      x ⬝ᵥ a = lam →
      IsNE A (rankOneB A a b) x y ∧
        -t = x ⬝ᵥ (A *ᵥ y) ∧
        v = x ⬝ᵥ ((rankOneB A a b) *ᵥ y)) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨hx, hy, hrow, hcol⟩
    set t : ℝ := -(x ⬝ᵥ (A *ᵥ y)) with ht
    set v : ℝ := x ⬝ᵥ ((-A + onesLam lam b) *ᵥ y) with hv
    let s : Fin n → ℝ := fun j => (Aᵀ *ᵥ x) j + v - b j * lam
    have hq : ((y, t) : DPoint n) ∈ DSet A := by
      refine ⟨hy, fun i => ?_⟩
      have h := hrow (Pi.single i 1) (single_mem_stdSimplex ℝ i)
      rw [single_dotProduct, one_mul] at h
      show (A *ᵥ y) i + t ≤ 0
      linarith
    have hp : ((x, v, s) : PPoint m n) ∈ PFeas A b lam := by
      refine ⟨hx, fun j => ?_, fun j => by simp only [s]; ring⟩
      have h := hcol (Pi.single j 1) (single_mem_stdSimplex ℝ j)
      rw [payB A b lam hx, dotProduct_single, mul_one] at h
      have e : x ⬝ᵥ (A *ᵥ Pi.single j 1) = (Aᵀ *ᵥ x) j := by
        rw [dotProduct_mulVec, mulVec_transpose, dotProduct_single, mul_one]
      show 0 ≤ (Aᵀ *ᵥ x) j + v - b j * lam
      linarith
    have heq : ((x, v, s) : PPoint m n).2.1 = DValue b lam (y, t) := by
      show v = lam * (b ⬝ᵥ y) + t
      rw [hv, payB A b lam hx, ht]; ring
    obtain ⟨hpo, hqo⟩ := opt_of_eq A b lam hp hq heq
    refine ⟨t, v, s, hqo, hpo, fun t' ht' => ?_, fun v' s' hps => ?_, by rw [ht, neg_neg], rfl⟩
    · have := hqo.2.unique ht'.2
      simp only [DValue] at this; linarith
    · have hvv : v' = v := hps.2.unique hpo.2
      refine ⟨hvv, funext fun j => ?_⟩
      have := hps.1.2.2 j
      simp only [s]; simp only at this; rw [← hvv]; linarith
  · rintro ⟨t, v, s, hyt, hpv, -, -, ht, hv⟩
    have hx : x ∈ Mixed m := hpv.1.1
    refine ⟨hx, hyt.1.1, fun x' hx' => ?_, fun y' hy' => ?_⟩
    · have := rowIneq A hx' hyt.1; simp only at this; linarith
    · have := colIneq A b lam hpv.1 hy'
      simp only at this
      rw [payB A b lam hx, payB A b lam hx]
      rw [payB A b lam hx] at hv; linarith
  · intro t v s hyt hpv hxa
    obtain ⟨p0, hp0, q0, hq0, he⟩ :=
      RankOneBimatrix.BinSearch.strong_duality hm hn A b lam
    have h1 : v = p0.2.1 := hpv.2.unique hp0.2
    have h2 : DValue b lam (y, t) = DValue b lam q0 := hyt.2.unique hq0.2
    have hval : v = lam * (b ⬝ᵥ y) + t := by
      rw [h1, he, ← h2]; rfl
    have hx : x ∈ Mixed m := hpv.1.1
    have c1 := colIneq A b lam hpv.1 hyt.1.1
    have c2 := rowIneq A hx hyt.1
    simp only at c1 c2
    have hxy : -t = x ⬝ᵥ (A *ᵥ y) := by linarith
    refine ⟨⟨hx, hyt.1.1, fun x' hx' => ?_, fun y' hy' => ?_⟩, hxy, ?_⟩
    · have := rowIneq A hx' hyt.1; simp only at this; linarith
    · have := colIneq A b lam hpv.1 hy'
      simp only at this
      rw [payR, payR, hxa]; linarith
    · rw [payR, hxa]; linarith
