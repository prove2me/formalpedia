-- Prove2me | solution 1 for VanderbeiLP.StrictComp.farkas_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:21:44.945551+00:00
-- url     : https://prove2.me/submissions/e7cd322c-ea9a-499b-b06d-998ea0855d18

import Mathlib

set_option autoImplicit false

namespace FarkasE598

open Matrix

lemma exists_between_fin {ι : Type} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (∃ x : Fin n → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℝ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℝ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℝ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℝ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2


end FarkasE598

open Matrix in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (¬ ∃ x : Fin n → ℝ, A *ᵥ x ≤ b) ↔
      ∃ y : Fin m → ℝ, Aᵀ *ᵥ y = 0 ∧ 0 ≤ y ∧ b ⬝ᵥ y < 0 := by
  constructor
  · intro h
    rcases FarkasE598.fm_alt n (fun i s => A i s) b with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
    · exact absurd ⟨x, fun i => by simpa [Matrix.mulVec, dotProduct] using hx i⟩ h
    · refine ⟨l, ?_, fun i => h0 i, ?_⟩
      · funext s
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
        rw [← h1 s]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      · simp only [dotProduct]
        have : ∑ i, b i * l i = ∑ i, l i * b i :=
          Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        linarith
  · rintro ⟨y, hy1, hy0, hy2⟩ ⟨x, hx⟩
    have hle : ∑ i, (∑ j, A i j * x j) * y i ≤ ∑ i, b i * y i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (by
        have := hx i
        simpa [Matrix.mulVec, dotProduct] using this) (hy0 i))
    have hz : ∑ i, (∑ j, A i j * x j) * y i = 0 := by
      have e : ∑ i, (∑ j, A i j * x j) * y i = ∑ j, x j * ∑ i, A i j * y i := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
      rw [e]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have := congrFun hy1 j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
      rw [this, mul_zero]
    have : b ⬝ᵥ y = ∑ i, b i * y i := rfl
    linarith
