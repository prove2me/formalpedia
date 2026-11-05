-- Prove2me | solution 1 for StochasticProg.RecourseKKT.normal_cone_firstStageSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T00:58:45.287185+00:00
-- url     : https://prove2.me/submissions/e08f17c1-6c92-46e1-b708-9e665fb5dddf

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_firstStageSet

set_option autoImplicit false

namespace P2MNormalCone

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

/-- Theorem of alternatives over an arbitrary finite variable type. -/
theorem fm_alt' {σ ι : Type} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ) (b : ι → ℝ) :
    (∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  classical
  let e := Fintype.equivFin σ
  rcases fm_alt _ (fun i k => a i (e.symm k)) b with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · left
    refine ⟨fun s => x (e s), fun i => ?_⟩
    rw [Fintype.sum_equiv e _ (fun k => a i (e.symm k) * x k) (fun s => by simp)]
    exact hx i
  · right
    exact ⟨l, h0, fun s => by simpa using h1 (e s), h2⟩


end P2MNormalCone

open Matrix StochasticProg.RecourseKKT in
theorem solution {n1 m1 : ℕ} (A : Matrix (Fin m1) (Fin n1) ℝ)
    (b : Fin m1 → ℝ) (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet A b) :
    {η : Fin n1 → ℝ | ∀ x ∈ firstStageSet A b, 0 ≤ η ⬝ᵥ (x - xs)} =
      {η | ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
        η = Aᵀ *ᵥ lam + mu} := by
  ext η
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hη
    rcases P2MNormalCone.fm_alt' (σ := Fin m1) (ι := Fin n1 ⊕ Fin n1)
      (Sum.elim (fun j k => A k j) (fun j k => -(xs j * A k j)))
      (Sum.elim (fun j => η j) (fun j => -(xs j * η j))) with ⟨lam, hlam⟩ | ⟨l, hl0, hl1, hl2⟩
    · have hT : ∀ j, (Aᵀ *ᵥ lam) j = ∑ k, A k j * lam k := by
        intro j; simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      have h1 : ∀ j, (Aᵀ *ᵥ lam) j ≤ η j := fun j => by
        rw [hT]; simpa using hlam (Sum.inl j)
      have h2 : ∀ j, xs j * η j ≤ xs j * (Aᵀ *ᵥ lam) j := fun j => by
        have := hlam (Sum.inr j)
        simp only [Sum.elim_inr] at this
        rw [hT, Finset.mul_sum]
        have e : ∑ k, -(xs j * A k j) * lam k = -∑ k, xs j * (A k j * lam k) := by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by ring)
        linarith
      refine ⟨lam, η - Aᵀ *ᵥ lam, fun j => ?_, ?_, by simp⟩
      · simp only [Pi.zero_apply, Pi.sub_apply]; linarith [h1 j]
      · simp only [dotProduct]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        have hx := hxs.2 j
        simp only [Pi.zero_apply] at hx
        simp only [Pi.sub_apply]
        exact le_antisymm (by nlinarith [h2 j]) (mul_nonneg (by linarith [h1 j]) hx)
    · exfalso
      let d : Fin n1 → ℝ := fun j => l (Sum.inl j) - l (Sum.inr j) * xs j
      have hAd : A *ᵥ d = 0 := by
        funext k
        have := hl1 k
        rw [Fintype.sum_sum_type] at this
        simp only [Sum.elim_inl, Sum.elim_inr] at this
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, d]
        rw [← this, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hηd : η ⬝ᵥ d < 0 := by
        rw [Fintype.sum_sum_type] at hl2
        simp only [Sum.elim_inl, Sum.elim_inr] at hl2
        have e : η ⬝ᵥ d = ∑ j, l (Sum.inl j) * η j + ∑ j, l (Sum.inr j) * -(xs j * η j) := by
          simp only [dotProduct, d]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [e]; exact hl2
      have hS0 : 0 ≤ ∑ j, l (Sum.inr j) := Finset.sum_nonneg (fun j _ => hl0 (Sum.inr j))
      set S : ℝ := 1 + ∑ j, l (Sum.inr j) with hS
      have hSpos : 0 < S := by linarith
      set t : ℝ := 1 / S with ht
      have htpos : 0 < t := by positivity
      have hle : ∀ j, t * l (Sum.inr j) ≤ 1 := by
        intro j
        have hj : l (Sum.inr j) ≤ ∑ j, l (Sum.inr j) :=
          Finset.single_le_sum (f := fun j => l (Sum.inr j)) (fun j _ => hl0 (Sum.inr j))
            (Finset.mem_univ j)
        rw [ht, div_mul_eq_mul_div, one_mul, div_le_one hSpos]
        linarith
      have hxmem : xs + t • d ∈ firstStageSet A b := by
        refine ⟨?_, fun j => ?_⟩
        · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAd, smul_zero, add_zero]; exact hxs.1
        · have hx := hxs.2 j
          simp only [Pi.zero_apply] at hx
          simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, d]
          have e : xs j + t * (l (Sum.inl j) - l (Sum.inr j) * xs j)
              = xs j * (1 - t * l (Sum.inr j)) + t * l (Sum.inl j) := by ring
          rw [e]
          exact add_nonneg (mul_nonneg hx (sub_nonneg.mpr (hle j)))
            (mul_nonneg htpos.le (hl0 (Sum.inl j)))
      have h := hη _ hxmem
      rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at h
      have := mul_neg_of_pos_of_neg htpos hηd
      linarith
  · rintro ⟨lam, mu, hmu, hmux, rfl⟩ x hx
    have hAx : A *ᵥ (x - xs) = 0 := by rw [Matrix.mulVec_sub, hx.1, hxs.1, sub_self]
    have hlam : (Aᵀ *ᵥ lam) ⬝ᵥ (x - xs) = 0 := by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hAx, dotProduct_zero]
    rw [add_dotProduct, hlam, dotProduct_sub, hmux, zero_add, sub_zero]
    exact dotProduct_nonneg_of_nonneg hmu hx.2
