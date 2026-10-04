-- Prove2me | solution 1 for VanderbeiLP.StrictComp.complementary_slackness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:11:38.439757+00:00
-- url     : https://prove2.me/submissions/0384b5b3-00f4-4d52-966b-2e1f625aee32

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

set_option autoImplicit false

namespace VLP9dc

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

section LP

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)

lemma strong (hX : ∃ x : Fin n → ℝ, (∀ i, b i ≤ (A *ᵥ x) i) ∧ ∀ j, 0 ≤ x j)
    (hU : ∃ u : Fin m → ℝ, (∀ j, (u ᵥ* A) j ≤ c j) ∧ ∀ i, 0 ≤ u i) :
    ∃ x : Fin n → ℝ, ((∀ i, b i ≤ (A *ᵥ x) i) ∧ ∀ j, 0 ≤ x j) ∧
      ∃ u : Fin m → ℝ, ((∀ j, (u ᵥ* A) j ≤ c j) ∧ ∀ i, 0 ≤ u i) ∧ c ⬝ᵥ x ≤ u ⬝ᵥ b := by
  classical
  rcases fm_alt' (σ := Fin n ⊕ Fin m) (ι := Fin m ⊕ (Fin n ⊕ (Fin n ⊕ (Fin m ⊕ Unit))))
      (Sum.elim (fun i => Sum.elim (fun j => -A i j) 0)
        (Sum.elim (fun j' => Sum.elim (fun j => if j = j' then -1 else 0) 0)
          (Sum.elim (fun j' => Sum.elim 0 (fun i => A i j'))
            (Sum.elim (fun i' => Sum.elim 0 (fun i => if i = i' then -1 else 0))
              (fun _ => Sum.elim c (fun i => -b i))))))
      (Sum.elim (fun i => -b i) (Sum.elim 0 (Sum.elim c (Sum.elim 0 0)))) with
    ⟨z, hz⟩ | ⟨l, h0, h1, h2⟩
  · let x : Fin n → ℝ := fun j => z (Sum.inl j)
    let u : Fin m → ℝ := fun i => z (Sum.inr i)
    refine ⟨x, ⟨fun i => ?_, fun j => ?_⟩, u, ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
    · have := hz (Sum.inl i)
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.mulVec, dotProduct, x]
      linarith
    · have := hz (Sum.inr (Sum.inl j))
      simp [Fintype.sum_sum_type] at this
      simp only [x, Pi.zero_apply]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inl j)))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.vecMul, dotProduct, u]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (z (Sum.inr i)) (A i j))]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      simp [Fintype.sum_sum_type] at this
      simp only [u, Pi.zero_apply]
      linarith
    · have := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, x, u]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm (z (Sum.inr i)) (b i))]
      linarith
  · exfalso
    obtain ⟨x0, hx1, hx2⟩ := hX
    obtain ⟨u0, hu1, hu2⟩ := hU
    let l1 : Fin m → ℝ := fun i => l (Sum.inl i)
    let l3 : Fin n → ℝ := fun j => l (Sum.inr (Sum.inr (Sum.inl j)))
    let τ : ℝ := l (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
    have hl1 : ∀ i, 0 ≤ l1 i := fun i => h0 _
    have hl3 : ∀ j, 0 ≤ l3 j := fun j => h0 _
    have hτ : 0 ≤ τ := h0 _
    have E1 : ∀ j, (l1 ᵥ* A) j ≤ τ * c j := by
      intro j
      have := h1 (Sum.inl j)
      have h2' := h0 (Sum.inr (Sum.inl j))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.vecMul, dotProduct, l1, τ]
      linarith
    have E2 : ∀ i, τ * b i ≤ (A *ᵥ l3) i := by
      intro i
      have := h1 (Sum.inr i)
      have h2' := h0 (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
      simp [Fintype.sum_sum_type] at this
      simp only [Matrix.mulVec, dotProduct, l3, τ]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (A i j) (l (Sum.inr (Sum.inr (Sum.inl j)))))]
      linarith
    have R : c ⬝ᵥ l3 < l1 ⬝ᵥ b := by
      have := h2
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, l1, l3]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (c j) (l (Sum.inr (Sum.inr (Sum.inl j)))))]
      linarith
    -- l1 ⬝ b ≤ τ * (c ⬝ x0)
    have K1 : l1 ⬝ᵥ b ≤ τ * (c ⬝ᵥ x0) := by
      calc l1 ⬝ᵥ b ≤ l1 ⬝ᵥ (A *ᵥ x0) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx1 i) (hl1 i)
        _ = (l1 ᵥ* A) ⬝ᵥ x0 := dotProduct_mulVec l1 A x0
        _ ≤ (τ • c) ⬝ᵥ x0 := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (by simpa using E1 j) (hx2 j)
        _ = τ * (c ⬝ᵥ x0) := by rw [smul_dotProduct, smul_eq_mul]
    have K2 : τ * (u0 ⬝ᵥ b) ≤ c ⬝ᵥ l3 := by
      calc τ * (u0 ⬝ᵥ b) = u0 ⬝ᵥ (τ • b) := by rw [dotProduct_smul, smul_eq_mul]
        _ ≤ u0 ⬝ᵥ (A *ᵥ l3) := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (by simpa using E2 i) (hu2 i)
        _ = (u0 ᵥ* A) ⬝ᵥ l3 := dotProduct_mulVec u0 A l3
        _ ≤ c ⬝ᵥ l3 := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hu1 j) (hl3 j)
    have K3 : τ * (l1 ⬝ᵥ b) ≤ τ * (c ⬝ᵥ l3) := by
      calc τ * (l1 ⬝ᵥ b) = l1 ⬝ᵥ (τ • b) := by rw [dotProduct_smul, smul_eq_mul]
        _ ≤ l1 ⬝ᵥ (A *ᵥ l3) := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (by simpa using E2 i) (hl1 i)
        _ = (l1 ᵥ* A) ⬝ᵥ l3 := dotProduct_mulVec l1 A l3
        _ ≤ (τ • c) ⬝ᵥ l3 := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (by simpa using E1 j) (hl3 j)
        _ = τ * (c ⬝ᵥ l3) := by rw [smul_dotProduct, smul_eq_mul]
    rcases hτ.lt_or_eq with hpos | hzero
    · have := (mul_le_mul_iff_of_pos_left hpos).1 K3
      linarith
    · rw [← hzero] at K1 K2
      simp at K1 K2
      linarith

end LP

open VanderbeiLP.StrictComp in
lemma ident {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    b ⬝ᵥ y - c ⬝ᵥ x = ∑ i, primalSlack A b x i * y i + ∑ j, x j * dualSlack A c y j := by
  have h1 : ∑ i, primalSlack A b x i * y i = (b - A *ᵥ x) ⬝ᵥ y := rfl
  have h2 : ∑ j, x j * dualSlack A c y j = x ⬝ᵥ (Aᵀ *ᵥ y - c) := rfl
  rw [h1, h2, sub_dotProduct, dotProduct_sub, mulVec_transpose, dotProduct_comm x (y ᵥ* A),
    ← dotProduct_mulVec, dotProduct_comm y (A *ᵥ x), dotProduct_comm x c]
  ring

open VanderbeiLP.StrictComp in
lemma weak' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) : c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  have := ident A b c x y
  have : 0 ≤ ∑ i, primalSlack A b x i * y i + ∑ j, x j * dualSlack A c y j :=
    add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hx.2 i) (hy.1 i))
      (Finset.sum_nonneg fun j _ => mul_nonneg (hx.1 j) (hy.2 j))
  linarith

end VLP9dc

open Matrix

open VanderbeiLP.StrictComp in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) :
    (PrimalOptimal A b c x ∧ DualOptimal A b c y) ↔
      ((∀ j, x j * dualSlack A c y j = 0) ∧ ∀ i, primalSlack A b x i * y i = 0) := by
  have hid := VLP9dc.ident A b c x y
  have hS1 : ∀ i ∈ Finset.univ, 0 ≤ primalSlack A b x i * y i :=
    fun i _ => mul_nonneg (hx.2 i) (hy.1 i)
  have hS2 : ∀ j ∈ Finset.univ, 0 ≤ x j * dualSlack A c y j :=
    fun j _ => mul_nonneg (hx.1 j) (hy.2 j)
  constructor
  · rintro ⟨⟨_, hxo⟩, ⟨_, hyo⟩⟩
    -- strong duality for the negated pair
    obtain ⟨x1, ⟨hx1a, hx1b⟩, u1, ⟨hu1a, hu1b⟩, hle⟩ := VLP9dc.strong (-A) (-b) (-c)
      ⟨x, fun i => by
          have := hx.2 i
          simp only [primalSlack, Pi.sub_apply] at this
          simp only [neg_mulVec, Pi.neg_apply]; linarith, hx.1⟩
      ⟨y, fun j => by
          have := hy.2 j
          simp only [dualSlack, Pi.sub_apply, mulVec_transpose] at this
          simp only [vecMul_neg, Pi.neg_apply]; linarith, hy.1⟩
    have hx1 : PrimalFeasible A b x1 := ⟨hx1b, fun i => by
      have := hx1a i
      simp only [neg_mulVec, Pi.neg_apply] at this
      simp only [primalSlack, Pi.sub_apply]; linarith⟩
    have hu1 : DualFeasible A c u1 := ⟨hu1b, fun j => by
      have := hu1a j
      simp only [vecMul_neg, Pi.neg_apply] at this
      simp only [dualSlack, Pi.sub_apply, mulVec_transpose]; linarith⟩
    have e1 := hxo x1 hx1
    have e2 := hyo u1 hu1
    have e3 : b ⬝ᵥ u1 ≤ c ⬝ᵥ x1 := by
      simp only [neg_dotProduct, dotProduct_neg, dotProduct_comm u1 b] at hle
      linarith
    have hsum : ∑ i, primalSlack A b x i * y i + ∑ j, x j * dualSlack A c y j = 0 := by
      have := Finset.sum_nonneg hS1
      have := Finset.sum_nonneg hS2
      linarith
    have hA : ∑ i, primalSlack A b x i * y i = 0 := by
      have := Finset.sum_nonneg hS1
      have := Finset.sum_nonneg hS2
      linarith
    have hB : ∑ j, x j * dualSlack A c y j = 0 := by linarith
    exact ⟨fun j => (Finset.sum_eq_zero_iff_of_nonneg hS2).1 hB j (Finset.mem_univ _),
      fun i => (Finset.sum_eq_zero_iff_of_nonneg hS1).1 hA i (Finset.mem_univ _)⟩
  · rintro ⟨h1, h2⟩
    have hA : ∑ i, primalSlack A b x i * y i = 0 := Finset.sum_eq_zero fun i _ => h2 i
    have hB : ∑ j, x j * dualSlack A c y j = 0 := Finset.sum_eq_zero fun j _ => h1 j
    have heq : b ⬝ᵥ y = c ⬝ᵥ x := by linarith
    refine ⟨⟨hx, fun x' hx' => ?_⟩, ⟨hy, fun y' hy' => ?_⟩⟩
    · have := VLP9dc.weak' A b c x' y hx' hy; linarith
    · have := VLP9dc.weak' A b c x y' hx hy'; linarith
