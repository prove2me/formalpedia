-- Prove2me | solution 1 for VanderbeiLP.StrictComp.strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:01:27.480849+00:00
-- url     : https://prove2.me/submissions/c3ac613b-91e4-4a07-8c3f-4a3187813fe9

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair

set_option autoImplicit false

namespace VB9bc

open Matrix

def PolyNonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, b i ≤ (A.mulVec x) i) ∧ 0 ≤ x}

def DualPoly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) : Set (Fin m → ℝ) :=
  {u | (∀ j, Matrix.vecMul u A j ≤ c j) ∧ 0 ≤ u}

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

lemma weak {x : Fin n → ℝ} {u : Fin m → ℝ} (hx : x ∈ PolyNonneg A b)
    (hu : u ∈ DualPoly A c) : u ⬝ᵥ b ≤ c ⬝ᵥ x := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hu1, hu2⟩ := hu
  calc u ⬝ᵥ b ≤ u ⬝ᵥ (A *ᵥ x) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx1 i) (hu2 i)
    _ = (u ᵥ* A) ⬝ᵥ x := dotProduct_mulVec u A x
    _ ≤ c ⬝ᵥ x := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hu1 j) (hx2 j)

lemma primal_unbdd (hX : (PolyNonneg A b).Nonempty)
    (hU : ¬ (DualPoly A c).Nonempty) :
    ∀ M : ℝ, ∃ x ∈ PolyNonneg A b, c ⬝ᵥ x < M := by
  classical
  rcases fm_alt' (σ := Fin m) (ι := Fin n ⊕ Fin m)
      (Sum.elim (fun j i => A i j) (fun i' i => if i = i' then -1 else 0)) (Sum.elim c 0) with
    ⟨u, hu⟩ | ⟨l, h0, h1, h2⟩
  · exfalso
    apply hU
    refine ⟨u, fun j => ?_, fun i => ?_⟩
    · have := hu (Sum.inl j)
      simpa [Matrix.vecMul, dotProduct, mul_comm] using this
    · have := hu (Sum.inr i)
      simp at this
      simpa using this
  · let d : Fin n → ℝ := fun j => l (Sum.inl j)
    have hd0 : ∀ j, 0 ≤ d j := fun j => h0 _
    have hAd : ∀ i, 0 ≤ (A *ᵥ d) i := by
      intro i
      have := h1 i
      simp [Fintype.sum_sum_type] at this
      have e : (A *ᵥ d) i = l (Sum.inr i) := by
        simp only [Matrix.mulVec, dotProduct, d]
        rw [Finset.sum_congr rfl (fun j _ => mul_comm (A i j) (l (Sum.inl j)))]
        linarith
      rw [e]; exact h0 _
    have hcd : c ⬝ᵥ d < 0 := by
      have := h2
      simp [Fintype.sum_sum_type] at this
      simp only [dotProduct, d]
      rw [Finset.sum_congr rfl (fun j _ => mul_comm (c j) (l (Sum.inl j)))]
      exact this
    intro M
    obtain ⟨x0, hx1, hx2⟩ := hX
    set δ := -(c ⬝ᵥ d) with hδ
    have hδ0 : 0 < δ := by linarith
    set t := (|c ⬝ᵥ x0| + |M| + 1) / δ with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) hδ0.le
    have htd : t * δ = |c ⬝ᵥ x0| + |M| + 1 := div_mul_cancel₀ _ hδ0.ne'
    refine ⟨x0 + t • d, ⟨fun i => ?_, fun j => ?_⟩, ?_⟩
    · rw [mulVec_add, mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx1 i, hAd i, mul_nonneg ht0 (hAd i)]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact add_nonneg (hx2 j) (mul_nonneg ht0 (hd0 j))
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have h3 : t * (c ⬝ᵥ d) = -(|c ⬝ᵥ x0| + |M| + 1) := by rw [← htd, hδ]; ring
      rw [h3]
      have := le_abs_self (c ⬝ᵥ x0)
      have := neg_abs_le M
      linarith

lemma strong (hX : (PolyNonneg A b).Nonempty)
    (hU : (DualPoly A c).Nonempty) :
    ∃ x ∈ PolyNonneg A b, ∃ u ∈ DualPoly A c,
      c ⬝ᵥ x ≤ u ⬝ᵥ b := by
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

open VanderbeiLP.StrictComp

lemma pf_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    PrimalFeasible A b x ↔ x ∈ PolyNonneg (-A) (-b) := by
  simp only [PrimalFeasible, primalSlack, PolyNonneg, Set.mem_setOf_eq, Pi.sub_apply,
    Pi.neg_apply, neg_mulVec, sub_nonneg, neg_le_neg_iff]
  exact ⟨fun h => ⟨h.2, fun j => h.1 j⟩, fun h => ⟨fun j => h.2 j, h.1⟩⟩

lemma df_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) :
    DualFeasible A c y ↔ y ∈ DualPoly (-A) (-c) := by
  simp only [DualFeasible, dualSlack, DualPoly, Set.mem_setOf_eq, Pi.sub_apply,
    vecMul_neg, Pi.neg_apply, mulVec_transpose, sub_nonneg, neg_le_neg_iff]
  exact ⟨fun h => ⟨h.2, fun j => h.1 j⟩, fun h => ⟨fun j => h.2 j, h.1⟩⟩

lemma weak' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {x : Fin n → ℝ} {y : Fin m → ℝ} (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) :
    c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  have := weak (-A) (-b) (-c) ((pf_iff A b x).1 hx) ((df_iff A c y).1 hy)
  rw [dotProduct_neg, neg_dotProduct, dotProduct_comm] at this
  linarith

end VB9bc

open Matrix in
open VanderbeiLP.StrictComp in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (xstar : Fin n → ℝ) (hx : PrimalOptimal A b c xstar) :
    ∃ ystar : Fin m → ℝ, DualOptimal A b c ystar ∧ c ⬝ᵥ xstar = b ⬝ᵥ ystar := by
  obtain ⟨hxf, hxo⟩ := hx
  have hX : (VB9bc.PolyNonneg (-A) (-b)).Nonempty := ⟨xstar, (VB9bc.pf_iff A b xstar).1 hxf⟩
  have hU : (VB9bc.DualPoly (-A) (-c)).Nonempty := by
    by_contra hU
    obtain ⟨x, hxm, hlt⟩ := VB9bc.primal_unbdd (-A) (-b) (-c) hX hU ((-c) ⬝ᵥ xstar)
    have := hxo x ((VB9bc.pf_iff A b x).2 hxm)
    rw [neg_dotProduct, neg_dotProduct] at hlt
    linarith
  obtain ⟨x, hxm, u, hum, hle⟩ := VB9bc.strong (-A) (-b) (-c) hX hU
  have hxF := (VB9bc.pf_iff A b x).2 hxm
  have huF := (VB9bc.df_iff A c u).2 hum
  have h1 := VB9bc.weak' A b c hxf huF
  have h2 := hxo x hxF
  rw [neg_dotProduct, dotProduct_neg, dotProduct_comm u b] at hle
  have heq : c ⬝ᵥ xstar = b ⬝ᵥ u := by linarith
  refine ⟨u, ⟨huF, fun y' hy' => ?_⟩, heq⟩
  have := VB9bc.weak' A b c hxf hy'
  linarith
