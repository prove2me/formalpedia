-- Prove2me | solution 1 for TwoEchelonVRP.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T07:47:30.543526+00:00
-- url     : https://prove2.me/submissions/36b8b382-1c31-43e3-8604-fb2b6764ca38

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_zF
import Definitions.Def_TwoEchelonVRP_zLF
import Definitions.Def_TwoEchelonVRP_MultFeasible
import Definitions.Def_TwoEchelonVRP_zRF
import Definitions.Def_TwoEchelonVRP_rfSup

set_option autoImplicit false

namespace TECcc0

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

/-- Affine Farkas lemma for a system `x ≥ 0, a x ≤ b` whose solutions all have cost `≥ v`. -/
theorem farkas_nn {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq ι] (a : ι → σ → ℝ)
    (b : ι → ℝ) (c : σ → ℝ) (v : ℝ)
    (hfeas : ∃ x : σ → ℝ, (∀ s, 0 ≤ x s) ∧ ∀ i, ∑ s, a i s * x s ≤ b i)
    (hbd : ∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → (∀ i, ∑ s, a i s * x s ≤ b i) →
      v ≤ ∑ s, c s * x s) :
    ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, 0 ≤ c s + ∑ i, l i * a i s) ∧
      v + ∑ i, l i * b i ≤ 0 := by
  classical
  let A : (ι ⊕ σ ⊕ Unit) → ι → ℝ :=
    Sum.elim (fun i j => if j = i then -1 else 0) (Sum.elim (fun s j => - a j s) (fun _ j => b j))
  let B : (ι ⊕ σ ⊕ Unit) → ℝ := Sum.elim (fun _ => 0) (Sum.elim c (fun _ => -v))
  rcases fm_alt' A B with ⟨l, hl⟩ | ⟨w, hw0, hw1, hw2⟩
  · refine ⟨l, fun i => ?_, fun s => ?_, ?_⟩
    · have h := hl (Sum.inl i)
      simp [A, B] at h
      linarith
    · have h := hl (Sum.inr (Sum.inl s))
      simp only [A, B, Sum.elim_inl, Sum.elim_inr] at h
      have e : ∑ j, -a j s * l j = -∑ i, l i * a i s := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      linarith
    · have h := hl (Sum.inr (Sum.inr ()))
      simp only [A, B, Sum.elim_inl, Sum.elim_inr] at h
      have e : ∑ j, b j * l j = ∑ i, l i * b i :=
        Finset.sum_congr rfl (fun j _ => by ring)
      linarith
  · exfalso
    set z : σ → ℝ := fun s => w (Sum.inr (Sum.inl s)) with hz
    set t : ℝ := w (Sum.inr (Sum.inr ())) with ht
    have hz0 : ∀ s, 0 ≤ z s := fun s => hw0 _
    have ht0 : 0 ≤ t := hw0 _
    have hA : ∀ j, ∑ s, a j s * z s ≤ t * b j := by
      intro j
      have h := hw1 j
      simp only [A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_neg, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.univ_unique,
        Finset.sum_singleton, Finset.sum_neg_distrib] at h
      have h0 := hw0 (Sum.inl j)
      have e : ∑ s, a j s * z s = ∑ s, w (Sum.inr (Sum.inl s)) * a j s :=
        Finset.sum_congr rfl (fun s _ => by simp only [hz]; ring)
      have e2 : w (Sum.inr (Sum.inr default)) = t := rfl
      rw [e2] at h
      linarith
    have hC : ∑ s, c s * z s < t * v := by
      have h := hw2
      simp only [B, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
        Finset.sum_const_zero, zero_add, Finset.univ_unique, Finset.sum_singleton, mul_neg] at h
      have e : ∑ s, c s * z s = ∑ s, w (Sum.inr (Sum.inl s)) * c s :=
        Finset.sum_congr rfl (fun s _ => by simp only [hz]; ring)
      have e2 : w (Sum.inr (Sum.inr default)) = t := rfl
      rw [e2] at h
      linarith
    rcases lt_or_eq_of_le ht0 with htp | ht0'
    · -- scale down
      have h := hbd (fun s => z s / t) (fun s => div_nonneg (hz0 s) ht0) (fun i => by
        have e : ∑ s, a i s * (z s / t) = (∑ s, a i s * z s) / t := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun s _ => by ring)
        rw [e, div_le_iff₀ htp]; linarith [hA i])
      have e : ∑ s, c s * (z s / t) = (∑ s, c s * z s) / t := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun s _ => by ring)
      rw [e, le_div_iff₀ htp] at h
      linarith
    · -- recession direction
      rw [← ht0'] at hA hC
      simp only [zero_mul] at hA hC
      obtain ⟨x0, hx00, hx0⟩ := hfeas
      set S := ∑ s, c s * z s with hS
      set D := |∑ s, c s * x0 s - v| with hD
      have hD0 : 0 ≤ D := abs_nonneg _
      set K := (D + 1) / (-S) with hK
      have hKpos : 0 ≤ K := div_nonneg (by linarith) (by linarith)
      have hKS : K * S = -(D + 1) := by
        rw [hK, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
      have h := hbd (fun s => x0 s + K * z s)
        (fun s => add_nonneg (hx00 s) (mul_nonneg hKpos (hz0 s))) (fun i => by
          have e : ∑ s, a i s * (x0 s + K * z s) = ∑ s, a i s * x0 s + K * ∑ s, a i s * z s := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun s _ => by ring)
          rw [e]; nlinarith [hA i, hx0 i])
      have e : ∑ s, c s * (x0 s + K * z s) = ∑ s, c s * x0 s + K * S := by
        rw [hS, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun s _ => by ring)
      rw [e, hKS] at h
      have := le_abs_self (∑ s, c s * x0 s - v)
      linarith

/-- The same lemma for rows given as linear functionals, in Lagrangian form. -/
theorem farkas_lin {σ ι : Type} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
    (row : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ) (c : (σ → ℝ) →ₗ[ℝ] ℝ) (v : ℝ)
    (hfeas : ∃ x : σ → ℝ, (∀ s, 0 ≤ x s) ∧ ∀ i, row i x ≤ b i)
    (hbd : ∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → (∀ i, row i x ≤ b i) → v ≤ c x) :
    ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧
      (∀ s, 0 ≤ c (fun j => if s = j then 1 else 0)
        + ∑ i, l i * row i (fun j => if s = j then 1 else 0)) ∧
      (∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → v ≤ c x + ∑ i, l i * (row i x - b i)) := by
  have key : ∀ (f : (σ → ℝ) →ₗ[ℝ] ℝ) (x : σ → ℝ),
      ∑ s, f (fun j => if s = j then 1 else 0) * x s = f x := by
    intro f x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    exact Finset.sum_congr rfl (fun s _ => by rw [smul_eq_mul, mul_comm])
  obtain ⟨l, hl0, hl1, hl2⟩ := farkas_nn (fun i s => row i (fun j => if s = j then 1 else 0)) b
    (fun s => c (fun j => if s = j then 1 else 0)) v
    (by
      obtain ⟨x, hx0, hx⟩ := hfeas
      exact ⟨x, hx0, fun i => by rw [key]; exact hx i⟩)
    (fun x hx0 hx => by rw [key]; exact hbd x hx0 (fun i => by rw [← key]; exact hx i))
  refine ⟨l, hl0, hl1, fun x hx0 => ?_⟩
  have h1 : ∑ s, (c (fun j => if s = j then 1 else 0)
        + ∑ i, l i * row i (fun j => if s = j then 1 else 0)) * x s
      = c x + ∑ i, l i * row i x := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, key c x]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← key (row i) x, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have h2 : 0 ≤ ∑ s, (c (fun j => if s = j then 1 else 0)
        + ∑ i, l i * row i (fun j => if s = j then 1 else 0)) * x s :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hl1 s) (hx0 s))
  have h3 : ∑ i, l i * (row i x - b i) = ∑ i, l i * row i x - ∑ i, l i * b i := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h3]
  linarith

/-- Lagrangian Farkas without primal feasibility, given a base multiplier `l1` whose reduced
costs are nonnegative and whose Lagrangian is bounded below by `K` on `x ≥ 0`. -/
theorem farkas_gen {σ ι : Type} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
    (row : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ) (c : (σ → ℝ) →ₗ[ℝ] ℝ) (v : ℝ)
    (l1 : ι → ℝ) (hl1 : ∀ i, 0 ≤ l1 i)
    (hc1 : ∀ s, 0 ≤ c (fun j => if s = j then 1 else 0)
        + ∑ i, l1 i * row i (fun j => if s = j then 1 else 0))
    (K : ℝ) (hK : ∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → K ≤ c x + ∑ i, l1 i * (row i x - b i))
    (hbd : ∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → (∀ i, row i x ≤ b i) → v ≤ c x) :
    ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧
      (∀ s, 0 ≤ c (fun j => if s = j then 1 else 0)
        + ∑ i, l i * row i (fun j => if s = j then 1 else 0)) ∧
      (∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → v ≤ c x + ∑ i, l i * (row i x - b i)) := by
  have key : ∀ (f : (σ → ℝ) →ₗ[ℝ] ℝ) (x : σ → ℝ),
      ∑ s, f (fun j => if s = j then 1 else 0) * x s = f x := by
    intro f x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    exact Finset.sum_congr rfl (fun s _ => by rw [smul_eq_mul, mul_comm])
  by_cases hfeas : ∃ x : σ → ℝ, (∀ s, 0 ≤ x s) ∧ ∀ i, row i x ≤ b i
  · exact farkas_lin row b c v hfeas hbd
  · let A : (ι ⊕ σ) → σ → ℝ := Sum.elim (fun i s => row i (fun j => if s = j then 1 else 0))
      (fun s' s => if s = s' then -1 else 0)
    let B : (ι ⊕ σ) → ℝ := Sum.elim b (fun _ => 0)
    rcases fm_alt' A B with ⟨x, hx⟩ | ⟨w, hw0, hw1, hw2⟩
    · exfalso
      refine hfeas ⟨x, fun s => ?_, fun i => ?_⟩
      · have h := hx (Sum.inr s)
        simp [A, B] at h
        linarith
      · have h := hx (Sum.inl i)
        simp only [A, B, Sum.elim_inl] at h
        rwa [key] at h
    · have hsplit : ∀ s, ∑ i, w (Sum.inl i) * row i (fun j => if s = j then 1 else 0)
          = w (Sum.inr s) := by
        intro s
        have h := hw1 s
        simp only [Fintype.sum_sum_type, A, Sum.elim_inl, Sum.elim_inr] at h
        have e : ∑ s', w (Sum.inr s') * (if s = s' then (-1 : ℝ) else 0) = - w (Sum.inr s) := by
          simp
        linarith
      have hB : ∑ i, w (Sum.inl i) * b i < 0 := by
        simp only [Fintype.sum_sum_type, B, Sum.elim_inl, Sum.elim_inr, mul_zero,
          Finset.sum_const_zero, add_zero] at hw2
        exact hw2
      have hlin : ∀ x : σ → ℝ, ∑ i, w (Sum.inl i) * row i x = ∑ s, w (Sum.inr s) * x s := by
        intro x
        have h1 : ∀ i, w (Sum.inl i) * row i x
            = ∑ s, w (Sum.inl i) * row i (fun j => if s = j then 1 else 0) * x s := by
          intro i
          rw [← key (row i) x, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun s _ => by ring)
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [← hsplit s, Finset.sum_mul]
      obtain ⟨δ, hδ⟩ : ∃ d : ℝ, d = - ∑ i, w (Sum.inl i) * b i := ⟨_, rfl⟩
      have hδpos : 0 < δ := by rw [hδ]; linarith
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = max 0 ((v - K) / δ) := ⟨_, rfl⟩
      have ht0 : 0 ≤ t := by rw [ht]; exact le_max_left _ _
      have htδ : v - K ≤ t * δ := by
        have h : (v - K) / δ ≤ t := by rw [ht]; exact le_max_right _ _
        rw [div_le_iff₀ hδpos] at h
        linarith
      refine ⟨fun i => l1 i + t * w (Sum.inl i), fun i => add_nonneg (hl1 i)
        (mul_nonneg ht0 (hw0 _)), fun s => ?_, fun x hx0 => ?_⟩
      · have e : ∑ i, (l1 i + t * w (Sum.inl i)) * row i (fun j => if s = j then 1 else 0)
            = ∑ i, l1 i * row i (fun j => if s = j then 1 else 0) + t * w (Sum.inr s) := by
          rw [← hsplit s, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [e]
        have h1 := hc1 s
        have h2 := mul_nonneg ht0 (hw0 (Sum.inr s))
        linarith
      · have e : ∑ i, (l1 i + t * w (Sum.inl i)) * (row i x - b i)
            = ∑ i, l1 i * (row i x - b i) + (t * ∑ i, w (Sum.inl i) * row i x
              - t * ∑ i, w (Sum.inl i) * b i) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        have hpos : 0 ≤ ∑ i, w (Sum.inl i) * row i x := by
          rw [hlin x]
          exact Finset.sum_nonneg (fun s _ => mul_nonneg (hw0 _) (hx0 s))
        have htd : t * δ = - (t * ∑ i, w (Sum.inl i) * b i) := by rw [hδ]; ring
        rw [e]
        have h1 := hK x hx0
        have h2 := mul_nonneg ht0 hpos
        linarith

/-- A finite affine system that is `ε`-feasible for every `ε > 0` is feasible. -/
theorem approx_feas {σ ι : Type} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ) (b : ι → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i + ε) :
    ∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i := by
  rcases fm_alt' a b with hx | ⟨l, hl0, hl1, hl2⟩
  · exact hx
  · exfalso
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ∑ i, l i := ⟨_, rfl⟩
    have hL0 : 0 ≤ L := by rw [hL]; exact Finset.sum_nonneg (fun i _ => hl0 i)
    have hne : L + 1 ≠ 0 := by linarith
    obtain ⟨ε, hε⟩ : ∃ e : ℝ, e = - (∑ i, l i * b i) / (L + 1) := ⟨_, rfl⟩
    have hεpos : 0 < ε := by rw [hε]; exact div_pos (by linarith) (by linarith)
    obtain ⟨x, hx⟩ := h ε hεpos
    have h0 : ∑ i, l i * ∑ s, a i s * x s = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun s _ => ?_)
      have e : ∑ i, l i * (a i s * x s) = (∑ i, l i * a i s) * x s := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e, hl1 s, zero_mul]
    have h1 : ∑ i, l i * ∑ s, a i s * x s ≤ ∑ i, l i * (b i + ε) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hl0 i))
    have h2 : ∑ i, l i * (b i + ε) = ∑ i, l i * b i + L * ε := by
      rw [hL, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have h3 : ε * (L + 1) = - ∑ i, l i * b i := by rw [hε]; exact div_mul_cancel₀ _ hne
    have h3' : L * ε + ε = - ∑ i, l i * b i := by rw [← h3]; ring
    linarith


/-- Lower bound for a Lagrangian whose reduced costs are nonnegative. -/
theorem lag_lb {σ ι : Type} [Fintype σ] [DecidableEq σ] [Fintype ι]
    (row : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ) (c : (σ → ℝ) →ₗ[ℝ] ℝ) (l1 : ι → ℝ)
    (hc1 : ∀ s, 0 ≤ c (fun j => if s = j then 1 else 0)
        + ∑ i, l1 i * row i (fun j => if s = j then 1 else 0)) :
    ∀ x : σ → ℝ, (∀ s, 0 ≤ x s) → -∑ i, l1 i * b i ≤ c x + ∑ i, l1 i * (row i x - b i) := by
  intro x hx
  set f : (σ → ℝ) →ₗ[ℝ] ℝ := c + ∑ i, l1 i • row i with hfdef
  have hf : ∀ y, f y = c y + ∑ i, l1 i * row i y := by
    intro y; simp [hfdef]
  have key : ∑ s, f (fun j => if s = j then 1 else 0) * x s = f x := by
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    exact Finset.sum_congr rfl (fun s _ => by rw [smul_eq_mul, mul_comm])
  have h0 : 0 ≤ f x := by
    rw [← key]
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (by rw [hf]; exact hc1 s) (hx s))
  rw [hf] at h0
  have e : ∑ i, l1 i * (row i x - b i) = ∑ i, l1 i * row i x - ∑ i, l1 i * b i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e]
  linarith

noncomputable section Enc

open TwoEchelonVRP Finset

variable {ns nc : ℕ} (I : Instance ns nc)

/-- Variables of `LF`: `x_{kl}`, `y_r`, `q_{rk}`. -/
abbrev Var := (Fin ns × Route2 I) ⊕ Route1 I ⊕ (Route1 I × Fin ns)

/-- Constraint labels of `LF` in `≤` form. -/
abbrev Con := Fin nc ⊕ Fin nc ⊕ Fin ns ⊕ Unit ⊕ Fin ns ⊕ Unit ⊕ Fin ns ⊕ Fin ns ⊕
  Route1 I ⊕ Route1 I ⊕ (Route1 I × Fin ns)

def px (p : Fin ns × Route2 I) : (Var I → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Sum.inl p)
def py (r : Route1 I) : (Var I → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Sum.inr (Sum.inl r))
def pq (r : Route1 I) (k : Fin ns) : (Var I → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (Sum.inr (Sum.inr (r, k)))

@[simp] lemma px_apply (p : Fin ns × Route2 I) (z : Var I → ℝ) : px I p z = z (Sum.inl p) := rfl
@[simp] lemma py_apply (r : Route1 I) (z : Var I → ℝ) : py I r z = z (Sum.inr (Sum.inl r)) := rfl
@[simp] lemma pq_apply (r : Route1 I) (k : Fin ns) (z : Var I → ℝ) :
    pq I r k z = z (Sum.inr (Sum.inr (r, k))) := rfl

def cst : (Var I → ℝ) →ₗ[ℝ] ℝ :=
  ∑ p : Fin ns × Route2 I, cost2 I p.1 p.2 • px I p + ∑ r, cost1 I r • py I r

def rowE (i : Fin nc) : (Var I → ℝ) →ₗ[ℝ] ℝ :=
  ∑ p ∈ univ.filter (fun p : Fin ns × Route2 I => i ∈ custSet p.2), px I p
def rowS (k : Fin ns) : (Var I → ℝ) →ₗ[ℝ] ℝ :=
  ∑ p ∈ univ.filter (fun p : Fin ns × Route2 I => p.1 = k), px I p
def rowW (k : Fin ns) : (Var I → ℝ) →ₗ[ℝ] ℝ :=
  ∑ p ∈ univ.filter (fun p : Fin ns × Route2 I => p.1 = k), (load2 p.2 : ℝ) • px I p
def rowBal (k : Fin ns) : (Var I → ℝ) →ₗ[ℝ] ℝ :=
  ∑ r ∈ univ.filter (fun r : Route1 I => k ∈ satSet r), pq I r k - rowW I k
def rowCap (r : Route1 I) : (Var I → ℝ) →ₗ[ℝ] ℝ :=
  ∑ k ∈ satSet r, pq I r k - (I.Q1 : ℝ) • py I r
def rowZ (p : Route1 I × Fin ns) : (Var I → ℝ) →ₗ[ℝ] ℝ :=
  (if p.2 ∈ satSet p.1 then (0 : ℝ) else 1) • pq I p.1 p.2

@[simp] lemma cst_apply (z : Var I → ℝ) :
    cst I z = ∑ p : Fin ns × Route2 I, cost2 I p.1 p.2 * z (Sum.inl p)
      + ∑ r, cost1 I r * z (Sum.inr (Sum.inl r)) := by
  simp [cst]
@[simp] lemma rowE_apply (i : Fin nc) (z : Var I → ℝ) :
    rowE I i z = ∑ p ∈ univ.filter (fun p : Fin ns × Route2 I => i ∈ custSet p.2),
      z (Sum.inl p) := by
  simp [rowE]
@[simp] lemma rowS_apply (k : Fin ns) (z : Var I → ℝ) :
    rowS I k z = ∑ p ∈ univ.filter (fun p : Fin ns × Route2 I => p.1 = k), z (Sum.inl p) := by
  simp [rowS]
@[simp] lemma rowW_apply (k : Fin ns) (z : Var I → ℝ) :
    rowW I k z = ∑ p ∈ univ.filter (fun p : Fin ns × Route2 I => p.1 = k),
      (load2 p.2 : ℝ) * z (Sum.inl p) := by
  simp [rowW]
@[simp] lemma rowBal_apply (k : Fin ns) (z : Var I → ℝ) :
    rowBal I k z = ∑ r ∈ univ.filter (fun r : Route1 I => k ∈ satSet r), z (Sum.inr (Sum.inr (r, k)))
      - ∑ p ∈ univ.filter (fun p : Fin ns × Route2 I => p.1 = k),
        (load2 p.2 : ℝ) * z (Sum.inl p) := by
  simp [rowBal]
@[simp] lemma rowCap_apply (r : Route1 I) (z : Var I → ℝ) :
    rowCap I r z = ∑ k ∈ satSet r, z (Sum.inr (Sum.inr (r, k)))
      - (I.Q1 : ℝ) * z (Sum.inr (Sum.inl r)) := by
  simp [rowCap]
@[simp] lemma rowZ_apply (p : Route1 I × Fin ns) (z : Var I → ℝ) :
    rowZ I p z = (if p.2 ∈ satSet p.1 then (0 : ℝ) else 1) * z (Sum.inr (Sum.inr p)) := by
  by_cases h : p.2 ∈ satSet p.1 <;> simp [rowZ, h]
@[simp] lemma sumx_apply (z : Var I → ℝ) :
    (∑ p : Fin ns × Route2 I, px I p) z = ∑ p, z (Sum.inl p) := by
  simp
@[simp] lemma sumy_apply (z : Var I → ℝ) :
    (∑ r, py I r) z = ∑ r, z (Sum.inr (Sum.inl r)) := by
  simp

def row : Con I → (Var I → ℝ) →ₗ[ℝ] ℝ :=
  Sum.elim (rowE I) (Sum.elim (fun i => - rowE I i) (Sum.elim (rowS I)
  (Sum.elim (fun _ => ∑ p : Fin ns × Route2 I, px I p) (Sum.elim (rowW I)
  (Sum.elim (fun _ => ∑ r, py I r)
  (Sum.elim (rowBal I) (Sum.elim (fun k => - rowBal I k) (Sum.elim (rowCap I)
  (Sum.elim (py I) (rowZ I))))))))))

def rhs : Con I → ℝ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => -1) (Sum.elim (fun k => (I.mSat k : ℝ))
  (Sum.elim (fun _ => (I.m2 : ℝ)) (Sum.elim (fun k => I.B k)
  (Sum.elim (fun _ => (I.m1 : ℝ)) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
  (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))))))))))

def xX (z : Var I → ℝ) : Fin ns → Route2 I → ℝ := fun k l => z (Sum.inl (k, l))
def yX (z : Var I → ℝ) : Route1 I → ℝ := fun r => z (Sum.inr (Sum.inl r))
def qX (z : Var I → ℝ) : Route1 I → Fin ns → ℝ := fun r k => z (Sum.inr (Sum.inr (r, k)))

lemma sum_fst (k : Fin ns) (f : Fin ns × Route2 I → ℝ) :
    ∑ p ∈ univ.filter (fun p : Fin ns × Route2 I => p.1 = k), f p = ∑ l, f (k, l) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma sum_cov (i : Fin nc) (f : Fin ns × Route2 I → ℝ) :
    ∑ p ∈ univ.filter (fun p : Fin ns × Route2 I => i ∈ custSet p.2), f p
      = ∑ k, ∑ l ∈ univ.filter (fun l : Route2 I => i ∈ custSet l), f (k, l) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Finset.sum_filter]

lemma mem_cust0 (l : Route2 I) : l.1.2 0 ∈ custSet l := by
  simp [custSet, InjSeq.toFinset]

lemma cst_X (z : Var I → ℝ) : cst I z = objF I (xX I z) (yX I z) := by
  simp [objF, xX, yX, Fintype.sum_prod_type]

lemma feas_of (z : Var I → ℝ) (hz : ∀ s, 0 ≤ z s) (h : ∀ i, row I i z ≤ rhs I i) :
    LFFeasible I (xX I z) (yX I z) (qX I z) := by
  have hE1 := fun i => h (Sum.inl i)
  have hE2 := fun i => h (Sum.inr (Sum.inl i))
  have h3 := fun k => h (Sum.inr (Sum.inr (Sum.inl k)))
  have h4 := h (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
  have h5 := fun k => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
  have h6 := h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))))
  have h7a := fun k => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))
  have h7b := fun k =>
    h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
  have h8 := fun r =>
    h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl r)))))))))
  have hy := fun r =>
    h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inl r))))))))))
  have hzq := fun pr =>
    h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inr pr))))))))))
  simp only [row, rhs, Sum.elim_inl, Sum.elim_inr, LinearMap.neg_apply, rowE_apply, rowS_apply,
    rowW_apply, rowBal_apply, rowCap_apply, rowZ_apply, sumx_apply, sumy_apply, py_apply]
    at hE1 hE2 h3 h4 h5 h6 h7a h7b h8 hy hzq
  simp only [sum_cov] at hE1 hE2
  simp only [sum_fst] at h3 h5 h7a h7b
  rw [Fintype.sum_prod_type] at h4
  have hx1 : ∀ i, ∑ k, ∑ l ∈ univ.filter (fun l : Route2 I => i ∈ custSet l), xX I z k l = 1 :=
    fun i => by simp only [xX]; exact le_antisymm (hE1 i) (by linarith [hE2 i])
  refine ⟨⟨fun i => hx1 i, fun k => h3 k, h4, fun k => h5 k, h6,
    fun k => by have := h7a k; have := h7b k; simp only [xX, qX]; linarith,
    fun r => by have := h8 r; simp only [yX, qX]; linarith,
    fun r k hk => ?_⟩, fun k l => ⟨hz _, ?_⟩, fun r => ⟨hz _, hy r⟩, fun r k => hz _⟩
  · have := hzq (r, k)
    simp only [hk, if_false, one_mul] at this
    simp only [qX]
    exact le_antisymm this (hz _)
  · have hil := mem_cust0 I l
    have hle1 := Finset.single_le_sum (f := fun l' => xX I z k l')
      (s := univ.filter (fun l' : Route2 I => l.1.2 0 ∈ custSet l')) (fun l' _ => hz _)
      (show l ∈ univ.filter (fun l' : Route2 I => l.1.2 0 ∈ custSet l') by simp [hil])
    have hle2 := Finset.single_le_sum
      (f := fun k' => ∑ l' ∈ univ.filter (fun l' : Route2 I => l.1.2 0 ∈ custSet l'), xX I z k' l')
      (s := univ) (fun k' _ => Finset.sum_nonneg (fun l' _ => hz _)) (Finset.mem_univ k)
    have := hx1 (l.1.2 0)
    linarith

lemma sum_aCoef (l : Route2 I) (f : Fin nc → ℝ) :
    ∑ i, aCoef l i * f i = ∑ i ∈ custSet l, f i := by
  simp only [aCoef, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

lemma load2_cast (l : Route2 I) : (load2 l : ℝ) = ∑ i ∈ custSet l, (I.q i : ℝ) := by
  simp [load2]

end Enc

section Part1

open TwoEchelonVRP Finset

set_option maxHeartbeats 1000000 in
theorem part1 {ns nc : ℕ} (I : Instance ns nc) (v : ℝ)
    (hv : ∀ x y qd, LFFeasible I x y qd → v ≤ objF I x y) :
    ∃ (β : Fin nc → Fin ns → ℝ) (lam : Fin nc → ℝ) (μ : Fin ns → ℝ) (μ0 : ℝ),
      MultFeasible I β lam μ μ0 ∧ (v : EReal) ≤ zRF I β lam μ μ0 := by
  classical
  set M : ℝ := ∑ p : Fin ns × Route2 I, |cost2 I p.1 p.2| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun p _ => abs_nonneg _)
  set l1 : Con I → ℝ := Sum.elim (fun _ => M) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun r => |cost1 I r|)
    (fun _ => 0)))))))))) with hl1def
  have hl1 : ∀ i, 0 ≤ l1 i := by
    rintro (i | i | k | u | k | u | k | k | r | r | pr) <;> simp [hl1def, hM0]
  have hc1 : ∀ s, 0 ≤ cst I (fun j => if s = j then 1 else 0)
      + ∑ i, l1 i * row I i (fun j => if s = j then 1 else 0) := by
    rintro (p | r | pr)
    · have hsum : ∑ i, l1 i * row I i (fun j => if Sum.inl p = j then 1 else 0)
          = ∑ i, M * (if i ∈ custSet p.2 then 1 else 0) := by
        simp [Fintype.sum_sum_type, hl1def, row]
      rw [hsum]
      have hcst : cst I (fun j => if Sum.inl p = j then 1 else 0) = cost2 I p.1 p.2 := by
        simp
      rw [hcst]
      have h1 : M * 1 ≤ ∑ i, M * (if i ∈ custSet p.2 then (1 : ℝ) else 0) := by
        have := Finset.single_le_sum (f := fun i => M * (if i ∈ custSet p.2 then (1 : ℝ) else 0))
          (s := univ) (fun i _ => by positivity) (Finset.mem_univ (p.2.1.2 0))
        simpa [mem_cust0] using this
      have h2 : |cost2 I p.1 p.2| ≤ M :=
        Finset.single_le_sum (f := fun p : Fin ns × Route2 I => |cost2 I p.1 p.2|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ p)
      linarith [neg_abs_le (cost2 I p.1 p.2)]
    · have hsum : ∑ i, l1 i * row I i (fun j => if Sum.inr (Sum.inl r) = j then 1 else 0)
          = |cost1 I r| := by
        simp [Fintype.sum_sum_type, hl1def, row]
      rw [hsum]
      have hcst : cst I (fun j => if Sum.inr (Sum.inl r) = j then 1 else 0) = cost1 I r := by
        simp
      rw [hcst]
      linarith [neg_abs_le (cost1 I r)]
    · have hsum : ∑ i, l1 i * row I i (fun j => if Sum.inr (Sum.inr pr) = j then 1 else 0)
          = 0 := by
        simp [Fintype.sum_sum_type, hl1def, row]
      rw [hsum]
      have hcst : cst I (fun j => if Sum.inr (Sum.inr pr) = j then 1 else 0) = 0 := by
        simp
      rw [hcst]; norm_num
  obtain ⟨l, hl0, hcoef, hlag⟩ := farkas_gen (row I) (rhs I) (cst I) v l1 hl1 hc1 _
    (lag_lb (row I) (rhs I) (cst I) l1 hc1)
    (fun z hz hr => by rw [cst_X]; exact hv _ _ _ (feas_of I z hz hr))
  -- the multipliers
  obtain ⟨lam, hlam⟩ : ∃ f : Fin nc → ℝ, ∀ i, f i = l (Sum.inr (Sum.inl i)) - l (Sum.inl i) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ f : Fin ns → ℝ, ∀ k, f k = - l (Sum.inr (Sum.inr (Sum.inl k))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨μ0, hμ0⟩ : ∃ t : ℝ, t = - l (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) :=
    ⟨_, rfl⟩
  obtain ⟨a5, ha5⟩ : ∃ f : Fin ns → ℝ,
      ∀ k, f k = l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))) := ⟨_, fun _ => rfl⟩
  obtain ⟨sg, hsg⟩ : ∃ f : Fin ns → ℝ,
      ∀ k, f k = l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))
        - l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ f : Fin nc → Fin ns → ℝ,
      ∀ i k, f i k = (I.q i : ℝ) * (sg k - a5 k) := ⟨_, fun _ _ => rfl⟩
  refine ⟨β, lam, μ, μ0, ⟨fun k => by rw [hμ]; linarith [hl0 (Sum.inr (Sum.inr (Sum.inl k)))],
    by rw [hμ0]; linarith [hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))], ?_⟩, ?_⟩
  · -- inequalities (12): the reduced cost of `x_{kl}` is nonnegative
    intro k0 l0
    have h := hcoef (Sum.inl (k0, l0))
    simp only [Fintype.sum_sum_type] at h
    set e : Var I → ℝ := fun j => if Sum.inl (k0, l0) = j then 1 else 0 with he
    have b0 : cst I e = cost2 I k0 l0 := by simp [he]
    have b1 : ∑ i, l (Sum.inl i) * row I (Sum.inl i) e = ∑ i ∈ custSet l0, l (Sum.inl i) := by
      simp [row, he]
    have b2 : ∑ i, l (Sum.inr (Sum.inl i)) * row I (Sum.inr (Sum.inl i)) e
        = - ∑ i ∈ custSet l0, l (Sum.inr (Sum.inl i)) := by
      simp [row, he]
    have b3 : ∑ k, l (Sum.inr (Sum.inr (Sum.inl k))) * row I (Sum.inr (Sum.inr (Sum.inl k))) e
        = l (Sum.inr (Sum.inr (Sum.inl k0))) := by
      simp [row, he]
    have b4 : ∑ u, l (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))
        * row I (Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))) e
        = l (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) := by
      simp [row, he]
    have b5 : ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        * row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))) e
        = a5 k0 * (load2 l0 : ℝ) := by
      simp [row, he, ha5]
    have b6 : ∑ u, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))))
        * row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))))) e = 0 := by
      simp [row, he]
    have b7 : ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))
        * row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))) e
        + ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
        * row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
          e
        = - sg k0 * (load2 l0 : ℝ) := by
      simp [row, he, hsg]
      ring
    have b8 : ∑ r, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl r)))))))))
        * row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl r))))))))) e = 0 := by
      simp [row, he]
    have b9 : ∑ r, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl r))))))))))
        * row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl r)))))))))) e = 0 := by
      simp [row, he]
    have b10 : ∑ pr, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr pr))))))))))
        * row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr pr)))))))))) e = 0 := by
      simp [row, he]
    have hlhs : ∑ i, aCoef l0 i * β i k0 = (sg k0 - a5 k0) * (load2 l0 : ℝ) := by
      rw [sum_aCoef, load2_cast, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [hβ]; ring)
    have hrhs : ∑ i, aCoef l0 i * lam i
        = ∑ i ∈ custSet l0, l (Sum.inr (Sum.inl i)) - ∑ i ∈ custSet l0, l (Sum.inl i) := by
      rw [sum_aCoef, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hlam i)
    rw [hlhs, hrhs, hμ, hμ0]
    linarith
  · -- every `RF` solution costs at least `v`
    refine le_sInf ?_
    rintro _ ⟨w, ⟨ξ, y, qd, hs, rfl⟩, rfl⟩
    obtain ⟨h14, h15, h16, h6, h8, hy01, hqn, h11, -⟩ := hs
    refine EReal.coe_le_coe_iff.2 ?_
    set z : Var I → ℝ := Sum.elim (fun _ => 0)
      (Sum.elim y (fun pr => qd pr.1 pr.2)) with hz
    have hz0 : ∀ j, 0 ≤ z j := by
      rintro (p | r | ⟨r, k⟩)
      · simp [hz]
      · rcases hy01 r with h | h <;> simp [hz, h]
      · by_cases hk : k ∈ satSet r
        · obtain ⟨n, hn⟩ := hqn r k hk
          simp [hz, hn]
        · simp [hz, h11 r k hk]
    have h := hlag z hz0
    simp only [Fintype.sum_sum_type] at h
    set D : Fin ns → ℝ := fun k => ∑ i, (I.q i : ℝ) * ξ i k with hD
    have F15 : ∀ k, ∑ r ∈ univ.filter (fun r : Route1 I => k ∈ satSet r), qd r k = D k := h15
    have F16 : ∀ k, D k ≤ I.B k := h16
    have Fy : ∀ r, y r ≤ 1 := fun r => by rcases hy01 r with h | h <;> simp [h]
    have c0 : cst I z = ∑ r, cost1 I r * y r := by simp [hz]
    have c12 : ∑ i, l (Sum.inl i) * (row I (Sum.inl i) z - rhs I (Sum.inl i))
        + ∑ i, l (Sum.inr (Sum.inl i)) * (row I (Sum.inr (Sum.inl i)) z
          - rhs I (Sum.inr (Sum.inl i))) = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [row, rhs, hz, hlam] <;> ring
    have c3 : ∑ k, l (Sum.inr (Sum.inr (Sum.inl k))) * (row I (Sum.inr (Sum.inr (Sum.inl k))) z
        - rhs I (Sum.inr (Sum.inr (Sum.inl k)))) = ∑ k, (I.mSat k : ℝ) * μ k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [row, rhs, hz, hμ] <;> ring
    have c4 : ∑ u, l (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))
        * (row I (Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))) z
          - rhs I (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))) = (I.m2 : ℝ) * μ0 := by
      simp [row, rhs, hz, hμ0] <;> ring
    have c5 : ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
        * (row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))) z
          - rhs I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))
        ≤ - ∑ k, a5 k * D k := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have h0 := hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))
      have := F16 k
      simp [row, rhs, hz, ha5]
      nlinarith
    have c6 : ∑ u, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))))
        * (row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))))) z
          - rhs I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))))) ≤ 0 := by
      have h0 := hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))))
      simp [row, rhs, hz]
      nlinarith
    have c7 : ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))))))
        * (row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))) z
          - rhs I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
        + ∑ k, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
        * (row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))))))
            z - rhs I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
            (Sum.inl k)))))))))
        = ∑ k, sg k * D k := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have := F15 k
      simp [row, rhs, hz, hsg]
      rw [this]
      ring
    have c8 : ∑ r, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl r)))))))))
        * (row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inl r))))))))) z - rhs I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr (Sum.inl r)))))))))) ≤ 0 := by
      refine Finset.sum_nonpos (fun r _ => ?_)
      have h0 := hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl r)))))))))
      have := h8 r
      simp [row, rhs, hz]
      nlinarith
    have c9 : ∑ r, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl r))))))))))
        * (row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inl r)))))))))) z - rhs I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl r))))))))))) ≤ 0 := by
      refine Finset.sum_nonpos (fun r _ => ?_)
      have h0 := hl0 (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl r))))))))))
      have := Fy r
      simp [row, rhs, hz]
      nlinarith
    have c10 : ∑ pr, l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr pr))))))))))
        * (row I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr pr)))))))))) z - rhs I (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr pr))))))))))) = 0 := by
      refine Finset.sum_eq_zero (fun pr _ => ?_)
      by_cases hk : pr.2 ∈ satSet pr.1
      · simp [row, rhs, hz, hk]
      · simp [row, rhs, hz, hk, h11 pr.1 pr.2 hk]
    have cobj : ∑ k, ∑ i, β i k * ξ i k = ∑ k, (sg k - a5 k) * D k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hD, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [hβ]; ring)
    have csub : ∑ k, (sg k - a5 k) * D k = ∑ k, sg k * D k - ∑ k, a5 k * D k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    unfold objRF
    rw [cobj, csub]
    linarith

/-- Clause (a). -/
theorem clause_a {ns nc : ℕ} (I : Instance ns nc) : zLF I ≤ rfSup I := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨v, hv1, hv2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hv : ∀ x y qd, LFFeasible I x y qd → v ≤ objF I x y := by
    intro x y qd h
    have h1 : zLF I ≤ ((objF I x y : ℝ) : EReal) := sInf_le ⟨_, ⟨x, y, qd, h, rfl⟩, rfl⟩
    exact EReal.coe_le_coe_iff.1 (le_of_lt (lt_of_lt_of_le hv2 h1))
  obtain ⟨β, lam, μ, μ0, hm, hz⟩ := part1 I v hv
  have : zRF I β lam μ μ0 ≤ rfSup I := le_sSup ⟨β, lam, μ, μ0, hm, rfl⟩
  exact absurd (lt_of_le_of_lt (hz.trans this) hv1) (lt_irrefl _)

end Part1


/-- `ε`-feasibility implies feasibility, for a system given by linear maps. -/
theorem approx_feas_lin {σ ι : Type} [Fintype σ] [DecidableEq σ] [Fintype ι]
    (row : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ x : σ → ℝ, ∀ i, row i x ≤ b i + ε) :
    ∃ x : σ → ℝ, ∀ i, row i x ≤ b i := by
  have key : ∀ i (x : σ → ℝ), ∑ s, row i (fun j => if s = j then 1 else 0) * x s = row i x := by
    intro i x
    rw [LinearMap.pi_apply_eq_sum_univ (row i) x]
    exact Finset.sum_congr rfl (fun s _ => by rw [smul_eq_mul, mul_comm])
  obtain ⟨x, hx⟩ := approx_feas (fun i s => row i (fun j => if s = j then 1 else 0)) b
    (fun ε hε => by
      obtain ⟨x, hx⟩ := h ε hε
      exact ⟨x, fun i => by rw [key]; exact hx i⟩)
  exact ⟨x, fun i => by rw [← key]; exact hx i⟩

section ClauseB

open TwoEchelonVRP Finset

def bv (b : Bool) : ℝ := if b then 1 else 0

lemma bv_dec (t : ℝ) (h : t = 0 ∨ t = 1) : bv (decide (t = 1)) = t := by
  rcases h with rfl | rfl <;> simp [bv]

/-- The `(ξ, y)` parts of `RF` solutions, as Boolean data. -/
abbrev SB {ns nc : ℕ} (I : Instance ns nc) : Type :=
  {s : (Fin nc → Fin ns → Bool) × (Route1 I → Bool) //
    ∃ qd, RFFeasible I (fun i k => bv (s.1 i k)) (fun r => bv (s.2 r)) qd}

noncomputable instance instFintypeSB {ns nc : ℕ} (I : Instance ns nc) : Fintype (SB I) := by
  classical
  exact Subtype.fintype _

/-- Multiplier space `(β, λ, μ, μ0)`. -/
abbrev MV (ns nc : ℕ) := (Fin nc × Fin ns) ⊕ Fin nc ⊕ Fin ns ⊕ Unit

variable {ns nc : ℕ}

def mB (m : MV ns nc → ℝ) : Fin nc → Fin ns → ℝ := fun i k => m (Sum.inl (i, k))
def mL (m : MV ns nc → ℝ) : Fin nc → ℝ := fun i => m (Sum.inr (Sum.inl i))
def mU (m : MV ns nc → ℝ) : Fin ns → ℝ := fun k => m (Sum.inr (Sum.inr (Sum.inl k)))
def mU0 (m : MV ns nc → ℝ) : ℝ := m (Sum.inr (Sum.inr (Sum.inr ())))
def enc (β : Fin nc → Fin ns → ℝ) (lam : Fin nc → ℝ) (μ : Fin ns → ℝ) (μ0 : ℝ) :
    MV ns nc → ℝ :=
  Sum.elim (fun p => β p.1 p.2) (Sum.elim lam (Sum.elim μ (fun _ => μ0)))

@[simp] lemma mB_enc (β : Fin nc → Fin ns → ℝ) (lam : Fin nc → ℝ) (μ : Fin ns → ℝ) (μ0 : ℝ) :
    mB (enc β lam μ μ0) = β := rfl
@[simp] lemma mL_enc (β : Fin nc → Fin ns → ℝ) (lam : Fin nc → ℝ) (μ : Fin ns → ℝ) (μ0 : ℝ) :
    mL (enc β lam μ μ0) = lam := rfl
@[simp] lemma mU_enc (β : Fin nc → Fin ns → ℝ) (lam : Fin nc → ℝ) (μ : Fin ns → ℝ) (μ0 : ℝ) :
    mU (enc β lam μ μ0) = μ := rfl
@[simp] lemma mU0_enc (β : Fin nc → Fin ns → ℝ) (lam : Fin nc → ℝ) (μ : Fin ns → ℝ) (μ0 : ℝ) :
    mU0 (enc β lam μ μ0) = μ0 := rfl

def qB (i : Fin nc) (k : Fin ns) : (MV ns nc → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Sum.inl (i, k))
def qL (i : Fin nc) : (MV ns nc → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Sum.inr (Sum.inl i))
def qU (k : Fin ns) : (MV ns nc → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Sum.inr (Sum.inr (Sum.inl k)))
def qU0 : (MV ns nc → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Sum.inr (Sum.inr (Sum.inr ())))

@[simp] lemma qB_apply (i : Fin nc) (k : Fin ns) (m : MV ns nc → ℝ) : qB i k m = mB m i k := rfl
@[simp] lemma qL_apply (i : Fin nc) (m : MV ns nc → ℝ) : qL i m = mL m i := rfl
@[simp] lemma qU_apply (k : Fin ns) (m : MV ns nc → ℝ) : qU k m = mU m k := rfl
@[simp] lemma qU0_apply (m : MV ns nc → ℝ) : (qU0 : (MV ns nc → ℝ) →ₗ[ℝ] ℝ) m = mU0 m := rfl

noncomputable def mrow (I : Instance ns nc) :
    SB I ⊕ Fin ns ⊕ Unit ⊕ (Fin ns × Route2 I) → (MV ns nc → ℝ) →ₗ[ℝ] ℝ :=
  Sum.elim (fun s => -(∑ k, ∑ i, bv (s.1.1 i k) • qB i k + ∑ i, qL i
      + ∑ k, (I.mSat k : ℝ) • qU k + (I.m2 : ℝ) • qU0))
    (Sum.elim (fun k => qU k) (Sum.elim (fun _ => qU0)
      (fun p => ∑ i, aCoef p.2 i • qB i p.1 + ∑ i, aCoef p.2 i • qL i + qU p.1 + qU0)))

noncomputable def mrhs (I : Instance ns nc) (v : ℝ) :
    SB I ⊕ Fin ns ⊕ Unit ⊕ (Fin ns × Route2 I) → ℝ :=
  Sum.elim (fun s => -v + ∑ r, cost1 I r * bv (s.1.2 r))
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun p => cost2 I p.1 p.2)))

lemma mrow_O (I : Instance ns nc) (s : SB I) (m : MV ns nc → ℝ) :
    mrow I (Sum.inl s) m = -(∑ k, ∑ i, mB m i k * bv (s.1.1 i k) + ∑ i, mL m i
      + ∑ k, (I.mSat k : ℝ) * mU m k + (I.m2 : ℝ) * mU0 m) := by
  simp [mrow, mul_comm]

lemma mrow_U (I : Instance ns nc) (k : Fin ns) (m : MV ns nc → ℝ) :
    mrow I (Sum.inr (Sum.inl k)) m = mU m k := by
  simp [mrow]

lemma mrow_U0 (I : Instance ns nc) (m : MV ns nc → ℝ) :
    mrow I (Sum.inr (Sum.inr (Sum.inl ()))) m = mU0 m := by
  simp [mrow]

lemma mrow_12 (I : Instance ns nc) (p : Fin ns × Route2 I) (m : MV ns nc → ℝ) :
    mrow I (Sum.inr (Sum.inr (Sum.inr p))) m
      = ∑ i, aCoef p.2 i * mB m i p.1 + ∑ i, aCoef p.2 i * mL m i + mU m p.1 + mU0 m := by
  simp [mrow]

set_option maxHeartbeats 1000000 in
/-- Clause (b). -/
theorem clause_b (I : Instance ns nc) (htop : rfSup I ≠ ⊤) :
    ∃ β lam μ μ0, MultFeasible I β lam μ μ0 ∧ zRF I β lam μ μ0 = rfSup I := by
  classical
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ∑ p : Fin ns × Route2 I, |cost2 I p.1 p.2| := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; exact Finset.sum_nonneg (fun p _ => abs_nonneg _)
  have hm0 : MultFeasible I (fun _ _ => -C) (fun _ => 0) (fun _ => 0) 0 := by
    refine ⟨fun _ => le_refl _, le_refl _, fun k l => ?_⟩
    have h1 : C ≤ ∑ i, aCoef l i * C := by
      have := Finset.single_le_sum (f := fun i => aCoef l i * C)
        (fun i _ => mul_nonneg (by unfold aCoef; split_ifs <;> norm_num) hC0)
        (Finset.mem_univ (l.1.2 0))
      simpa [aCoef, mem_cust0] using this
    have h2 : |cost2 I k l| ≤ C := by
      rw [hCdef]
      exact Finset.single_le_sum (f := fun p : Fin ns × Route2 I => |cost2 I p.1 p.2|)
        (fun p _ => abs_nonneg _) (Finset.mem_univ (k, l))
    have h3 : ∑ i, aCoef l i * (-C) = - ∑ i, aCoef l i * C := by
      simp only [mul_neg, Finset.sum_neg_distrib]
    simp only [mul_zero, Finset.sum_const_zero, sub_zero]
    rw [h3]
    linarith [neg_abs_le (cost2 I k l)]
  have hRF : ∃ ξ y qd, RFFeasible I ξ y qd := by
    by_contra hno
    have htop' : zRF I (fun _ _ => -C) (fun _ => 0) (fun _ => 0) 0 = ⊤ := by
      unfold zRF
      rw [sInf_eq_top]
      rintro _ ⟨w, ⟨ξ, y, qd, hs, -⟩, -⟩
      exact absurd ⟨ξ, y, qd, hs⟩ hno
    apply htop
    rw [eq_top_iff, ← htop']
    exact le_sSup ⟨_, _, _, _, hm0, rfl⟩
  have hzlb : (((∑ k : Fin ns, ∑ i : Fin nc, (-C)) - ∑ r, |cost1 I r| : ℝ) : EReal)
      ≤ zRF I (fun _ _ => -C) (fun _ => 0) (fun _ => 0) 0 := by
    refine le_sInf ?_
    rintro _ ⟨w, ⟨ξ, y, qd, hs, rfl⟩, rfl⟩
    refine EReal.coe_le_coe_iff.2 ?_
    obtain ⟨-, -, -, -, -, hy01, -, -, hξ01⟩ := hs
    have t1 : ∀ k i, -C ≤ -C * ξ i k := fun k i => by
      rcases hξ01 i k with h | h <;> rw [h] <;> linarith
    have t2 : ∀ r, -|cost1 I r| ≤ cost1 I r * y r := fun r => by
      rcases hy01 r with h | h <;> rw [h] <;>
        linarith [neg_abs_le (cost1 I r), abs_nonneg (cost1 I r)]
    have s1 := Finset.sum_le_sum (fun k (_ : k ∈ (univ : Finset (Fin ns))) =>
      Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin nc))) => t1 k i))
    have s2 := Finset.sum_le_sum (fun r (_ : r ∈ (univ : Finset (Route1 I))) => t2 r)
    simp only [Finset.sum_neg_distrib] at s2
    simp only [objRF, mul_zero, Finset.sum_const_zero, add_zero]
    linarith
  have hbot : rfSup I ≠ ⊥ := by
    intro h
    have h1 : zRF I (fun _ _ => -C) (fun _ => 0) (fun _ => 0) 0 ≤ rfSup I :=
      le_sSup ⟨_, _, _, _, hm0, rfl⟩
    rw [h] at h1
    exact EReal.coe_ne_bot _ (le_bot_iff.1 (hzlb.trans h1))
  set v : ℝ := (rfSup I).toReal with hvdef
  have hv : rfSup I = (v : EReal) := (EReal.coe_toReal htop hbot).symm
  obtain ⟨m, hm⟩ := approx_feas_lin (mrow I) (mrhs I v) (by
    intro ε hε
    have hlt : ((v - ε : ℝ) : EReal) < rfSup I := by
      rw [hv]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    obtain ⟨a, ⟨β, lam, μ, μ0, hmf, rfl⟩, ha⟩ := lt_sSup_iff.1 hlt
    refine ⟨enc β lam μ μ0, ?_⟩
    obtain ⟨hμ, hμ0, h12⟩ := hmf
    rintro (s | k | u | ⟨k, l⟩)
    · obtain ⟨qd, hqd⟩ := s.2
      have h1 : zRF I β lam μ μ0 ≤ ((objRF I β lam μ μ0 (fun i k => bv (s.1.1 i k))
          (fun r => bv (s.1.2 r)) : ℝ) : EReal) := sInf_le ⟨_, ⟨_, _, qd, hqd, rfl⟩, rfl⟩
      have h2 := EReal.coe_lt_coe_iff.1 (lt_of_lt_of_le ha h1)
      rw [mrow_O]
      simp only [mrhs, Sum.elim_inl, mB_enc, mL_enc, mU_enc, mU0_enc]
      simp only [objRF] at h2
      linarith
    · rw [mrow_U]
      simp only [mrhs, Sum.elim_inl, Sum.elim_inr, mU_enc]
      linarith [hμ k]
    · rw [mrow_U0]
      simp only [mrhs, Sum.elim_inl, Sum.elim_inr, mU0_enc]
      linarith
    · rw [mrow_12]
      simp only [mrhs, Sum.elim_inl, Sum.elim_inr, mB_enc, mL_enc, mU_enc, mU0_enc]
      have := h12 k l
      linarith)
  have hmf : MultFeasible I (mB m) (mL m) (mU m) (mU0 m) := by
    refine ⟨fun k => ?_, ?_, fun k l => ?_⟩
    · have := hm (Sum.inr (Sum.inl k))
      rw [mrow_U] at this
      simpa [mrhs] using this
    · have := hm (Sum.inr (Sum.inr (Sum.inl ())))
      rw [mrow_U0] at this
      simpa [mrhs] using this
    · have := hm (Sum.inr (Sum.inr (Sum.inr (k, l))))
      rw [mrow_12] at this
      simp only [mrhs, Sum.elim_inr] at this
      linarith
  refine ⟨mB m, mL m, mU m, mU0 m, hmf, le_antisymm (le_sSup ⟨_, _, _, _, hmf, rfl⟩) ?_⟩
  rw [hv]
  refine le_sInf ?_
  rintro _ ⟨w, ⟨ξ, y, qd, hs, rfl⟩, rfl⟩
  refine EReal.coe_le_coe_iff.2 ?_
  have hξp : ∀ i k, bv (decide (ξ i k = 1)) = ξ i k := fun i k => bv_dec _ (hs.2.2.2.2.2.2.2.2 i k)
  have hyp : ∀ r, bv (decide (y r = 1)) = y r := fun r => bv_dec _ (hs.2.2.2.2.2.1 r)
  have hξf : (fun i k => bv (decide (ξ i k = 1))) = ξ := funext fun i => funext fun k => hξp i k
  have hyf : (fun r => bv (decide (y r = 1))) = y := funext fun r => hyp r
  let s : SB I := ⟨(fun i k => decide (ξ i k = 1), fun r => decide (y r = 1)), qd,
    by simp only; rw [hξf, hyf]; exact hs⟩
  have h := hm (Sum.inl s)
  rw [mrow_O] at h
  simp only [mrhs, Sum.elim_inl, s, hξp, hyp] at h
  simp only [objRF]
  linarith

end ClauseB

section ClauseC

open TwoEchelonVRP Finset

/-- The witness instance: one satellite, one customer. -/
def I0 : Instance 1 1 where
  d := fun _ _ => 1
  d_symm := fun _ _ _ => rfl
  triangle := fun _ _ _ _ _ _ => by norm_num
  q := fun _ => 1
  m1 := 1
  Q1 := 2
  U1 := 0
  B := fun _ => 1
  mSat := fun _ => 1
  Q2 := 1
  Q2_lt_Q1 := by norm_num
  m2 := 1
  m2_le := by simp
  U2 := 0
  H := fun _ => 0

@[simp] lemma I0_d (u v : Vertex 1 1) : I0.d u v = 1 := rfl
@[simp] lemma I0_q (i : Fin 1) : I0.q i = 1 := rfl
@[simp] lemma I0_m1 : I0.m1 = 1 := rfl
@[simp] lemma I0_Q1 : I0.Q1 = 2 := rfl
@[simp] lemma I0_U1 : I0.U1 = 0 := rfl
@[simp] lemma I0_B (k : Fin 1) : I0.B k = 1 := rfl
@[simp] lemma I0_mSat (k : Fin 1) : I0.mSat k = 1 := rfl
@[simp] lemma I0_Q2 : I0.Q2 = 1 := rfl
@[simp] lemma I0_m2 : I0.m2 = 1 := rfl
@[simp] lemma I0_U2 : I0.U2 = 0 := rfl
@[simp] lemma I0_H (k : Fin 1) : I0.H k = 0 := rfl

lemma injseq_eq (a b : InjSeq 1) : a = b := by
  obtain ⟨m, f⟩ := a
  obtain ⟨m', f'⟩ := b
  obtain rfl : m = m' := Subsingleton.elim _ _
  exact Sigma.ext rfl (heq_of_eq (Function.Embedding.ext (fun x => Subsingleton.elim _ _)))

lemma copies_one (s : InjSeq 1) : copies I0 s = 1 := by
  unfold copies
  split_ifs
  · simp [I0, qtot]
    first | rfl | decide | simp [Nat.ceilDiv_eq_add_pred_div]
  · rfl

def c1 : InjSeq 1 := ⟨⟨0, by norm_num⟩, ⟨fun _ => 0, fun a b _ => @Subsingleton.elim (Fin 1) _ a b⟩⟩

def l0 : Route2 I0 :=
  ⟨c1, Or.inl rfl, by
    calc ∑ i ∈ c1.toFinset, I0.q i ≤ ∑ i : Fin 1, I0.q i :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = I0.Q2 := by simp [I0]⟩

def r0 : Route1 I0 := ⟨⟨c1, Or.inl rfl⟩, ⟨0, by rw [copies_one]; norm_num⟩⟩

lemma r2_eq (l l' : Route2 I0) : l = l' := Subtype.ext (injseq_eq _ _)

lemma r1_eq (r r' : Route1 I0) : r = r' := by
  obtain ⟨s, j⟩ := r
  obtain ⟨s', j'⟩ := r'
  obtain rfl : s = s' := Subtype.ext (injseq_eq _ _)
  refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
  have h1 := lt_of_lt_of_eq j.isLt (copies_one s.1)
  have h2 := lt_of_lt_of_eq j'.isLt (copies_one s.1)
  show (j : ℕ) = (j' : ℕ)
  omega

lemma card2 : Fintype.card (Route2 I0) = 1 := Fintype.card_eq_one_iff.2 ⟨l0, fun l => r2_eq l l0⟩
lemma card1 : Fintype.card (Route1 I0) = 1 := Fintype.card_eq_one_iff.2 ⟨r0, fun r => r1_eq r r0⟩

lemma cust_all (l : Route2 I0) (i : Fin 1) : i ∈ custSet l := by
  rw [Subsingleton.elim i (l.1.2 0)]
  exact mem_cust0 I0 l

lemma sat_all (r : Route1 I0) (k : Fin 1) : k ∈ satSet r := by
  rw [Subsingleton.elim k (r.1.1.2 0)]
  simp [satSet, InjSeq.toFinset]

lemma load2_one (l : Route2 I0) : load2 l = 1 := by
  unfold load2
  rw [Finset.eq_univ_of_forall (cust_all l)]
  simp [I0]

lemma cost2_eq (k : Fin 1) (l : Route2 I0) : cost2 I0 k l = 2 := by
  have hz : ∑ j : Fin l.1.1.val, modCost I0 (some (Sum.inr (l.1.2 j.castSucc)))
      (some (Sum.inr (l.1.2 j.succ))) = 0 :=
    Finset.sum_eq_zero (fun j _ => absurd j.isLt (by have := l.1.1.isLt; omega))
  unfold cost2
  rw [hz]
  simp [modCost, load2_one]
  norm_num

lemma cost1_eq (r : Route1 I0) : cost1 I0 r = 2 := by
  have hz : ∑ j : Fin r.1.1.1.val, modCost I0 (some (Sum.inl (r.1.1.2 j.castSucc)))
      (some (Sum.inl (r.1.1.2 j.succ))) = 0 :=
    Finset.sum_eq_zero (fun j _ => absurd j.isLt (by have := r.1.1.1.isLt; omega))
  unfold cost1
  rw [hz]
  simp [modCost]
  norm_num

lemma lc0 (t : ℝ) (ht1 : 1 ≤ 2 * t) (ht2 : t ≤ 1) :
    LinearConstraints I0 (fun _ _ => 1) (fun _ => t) (fun _ _ => 1) := by
  have hf2 : ∀ i : Fin 1, univ.filter (fun l : Route2 I0 => i ∈ custSet l) = univ :=
    fun i => Finset.filter_true_of_mem (fun l _ => cust_all l i)
  have hf1 : ∀ k : Fin 1, univ.filter (fun r : Route1 I0 => k ∈ satSet r) = univ :=
    fun k => Finset.filter_true_of_mem (fun r _ => sat_all r k)
  have hs : ∀ r : Route1 I0, satSet r = univ := fun r => Finset.eq_univ_of_forall (sat_all r)
  refine ⟨fun i => ?_, fun k => ?_, ?_, fun k => ?_, ?_, fun k => ?_, fun r => ?_,
    fun r k hk => absurd (sat_all r k) hk⟩
  · rw [hf2]; simp [Finset.card_univ, card2]
  · simp [Finset.card_univ, card2]
  · simp [Finset.card_univ, card2]
  · simp [Finset.card_univ, card2, load2_one]
  · simp [Finset.card_univ, card1]; linarith
  · rw [hf1]; simp [Finset.card_univ, card1, card2, load2_one]
  · rw [hs]; simp; linarith

/-- Clause (c). -/
theorem clause_c : ∃ (ns nc : ℕ) (I : Instance ns nc),
      ((∀ u v, IsEdge u v → 0 ≤ I.d u v) ∧ 0 ≤ I.U1 ∧ 0 ≤ I.U2 ∧ (∀ k, 0 ≤ I.H k) ∧
        (∀ k, 0 ≤ I.B k) ∧ (∀ i, 0 < I.q i)) ∧
      (∃ x y qd, FFeasible I x y qd) ∧ zLF I < rfSup I := by
  refine ⟨1, 1, I0, ⟨fun _ _ _ => by simp [I0], by simp [I0], by simp [I0], fun _ => by simp [I0],
    fun _ => by simp [I0], fun _ => by simp [I0]⟩, ⟨fun _ _ => 1, fun _ => 1, fun _ _ => 1,
    lc0 1 (by norm_num) le_rfl, fun _ _ => Or.inr rfl, fun _ => Or.inr rfl,
    fun _ _ _ => ⟨1, by simp⟩⟩, ?_⟩
  have hLF : zLF I0 ≤ ((3 : ℝ) : EReal) := by
    refine sInf_le ⟨3, ⟨fun _ _ => 1, fun _ => 1 / 2, fun _ _ => 1,
      ⟨lc0 (1 / 2) (by norm_num) (by norm_num), fun _ _ => ⟨by norm_num, le_rfl⟩,
        fun _ => ⟨by norm_num, by norm_num⟩, fun _ _ => by norm_num⟩, ?_⟩, rfl⟩
    simp [objF, cost2_eq, cost1_eq, Finset.card_univ, card1, card2]
    norm_num
  have hmf : MultFeasible I0 (fun _ _ => 2) (fun _ => 0) (fun _ => 0) 0 := by
    refine ⟨fun _ => le_rfl, le_rfl, fun k l => ?_⟩
    simp [aCoef, cust_all, cost2_eq]
  have hRF : ((4 : ℝ) : EReal) ≤ zRF I0 (fun _ _ => 2) (fun _ => 0) (fun _ => 0) 0 := by
    refine le_sInf ?_
    rintro _ ⟨w, ⟨ξ, y, qd, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, rfl⟩, rfl⟩
    refine EReal.coe_le_coe_iff.2 ?_
    have hξ : ξ 0 0 = 1 := by simpa using h1 0
    have hb := h2 0
    rw [Finset.filter_true_of_mem (fun r _ => sat_all r 0)] at hb
    have hb1 : ∑ r, qd r 0 = 1 := by rw [hb]; simp [hξ]
    obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hb1]; norm_num :
      ∑ r, qd r 0 ≠ 0)
    have hcap := h5 r
    rw [Finset.eq_univ_of_forall (sat_all r)] at hcap
    simp only [Fin.sum_univ_one, I0_Q1] at hcap
    obtain ⟨n, hn⟩ := h7 r 0 (sat_all r 0)
    have hq0 : 0 < qd r 0 := by
      rw [hn] at hr ⊢
      exact lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hr)
    have hyr : y r = 1 := by
      rcases h6 r with h | h
      · rw [h] at hcap; push_cast at hcap; linarith
      · exact h
    have hy0 : ∀ r', 0 ≤ y r' := fun r' => by rcases h6 r' with h | h <;> rw [h] <;> norm_num
    have hsy : y r ≤ ∑ r', y r' :=
      Finset.single_le_sum (f := y) (fun r' _ => hy0 r') (Finset.mem_univ r)
    simp only [objRF, cost1_eq, Fin.sum_univ_one, hξ, Finset.sum_const_zero, mul_zero, add_zero]
    rw [← Finset.mul_sum]
    linarith
  have h34 : ((3 : ℝ) : EReal) < ((4 : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by norm_num)
  calc zLF I0 ≤ ((3 : ℝ) : EReal) := hLF
    _ < ((4 : ℝ) : EReal) := h34
    _ ≤ zRF I0 (fun _ _ => 2) (fun _ => 0) (fun _ => 0) 0 := hRF
    _ ≤ rfSup I0 := le_sSup ⟨_, _, _, _, hmf, rfl⟩

end ClauseC

end TECcc0

open TwoEchelonVRP in
theorem solution :
    (∀ (ns nc : ℕ) (I : Instance ns nc), zLF I ≤ rfSup I) ∧
    (∀ (ns nc : ℕ) (I : Instance ns nc), rfSup I ≠ ⊤ →
      ∃ β lam μ μ0, MultFeasible I β lam μ μ0 ∧ zRF I β lam μ μ0 = rfSup I) ∧
    (∃ (ns nc : ℕ) (I : Instance ns nc),
      ((∀ u v, IsEdge u v → 0 ≤ I.d u v) ∧ 0 ≤ I.U1 ∧ 0 ≤ I.U2 ∧ (∀ k, 0 ≤ I.H k) ∧
        (∀ k, 0 ≤ I.B k) ∧ (∀ i, 0 < I.q i)) ∧
      (∃ x y qd, FFeasible I x y qd) ∧ zLF I < rfSup I) := by
  exact ⟨fun ns nc I => TECcc0.clause_a I, fun ns nc I h => TECcc0.clause_b I h, TECcc0.clause_c⟩
