-- Prove2me | solution 1 for SelfDualLP.Regularity.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T15:45:53.014147+00:00
-- url     : https://prove2.me/submissions/fe4f98e2-b9b7-4308-8a28-3f3bef9b2d4e

import Mathlib
import Definitions.Def_SelfDualLP_Regularity_HLP

set_option autoImplicit false

namespace SDLP65

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


lemma key {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

lemma dot_nonneg {n : ℕ} (u v : Fin n → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) :
    0 ≤ u ⬝ᵥ v := by
  unfold dotProduct
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hu j) (hv j))

lemma dot_zero_imp {n : ℕ} (u v : Fin n → ℝ) (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 ≤ v j)
    (h : u ⬝ᵥ v = 0) : v = 0 := by
  unfold dotProduct at h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hu j).le (hv j))] at h
  funext j
  have := h j (Finset.mem_univ j)
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (hu j).ne'
  · simpa using h1

/-- An optimal primal-dual pair exists when both programs are feasible. -/
lemma lp_pair {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xp : Fin n → ℝ) (hxpA : A *ᵥ xp = b) (hxp0 : ∀ j, 0 ≤ xp j)
    (yp : Fin m → ℝ) (hyp : ∀ j, 0 ≤ c j - (Aᵀ *ᵥ yp) j) :
    ∃ x y, A *ᵥ x = b ∧ (∀ j, 0 ≤ x j) ∧ (∀ j, (Aᵀ *ᵥ y) j ≤ c j) ∧ c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  classical
  let a : (Fin m ⊕ Fin m ⊕ Fin n ⊕ Fin n ⊕ Unit) → (Fin n ⊕ Fin m) → ℝ :=
    Sum.elim (fun i => Sum.elim (fun j => A i j) (fun _ => 0))
      (Sum.elim (fun i => Sum.elim (fun j => -A i j) (fun _ => 0))
        (Sum.elim (fun j => Sum.elim (fun j' => if j' = j then -1 else 0) (fun _ => 0))
          (Sum.elim (fun j => Sum.elim (fun _ => 0) (fun i => A i j))
            (fun _ => Sum.elim c (fun i => -b i)))))
  let bb : (Fin m ⊕ Fin m ⊕ Fin n ⊕ Fin n ⊕ Unit) → ℝ :=
    Sum.elim b (Sum.elim (fun i => -b i) (Sum.elim (fun _ => 0) (Sum.elim c (fun _ => 0))))
  rcases fm_alt' a bb with ⟨z, hz⟩ | ⟨l, hl0, hl1, hl2⟩
  · refine ⟨fun j => z (Sum.inl j), fun i => z (Sum.inr i), ?_, ?_, ?_, ?_⟩
    · funext i
      have h1 := hz (Sum.inl i)
      have h2 := hz (Sum.inr (Sum.inl i))
      simp [a, bb, Fintype.sum_sum_type] at h1 h2
      simp only [Matrix.mulVec, dotProduct]
      linarith
    · intro j
      have h1 := hz (Sum.inr (Sum.inr (Sum.inl j)))
      simp [a, bb, Fintype.sum_sum_type] at h1
      linarith
    · intro j
      have h1 := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
      simp [a, bb, Fintype.sum_sum_type] at h1
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      linarith
    · have h1 := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
      simp [a, bb, Fintype.sum_sum_type] at h1
      simp only [dotProduct]
      have e1 : ∑ j, c j * z (Sum.inl j) = ∑ j, z (Sum.inl j) * c j :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      have e2 : ∑ i, b i * z (Sum.inr i) = ∑ i, z (Sum.inr i) * b i :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      linarith
  · exfalso
    let u : Fin m → ℝ := fun i => l (Sum.inl i) - l (Sum.inr (Sum.inl i))
    let v : Fin n → ℝ := fun j => l (Sum.inr (Sum.inr (Sum.inl j)))
    let w : Fin n → ℝ := fun j => l (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
    let t : ℝ := l (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
    have hv0 : ∀ j, 0 ≤ v j := fun j => hl0 _
    have hw0 : ∀ j, 0 ≤ w j := fun j => hl0 _
    have ht0 : 0 ≤ t := hl0 _
    have hX : Aᵀ *ᵥ u - v + t • c = 0 := by
      funext j
      have h1 := hl1 (Sum.inl j)
      simp [a, Fintype.sum_sum_type] at h1
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Matrix.mulVec, dotProduct, Matrix.transpose_apply, u, v, t, mul_sub,
        Finset.sum_sub_distrib]
      have e1 : ∑ i, A i j * l (Sum.inl i) = ∑ i, l (Sum.inl i) * A i j :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      have e2 : ∑ i, A i j * l (Sum.inr (Sum.inl i)) = ∑ i, l (Sum.inr (Sum.inl i)) * A i j :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      linarith
    have hY : A *ᵥ w - t • b = 0 := by
      funext i
      have h1 := hl1 (Sum.inr i)
      simp [a, Fintype.sum_sum_type] at h1
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Matrix.mulVec, dotProduct, w, t]
      have e1 : ∑ j, A i j * l (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))) =
          ∑ j, l (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))) * A i j :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      linarith
    have hS : u ⬝ᵥ b + w ⬝ᵥ c < 0 := by
      simp [bb, Fintype.sum_sum_type] at hl2
      simp only [dotProduct, u, w, sub_mul, Finset.sum_sub_distrib]
      linarith
    -- t * S = w ⬝ v
    have hXw := congrArg (fun z => w ⬝ᵥ z) hX
    have hYu := congrArg (fun z => u ⬝ᵥ z) hY
    have hXx := congrArg (fun z => xp ⬝ᵥ z) hX
    have hYy := congrArg (fun z => yp ⬝ᵥ z) hY
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      dotProduct_zero] at hXw hYu hXx hYy
    rw [key A w u] at hYu
    rw [key A w yp] at hYy
    rw [← key A xp u, hxpA] at hXx
    have hwv := dot_nonneg w v hw0 hv0
    have hxv := dot_nonneg xp v hxp0 hv0
    let sp : Fin n → ℝ := c - Aᵀ *ᵥ yp
    have hsp : ∀ j, 0 ≤ sp j := fun j => by simpa [sp] using hyp j
    have hws := dot_nonneg w sp hw0 hsp
    have hws' : w ⬝ᵥ sp = w ⬝ᵥ c - w ⬝ᵥ (Aᵀ *ᵥ yp) := by
      simp [sp, dotProduct_sub]
    have c1 : dotProduct u b = dotProduct b u := dotProduct_comm _ _
    have c2 : dotProduct w c = dotProduct c w := dotProduct_comm _ _
    have c3 : dotProduct yp b = dotProduct b yp := dotProduct_comm _ _
    have c4 : dotProduct xp c = dotProduct c xp := dotProduct_comm _ _
    -- t * S = w ⬝ v ≥ 0
    have htS : t * (u ⬝ᵥ b + w ⬝ᵥ c) = w ⬝ᵥ v := by
      linear_combination hXw - hYu
    have ht : t = 0 := by
      by_contra hne
      have : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hne)
      nlinarith
    rw [ht] at hXx hYy
    linarith

end SDLP65

open SelfDualLP.Regularity in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : ∃ x, PrimalInterior A b x)
    (hD : ∃ y, DualInterior A c y)
    (w : HLPPoint m n) (hw : IsSelfComplementary A b c w) :
    0 < w.τ := by
  obtain ⟨xp, hxpA, hxp0⟩ := hP
  obtain ⟨yp, hyp⟩ := hD
  obtain ⟨x', y', h1, h2, h3, h4⟩ := SDLP65.lp_pair A b c xp hxpA (fun j => (hxp0 j).le) yp
    (fun j => (hyp j).le)
  obtain ⟨hwF, hwopt⟩ := hw
  set e : Fin n → ℝ := fun _ => 1 with he
  set N : ℝ := e ⬝ᵥ e with hN
  have hN0 : 0 ≤ N := SDLP65.dot_nonneg e e (fun _ => zero_le_one) (fun _ => zero_le_one)
  -- general identity for HLP-feasible points
  have ident : ∀ z : HLPPoint m n, HLPFeasible A b c e (fun _ => 0) e z →
      z.x ⬝ᵥ z.s + z.τ * z.κ = (N + 1) * z.θ := by
    intro z hz
    obtain ⟨e1, e2, e3, e4, -⟩ := hz
    have e1y := congrArg (fun q => z.y ⬝ᵥ q) e1
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      dotProduct_zero] at e1y
    rw [SDLP65.key A z.x z.y] at e1y
    rw [e2, e3]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    have c1 : z.y ⬝ᵥ b = b ⬝ᵥ z.y := dotProduct_comm _ _
    have c2 : z.y ⬝ᵥ bBar A b e = bBar A b e ⬝ᵥ z.y := dotProduct_comm _ _
    have c3 : z.x ⬝ᵥ c = c ⬝ᵥ z.x := dotProduct_comm _ _
    have c4 : z.x ⬝ᵥ cBar A c (fun _ => 0) e = cBar A c (fun _ => 0) e ⬝ᵥ z.x :=
      dotProduct_comm _ _
    rw [c3, c4]
    rw [c1, c2] at e1y
    linear_combination (-1 : ℝ) * e1y - z.θ * e4
  -- a feasible point with θ = 0
  set s' : Fin n → ℝ := c - A.transpose.mulVec y' with hs'
  set κ' : ℝ := b ⬝ᵥ y' - c ⬝ᵥ x' with hκ'
  set V : ℝ := -(bBar A b e ⬝ᵥ y') + cBar A c (fun _ => 0) e ⬝ᵥ x' - zBar b c e (fun _ => 0)
    with hV
  have hs'0 : ∀ j, 0 ≤ s' j := fun j => by simpa [hs'] using h3 j
  have hκ'0 : 0 ≤ κ' := by simp only [hκ']; linarith
  have hVeq : V = -κ' - e ⬝ᵥ s' - e ⬝ᵥ x' - 1 := by
    simp only [hV, hκ', hs', bBar, cBar, zBar, sub_dotProduct, dotProduct_sub, dotProduct_zero,
      Matrix.mulVec_zero, sub_zero]
    rw [← SDLP65.key A e y']
    have c1 : y' ⬝ᵥ (A.mulVec e) = (A.mulVec e) ⬝ᵥ y' := dotProduct_comm _ _
    have c2 : c ⬝ᵥ e = e ⬝ᵥ c := dotProduct_comm _ _
    have c3 : e ⬝ᵥ x' = x' ⬝ᵥ e := dotProduct_comm _ _
    have z1 : (A.transpose.mulVec fun _ => (0:ℝ)) ⬝ᵥ x' = 0 := by
      simp only [Matrix.mulVec, dotProduct, mul_zero, Finset.sum_const_zero, zero_mul]
    have z2 : (b ⬝ᵥ fun _ => (0:ℝ)) = 0 := dotProduct_zero b
    rw [c1, c2, c3]
    linear_combination (-1:ℝ) * z1 + z2
  have hes := SDLP65.dot_nonneg e s' (fun _ => zero_le_one) hs'0
  have hex := SDLP65.dot_nonneg e x' (fun _ => zero_le_one) h2
  have hVneg : V ≤ -1 := by rw [hVeq]; linarith
  set lam : ℝ := (N + 1) / (-V) with hlam
  have hlam0 : 0 < lam := div_pos (by linarith) (by linarith)
  let v : HLPPoint m n := ⟨lam • y', lam • x', lam, 0, lam • s', lam * κ'⟩
  have hvF : HLPFeasible A b c e (fun _ => 0) e v := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [v, Matrix.mulVec_smul, h1, zero_smul, add_zero, sub_self]
    · simp only [v, hs', Matrix.mulVec_smul, zero_smul, sub_zero, smul_sub]
      abel
    · simp only [v, hκ', dotProduct_smul, smul_eq_mul, mul_zero, add_zero]
      ring
    · simp only [v, dotProduct_smul, smul_eq_mul]
      have : lam * V = -N - 1 := by
        rw [hlam, div_mul_eq_mul_div, div_eq_iff (by linarith : -V ≠ 0)]; ring
      rw [hV] at this
      linear_combination this
    · intro j; simp only [v, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hlam0.le (h2 j)
    · exact hlam0.le
    · intro j; simp only [v, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hlam0.le (hs'0 j)
    · exact mul_nonneg hlam0.le hκ'0
  have hθle : w.θ ≤ 0 := by
    have := hwopt v hvF
    simp only [HLPObjective, v, mul_zero] at this
    have hN1 : 0 < e ⬝ᵥ e + 1 := by linarith
    nlinarith
  have hθge : 0 ≤ w.θ := by
    have hid := ident w hwF
    obtain ⟨-, -, -, -, hx0, hτ0, hs0, hκ0⟩ := hwF
    have := SDLP65.dot_nonneg w.x w.s hx0 hs0
    have := mul_nonneg hτ0 hκ0
    nlinarith
  have hθ : w.θ = 0 := le_antisymm hθle hθge
  obtain ⟨e1, e2, e3, e4, hx0, hτ0, hs0, hκ0⟩ := hwF
  rcases lt_or_eq_of_le hτ0 with hτ | hτ
  · exact hτ
  exfalso
  rw [hθ] at e1 e2 e3
  rw [← hτ] at e1 e2 e4
  simp only [zero_smul, sub_zero, add_zero, mul_zero] at e1 e2 e3 e4
  -- e1 : A x = 0, e2 : s = -(A.transpose y), e3 : κ = b y - c x
  have hA1 : xp ⬝ᵥ w.s = -(b ⬝ᵥ w.y) := by
    rw [e2, dotProduct_neg, ← SDLP65.key A xp w.y, hxpA, dotProduct_comm]
  set sp : Fin n → ℝ := c - A.transpose.mulVec yp with hsp
  have hA2 : sp ⬝ᵥ w.x = c ⬝ᵥ w.x := by
    rw [hsp, sub_dotProduct, dotProduct_comm (A.transpose.mulVec yp), ← SDLP65.key A w.x yp, e1,
      dotProduct_zero, sub_zero]
  have hsp0 : ∀ j, 0 < sp j := fun j => by simpa [hsp] using hyp j
  have p1 := SDLP65.dot_nonneg xp w.s (fun j => (hxp0 j).le) hs0
  have p2 := SDLP65.dot_nonneg sp w.x (fun j => (hsp0 j).le) hx0
  have hs_z : w.s = 0 := SDLP65.dot_zero_imp xp w.s hxp0 hs0 (by linarith)
  have hx_z : w.x = 0 := SDLP65.dot_zero_imp sp w.x hsp0 hx0 (by linarith)
  have hby : b ⬝ᵥ w.y = 0 := by linarith
  have hAy : A.transpose.mulVec w.y = 0 := by
    have := e2; rw [hs_z] at this
    have h' := congrArg Neg.neg this
    simpa using h'.symm
  rw [hx_z] at e4
  simp only [bBar, sub_dotProduct, dotProduct_zero, add_zero] at e4
  rw [dotProduct_comm (A.mulVec e), SDLP65.key A e w.y, hAy, dotProduct_zero, hby] at e4
  linarith
