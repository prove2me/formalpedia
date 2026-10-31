-- Prove2me | solution 1 for SwitchCostGames.Stationary.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:23:58.246656+00:00
-- url     : https://prove2.me/submissions/adcec227-2d1d-4441-a978-480bd326a75e

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

open SwitchCostGames.Stationary

namespace SCGLemma1

open Finset

/-- If a probability vector `w` averages `f` to at least an upper bound `M` of `f`, then `f = M`
on the support of `w`. -/
theorem eq_of_avg_ge {α : Type*} [Fintype α] (w f : α → ℝ) (hw : BlottoLP.Flow.IsMixed w)
    (M : ℝ) (hM : ∀ a, f a ≤ M) (havg : M ≤ ∑ a, w a * f a) : ∀ a, w a ≠ 0 → f a = M := by
  have hsum : ∑ a, w a * (M - f a) = 0 := by
    have e : ∑ a, w a * (M - f a) = M * ∑ a, w a - ∑ a, w a * f a := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    have hnn : 0 ≤ ∑ a, w a * (M - f a) :=
      Finset.sum_nonneg (fun a _ => mul_nonneg (hw.1 a) (by linarith [hM a]))
    rw [hw.2] at e
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    mul_nonneg (hw.1 a) (by linarith [hM a]))).1 hsum
  intro a ha
  have := hz a (Finset.mem_univ a)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h ha
  · linarith

theorem expPay_pure_left {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : ι → κ → ℝ) (i : ι) (q : κ → ℝ) :
    BlottoLP.Flow.expPay M (BlottoLP.Flow.pureMixed i) q = ∑ j, q j * M i j := by
  simp [BlottoLP.Flow.expPay, BlottoLP.Flow.pureMixed]

theorem expPay_pure_right {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : ι → κ → ℝ) (p : ι → ℝ) (j : κ) :
    BlottoLP.Flow.expPay M p (BlottoLP.Flow.pureMixed j) = ∑ i, p i * M i j := by
  simp [BlottoLP.Flow.expPay, BlottoLP.Flow.pureMixed]

theorem pureMixed_isMixed {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    BlottoLP.Flow.IsMixed (BlottoLP.Flow.pureMixed a) := by
  refine ⟨fun b => ?_, ?_⟩
  · unfold BlottoLP.Flow.pureMixed; split_ifs <;> norm_num
  · simp [BlottoLP.Flow.pureMixed]

theorem expPay_rows {ι κ : Type*} [Fintype ι] [Fintype κ] (M : ι → κ → ℝ) (p : ι → ℝ)
    (q : κ → ℝ) : BlottoLP.Flow.expPay M p q = ∑ i, p i * ∑ j, q j * M i j := by
  unfold BlottoLP.Flow.expPay
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem expPay_cols {ι κ : Type*} [Fintype ι] [Fintype κ] (M : ι → κ → ℝ) (p : ι → ℝ)
    (q : κ → ℝ) : BlottoLP.Flow.expPay M p q = ∑ j, q j * ∑ i, p i * M i j := by
  unfold BlottoLP.Flow.expPay
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The minimum of finitely many affine functions of one real variable is piecewise affine. -/
theorem pw_inf {P : Type*} [Fintype P] [Nonempty P] (a c : P → ℝ) :
    IsPiecewiseAffineOn (fun t : ℝ => (univ : Finset P).inf' univ_nonempty
      (fun p => a p + c p * t)) Set.univ := by
  classical
  refine ⟨(univ : Finset (P × P)).image
    (fun pq => if c pq.1 = c pq.2 then 0 else (a pq.2 - a pq.1) / (c pq.1 - c pq.2)), ?_⟩
  intro lo hi hlohi _ hB
  rcases eq_or_lt_of_le hlohi with heq | hlt
  · refine ⟨(univ : Finset P).inf' univ_nonempty (fun p => a p + c p * lo), 0, ?_⟩
    intro t ht
    have : t = lo := le_antisymm (heq ▸ ht.2) ht.1
    subst this; simp
  · set t0 := (lo + hi) / 2 with ht0
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := P))
      (fun p => a p + c p * t0)
    refine ⟨a p, c p, ?_⟩
    intro t ht
    apply le_antisymm
    · exact Finset.inf'_le _ (Finset.mem_univ p)
    · refine Finset.le_inf' _ _ (fun q _ => ?_)
      by_contra hcon
      push_neg at hcon
      have h0 : a p + c p * t0 ≤ a q + c q * t0 := by
        rw [← hp]; exact Finset.inf'_le _ (Finset.mem_univ q)
      have hne : c p ≠ c q := by
        intro h; rw [h] at h0 hcon; linarith
      set z := (a q - a p) / (c p - c q) with hz
      have hzB : z ∈ (univ : Finset (P × P)).image
          (fun pq => if c pq.1 = c pq.2 then 0 else (a pq.2 - a pq.1) / (c pq.1 - c pq.2)) := by
        refine Finset.mem_image.2 ⟨(p, q), Finset.mem_univ _, ?_⟩
        simp [hne, hz]
      have hd : c p - c q ≠ 0 := sub_ne_zero.2 hne
      have hzeq : a q - a p = z * (c p - c q) := by rw [hz]; field_simp
      apply hB z hzB
      -- D(s) = (a q + c q s) - (a p + c p s) = (c p - c q) * (z - s)
      have hD0 : 0 ≤ (c p - c q) * (z - t0) := by nlinarith
      have hDt : (c p - c q) * (z - t) < 0 := by nlinarith
      rcases lt_or_gt_of_ne hd with hneg | hpos
      · -- c p - c q < 0 : z ≤ t0 and z > t
        have h1 : z - t0 ≤ 0 := by
          by_contra h; push_neg at h; nlinarith
        have h2 : 0 < z - t := by
          by_contra h; push_neg at h; nlinarith
        constructor <;> linarith [ht.1, ht.2]
      · have h1 : 0 ≤ z - t0 := by
          by_contra h; push_neg at h; nlinarith
        have h2 : z - t < 0 := by
          by_contra h; push_neg at h; nlinarith
        constructor <;> linarith [ht.1, ht.2]

end SCGLemma1

open SCGLemma1 Finset

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A : ι → κ → ℝ) (b : κ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (v : (κ → ℝ) → ℝ) (hv : ∀ x, IsSaddleValue (paramGame A b x) (v x)) :
    Continuous v ∧ Monotone v ∧ ConcaveOn ℝ Set.univ v ∧
      ∀ x d : κ → ℝ, IsPiecewiseAffineOn (fun t : ℝ => v (x + t • d)) Set.univ := by
  classical
  -- candidate strategies of player 2, one per pair of supports `(I₁, I₂)`
  let Cond : Finset ι × Finset κ → (κ → ℝ) → Prop := fun P y =>
    BlottoLP.Flow.IsMixed y ∧ (∀ j, j ∉ P.2 → y j = 0) ∧
      (∀ k ∈ P.1, ∀ i, ∑ j, y j * A i j ≤ ∑ j, y j * A k j)
  let j0 : κ := Classical.arbitrary κ
  let y : Finset ι × Finset κ → κ → ℝ := fun P =>
    if h : ∃ y, Cond P y then Classical.choose h else BlottoLP.Flow.pureMixed j0
  have hy_mixed : ∀ P, BlottoLP.Flow.IsMixed (y P) := by
    intro P
    by_cases h : ∃ y, Cond P y
    · simp only [y, dif_pos h]; exact (Classical.choose_spec h).1
    · simp only [y, dif_neg h]; exact pureMixed_isMixed j0
  have hy_cond : ∀ P, (∃ y, Cond P y) → Cond P (y P) := by
    intro P h
    simp only [y, dif_pos h]; exact Classical.choose_spec h
  let α : Finset ι × Finset κ → ℝ := fun P =>
    (univ : Finset ι).sup' univ_nonempty (fun i => ∑ j, y P j * A i j)
  let g : Finset ι × Finset κ → (κ → ℝ) → ℝ := fun P x => α P + ∑ j, y P j * b j * x j
  -- the row payoff against `y P` in `Γ(x)` splits off the row-independent part
  have hrow : ∀ P x i, ∑ j, y P j * paramGame A b x i j =
      ∑ j, y P j * A i j + ∑ j, y P j * b j * x j := by
    intro P x i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp only [paramGame]; ring)
  -- main identity: `v x = min_P g P x`
  have hmain : ∀ x, v x = (univ : Finset (Finset ι × Finset κ)).inf' univ_nonempty
      (fun P => g P x) := by
    intro x
    obtain ⟨p, q, ⟨hp, hq, hp1, hq1⟩, hval⟩ := hv x
    set M := paramGame A b x with hMdef
    apply le_antisymm
    · -- `v x ≤ g P x` for every `P`
      refine Finset.le_inf' _ _ (fun P _ => ?_)
      rw [← hval]
      calc BlottoLP.Flow.expPay M p q ≤ BlottoLP.Flow.expPay M p (y P) := hq1 _ (hy_mixed P)
        _ = ∑ i, p i * ∑ j, y P j * M i j := expPay_rows M p (y P)
        _ ≤ ∑ i, p i * g P x := by
          refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (hp.1 i))
          rw [hrow]
          have : ∑ j, y P j * A i j ≤ α P :=
            Finset.le_sup' (fun i => ∑ j, y P j * A i j) (Finset.mem_univ i)
          simp only [g]; linarith
        _ = g P x := by rw [← Finset.sum_mul, hp.2, one_mul]
    · -- the support pair of `(p, q)`
      let colpay : κ → ℝ := fun j => ∑ i, p i * M i j
      let mn : ℝ := (univ : Finset κ).inf' univ_nonempty colpay
      let rowpay : ι → ℝ := fun i => ∑ j, q j * M i j
      let mx : ℝ := (univ : Finset ι).sup' univ_nonempty rowpay
      have hv_col : BlottoLP.Flow.expPay M p q = ∑ j, q j * colpay j := expPay_cols M p q
      have hv_row : BlottoLP.Flow.expPay M p q = ∑ i, p i * rowpay i := expPay_rows M p q
      -- `q` is supported on minimizing columns
      have hq_supp : ∀ j, q j ≠ 0 → colpay j = mn := by
        have := eq_of_avg_ge q (fun j => - colpay j) hq (-mn)
          (fun j => neg_le_neg (Finset.inf'_le _ (Finset.mem_univ j)))
          (by
            obtain ⟨j1, -, hj1⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := κ)) colpay
            have h := hq1 _ (pureMixed_isMixed j1)
            rw [expPay_pure_right, hv_col] at h
            have e : ∑ j, q j * -colpay j = -∑ j, q j * colpay j := by
              rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
            rw [e]
            change ∑ j, q j * colpay j ≤ colpay j1 at h
            have hmn : mn = colpay j1 := hj1
            rw [hmn]; linarith)
        intro j hj
        have := this j hj
        linarith
      have hp_supp : ∀ i, p i ≠ 0 → rowpay i = mx := by
        refine eq_of_avg_ge p rowpay hp mx
          (fun i => Finset.le_sup' _ (Finset.mem_univ i)) ?_
        obtain ⟨i1, -, hi1⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := ι)) rowpay
        have h := hp1 _ (pureMixed_isMixed i1)
        rw [expPay_pure_left, hv_row] at h
        have hmx : mx = rowpay i1 := hi1
        rw [hmx]; exact h
      let P : Finset ι × Finset κ :=
        ((univ : Finset ι).filter (fun i => p i ≠ 0),
          (univ : Finset κ).filter (fun j => colpay j = mn))
      have hqcond : Cond P q := by
        refine ⟨hq, ?_, ?_⟩
        · intro j hj
          by_contra hne
          exact hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, hq_supp j hne⟩)
        · intro k hk i
          have hk' : p k ≠ 0 := (Finset.mem_filter.1 hk).2
          have h1 : rowpay i ≤ rowpay k := by
            rw [hp_supp k hk']; exact Finset.le_sup' _ (Finset.mem_univ i)
          have e : ∀ i, rowpay i = ∑ j, q j * A i j + ∑ j, q j * b j * x j := by
            intro i
            change ∑ j, q j * paramGame A b x i j = _
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun j _ => by simp only [paramGame]; ring)
          rw [e, e] at h1
          linarith
      obtain ⟨hyP, hyP2, hyP1⟩ := hy_cond P ⟨q, hqcond⟩
      refine (Finset.inf'_le _ (Finset.mem_univ P)).trans ?_
      -- `g P x` equals the payoff of `(p, y P)`, which equals `mn ≤ v x`
      have hrow_eq : ∀ i, p i ≠ 0 → ∑ j, y P j * M i j = g P x := by
        intro i hi
        rw [hrow]
        have hiP : i ∈ P.1 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
        have : α P = ∑ j, y P j * A i j := by
          apply le_antisymm
          · exact Finset.sup'_le _ _ (fun i' _ => hyP1 i hiP i')
          · exact Finset.le_sup' (fun i => ∑ j, y P j * A i j) (Finset.mem_univ i)
        simp only [g]; rw [this]
      have hcol_eq : ∀ j, y P j ≠ 0 → colpay j = mn := by
        intro j hj
        by_contra hne
        exact hj (hyP2 j (fun hm => hne (Finset.mem_filter.1 hm).2))
      have e1 : BlottoLP.Flow.expPay M p (y P) = g P x := by
        rw [expPay_rows]
        calc ∑ i, p i * ∑ j, y P j * M i j = ∑ i, p i * g P x := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              by_cases hi : p i = 0
              · simp [hi]
              · rw [hrow_eq i hi]
          _ = g P x := by rw [← Finset.sum_mul, hp.2, one_mul]
      have e2 : BlottoLP.Flow.expPay M p (y P) = mn := by
        rw [expPay_cols]
        calc ∑ j, y P j * ∑ i, p i * M i j = ∑ j, y P j * mn := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              by_cases hj : y P j = 0
              · simp [hj]
              · exact congrArg _ (hcol_eq j hj)
          _ = mn := by rw [← Finset.sum_mul, hyP.2, one_mul]
      have e3 : mn ≤ v x := by
        rw [← hval, hv_col]
        calc mn = ∑ j, q j * mn := by rw [← Finset.sum_mul, hq.2, one_mul]
          _ ≤ ∑ j, q j * colpay j := Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ j)) (hq.1 j))
      linarith
  have hvfun : v = fun x => (univ : Finset (Finset ι × Finset κ)).inf' univ_nonempty
      (fun P => g P x) := funext hmain
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hvfun]
    refine Continuous.finset_inf'_apply _ (fun P _ => ?_)
    simp only [g]
    fun_prop
  · intro x x' hxx'
    rw [hmain x, hmain x']
    refine Finset.le_inf' _ _ (fun P _ => (Finset.inf'_le _ (Finset.mem_univ P)).trans ?_)
    simp only [g]
    have : ∑ j, y P j * b j * x j ≤ ∑ j, y P j * b j * x' j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxx' j)
        (mul_nonneg ((hy_mixed P).1 j) (hb j)))
    linarith
  · refine ⟨convex_univ, ?_⟩
    intro x _ x' _ s t hs ht hst
    rw [hmain x, hmain x', hmain (s • x + t • x')]
    refine Finset.le_inf' _ _ (fun P _ => ?_)
    have h1 := Finset.inf'_le (fun P => g P x) (Finset.mem_univ P)
    have h2 := Finset.inf'_le (fun P => g P x') (Finset.mem_univ P)
    have e : g P (s • x + t • x') = s * g P x + t * g P x' := by
      simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e2 : ∑ j, y P j * b j * (s * x j + t * x' j) =
          s * ∑ j, y P j * b j * x j + t * ∑ j, y P j * b j * x' j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [e2]; linear_combination (-α P) * hst
    rw [e, smul_eq_mul, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
  · intro x d
    have := pw_inf (P := Finset ι × Finset κ) (fun P => α P + ∑ j, y P j * b j * x j)
      (fun P => ∑ j, y P j * b j * d j)
    convert this using 2 with t
    rw [hmain]
    refine Finset.inf'_congr _ rfl (fun P _ => ?_)
    simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_assoc, Finset.sum_mul, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
