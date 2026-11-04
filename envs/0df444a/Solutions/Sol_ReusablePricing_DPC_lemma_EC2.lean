-- Prove2me | solution 1 for ReusablePricing.DPC.lemma_EC2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T04:05:56.959208+00:00
-- url     : https://prove2.me/submissions/1fde5895-4692-4b95-813d-90dfe635a78c

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control

open Finset ReusablePricing.DPC

/-- Supermartingale form of the chain rule: if each one-step weight is nonnegative, depends only on
the past, and has total mass at most one, then the path weights have total mass at most one. -/
lemma dpc_chain_le_one {α : Type} [Fintype α] [DecidableEq α] [Inhabited α] :
    ∀ (N : ℕ) (f : ℕ → (Fin N → α) → α → ℝ),
      (∀ t ω a, 0 ≤ f t ω a) →
      (∀ t ω, ∑ a, f t ω a ≤ 1) →
      (∀ t ω ω', (∀ s : Fin N, s.val < t → ω s = ω' s) → f t ω = f t ω') →
      ∑ ω : Fin N → α, ∏ t : Fin N, f t ω (ω t) ≤ 1 := by
  intro N
  induction N with
  | zero => intro f _ _ _; simp
  | succ N ih =>
    intro f hnn hsum hdep
    let a0 : α := default
    let g : ℕ → (Fin N → α) → α → ℝ := fun t ω => f t (Fin.snoc ω a0)
    have hgnn : ∀ t ω a, 0 ≤ g t ω a := fun t ω a => hnn t _ a
    have hg1 : ∀ t ω, ∑ a, g t ω a ≤ 1 := fun t ω => hsum t _
    have hgdep : ∀ t ω ω', (∀ s : Fin N, s.val < t → ω s = ω' s) → g t ω = g t ω' := by
      intro t ω ω' h
      apply hdep
      intro s hs
      cases s using Fin.lastCases with
      | last => simp
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact h i (by simpa using hs)
    have hsn : ∀ (ω : Fin N → α) (a : α) (t : ℕ), t ≤ N →
        f t (Fin.snoc ω a) = f t (Fin.snoc ω a0) := by
      intro ω a t ht
      apply hdep
      intro s hs
      cases s using Fin.lastCases with
      | last => simp at hs; omega
      | cast i => simp
    have key : ∀ (ω : Fin N → α) (a : α),
        ∏ t : Fin (N + 1), f t (Fin.snoc ω a) ((Fin.snoc ω a : Fin (N+1) → α) t)
          = (∏ t : Fin N, g t ω (ω t)) * f N (Fin.snoc ω a0) a := by
      intro ω a
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro t _
        simp only [Fin.snoc_castSucc, Fin.val_castSucc, g]
        rw [hsn ω a t (by omega)]
      · simp only [Fin.snoc_last, Fin.val_last]
        rw [hsn ω a N le_rfl]
    rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine le_trans ?_ (ih g hgnn hg1 hgdep)
    apply Finset.sum_le_sum
    intro ω _
    have : ∀ a, (fun x : (fun _ => α) (Fin.last N) × ((i : Fin N) → (fun _ => α) i.castSucc) =>
        ∏ t : Fin (N + 1), f t ((Fin.snocEquiv fun _ => α) x) ((Fin.snocEquiv fun _ => α) x t)) (a, ω)
        = (∏ t : Fin N, g t ω (ω t)) * f N (Fin.snoc ω a0) a := fun a => key ω a
    simp only at this
    rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.mul_sum]
    have hp : 0 ≤ ∏ t : Fin N, g t ω (ω t) := Finset.prod_nonneg (fun t _ => hgnn _ _ _)
    calc (∏ t : Fin N, g t ω (ω t)) * ∑ a, f N (Fin.snoc ω a0) a
        ≤ (∏ t : Fin N, g t ω (ω t)) * 1 := mul_le_mul_of_nonneg_left (hsum _ _) hp
      _ = _ := mul_one _

lemma dpc_q_sum (P : Basic) (x : Fin P.J → ℝ) : ∑ a, P.q x a = 1 := by
  rw [Fintype.sum_option]
  simp [Basic.q]

lemma dpc_outcome_succ (P : Basic) (ω : P.Path) (i : Fin P.T) :
    P.outcome (i.val + 1) ω = ω i := by
  unfold Basic.outcome
  rw [dif_pos ⟨by omega, by omega⟩]
  exact congrArg ω (Fin.ext (by simp))

lemma dpc_D_dep (P : Basic) (ω ω' : P.Path) (t s : ℕ) (hs : s ≤ t)
    (h : ∀ u : Fin P.T, u.val < t → ω u = ω' u) : ∀ j, P.D s ω j = P.D s ω' j := by
  intro j
  unfold Basic.D Basic.outcome
  by_cases hc : 1 ≤ s ∧ s ≤ P.T
  · rw [dif_pos hc, dif_pos hc, h ⟨s - 1, by omega⟩ (by simp; omega)]
  · rw [dif_neg hc, dif_neg hc]

lemma dpc_rate_dep (P : Basic) (ε : ℝ) (nl : ℕ) (t : ℕ) (ω ω' : P.Path)
    (h : ∀ u : Fin P.T, u.val < t → ω u = ω' u) :
    P.dpcRate ε nl (t + 1) ω = P.dpcRate ε nl (t + 1) ω' := by
  have hf : ∀ i, P.freeCap (t + 1) ω i = P.freeCap (t + 1) ω' i := by
    intro i
    unfold Basic.freeCap
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_Icc] at hs
    apply Finset.sum_congr rfl
    intro j _
    rw [dpc_D_dep P ω ω' t s (by omega) h j]
  funext j
  unfold Basic.dpcRate
  simp only [hf]

lemma dpc_rate_mem (P : Basic) (ε : ℝ) (nl : ℕ) (hU : 0 ≤ P.lamU) (t : ℕ) (ω : P.Path)
    (j : Fin P.J) : 0 ≤ P.dpcRate ε nl t ω j ∧ P.dpcRate ε nl t ω j ≤ P.lamU := by
  unfold Basic.dpcRate
  split_ifs <;> first
    | exact ⟨le_max_left _ _, max_le hU (min_le_left _ _)⟩
    | exact ⟨le_rfl, hU⟩

lemma dpc_pathProb_nonneg (P : Basic) (ε : ℝ) (nl : ℕ) (hU : 0 ≤ P.lamU)
    (hJU : (P.J : ℝ) * P.lamU ≤ 1) (ω : P.Path) : 0 ≤ P.pathProb ε nl ω := by
  unfold Basic.pathProb
  apply Finset.prod_nonneg
  intro t _
  cases h : P.outcome t ω with
  | none =>
    simp only [Basic.q]
    have : ∑ j, P.dpcRate ε nl t ω j ≤ ∑ _j : Fin P.J, P.lamU :=
      Finset.sum_le_sum (fun j _ => (dpc_rate_mem P ε nl hU t ω j).2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  | some j => exact (dpc_rate_mem P ε nl hU t ω j).1


/-- Bernoulli MGF bound: `(1-l)e^{-xl} + l e^{x(1-l)} ≤ e^{x² l}` for `|x| ≤ 1`, `l ∈ [0,1]`. -/
lemma dpc_mgf (x l : ℝ) (hx : |x| ≤ 1) (hl0 : 0 ≤ l) :
    (1 - l) * Real.exp (-x * l) + l * Real.exp (x * (1 - l)) ≤ Real.exp (x ^ 2 * l) := by
  have h1 : (1 - l) * Real.exp (-x * l) + l * Real.exp (x * (1 - l)) =
      Real.exp (-x * l) * (1 + l * (Real.exp x - 1)) := by
    rw [show x * (1 - l) = x + -x * l by ring, Real.exp_add]; ring
  have h2 : 1 + l * (Real.exp x - 1) ≤ Real.exp (l * (Real.exp x - 1)) := by
    linarith [Real.add_one_le_exp (l * (Real.exp x - 1))]
  have h3 : Real.exp x - 1 ≤ x + x ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le hx
    linarith [le_abs_self (Real.exp x - 1 - x)]
  have h4 : l * (Real.exp x - 1) ≤ l * (x + x ^ 2) := mul_le_mul_of_nonneg_left h3 hl0
  rw [h1]
  calc Real.exp (-x * l) * (1 + l * (Real.exp x - 1))
      ≤ Real.exp (-x * l) * Real.exp (l * (x + x ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact h2.trans (Real.exp_le_exp.mpr h4)
    _ = Real.exp (x ^ 2 * l) := by rw [← Real.exp_add]; ring_nf

lemma dpc_q_sum_ind (P : Basic) (x : Fin P.J → ℝ) (j : Fin P.J) (h0 h1 : ℝ) :
    ∑ a, P.q x a * (if a = some j then h1 else h0) = (1 - x j) * h0 + x j * h1 := by
  rw [Fintype.sum_option]
  simp only [Basic.q, reduceCtorEq, if_false, Option.some.injEq]
  have : ∑ j' : Fin P.J, x j' * (if j' = j then h1 else h0) =
      ∑ j' : Fin P.J, x j' * h0 + x j * (h1 - h0) := by
    have e : ∀ j', x j' * (if j' = j then h1 else h0) =
        x j' * h0 + (if j' = j then x j' * (h1 - h0) else 0) := by
      intro j'; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j' _ => e j'), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  rw [this, ← Finset.sum_mul]; ring

lemma dpc_pathProb_prod (P : Basic) (ε : ℝ) (nl : ℕ) (ω : P.Path) :
    P.pathProb ε nl ω = ∏ i : Fin P.T, P.q (P.dpcRate ε nl (i.val + 1) ω) (ω i) := by
  unfold Basic.pathProb
  have hI : Icc 1 P.T = Ico (0 + 1) (P.T + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [hI, ← Finset.prod_Ico_add', ← Finset.range_eq_Ico,
    ← Fin.prod_univ_eq_prod_range (fun i => P.q (P.dpcRate ε nl (i + 1) ω)
      (P.outcome (i + 1) ω))]
  apply Finset.prod_congr rfl
  intro i _
  rw [dpc_outcome_succ]

lemma dpc_Icc_prod (P : Basic) (F : ℕ → ℝ) :
    ∏ t ∈ Icc 1 P.T, F t = ∏ i : Fin P.T, F (i.val + 1) := by
  have hI : Icc 1 P.T = Ico (0 + 1) (P.T + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [hI, ← Finset.prod_Ico_add', ← Finset.range_eq_Ico, ← Fin.prod_univ_eq_prod_range]

/-- The exponential supermartingale factor of period `t`, switched on by `act t ω`. -/
noncomputable def dpcG (P : Basic) (ε : ℝ) (nl : ℕ) (j : Fin P.J) (y : ℝ)
    (act : ℕ → P.Path → Prop) [∀ t ω, Decidable (act t ω)] (t : ℕ) (ω : P.Path) : ℝ :=
  if act t ω then Real.exp (y * P.Delta ε nl t ω j - y ^ 2 * P.dpcRate ε nl t ω j) else 1

/-- `E[∏_t G_t] ≤ 1` for a predictable switch `act`. -/
lemma dpc_E_prod_le_one (P : Basic) (ε : ℝ) (nl : ℕ) (hU : 0 ≤ P.lamU)
    (hJU : (P.J : ℝ) * P.lamU ≤ 1) (j : Fin P.J) (y : ℝ) (hy : |y| ≤ 1)
    (act : ℕ → P.Path → Prop) [∀ t ω, Decidable (act t ω)]
    (hact : ∀ t ω ω', (∀ u : Fin P.T, u.val + 1 < t → ω u = ω' u) → (act t ω ↔ act t ω')) :
    ∑ ω, P.pathProb ε nl ω * ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω ≤ 1 := by
  let f : ℕ → P.Path → Option (Fin P.J) → ℝ := fun i ω a =>
    P.q (P.dpcRate ε nl (i + 1) ω) a *
      (if act (i + 1) ω then
        Real.exp (y * ((if a = some j then 1 else 0) - P.dpcRate ε nl (i + 1) ω j) -
          y ^ 2 * P.dpcRate ε nl (i + 1) ω j) else 1)
  have hrw : ∀ ω, P.pathProb ε nl ω * ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω =
      ∏ i : Fin P.T, f i ω (ω i) := by
    intro ω
    rw [dpc_pathProb_prod, dpc_Icc_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [f, dpcG, Basic.Delta, Basic.D, dpc_outcome_succ]
  simp_rw [hrw]
  have hq0 : ∀ i ω a, 0 ≤ P.q (P.dpcRate ε nl (i + 1) ω) a := by
    intro i ω a
    cases a with
    | none =>
      simp only [Basic.q]
      have : ∑ j, P.dpcRate ε nl (i + 1) ω j ≤ ∑ _j : Fin P.J, P.lamU :=
        Finset.sum_le_sum (fun j _ => (dpc_rate_mem P ε nl hU (i + 1) ω j).2)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    | some j => exact (dpc_rate_mem P ε nl hU (i + 1) ω j).1
  apply dpc_chain_le_one P.T f
  · intro i ω a
    apply mul_nonneg (hq0 i ω a)
    split_ifs <;> first | exact (Real.exp_pos _).le | norm_num
  · intro i ω
    simp only [f]
    split_ifs with hac
    · set x := P.dpcRate ε nl (i + 1) ω with hx
      have e : ∀ a : Option (Fin P.J), Real.exp (y * ((if a = some j then 1 else 0) - x j) -
          y ^ 2 * x j) = if a = some j then Real.exp (y * (1 - x j) - y ^ 2 * x j)
            else Real.exp (y * (0 - x j) - y ^ 2 * x j) := by
        intro a; split_ifs <;> rfl
      simp_rw [e]
      rw [dpc_q_sum_ind]
      have hm := dpc_mgf y (x j) hy (dpc_rate_mem P ε nl hU (i + 1) ω j).1
      have e2 : (1 - x j) * Real.exp (y * (0 - x j) - y ^ 2 * x j) +
          x j * Real.exp (y * (1 - x j) - y ^ 2 * x j) =
          ((1 - x j) * Real.exp (-y * x j) + x j * Real.exp (y * (1 - x j))) *
            Real.exp (-(y ^ 2 * x j)) := by
        rw [show y * (0 - x j) - y ^ 2 * x j = -y * x j + -(y ^ 2 * x j) by ring,
          show y * (1 - x j) - y ^ 2 * x j = y * (1 - x j) + -(y ^ 2 * x j) by ring,
          Real.exp_add, Real.exp_add]; ring
      rw [e2]
      calc ((1 - x j) * Real.exp (-y * x j) + x j * Real.exp (y * (1 - x j))) *
            Real.exp (-(y ^ 2 * x j))
          ≤ Real.exp (y ^ 2 * x j) * Real.exp (-(y ^ 2 * x j)) :=
            mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    · simp only [mul_one]; rw [dpc_q_sum]
  · intro i ω ω' h
    have hr := dpc_rate_dep P ε nl i ω ω' h
    have ha := hact (i + 1) ω ω' (fun u hu => h u (by omega))
    funext a
    simp only [f, hr]
    by_cases hc : act (i + 1) ω
    · rw [if_pos hc, if_pos (ha.mp hc)]
    · rw [if_neg hc, if_neg (fun h' => hc (ha.mpr h'))]

/-- Along every path, the rates DPC posts for type `j` within one service cycle sum to at most
`min{max_i C_i, n}`. -/
lemma dpc_cycle_rate (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε : ℝ)
    (hP : P.Standing φL φU Ψ R nl) (hε : 0 ≤ ε) (j : Fin P.J) (b : ℕ)
    (hb : b ∈ Icc 1 (P.T / P.n)) (ω : P.Path) (A : Finset ℕ)
    (hA : A ⊆ Icc ((b - 1) * P.n + 1) (b * P.n)) :
    ∑ s ∈ A, P.dpcRate ε nl s ω j ≤ P.minCapN := by
  obtain ⟨hMF, hOpt, -⟩ := hP
  obtain ⟨-, -, hn1, hT1, hdvd, hA1, hcol, -, hU0, hU1, -⟩ := hMF
  rw [Finset.mem_Icc] at hb
  have hbT : b * P.n ≤ P.T := by
    obtain ⟨k, hk⟩ := hdvd
    have : P.T / P.n = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega)]
    rw [this] at hb; rw [hk]; nlinarith [hb.2]
  have hb1 : P.n ≤ b * P.n := by nlinarith [hb.1]
  set Cy := Icc ((b - 1) * P.n + 1) (b * P.n) with hCy
  have hCyT : Cy ⊆ Icc 1 P.T := Finset.Icc_subset_Icc (by omega) hbT
  have hr0 : ∀ s, 0 ≤ P.dpcRate ε nl s ω j := fun s => (dpc_rate_mem P ε nl hU0.le s ω j).1
  have hsub : ∑ s ∈ A, P.dpcRate ε nl s ω j ≤ ∑ s ∈ Cy, P.dpcRate ε nl s ω j :=
    Finset.sum_le_sum_of_subset_of_nonneg hA (fun s _ _ => hr0 s)
  have hcard : (Cy.card : ℝ) = P.n := by
    rw [hCy, Nat.card_Icc]
    have : b * P.n + 1 - ((b - 1) * P.n + 1) = P.n := by
      have : (b - 1) * P.n + P.n = b * P.n := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hb.1]
      omega
    rw [this]
  -- bound by `n`
  have hN : ∑ s ∈ Cy, P.dpcRate ε nl s ω j ≤ P.n := by
    calc ∑ s ∈ Cy, P.dpcRate ε nl s ω j ≤ ∑ _s ∈ Cy, (1 : ℝ) :=
          Finset.sum_le_sum (fun s _ => (dpc_rate_mem P ε nl hU0.le s ω j).2.trans hU1)
      _ = P.n := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  -- bound by `max_i C_i`
  obtain ⟨i, hi⟩ := hcol j
  have hrD : ∀ s ∈ Cy, P.dpcRate ε nl s ω j ≤ P.lamD s j := by
    intro s hs
    have h0 : 0 ≤ P.lamD s j := (hOpt.1.1 s (hCyT hs) j).1
    have key : P.lamD s j - ε / nl * (if 0 < P.lamD s j then (1 : ℝ) else 0) ≤ P.lamD s j := by
      have : 0 ≤ ε / nl * (if 0 < P.lamD s j then (1 : ℝ) else 0) := by
        apply mul_nonneg (div_nonneg hε (Nat.cast_nonneg _)); split_ifs <;> norm_num
      linarith
    unfold Basic.dpcRate
    by_cases hc : ∀ i, (P.A i j : ℝ) ≤ P.freeCap s ω i
    · rw [if_pos hc]; exact max_le h0 ((min_le_right _ _).trans key)
    · rw [if_neg hc]; exact h0
  have hDET := hOpt.1.2 (b * P.n) (Finset.mem_Icc.mpr ⟨by omega, hbT⟩) i
  have hws : P.winStart (b * P.n) = (b - 1) * P.n + 1 := by
    unfold Basic.winStart
    have : (b - 1) * P.n + P.n = b * P.n := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hb.1]
    rw [show b * P.n + 1 - P.n = (b - 1) * P.n + 1 by omega]
    exact max_eq_right (by omega)
  rw [hws] at hDET
  have hlam : ∑ s ∈ Cy, P.lamD s j ≤ P.C i := by
    refine le_trans ?_ hDET
    apply Finset.sum_le_sum
    intro s hs
    have : ∀ j', 0 ≤ (P.A i j' : ℝ) * P.lamD s j' :=
      fun j' => mul_nonneg (Nat.cast_nonneg _) (hOpt.1.1 s (hCyT hs) j').1
    calc P.lamD s j = (P.A i j : ℝ) * P.lamD s j := by rw [hi]; simp
      _ ≤ ∑ j', (P.A i j' : ℝ) * P.lamD s j' :=
        Finset.single_le_sum (fun j' _ => this j') (Finset.mem_univ j)
  have hCmax : (P.C i : ℝ) ≤ ((Finset.univ.sup P.C : ℕ) : ℝ) := by
    exact_mod_cast Finset.le_sup (Finset.mem_univ i)
  have hC : ∑ s ∈ Cy, P.dpcRate ε nl s ω j ≤ ((Finset.univ.sup P.C : ℕ) : ℝ) :=
    (Finset.sum_le_sum hrD).trans (hlam.trans hCmax)
  unfold Basic.minCapN
  exact hsub.trans (le_min hC hN)

/-- (EC.15) in the one-sided form, for `y = ±γ`. -/
lemma dpc_ec15_one (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε : ℝ)
    (hP : P.Standing φL φU Ψ R nl) (hε : 0 ≤ ε) (j : Fin P.J) (b : ℕ)
    (hb : b ∈ Icc 1 (P.T / P.n)) (γ y : ℝ) (hy : |y| ≤ 1) (hyγ : y ^ 2 = γ ^ 2) :
    P.E ε nl (fun ω => Real.exp (y * ∑ s ∈ Icc ((b - 1) * P.n + 1) (b * P.n),
        P.Delta ε nl s ω j)) ≤ Real.exp (P.minCapN * γ ^ 2) := by
  classical
  obtain ⟨hMF, -⟩ := id hP
  obtain ⟨-, -, hn1, hT1, hdvd, -, -, -, hU0, -, hJU⟩ := hMF
  set Cy := Icc ((b - 1) * P.n + 1) (b * P.n) with hCy
  have hbT : b * P.n ≤ P.T := by
    rw [Finset.mem_Icc] at hb
    obtain ⟨k, hk⟩ := hdvd
    have : P.T / P.n = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega)]
    rw [this] at hb; rw [hk]; nlinarith [hb.2]
  have hCyT : Cy ⊆ Icc 1 P.T := Finset.Icc_subset_Icc (by omega) hbT
  let act : ℕ → P.Path → Prop := fun t _ => t ∈ Cy
  have hsup := dpc_E_prod_le_one P ε nl hU0.le hJU j y hy act (fun t ω ω' _ => Iff.rfl)
  have hprod : ∀ ω, ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω =
      Real.exp (y * ∑ s ∈ Cy, P.Delta ε nl s ω j - y ^ 2 * ∑ s ∈ Cy, P.dpcRate ε nl s ω j) := by
    intro ω
    simp only [dpcG, act]
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hCyT, ← Real.exp_sum,
      Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  unfold Basic.E
  have hpt : ∀ ω, P.pathProb ε nl ω * Real.exp (y * ∑ s ∈ Cy, P.Delta ε nl s ω j) ≤
      Real.exp (P.minCapN * γ ^ 2) *
        (P.pathProb ε nl ω * ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω) := by
    intro ω
    rw [hprod ω]
    have hp := dpc_pathProb_nonneg P ε nl hU0.le hJU ω
    have hΛ := dpc_cycle_rate P φL φU Ψ R nl ε hP hε j b hb ω Cy le_rfl
    have : Real.exp (y * ∑ s ∈ Cy, P.Delta ε nl s ω j) ≤ Real.exp (P.minCapN * γ ^ 2) *
        Real.exp (y * ∑ s ∈ Cy, P.Delta ε nl s ω j - y ^ 2 * ∑ s ∈ Cy, P.dpcRate ε nl s ω j) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hyγ]
      nlinarith [sq_nonneg γ]
    calc P.pathProb ε nl ω * Real.exp (y * ∑ s ∈ Cy, P.Delta ε nl s ω j)
        ≤ P.pathProb ε nl ω * (Real.exp (P.minCapN * γ ^ 2) *
          Real.exp (y * ∑ s ∈ Cy, P.Delta ε nl s ω j -
            y ^ 2 * ∑ s ∈ Cy, P.dpcRate ε nl s ω j)) := mul_le_mul_of_nonneg_left this hp
      _ = _ := by ring
  calc ∑ ω, P.pathProb ε nl ω * Real.exp (y * ∑ s ∈ Cy, P.Delta ε nl s ω j)
      ≤ ∑ ω, Real.exp (P.minCapN * γ ^ 2) *
        (P.pathProb ε nl ω * ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω) :=
        Finset.sum_le_sum (fun ω _ => hpt ω)
    _ = Real.exp (P.minCapN * γ ^ 2) *
        ∑ ω, P.pathProb ε nl ω * ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (P.minCapN * γ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hsup (Real.exp_pos _).le
    _ = _ := mul_one _

lemma dpc_Delta_dep (P : Basic) (ε : ℝ) (nl : ℕ) (ω ω' : P.Path) (t s : ℕ)
    (h : ∀ u : Fin P.T, u.val + 1 < t → ω u = ω' u) (hs : 1 ≤ s) (hst : s < t) (j : Fin P.J) :
    P.Delta ε nl s ω j = P.Delta ε nl s ω' j := by
  unfold Basic.Delta
  have hD := dpc_D_dep P ω ω' (t - 1) s (by omega) (fun u hu => h u (by omega)) j
  have hr := dpc_rate_dep P ε nl (s - 1) ω ω' (fun u hu => h u (by omega))
  rw [Nat.sub_add_cancel hs] at hr
  rw [hD, hr]

/-- Stopped-supermartingale (maximal) bound for one type, one cycle and one sign. -/
lemma dpc_max_one (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl) (hε : 0 ≤ ε) (j : Fin P.J) (b : ℕ)
    (hb : b ∈ Icc 1 (P.T / P.n)) (γ y : ℝ) (hγ0 : 0 < γ) (hy : |y| ≤ 1) (hyγ : y ^ 2 = γ ^ 2) :
    P.prob ε nl (fun ω => ∃ t ∈ Icc ((b - 1) * P.n + 1) (b * P.n),
        γ * δ ≤ y * ∑ s ∈ Icc ((b - 1) * P.n + 1) t, P.Delta ε nl s ω j) ≤
      Real.exp (P.minCapN * γ ^ 2 - δ * γ) := by
  classical
  obtain ⟨hMF, -⟩ := id hP
  obtain ⟨-, -, hn1, hT1, hdvd, -, -, -, hU0, -, hJU⟩ := hMF
  set st := (b - 1) * P.n + 1 with hst
  set Cy := Icc st (b * P.n) with hCy
  have hbT : b * P.n ≤ P.T := by
    rw [Finset.mem_Icc] at hb
    obtain ⟨k, hk⟩ := hdvd
    have : P.T / P.n = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega)]
    rw [this] at hb; rw [hk]; nlinarith [hb.2]
  have hCyT : Cy ⊆ Icc 1 P.T := Finset.Icc_subset_Icc (by omega) hbT
  let S : ℕ → P.Path → ℝ := fun t ω => ∑ s ∈ Icc st t, P.Delta ε nl s ω j
  let act : ℕ → P.Path → Prop := fun t ω => t ∈ Cy ∧ ∀ t' ∈ Icc st (t - 1), y * S t' ω < γ * δ
  have hact : ∀ t ω ω', (∀ u : Fin P.T, u.val + 1 < t → ω u = ω' u) → (act t ω ↔ act t ω') := by
    intro t ω ω' h
    have hS : ∀ t' ∈ Icc st (t - 1), S t' ω = S t' ω' := by
      intro t' ht'
      rw [Finset.mem_Icc] at ht'
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_Icc] at hs
      exact dpc_Delta_dep P ε nl ω ω' t s h (by omega) (by omega) j
    simp only [act]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun t' ht' => (hS t' ht') ▸ h2 t' ht'⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun t' ht' => (hS t' ht').symm ▸ h2 t' ht'⟩
  have hsup := dpc_E_prod_le_one P ε nl hU0.le hJU j y hy act hact
  set K := Real.exp (γ * δ - γ ^ 2 * P.minCapN) with hK
  have hpt : ∀ ω, (if (∃ t ∈ Cy, γ * δ ≤ y * S t ω) then P.pathProb ε nl ω else 0) * K ≤
      P.pathProb ε nl ω * ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω := by
    intro ω
    have hp := dpc_pathProb_nonneg P ε nl hU0.le hJU ω
    have hG0 : 0 ≤ ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω := by
      apply Finset.prod_nonneg; intro t _; unfold dpcG
      split_ifs
      · exact (Real.exp_pos _).le
      · norm_num
    split_ifs with hE
    · apply mul_le_mul_of_nonneg_left _ hp
      have hE' : ∃ t, t ∈ Cy ∧ γ * δ ≤ y * S t ω := by
        obtain ⟨t, ht, h⟩ := hE; exact ⟨t, ht, h⟩
      set τ := Nat.find hE' with hτ
      have hτspec := Nat.find_spec hE'
      have hτCy : τ ∈ Cy := hτspec.1
      rw [Finset.mem_Icc] at hτCy
      have hiff : ∀ t ∈ Icc 1 P.T, act t ω ↔ t ∈ Icc st τ := by
        intro t _
        show (t ∈ Cy ∧ ∀ t' ∈ Icc st (t - 1), y * S t' ω < γ * δ) ↔ t ∈ Icc st τ
        constructor
        · rintro ⟨h1, h3⟩
          rw [hCy, Finset.mem_Icc] at h1
          rw [Finset.mem_Icc]
          refine ⟨h1.1, ?_⟩
          by_contra hc
          push Not at hc
          have := h3 τ (Finset.mem_Icc.mpr ⟨hτCy.1, by omega⟩)
          linarith [hτspec.2]
        · intro h
          rw [Finset.mem_Icc] at h
          refine ⟨by rw [hCy, Finset.mem_Icc]; omega, ?_⟩
          intro t' ht'
          rw [Finset.mem_Icc] at ht'
          have hlt : t' < τ := by omega
          have hmin := Nat.find_min hE' hlt
          have hmem : t' ∈ Cy := by rw [hCy, Finset.mem_Icc]; omega
          by_contra hc
          push Not at hc
          exact hmin ⟨hmem, hc⟩
      have hsubT : Icc st τ ⊆ Icc 1 P.T := (Finset.Icc_subset_Icc le_rfl hτCy.2).trans hCyT
      have hprod : ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω =
          Real.exp (y * S τ ω - y ^ 2 * ∑ s ∈ Icc st τ, P.dpcRate ε nl s ω j) := by
        rw [show ∏ t ∈ Icc 1 P.T, dpcG P ε nl j y act t ω =
            ∏ t ∈ Icc 1 P.T, (if t ∈ Icc st τ then
              Real.exp (y * P.Delta ε nl t ω j - y ^ 2 * P.dpcRate ε nl t ω j) else 1) from
            Finset.prod_congr rfl (fun t ht => by
              unfold dpcG
              by_cases hc : act t ω
              · rw [if_pos hc, if_pos ((hiff t ht).mp hc)]
              · rw [if_neg hc, if_neg (fun h' => hc ((hiff t ht).mpr h'))])]
        rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hsubT, ← Real.exp_sum,
          Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hprod]
      apply Real.exp_le_exp.mpr
      have hΛ := dpc_cycle_rate P φL φU Ψ R nl ε hP hε j b hb ω (Icc st τ)
        (Finset.Icc_subset_Icc le_rfl hτCy.2)
      rw [hyγ]
      have : γ * δ ≤ y * S τ ω := hτspec.2
      nlinarith [sq_nonneg γ]
    · rw [zero_mul]; exact mul_nonneg hp hG0
  have hKpos : 0 < K := Real.exp_pos _
  have hsum : P.prob ε nl (fun ω => ∃ t ∈ Cy, γ * δ ≤ y * S t ω) * K ≤ 1 := by
    unfold Basic.prob
    rw [Finset.sum_mul]
    calc _ = ∑ ω, (if (∃ t ∈ Cy, γ * δ ≤ y * S t ω) then P.pathProb ε nl ω else 0) * K :=
          Finset.sum_congr rfl (fun ω _ => by congr 1; split_ifs <;> rfl)
      _ ≤ _ := (Finset.sum_le_sum (fun ω _ => hpt ω)).trans hsup
  have : Real.exp (P.minCapN * γ ^ 2 - δ * γ) = 1 / K := by
    rw [hK, one_div, ← Real.exp_neg]; ring_nf
  rw [this, le_div_iff₀ hKpos]
  exact hsum

open scoped Classical in
theorem solution (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl) (hε : 0 < ε) (hδ : 0 < δ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    P.prob ε nl (fun ω => ¬ P.InG ε nl δ ω) ≤
      2 * (P.J : ℝ) * P.T / P.n * Real.exp (P.minCapN * γ ^ 2 - δ * γ) := by
  obtain ⟨hMF, -⟩ := id hP
  obtain ⟨-, -, hn1, hT1, hdvd, -, -, -, hU0, -, hJU⟩ := hMF
  set K := Real.exp (P.minCapN * γ ^ 2 - δ * γ) with hK
  have hy1 : |γ| ≤ 1 := by rw [abs_of_pos hγ0]; exact hγ1
  have hy2 : |-γ| ≤ 1 := by rw [abs_neg]; exact hy1
  let Ev : ℝ → Fin P.J → ℕ → P.Path → Prop := fun y j b ω =>
    ∃ t ∈ Icc ((b - 1) * P.n + 1) (b * P.n),
      γ * δ ≤ y * ∑ s ∈ Icc ((b - 1) * P.n + 1) t, P.Delta ε nl s ω j
  have hEv : ∀ y, |y| ≤ 1 → y ^ 2 = γ ^ 2 → ∀ j, ∀ b ∈ Icc 1 (P.T / P.n),
      ∑ ω, (if Ev y j b ω then P.pathProb ε nl ω else 0) ≤ K := by
    intro y hy hyγ j b hb
    have := dpc_max_one P φL φU Ψ R nl ε δ hP hε.le j b hb γ y hγ0 hy hyγ
    unfold Basic.prob at this
    refine le_trans (le_of_eq ?_) this
    exact Finset.sum_congr rfl (fun ω _ => by split_ifs <;> rfl)
  have hp0 : ∀ ω, 0 ≤ P.pathProb ε nl ω := dpc_pathProb_nonneg P ε nl hU0.le hJU
  set B := Icc 1 (P.T / P.n) with hB
  have hpt : ∀ ω, (if ¬ P.InG ε nl δ ω then P.pathProb ε nl ω else 0) ≤
      ∑ j, ∑ b ∈ B, ((if Ev γ j b ω then P.pathProb ε nl ω else 0) +
        (if Ev (-γ) j b ω then P.pathProb ε nl ω else 0)) := by
    intro ω
    have hnn : ∀ j, ∀ b ∈ B, 0 ≤ (if Ev γ j b ω then P.pathProb ε nl ω else 0) +
        (if Ev (-γ) j b ω then P.pathProb ε nl ω else 0) := by
      intro j b _
      apply add_nonneg <;> split_ifs <;> first | exact hp0 ω | exact le_rfl
    by_cases hG0 : P.InG ε nl δ ω
    · rw [if_neg (not_not.mpr hG0)]
      exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (hnn j))
    · rw [if_pos hG0]
      have hG := hG0
      unfold Basic.InG Basic.InA at hG
      push Not at hG
      obtain ⟨j, b, hb, t, ht, hS⟩ := hG
      have hjb : (if Ev γ j b ω then P.pathProb ε nl ω else 0) +
          (if Ev (-γ) j b ω then P.pathProb ε nl ω else 0) ≥ P.pathProb ε nl ω := by
        rcases le_abs'.mp hS with h | h
        · have : Ev (-γ) j b ω := ⟨t, ht, by nlinarith⟩
          rw [if_pos this]
          have : 0 ≤ (if Ev γ j b ω then P.pathProb ε nl ω else 0) := by
            split_ifs <;> first | exact hp0 ω | exact le_rfl
          linarith
        · have : Ev γ j b ω := ⟨t, ht, by nlinarith⟩
          rw [if_pos this]
          have : 0 ≤ (if Ev (-γ) j b ω then P.pathProb ε nl ω else 0) := by
            split_ifs <;> first | exact hp0 ω | exact le_rfl
          linarith
      calc P.pathProb ε nl ω
          ≤ ∑ b ∈ B, ((if Ev γ j b ω then P.pathProb ε nl ω else 0) +
              (if Ev (-γ) j b ω then P.pathProb ε nl ω else 0)) :=
            le_trans hjb (Finset.single_le_sum (hnn j) hb)
        _ ≤ _ := Finset.single_le_sum (f := fun j => ∑ b ∈ B, ((if Ev γ j b ω then
              P.pathProb ε nl ω else 0) + (if Ev (-γ) j b ω then P.pathProb ε nl ω else 0)))
              (fun j _ => Finset.sum_nonneg (hnn j)) (Finset.mem_univ j)
  have hcardB : ((B.card : ℕ) : ℝ) = (P.T : ℝ) / P.n := by
    rw [hB, Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_div hdvd (by positivity)]
  unfold Basic.prob
  calc _ = ∑ ω, (if ¬ P.InG ε nl δ ω then P.pathProb ε nl ω else 0) :=
        Finset.sum_congr rfl (fun ω _ => by split_ifs <;> rfl)
    _ ≤ ∑ ω, ∑ j, ∑ b ∈ B, ((if Ev γ j b ω then P.pathProb ε nl ω else 0) +
        (if Ev (-γ) j b ω then P.pathProb ε nl ω else 0)) := Finset.sum_le_sum (fun ω _ => hpt ω)
    _ = ∑ j, ∑ b ∈ B, (∑ ω, (if Ev γ j b ω then P.pathProb ε nl ω else 0) +
        ∑ ω, (if Ev (-γ) j b ω then P.pathProb ε nl ω else 0)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_add_distrib]
    _ ≤ ∑ _j : Fin P.J, ∑ _b ∈ B, (K + K) := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro b hb
        exact add_le_add (hEv γ hy1 rfl j b hb) (hEv (-γ) hy2 (by ring) j b hb)
    _ = 2 * (P.J : ℝ) * P.T / P.n * K := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, nsmul_eq_mul, hcardB]
        ring
