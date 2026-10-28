-- Prove2me | solution 1 for PeakEndPricing.Convergence.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T23:53:03.98298+00:00
-- url     : https://prove2.me/submissions/df523b34-8a12-484f-962c-55a5b95ba85c

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

set_option autoImplicit false

namespace PEP3
open PeakEndPricing.Convergence

/-- `Standing` with `0 ≤ theta` (so that the auxiliary `theta = 0, lam = gam` problem is covered). -/
structure Std0 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ) : Prop where
  assumption1 : Assumption1 pbar d0
  differentiable : ∀ p ∈ Set.Icc (0 : ℝ) pbar, DifferentiableAt ℝ (baseProfit d0) p
  gam_pos : 0 < gam
  gam_le_lam : gam ≤ lam
  theta_nonneg : 0 ≤ theta
  theta_le_one : theta ≤ 1
  beta_pos : 0 < beta
  beta_lt_one : beta < 1

lemma Std0.of {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (h : Standing pbar d0 lam gam theta beta) : Std0 pbar d0 lam gam theta beta :=
  ⟨h.assumption1, h.differentiable, h.gam_pos, h.gam_le_lam, h.theta_pos.le, h.theta_le_one,
    h.beta_pos, h.beta_lt_one⟩

/-- The auxiliary problem: `lam := gam`, `theta := 0`. -/
lemma Std0.aux {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (h : Std0 pbar d0 lam gam theta beta) : Std0 pbar d0 gam gam 0 beta :=
  ⟨h.assumption1, h.differentiable, h.gam_pos, le_rfl, le_rfl, zero_le_one,
    h.beta_pos, h.beta_lt_one⟩

/-! ## Foundation: ranges, bounds, shift identity, existence, Bellman. -/

lemma minPrice_mem {pbar : ℝ} (m0 : ℝ) (q : ℕ → ℝ) (hm : m0 ∈ Set.Icc (0:ℝ) pbar)
    (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) : ∀ n, minPrice m0 q n ∈ Set.Icc (0:ℝ) pbar := by
  intro n
  induction n with
  | zero => simpa [minPrice] using hm
  | succ n ih =>
    show min (minPrice m0 q n) (q n) ∈ Set.Icc (0:ℝ) pbar
    exact ⟨le_min ih.1 (hq n).1, (min_le_left _ _).trans ih.2⟩

lemma price_mem {pbar : ℝ} (p0 : ℝ) (q : ℕ → ℝ) (hp : p0 ∈ Set.Icc (0:ℝ) pbar)
    (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) : ∀ n, price p0 q n ∈ Set.Icc (0:ℝ) pbar := by
  intro n
  cases n with
  | zero => exact hp
  | succ n => exact hq n

lemma refPrice_mem {pbar : ℝ} (theta m0 p0 : ℝ) (q : ℕ → ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar)
    (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) (n : ℕ) :
    refPrice theta m0 p0 q n ∈ Set.Icc (0:ℝ) pbar := by
  obtain ⟨a1, a2⟩ := minPrice_mem m0 q hm hq n
  obtain ⟨b1, b2⟩ := price_mem p0 q hp hq n
  unfold refPrice
  constructor <;> nlinarith

lemma minPrice_le (m0 : ℝ) (q : ℕ → ℝ) : ∀ n, minPrice m0 q n ≤ m0 := by
  intro n
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact (min_le_left _ _).trans ih

lemma profit_abs_le {pbar : ℝ} {d0 : ℝ → ℝ} (lam gam D : ℝ) (hlam : 0 ≤ lam) (hgam : 0 ≤ gam)
    (hD : ∀ p ∈ Set.Icc (0:ℝ) pbar, 0 ≤ d0 p ∧ d0 p ≤ D) (p r : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) pbar) (hr : r ∈ Set.Icc (0:ℝ) pbar) :
    |profit d0 lam gam p r| ≤ pbar * (D + (lam + gam) * pbar) := by
  unfold profit demand
  have h1 : max (p - r) 0 ≤ pbar := max_le (by linarith [hp.2, hr.1]) (by linarith [hp.1, hp.2])
  have h2 : max (r - p) 0 ≤ pbar := max_le (by linarith [hr.2, hp.1]) (by linarith [hp.1, hp.2])
  have h3 : 0 ≤ max (p - r) 0 := le_max_right _ _
  have h4 : 0 ≤ max (r - p) 0 := le_max_right _ _
  obtain ⟨d1, d2⟩ := hD p hp
  have hX : |d0 p - lam * max (p - r) 0 + gam * max (r - p) 0| ≤ D + (lam + gam) * pbar := by
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hlam, mul_le_mul_of_nonneg_left h2 hgam,
      mul_nonneg hlam h3, mul_nonneg hgam h4]
  rw [abs_mul, abs_of_nonneg hp.1]
  exact mul_le_mul hp.2 hX (abs_nonneg _) (le_trans hp.1 hp.2)

lemma demand_bound {pbar : ℝ} {d0 : ℝ → ℝ} (h : Assumption1 pbar d0) :
    ∃ D, ∀ p ∈ Set.Icc (0:ℝ) pbar, 0 ≤ d0 p ∧ d0 p ≤ D := by
  obtain ⟨D, hD⟩ := h.bounded
  exact ⟨D, fun p hp => ⟨h.nonneg p hp, hD ⟨p, hp, rfl⟩⟩⟩

/-- The summand of `pathValue`. -/
noncomputable def term (d0 : ℝ → ℝ) (lam gam theta beta m0 p0 : ℝ) (q : ℕ → ℝ) (n : ℕ) : ℝ :=
  beta ^ n * profit d0 lam gam (q n) (refPrice theta m0 p0 q n)

lemma term_abs_le {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (D : ℝ)
    (hD : ∀ p ∈ Set.Icc (0:ℝ) pbar, 0 ≤ d0 p ∧ d0 p ≤ D) (m0 p0 : ℝ) (q : ℕ → ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar)
    (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) (n : ℕ) :
    |term d0 lam gam theta beta m0 p0 q n| ≤ beta ^ n * (pbar * (D + (lam + gam) * pbar)) := by
  unfold term
  rw [abs_mul, abs_of_nonneg (pow_nonneg hst.beta_pos.le n)]
  exact mul_le_mul_of_nonneg_left
    (profit_abs_le lam gam D (hst.gam_pos.le.trans hst.gam_le_lam) hst.gam_pos.le hD _ _ (hq n)
      (refPrice_mem theta m0 p0 q hst.theta_nonneg hst.theta_le_one hm hp hq n))
    (pow_nonneg hst.beta_pos.le n)

lemma term_summable {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ) (q : ℕ → ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar)
    (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) :
    Summable (term d0 lam gam theta beta m0 p0 q) := by
  obtain ⟨D, hD⟩ := demand_bound hst.assumption1
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hst.beta_pos.le hst.beta_lt_one).mul_right
      (pbar * (D + (lam + gam) * pbar))) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact term_abs_le hst D hD m0 p0 q hm hp hq n

/-! ### Shift identity -/

lemma minPrice_succ (m0 : ℝ) (q : ℕ → ℝ) :
    ∀ n, minPrice m0 q (n + 1) = minPrice (min m0 (q 0)) (fun k => q (k + 1)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show min (minPrice m0 q (n + 1)) (q (n + 1)) =
      min (minPrice (min m0 (q 0)) (fun k => q (k + 1)) n) (q (n + 1))
    rw [ih]

lemma price_succ (p0 : ℝ) (q : ℕ → ℝ) :
    ∀ n, price p0 q (n + 1) = price (q 0) (fun k => q (k + 1)) n := by
  intro n
  cases n <;> rfl

lemma refPrice_succ (theta m0 p0 : ℝ) (q : ℕ → ℝ) (n : ℕ) :
    refPrice theta m0 p0 q (n + 1) =
      refPrice theta (min m0 (q 0)) (q 0) (fun k => q (k + 1)) n := by
  unfold refPrice
  rw [minPrice_succ, price_succ]

lemma pathValue_shift {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ) (q : ℕ → ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar)
    (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) :
    pathValue d0 lam gam theta beta m0 p0 q =
      profit d0 lam gam (q 0) (refPrice theta m0 p0 q 0) +
        beta * pathValue d0 lam gam theta beta (min m0 (q 0)) (q 0) (fun k => q (k + 1)) := by
  have hs := term_summable hst m0 p0 q hm hp hq
  have h1 : pathValue d0 lam gam theta beta m0 p0 q = ∑' n, term d0 lam gam theta beta m0 p0 q n :=
    rfl
  rw [h1, hs.tsum_eq_zero_add]
  unfold pathValue
  rw [← tsum_mul_left]
  congr 1
  · simp [term]
  · congr 1
    funext n
    simp only [term]
    rw [refPrice_succ, pow_succ]
    ring

/-! ### Existence of an optimal path -/

lemma minPrice_continuous {pbar : ℝ} (m0 : ℝ) (n : ℕ) :
    Continuous (fun q : ℕ → Set.Icc (0:ℝ) pbar => minPrice m0 (fun k => (q k : ℝ)) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact ih.min (continuous_subtype_val.comp (continuous_apply n))

lemma price_continuous {pbar : ℝ} (p0 : ℝ) (n : ℕ) :
    Continuous (fun q : ℕ → Set.Icc (0:ℝ) pbar => price p0 (fun k => (q k : ℝ)) n) := by
  cases n with
  | zero => exact continuous_const
  | succ n => exact continuous_subtype_val.comp (continuous_apply n)

lemma term_continuous {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ) (n : ℕ) :
    Continuous (fun q : ℕ → Set.Icc (0:ℝ) pbar =>
      term d0 lam gam theta beta m0 p0 (fun k => (q k : ℝ)) n) := by
  have hqn : Continuous (fun q : ℕ → Set.Icc (0:ℝ) pbar => (q n : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply n)
  have hr : Continuous (fun q : ℕ → Set.Icc (0:ℝ) pbar =>
      refPrice theta m0 p0 (fun k => (q k : ℝ)) n) := by
    unfold refPrice
    exact (continuous_const.mul (minPrice_continuous m0 n)).add
      (continuous_const.mul (price_continuous p0 n))
  have hd : Continuous (fun q : ℕ → Set.Icc (0:ℝ) pbar => d0 (q n : ℝ)) :=
    hst.assumption1.continuous.comp_continuous hqn (fun q => (q n).2)
  unfold term profit demand
  exact continuous_const.mul (hqn.mul ((hd.sub (continuous_const.mul
    ((hqn.sub hr).max continuous_const))).add (continuous_const.mul
    ((hr.sub hqn).max continuous_const))))

lemma pathValue_continuous {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) :
    Continuous (fun q : ℕ → Set.Icc (0:ℝ) pbar =>
      pathValue d0 lam gam theta beta m0 p0 (fun k => (q k : ℝ))) := by
  obtain ⟨D, hD⟩ := demand_bound hst.assumption1
  have h := continuous_tsum (fun n => term_continuous hst m0 p0 n)
    ((summable_geometric_of_lt_one hst.beta_pos.le hst.beta_lt_one).mul_right
      (pbar * (D + (lam + gam) * pbar)))
    (fun n q => by
      rw [Real.norm_eq_abs]
      exact term_abs_le hst D hD m0 p0 _ hm hp (fun k => (q k).2) n)
  exact h

lemma J_bdd {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) :
    BddAbove (Set.range (fun q : ℕ → Set.Icc (0:ℝ) pbar =>
      pathValue d0 lam gam theta beta m0 p0 (fun k => (q k : ℝ)))) := by
  obtain ⟨D, hD⟩ := demand_bound hst.assumption1
  refine ⟨∑' n, beta ^ n * (pbar * (D + (lam + gam) * pbar)), ?_⟩
  rintro _ ⟨q, rfl⟩
  have hs := term_summable hst m0 p0 (fun k => (q k : ℝ)) hm hp (fun k => (q k).2)
  exact hs.tsum_le_tsum (fun n => (le_abs_self _).trans
      (term_abs_le hst D hD m0 p0 _ hm hp (fun k => (q k).2) n))
    ((summable_geometric_of_lt_one hst.beta_pos.le hst.beta_lt_one).mul_right _)

lemma pathValue_le_J {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (q : ℕ → ℝ)
    (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) :
    pathValue d0 lam gam theta beta m0 p0 q ≤ J pbar d0 lam gam theta beta m0 p0 := by
  have := le_ciSup (J_bdd hst m0 p0 hm hp) (fun n => (⟨q n, hq n⟩ : Set.Icc (0:ℝ) pbar))
  exact this

theorem exists_optimal {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) :
    ∃ q : ℕ → ℝ, IsOptimalPath pbar d0 lam gam theta beta m0 p0 q := by
  have : CompactSpace (Set.Icc (0:ℝ) pbar) := isCompact_iff_compactSpace.mp isCompact_Icc
  have : Nonempty (ℕ → Set.Icc (0:ℝ) pbar) := ⟨fun _ => ⟨0, le_refl _, hm.1.trans hm.2⟩⟩
  obtain ⟨qs, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (pathValue_continuous hst m0 p0 hm hp).continuousOn
  refine ⟨fun k => (qs k : ℝ), fun n => (qs n).2, ?_⟩
  apply le_antisymm
  · exact pathValue_le_J hst m0 p0 hm hp _ (fun n => (qs n).2)
  · exact ciSup_le (fun q => hmax (Set.mem_univ q))

/-! ### Bellman / principle of optimality -/

/-- Prepend a first price. -/
def cons (x : ℝ) (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => q n

lemma bellman_ge {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) pbar) :
    profit d0 lam gam x (theta * m0 + (1 - theta) * p0) +
        beta * J pbar d0 lam gam theta beta (min m0 x) x ≤
      J pbar d0 lam gam theta beta m0 p0 := by
  have hm1 : min m0 x ∈ Set.Icc (0:ℝ) pbar := ⟨le_min hm.1 hx.1, (min_le_left _ _).trans hm.2⟩
  obtain ⟨q, hq, hqv⟩ := exists_optimal hst (min m0 x) x hm1 hx
  have hc : ∀ n, cons x q n ∈ Set.Icc (0:ℝ) pbar := by
    intro n; cases n with
    | zero => exact hx
    | succ n => exact hq n
  have h := pathValue_shift hst m0 p0 (cons x q) hm hp hc
  have h2 : (fun k => cons x q (k + 1)) = q := rfl
  rw [h2] at h
  have h3 : refPrice theta m0 p0 (cons x q) 0 = theta * m0 + (1 - theta) * p0 := rfl
  have h4 : cons x q 0 = x := rfl
  rw [h3, h4, hqv] at h
  rw [← h]
  exact pathValue_le_J hst m0 p0 hm hp _ hc

/-- Principle of optimality: the first move of an optimal path attains the Bellman maximum and
its tail is optimal from the next state. -/
lemma optimal_step {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) :
    IsOptimalPath pbar d0 lam gam theta beta (min m0 (q 0)) (q 0) (fun k => q (k + 1)) ∧
    J pbar d0 lam gam theta beta m0 p0 =
      profit d0 lam gam (q 0) (theta * m0 + (1 - theta) * p0) +
        beta * J pbar d0 lam gam theta beta (min m0 (q 0)) (q 0) := by
  obtain ⟨hqP, hqv⟩ := hq
  have hx := hqP 0
  have hm1 : min m0 (q 0) ∈ Set.Icc (0:ℝ) pbar :=
    ⟨le_min hm.1 hx.1, (min_le_left _ _).trans hm.2⟩
  have htP : ∀ n, (fun k => q (k + 1)) n ∈ Set.Icc (0:ℝ) pbar := fun n => hqP (n + 1)
  have h := pathValue_shift hst m0 p0 q hm hp hqP
  have h3 : refPrice theta m0 p0 q 0 = theta * m0 + (1 - theta) * p0 := rfl
  rw [h3, hqv] at h
  have hle := pathValue_le_J hst (min m0 (q 0)) (q 0) hm1 hx _ htP
  have hge := bellman_ge hst m0 p0 hm hp (q 0) hx
  have hb := hst.beta_pos
  have heq : pathValue d0 lam gam theta beta (min m0 (q 0)) (q 0) (fun k => q (k + 1)) =
      J pbar d0 lam gam theta beta (min m0 (q 0)) (q 0) := by
    by_contra hne
    have hlt := lt_of_le_of_ne hle hne
    have := mul_lt_mul_of_pos_left hlt hb
    linarith
  refine ⟨⟨htP, heq⟩, ?_⟩
  rw [heq] at h
  exact h

/-! ### C. Lifting a path to `max q mu` (prices never go below `min m0 S`) -/

lemma summable_of_geom_bound {beta : ℝ} (hb0 : 0 ≤ beta) (hb1 : beta < 1) (f : ℕ → ℝ) (C : ℝ)
    (h : ∀ n, |f n| ≤ beta ^ n * C) : Summable f :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hb0 hb1).mul_right C)
    (fun n => by rw [Real.norm_eq_abs]; exact h n)

lemma profit_eq (d0 : ℝ → ℝ) (lam gam x r : ℝ) :
    profit d0 lam gam x r =
      baseProfit d0 x + x * (-lam * max (x - r) 0 + gam * max (r - x) 0) := by
  unfold profit demand baseProfit; ring

lemma psi_incr (lam gam : ℝ) (hgam : 0 ≤ gam) (hlg : gam ≤ lam) (x r r' : ℝ) (hrr : r ≤ r') :
    gam * (r' - r) ≤ (-lam * max (x - r') 0 + gam * max (r' - x) 0) -
      (-lam * max (x - r) 0 + gam * max (r - x) 0) := by
  rcases le_total x r with h1 | h1 <;> rcases le_total x r' with h2 | h2
  · rw [max_eq_right (by linarith : x - r' ≤ 0), max_eq_left (by linarith : 0 ≤ r' - x),
      max_eq_right (by linarith : x - r ≤ 0), max_eq_left (by linarith : 0 ≤ r - x)]; nlinarith
  · have : r = x := by linarith
    have : r' = x := by linarith
    subst_vars; simp
  · rw [max_eq_right (by linarith : x - r' ≤ 0), max_eq_left (by linarith : 0 ≤ r' - x),
      max_eq_left (by linarith : 0 ≤ x - r), max_eq_right (by linarith : r - x ≤ 0)]
    nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ x - r'), max_eq_right (by linarith : r' - x ≤ 0),
      max_eq_left (by linarith : 0 ≤ x - r), max_eq_right (by linarith : r - x ≤ 0)]
    nlinarith

lemma period_gain {d0 : ℝ → ℝ} {lam gam beta : ℝ} (hgam : 0 ≤ gam) (hlg : gam ≤ lam)
    (mu x r r' : ℝ) (hx0 : 0 ≤ x) (hmu0 : 0 ≤ mu) (hrr : r ≤ r') (hmur : mu ≤ r')
    (hd : gam * (1 - beta) * mu ≤ deriv (baseProfit d0) mu)
    (htan : x < mu → baseProfit d0 x ≤
      baseProfit d0 mu + deriv (baseProfit d0) mu * (x - mu)) :
    gam * (max x mu - x) ^ 2 - gam * beta * mu * (max x mu - x) +
        gam * (mu - (max x mu - x)) * (r' - r) ≤
      profit d0 lam gam (max x mu) r' - profit d0 lam gam x r := by
  rw [profit_eq, profit_eq]
  have hps := psi_incr lam gam hgam hlg x r r' hrr
  rcases le_or_gt mu x with hxm | hxm
  · rw [max_eq_left hxm]
    have h1 : 0 ≤ gam * (r' - r) := mul_nonneg hgam (by linarith)
    have h2 : mu * (gam * (r' - r)) ≤ x * (gam * (r' - r)) := mul_le_mul_of_nonneg_right hxm h1
    have h3 := mul_le_mul_of_nonneg_left hps hx0
    nlinarith
  · rw [max_eq_right hxm.le]
    rw [max_eq_right (by linarith : mu - r' ≤ 0), max_eq_left (by linarith : 0 ≤ r' - mu)]
    have hps' : gam * (r' - r) ≤ gam * (r' - x) - (-lam * max (x - r) 0 + gam * max (r - x) 0) := by
      have := hps
      rw [max_eq_right (by linarith : x - r' ≤ 0), max_eq_left (by linarith : 0 ≤ r' - x)] at this
      linarith
    have h3 := mul_le_mul_of_nonneg_left hps' hx0
    have ht := htan hxm
    have h4 : 0 ≤ (mu - x) * (r' - mu) := mul_nonneg (by linarith) (by linarith)
    have h5 : gam * (1 - beta) * mu * (mu - x) ≤ deriv (baseProfit d0) mu * (mu - x) :=
      mul_le_mul_of_nonneg_right hd (by linarith)
    nlinarith [mul_nonneg hgam h4]

lemma minPrice_lift (m0 mu : ℝ) (q : ℕ → ℝ) (hmum : mu ≤ m0) :
    ∀ n, minPrice m0 (fun k => max (q k) mu) n = max (minPrice m0 q n) mu := by
  intro n
  induction n with
  | zero => exact (max_eq_left hmum).symm
  | succ n ih =>
    show min (minPrice m0 (fun k => max (q k) mu) n) (max (q n) mu) =
      max (min (minPrice m0 q n) (q n)) mu
    rw [ih]
    rcases le_total (minPrice m0 q n) (q n) with h | h
    · rw [min_eq_left h, min_eq_left (max_le_max h (le_refl mu))]
    · rw [min_eq_right h, min_eq_right (max_le_max h (le_refl mu))]

lemma price_lift (p0 mu : ℝ) (q : ℕ → ℝ) (hmup : mu ≤ p0) :
    ∀ n, price p0 (fun k => max (q k) mu) n = max (price p0 q n) mu := by
  intro n
  cases n with
  | zero => exact (max_eq_left hmup).symm
  | succ n => rfl

theorem lift_gain {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 mu : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar)
    (hmu0 : 0 ≤ mu) (hmum : mu ≤ m0) (hmup : mu ≤ p0)
    (hd : gam * (1 - beta) * mu ≤ deriv (baseProfit d0) mu)
    (htan : ∀ x ∈ Set.Icc (0:ℝ) pbar, x < mu →
      baseProfit d0 x ≤ baseProfit d0 mu + deriv (baseProfit d0) mu * (x - mu))
    (q : ℕ → ℝ) (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) (k : ℕ) :
    pathValue d0 lam gam theta beta m0 p0 q +
        gam * (1 - beta) / 2 * (beta ^ k * (max (q k) mu - q k) ^ 2) ≤
      pathValue d0 lam gam theta beta m0 p0 (fun n => max (q n) mu) := by
  have hb0 := hst.beta_pos.le
  have hb1 := hst.beta_lt_one
  have hg0 := hst.gam_pos.le
  have hlg := hst.gam_le_lam
  have ht0 := hst.theta_nonneg
  have ht1 := hst.theta_le_one
  set q' : ℕ → ℝ := fun n => max (q n) mu with hq'def
  have hq' : ∀ n, q' n ∈ Set.Icc (0:ℝ) pbar := fun n =>
    ⟨(hq n).1.trans (le_max_left _ _), max_le (hq n).2 (hmum.trans hm.2)⟩
  set Δ : ℕ → ℝ := fun n => max (q n) mu - q n with hΔdef
  set E : ℕ → ℝ := cons 0 Δ with hEdef
  have hΔ0 : ∀ n, 0 ≤ Δ n := fun n => by simp only [hΔdef]; linarith [le_max_left (q n) mu]
  have hΔmu : ∀ n, Δ n ≤ mu := fun n => by
    simp only [hΔdef]; rcases le_total (q n) mu with h | h
    · rw [max_eq_right h]; linarith [(hq n).1]
    · rw [max_eq_left h]; linarith
  have hE0 : ∀ n, 0 ≤ E n := fun n => by cases n with
    | zero => exact le_refl _
    | succ n => exact hΔ0 n
  have hEmu : ∀ n, E n ≤ mu := fun n => by cases n with
    | zero => exact hmu0
    | succ n => exact hΔmu n
  -- references
  have hr'mu : ∀ n, mu ≤ refPrice theta m0 p0 q' n := by
    intro n
    unfold refPrice
    rw [minPrice_lift m0 mu q hmum, price_lift p0 mu q hmup]
    nlinarith [le_max_right (minPrice m0 q n) mu, le_max_right (price p0 q n) mu]
  have hrr : ∀ n, refPrice theta m0 p0 q n + E n ≤ refPrice theta m0 p0 q' n := by
    intro n
    unfold refPrice
    rw [minPrice_lift m0 mu q hmum, price_lift p0 mu q hmup]
    cases n with
    | zero =>
      show _ + 0 ≤ _
      nlinarith [le_max_left (minPrice m0 q 0) mu, le_max_left (price p0 q 0) mu]
    | succ n =>
      show theta * minPrice m0 q (n+1) + (1 - theta) * q n + (max (q n) mu - q n) ≤
        theta * max (minPrice m0 q (n+1)) mu + (1 - theta) * max (q n) mu
      have hmq : minPrice m0 q (n+1) ≤ q n := min_le_right _ _
      have : max (q n) mu - q n ≤ max (minPrice m0 q (n+1)) mu - minPrice m0 q (n+1) := by
        rcases le_total (q n) mu with h | h
        · rw [max_eq_right h, max_eq_right (hmq.trans h)]; linarith
        · rw [max_eq_left h]; linarith [le_max_left (minPrice m0 q (n+1)) mu]
      nlinarith
  -- per-period bound
  have hper : ∀ n, beta ^ n * (gam * (Δ n ^ 2 / 2 - E n ^ 2 / 2 + mu * E n - beta * mu * Δ n)) ≤
      term d0 lam gam theta beta m0 p0 q' n - term d0 lam gam theta beta m0 p0 q n := by
    intro n
    have hg := period_gain (d0 := d0) (beta := beta) hg0 hlg mu (q n)
      (refPrice theta m0 p0 q n) (refPrice theta m0 p0 q' n) (hq n).1 hmu0
      (by linarith [hrr n, hE0 n]) (hr'mu n) hd (htan (q n) (hq n))
    have h2 : (mu - Δ n) * E n ≤ (mu - Δ n) *
        (refPrice theta m0 p0 q' n - refPrice theta m0 p0 q n) :=
      mul_le_mul_of_nonneg_left (by linarith [hrr n]) (by linarith [hΔmu n])
    have h3 : 0 ≤ (Δ n - E n) ^ 2 := sq_nonneg _
    unfold term
    rw [← mul_sub]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hb0 n)
    simp only [hΔdef, hq'def] at hg h2 h3 ⊢
    nlinarith [mul_le_mul_of_nonneg_left h2 hg0]
  -- sums
  have hC : ∀ n, |beta ^ n * Δ n ^ 2| ≤ beta ^ n * mu ^ 2 := fun n => by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hb0 n) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hΔ0 n) (hΔmu n) 2) (pow_nonneg hb0 n)
  have hC1 : ∀ n, |beta ^ n * Δ n| ≤ beta ^ n * mu := fun n => by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hb0 n) (hΔ0 n))]
    exact mul_le_mul_of_nonneg_left (hΔmu n) (pow_nonneg hb0 n)
  have sA := (summable_of_geom_bound hb0 hb1 _ _ hC).hasSum
  have sB := (summable_of_geom_bound hb0 hb1 _ _ hC1).hasSum
  set A := ∑' n, beta ^ n * Δ n ^ 2
  set B := ∑' n, beta ^ n * Δ n
  have sE2 : HasSum (fun n => beta ^ n * E n ^ 2) (beta * A) := by
    have h := (hasSum_nat_add_iff (f := fun n => beta ^ n * E n ^ 2) 1).mp
      (by
        have : (fun n => beta ^ (n + 1) * E (n + 1) ^ 2) = fun n => beta * (beta ^ n * Δ n ^ 2) := by
          funext n; simp only [hEdef, cons]; ring
        rw [this]; exact sA.mul_left beta)
    simpa [hEdef, cons] using h
  have sE1 : HasSum (fun n => beta ^ n * E n) (beta * B) := by
    have h := (hasSum_nat_add_iff (f := fun n => beta ^ n * E n) 1).mp
      (by
        have : (fun n => beta ^ (n + 1) * E (n + 1)) = fun n => beta * (beta ^ n * Δ n) := by
          funext n; simp only [hEdef, cons]; ring
        rw [this]; exact sB.mul_left beta)
    simpa [hEdef, cons] using h
  have hL : HasSum (fun n => beta ^ n * (gam * (Δ n ^ 2 / 2 - E n ^ 2 / 2 + mu * E n -
      beta * mu * Δ n))) (gam * (A / 2 - beta * A / 2 + mu * (beta * B) - beta * mu * B)) := by
    have := ((((sA.div_const 2).sub (sE2.div_const 2)).add (sE1.mul_left mu)).sub
      (sB.mul_left (beta * mu))).mul_left gam
    have e : (fun n => beta ^ n * (gam * (Δ n ^ 2 / 2 - E n ^ 2 / 2 + mu * E n -
        beta * mu * Δ n))) = (fun n => gam * ((beta ^ n * Δ n ^ 2 / 2 - beta ^ n * E n ^ 2 / 2 +
        mu * (beta ^ n * E n)) - beta * mu * (beta ^ n * Δ n))) := by
      funext n; ring
    rw [e]; exact this
  have hR : HasSum (fun n => term d0 lam gam theta beta m0 p0 q' n -
      term d0 lam gam theta beta m0 p0 q n)
      (pathValue d0 lam gam theta beta m0 p0 q' - pathValue d0 lam gam theta beta m0 p0 q) :=
    (term_summable hst m0 p0 q' hm hp hq').hasSum.sub (term_summable hst m0 p0 q hm hp hq).hasSum
  have hle := hasSum_le hper hL hR
  have hk : beta ^ k * Δ k ^ 2 ≤ A :=
    (summable_of_geom_bound hb0 hb1 _ _ hC).le_tsum k
      (fun j _ => mul_nonneg (pow_nonneg hb0 j) (sq_nonneg _))
  have hc : 0 ≤ gam * (1 - beta) / 2 := by
    apply div_nonneg (mul_nonneg hg0 (by linarith)) (by norm_num)
  have := mul_le_mul_of_nonneg_left hk hc
  simp only [hΔdef] at this
  nlinarith

/-- Every optimal path stays at or above any admissible floor `mu` (applied with `mu = min m0 S`). -/
theorem optimal_ge_floor {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 mu : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar)
    (hmu0 : 0 ≤ mu) (hmum : mu ≤ m0) (hmup : mu ≤ p0)
    (hd : gam * (1 - beta) * mu ≤ deriv (baseProfit d0) mu)
    (htan : ∀ x ∈ Set.Icc (0:ℝ) pbar, x < mu →
      baseProfit d0 x ≤ baseProfit d0 mu + deriv (baseProfit d0) mu * (x - mu))
    (q : ℕ → ℝ) (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) (k : ℕ) : mu ≤ q k := by
  have hq' : ∀ n, (fun n => max (q n) mu) n ∈ Set.Icc (0:ℝ) pbar := fun n =>
    ⟨(hq.1 n).1.trans (le_max_left _ _), max_le (hq.1 n).2 (hmum.trans hm.2)⟩
  have h1 := lift_gain hst m0 p0 mu hm hp hmu0 hmum hmup hd htan q hq.1 k
  have h2 := pathValue_le_J hst m0 p0 hm hp _ hq'
  rw [← hq.2] at h2
  have hc : 0 < gam * (1 - beta) / 2 :=
    div_pos (mul_pos hst.gam_pos (by linarith [hst.beta_lt_one])) (by norm_num)
  have h3 : beta ^ k * (max (q k) mu - q k) ^ 2 ≤ 0 := by
    by_contra h
    push_neg at h
    nlinarith [mul_pos hc h]
  have h4 : (max (q k) mu - q k) ^ 2 ≤ 0 := by
    by_contra h
    push_neg at h
    nlinarith [mul_pos (pow_pos hst.beta_pos k) h]
  have h5 : max (q k) mu - q k = 0 := by nlinarith [sq_nonneg (max (q k) mu - q k)]
  have := le_max_right (q k) mu
  linarith

/-- Derivative facts for the floor: `pi0'` is antitone on `P`, and the tangent-line bound. -/
lemma deriv_antitone {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) :
    AntitoneOn (deriv (baseProfit d0)) (Set.Icc (0:ℝ) pbar) :=
  hst.assumption1.strictConcave.concaveOn.antitoneOn_deriv hst.differentiable

lemma tangent_below {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (mu : ℝ) (hmu : mu ∈ Set.Icc (0:ℝ) pbar) :
    ∀ x ∈ Set.Icc (0:ℝ) pbar, x < mu →
      baseProfit d0 x ≤ baseProfit d0 mu + deriv (baseProfit d0) mu * (x - mu) := by
  intro x hx hxm
  have h := hst.assumption1.strictConcave.concaveOn.deriv_le_slope hx hmu hxm
    (hst.differentiable mu hmu)
  rw [slope_def_field] at h
  rw [le_div_iff₀ (by linarith)] at h
  nlinarith

theorem optimal_ge_minS {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (S : ℝ)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 : ℝ) (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (hmp : m0 ≤ p0)
    (q : ℕ → ℝ) (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) (k : ℕ) :
    min m0 S ≤ q k := by
  have hmuP : min m0 S ∈ Set.Icc (0:ℝ) pbar := ⟨le_min hm.1 hS.1.1, (min_le_left _ _).trans hm.2⟩
  apply optimal_ge_floor hst m0 p0 (min m0 S) hm hp hmuP.1 (min_le_left _ _)
    ((min_le_left _ _).trans hmp) _ (tangent_below hst _ hmuP) q hq k
  have h10 := hS.2
  unfold eq10 at h10
  have ha := deriv_antitone hst hmuP hS.1 (min_le_right _ _)
  have hc : 0 ≤ gam * (1 - beta) := mul_nonneg hst.gam_pos.le (by linarith [hst.beta_lt_one])
  have := mul_le_mul_of_nonneg_left (min_le_right m0 S) hc
  linarith

/-! ### D. Monotonicity when the minimum price is frozen -/

lemma psi_alt (lam gam x r : ℝ) :
    -lam * max (x - r) 0 + gam * max (r - x) 0 = gam * (r - x) - (lam - gam) * max (x - r) 0 := by
  rcases le_total x r with h | h
  · rw [max_eq_right (by linarith : x - r ≤ 0), max_eq_left (by linarith : 0 ≤ r - x)]; ring
  · rw [max_eq_left (by linarith : 0 ≤ x - r), max_eq_right (by linarith : r - x ≤ 0)]; ring

lemma clamp_mono (r r' b a : ℝ) (hr : r ≤ r') (hab : b ≤ a) :
    max (b - r) 0 - max (b - r') 0 ≤ max (a - r) 0 - max (a - r') 0 := by
  rcases le_total b r with h1 | h1 <;> rcases le_total b r' with h2 | h2 <;>
  rcases le_total a r with h3 | h3 <;> rcases le_total a r' with h4 | h4 <;>
  simp only [max_eq_right, max_eq_left, sub_nonpos, sub_nonneg, h1, h2, h3, h4] <;> linarith

lemma clamp_nonneg (r r' b : ℝ) (hr : r ≤ r') : 0 ≤ max (b - r) 0 - max (b - r') 0 := by
  have := max_le_max (by linarith : b - r' ≤ b - r) (le_refl (0:ℝ))
  linarith

/-- Strict increasing differences of the one-period profit in (price, reference). -/
lemma profit_strictID (d0 : ℝ → ℝ) (lam gam : ℝ) (hgam : 0 < gam) (hlg : gam ≤ lam)
    (a b r r' : ℝ) (hb : 0 ≤ b) (hba : b < a) (hr : r < r') :
    profit d0 lam gam a r - profit d0 lam gam b r <
      profit d0 lam gam a r' - profit d0 lam gam b r' := by
  rw [profit_eq, profit_eq, profit_eq, profit_eq, psi_alt, psi_alt, psi_alt, psi_alt]
  have hc := clamp_mono r r' b a hr.le hba.le
  have hn := clamp_nonneg r r' b hr.le
  have hl : 0 ≤ lam - gam := by linarith
  have I_b : gam * (r' - r) ≤ (gam * (r' - b) - (lam - gam) * max (b - r') 0) -
      (gam * (r - b) - (lam - gam) * max (b - r) 0) := by nlinarith [mul_nonneg hl hn]
  have I_ab : (gam * (r' - b) - (lam - gam) * max (b - r') 0) -
      (gam * (r - b) - (lam - gam) * max (b - r) 0) ≤
      (gam * (r' - a) - (lam - gam) * max (a - r') 0) -
      (gam * (r - a) - (lam - gam) * max (a - r) 0) := by nlinarith [mul_le_mul_of_nonneg_left hc hl]
  have hpos : 0 < gam * (r' - r) := mul_pos hgam (by linarith)
  have ha0 : 0 ≤ a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left I_ab ha0, mul_lt_mul_of_pos_right (sub_pos.mpr hba) hpos]

lemma tail_optimal {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) :
    ∀ n, IsOptimalPath pbar d0 lam gam theta beta (minPrice m0 q n) (price p0 q n)
      (fun k => q (n + k)) := by
  intro n
  induction n with
  | zero =>
    have e : (fun k => q (0 + k)) = q := by funext k; simp
    rw [e]; exact hq
  | succ n ih =>
    have hmn := minPrice_mem m0 q hm hq.1 n
    have hpn := price_mem p0 q hp hq.1 n
    have h := (optimal_step hst _ _ hmn hpn _ ih).1
    have e : (fun k => q (n + 1 + k)) = (fun k => q (n + (k + 1))) := by
      funext k; congr 1; omega
    rw [e]
    simpa [minPrice, price] using h

/-- Along an optimal path, each price maximizes the Bellman objective at its state. -/
lemma step_max {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) (n : ℕ)
    (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) pbar) :
    profit d0 lam gam y (theta * minPrice m0 q n + (1 - theta) * price p0 q n) +
        beta * J pbar d0 lam gam theta beta (min (minPrice m0 q n) y) y ≤
      profit d0 lam gam (q n) (theta * minPrice m0 q n + (1 - theta) * price p0 q n) +
        beta * J pbar d0 lam gam theta beta (minPrice m0 q (n + 1)) (q n) := by
  have hmn := minPrice_mem m0 q hm hq.1 n
  have hpn := price_mem p0 q hp hq.1 n
  have h1 := bellman_ge hst _ _ hmn hpn y hy
  have h2 := (optimal_step hst _ _ hmn hpn _ (tail_optimal hst m0 p0 hm hp q hq n)).2
  simp only [add_zero] at h2
  rw [h2] at h1
  exact h1

/-- Plateau lemma: a sequence whose successor map is order-preserving on strict comparisons is
monotone or antitone. -/
lemma plateau_aux (x : ℕ → ℝ) (hP : ∀ t u, x t < x u → x (t + 1) ≤ x (u + 1)) (t : ℕ)
    (ht : x t < x (t + 1)) : ∀ v, t ≤ v → x v ≤ x (v + 1) := by
  have inv : ∀ j, ∃ w, x w < x (t + 1 + j) ∧ x (t + 1 + j) ≤ x (w + 1) := by
    intro j
    induction j with
    | zero => exact ⟨t, by simpa using ht, by simp⟩
    | succ j ih =>
      obtain ⟨w, hw1, hw2⟩ := ih
      have hstep : x (t + 1 + j) ≤ x (t + 1 + j + 1) := hw2.trans (hP w _ hw1)
      rcases lt_or_eq_of_le hstep with hlt | heq
      · exact ⟨t + 1 + j, hlt, le_refl _⟩
      · refine ⟨w, ?_, ?_⟩
        · rw [show t + 1 + (j + 1) = t + 1 + j + 1 by omega, ← heq]; exact hw1
        · rw [show t + 1 + (j + 1) = t + 1 + j + 1 by omega, ← heq]; exact hw2
  intro v hv
  rcases Nat.eq_or_lt_of_le hv with rfl | hlt
  · exact ht.le
  · obtain ⟨w, hw1, hw2⟩ := inv (v - (t + 1))
    have e : t + 1 + (v - (t + 1)) = v := by omega
    rw [e] at hw1 hw2
    exact hw2.trans (hP w v hw1)

lemma plateau (x : ℕ → ℝ) (hP : ∀ t u, x t < x u → x (t + 1) ≤ x (u + 1)) :
    Monotone x ∨ Antitone x := by
  have hP' : ∀ t u, (-x) t < (-x) u → (-x) (t + 1) ≤ (-x) (u + 1) := by
    intro t u h
    simp only [Pi.neg_apply, neg_lt_neg_iff, neg_le_neg_iff] at h ⊢
    exact hP u t h
  by_cases hup : ∃ t, x t < x (t + 1)
  · obtain ⟨t, ht⟩ := hup
    left
    apply monotone_nat_of_le_succ
    intro v
    rcases le_total t v with h | h
    · exact plateau_aux x hP t ht v h
    · by_contra hc
      push_neg at hc
      have hd := plateau_aux (-x) hP' v (by simp only [Pi.neg_apply]; linarith) t h
      simp only [Pi.neg_apply] at hd
      linarith
  · by_cases hdn : ∃ t, x (t + 1) < x t
    · obtain ⟨t, ht⟩ := hdn
      right
      apply antitone_nat_of_succ_le
      intro v
      rcases le_total t v with h | h
      · have := plateau_aux (-x) hP' t (by simp only [Pi.neg_apply]; linarith) v h
        simp only [Pi.neg_apply] at this
        linarith
      · by_contra hc
        push_neg at hc
        exact hup ⟨v, hc⟩
    · left
      apply monotone_nat_of_le_succ
      intro v
      push_neg at hup hdn
      exact hdn v

/-- Comparison of maximizers for two states with the same minimum price (`theta < 1`). -/
lemma argmax_mono {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (htl : theta < 1)
    (m x x' a b : ℝ) (hx : x < x') (ha : a ∈ Set.Icc (0:ℝ) pbar) (hb : b ∈ Set.Icc (0:ℝ) pbar)
    (Ja Jb : ℝ)
    (hA : profit d0 lam gam b (theta * m + (1 - theta) * x) + beta * Jb ≤
      profit d0 lam gam a (theta * m + (1 - theta) * x) + beta * Ja)
    (hB : profit d0 lam gam a (theta * m + (1 - theta) * x') + beta * Ja ≤
      profit d0 lam gam b (theta * m + (1 - theta) * x') + beta * Jb) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have hr : theta * m + (1 - theta) * x < theta * m + (1 - theta) * x' := by
    have : 0 < 1 - theta := by linarith
    nlinarith
  have := profit_strictID d0 lam gam hst.gam_pos hst.gam_le_lam a b _ _ hb.1 hab hr
  linarith

lemma profit_above (d0 : ℝ → ℝ) (lam gam m y : ℝ) (h : m ≤ y) :
    profit d0 lam gam y m = baseProfit d0 y - lam * (y - m) * y := by
  rw [profit_eq, max_eq_left (by linarith : 0 ≤ y - m), max_eq_right (by linarith : m - y ≤ 0)]
  ring

lemma J_theta_one (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam beta m p p' : ℝ) :
    J pbar d0 lam gam 1 beta m p = J pbar d0 lam gam 1 beta m p' := by
  simp only [J, pathValue, refPrice, sub_self, zero_mul, add_zero]

/-- D(a/b): if every price of an optimal path stays at or above `m0`, the path is monotone. -/
theorem monotone_frozen {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) (hge : ∀ n, m0 ≤ q n) :
    Monotone q ∨ Antitone q := by
  have hmin : ∀ n, minPrice m0 q n = m0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show min (minPrice m0 q n) (q n) = m0
      rw [ih]; exact min_eq_left (hge n)
  rcases lt_or_eq_of_le hst.theta_le_one with htl | hte
  · have hP : ∀ t u, price p0 q t < price p0 q u → price p0 q (t + 1) ≤ price p0 q (u + 1) := by
      intro t u htu
      have h1 := step_max hst m0 p0 hm hp q hq t (q u) (hq.1 u)
      have h2 := step_max hst m0 p0 hm hp q hq u (q t) (hq.1 t)
      simp only [hmin, min_eq_left (hge u), min_eq_left (hge t)] at h1 h2
      exact argmax_mono hst htl m0 _ _ (q t) (q u) htu (hq.1 t) (hq.1 u) _ _ h1 h2
    rcases plateau _ hP with h | h
    · left; exact fun a b hab => h (Nat.succ_le_succ hab)
    · right; exact fun a b hab => h (Nat.succ_le_succ hab)
  · subst hte
    have key : ∀ n k, q n = q k := by
      intro n k
      by_contra hne
      have h1 := step_max hst m0 p0 hm hp q hq n (q k) (hq.1 k)
      have h2 := step_max hst m0 p0 hm hp q hq k (q n) (hq.1 n)
      set c := (q n + q k) / 2 with hc
      have hcP : c ∈ Set.Icc (0:ℝ) pbar :=
        ⟨by linarith [(hq.1 n).1, (hq.1 k).1], by linarith [(hq.1 n).2, (hq.1 k).2]⟩
      have hcm : m0 ≤ c := by linarith [hge n, hge k]
      have h3 := step_max hst m0 p0 hm hp q hq n c hcP
      simp only [hmin, min_eq_left (hge k), min_eq_left (hge n), min_eq_left hcm, one_mul,
        sub_self, zero_mul, add_zero] at h1 h2 h3
      rw [J_theta_one pbar d0 lam gam beta m0 (q k) (q n)] at h1 h2
      rw [J_theta_one pbar d0 lam gam beta m0 c (q n)] at h3
      rw [profit_above d0 lam gam m0 _ (hge n), profit_above d0 lam gam m0 _ (hge k)] at h1 h2
      rw [profit_above d0 lam gam m0 _ (hge n), profit_above d0 lam gam m0 _ hcm] at h3
      have hsc := hst.assumption1.strictConcave.2 (hq.1 n) (hq.1 k) hne
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hsc
      have hce : 1 / 2 * q n + 1 / 2 * q k = c := by rw [hc]; ring
      rw [hce] at hsc
      have hl := hst.gam_pos.trans_le hst.gam_le_lam
      have hq2 : lam * (c - m0) * c ≤ (lam * (q n - m0) * q n + lam * (q k - m0) * q k) / 2 := by
        have e : (lam * (q n - m0) * q n + lam * (q k - m0) * q k) / 2 - lam * (c - m0) * c =
            lam * (q n - q k) ^ 2 / 4 := by rw [hc]; ring
        nlinarith [mul_nonneg hl.le (sq_nonneg (q n - q k))]
      linarith
    left
    intro a b _
    rw [key a b]

/-! ### E. The limit of an optimal path is a steady state -/

lemma pathValue_continuous3 {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) :
    Continuous (fun z : Set.Icc (0:ℝ) pbar × Set.Icc (0:ℝ) pbar × (ℕ → Set.Icc (0:ℝ) pbar) =>
      pathValue d0 lam gam theta beta (z.1 : ℝ) (z.2.1 : ℝ) (fun k => (z.2.2 k : ℝ))) := by
  obtain ⟨D, hD⟩ := demand_bound hst.assumption1
  show Continuous (fun z : Set.Icc (0:ℝ) pbar × Set.Icc (0:ℝ) pbar × (ℕ → Set.Icc (0:ℝ) pbar) =>
      ∑' n, term d0 lam gam theta beta (z.1 : ℝ) (z.2.1 : ℝ) (fun k => (z.2.2 k : ℝ)) n)
  have hqk : ∀ k, Continuous (fun z : Set.Icc (0:ℝ) pbar × Set.Icc (0:ℝ) pbar ×
      (ℕ → Set.Icc (0:ℝ) pbar) => ((z.2.2 k : Set.Icc (0:ℝ) pbar) : ℝ)) := fun k =>
    continuous_subtype_val.comp ((continuous_apply k).comp (continuous_snd.comp continuous_snd))
  have hmin : ∀ n, Continuous (fun z : Set.Icc (0:ℝ) pbar × Set.Icc (0:ℝ) pbar ×
      (ℕ → Set.Icc (0:ℝ) pbar) => minPrice (z.1 : ℝ) (fun k => (z.2.2 k : ℝ)) n) := by
    intro n
    induction n with
    | zero => exact continuous_subtype_val.comp continuous_fst
    | succ n ih => exact ih.min (hqk n)
  have hpr : ∀ n, Continuous (fun z : Set.Icc (0:ℝ) pbar × Set.Icc (0:ℝ) pbar ×
      (ℕ → Set.Icc (0:ℝ) pbar) => price (z.2.1 : ℝ) (fun k => (z.2.2 k : ℝ)) n) := by
    intro n
    cases n with
    | zero => exact continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    | succ n => exact hqk n
  refine continuous_tsum (fun n => ?_)
    ((summable_geometric_of_lt_one hst.beta_pos.le hst.beta_lt_one).mul_right
      (pbar * (D + (lam + gam) * pbar))) (fun n z => ?_)
  · have hr : Continuous (fun z : Set.Icc (0:ℝ) pbar × Set.Icc (0:ℝ) pbar ×
        (ℕ → Set.Icc (0:ℝ) pbar) => refPrice theta (z.1 : ℝ) (z.2.1 : ℝ)
          (fun k => (z.2.2 k : ℝ)) n) := by
      unfold refPrice
      exact (continuous_const.mul (hmin n)).add (continuous_const.mul (hpr n))
    have hd : Continuous (fun z : Set.Icc (0:ℝ) pbar × Set.Icc (0:ℝ) pbar ×
        (ℕ → Set.Icc (0:ℝ) pbar) => d0 ((z.2.2 n : Set.Icc (0:ℝ) pbar) : ℝ)) :=
      hst.assumption1.continuous.comp_continuous (hqk n) (fun z => (z.2.2 n).2)
    unfold term profit demand
    exact continuous_const.mul ((hqk n).mul ((hd.sub (continuous_const.mul
      (((hqk n).sub hr).max continuous_const))).add (continuous_const.mul
      ((hr.sub (hqk n)).max continuous_const))))
  · rw [Real.norm_eq_abs]
    exact term_abs_le hst D hD _ _ _ z.1.2 z.2.1.2 (fun k => (z.2.2 k).2) n

theorem limit_steady {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) (M L : ℝ)
    (hqL : Filter.Tendsto q Filter.atTop (nhds L))
    (hM : Filter.Tendsto (minPrice m0 q) Filter.atTop (nhds M)) :
    M ∈ Set.Icc (0:ℝ) pbar ∧ L ∈ Set.Icc (0:ℝ) pbar ∧
      IsOptimalPath pbar d0 lam gam theta beta M L (fun _ => L) := by
  have hLP : L ∈ Set.Icc (0:ℝ) pbar :=
    isClosed_Icc.mem_of_tendsto hqL (Filter.Eventually.of_forall hq.1)
  have hMP : M ∈ Set.Icc (0:ℝ) pbar :=
    isClosed_Icc.mem_of_tendsto hM (Filter.Eventually.of_forall (minPrice_mem m0 q hm hq.1))
  have hx : Filter.Tendsto (price p0 q) Filter.atTop (nhds L) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mp hqL
  have hmP := minPrice_mem m0 q hm hq.1
  have hpP := price_mem p0 q hp hq.1
  have hcont := pathValue_continuous3 hst (d0 := d0) (lam := lam) (gam := gam) (theta := theta)
    (beta := beta)
  have hs1 : Filter.Tendsto (fun n => ((⟨minPrice m0 q n, hmP n⟩ : Set.Icc (0:ℝ) pbar),
      (⟨price p0 q n, hpP n⟩ : Set.Icc (0:ℝ) pbar))) Filter.atTop
      (nhds ((⟨M, hMP⟩ : Set.Icc (0:ℝ) pbar), (⟨L, hLP⟩ : Set.Icc (0:ℝ) pbar))) :=
    (tendsto_subtype_rng.mpr hM).prodMk_nhds (tendsto_subtype_rng.mpr hx)
  -- value along the optimal tails
  have hT : Filter.Tendsto (fun n => pathValue d0 lam gam theta beta (minPrice m0 q n)
      (price p0 q n) (fun k => q (n + k))) Filter.atTop
      (nhds (pathValue d0 lam gam theta beta M L (fun _ => L))) := by
    have hz : Filter.Tendsto (fun n => ((⟨minPrice m0 q n, hmP n⟩ : Set.Icc (0:ℝ) pbar),
        (⟨price p0 q n, hpP n⟩ : Set.Icc (0:ℝ) pbar),
        (fun k => (⟨q (n + k), hq.1 (n + k)⟩ : Set.Icc (0:ℝ) pbar)))) Filter.atTop
        (nhds ((⟨M, hMP⟩ : Set.Icc (0:ℝ) pbar), (⟨L, hLP⟩ : Set.Icc (0:ℝ) pbar),
          (fun _ => (⟨L, hLP⟩ : Set.Icc (0:ℝ) pbar)))) := by
      refine (tendsto_subtype_rng.mpr hM).prodMk_nhds
        ((tendsto_subtype_rng.mpr hx).prodMk_nhds (tendsto_pi_nhds.mpr (fun k => ?_)))
      exact tendsto_subtype_rng.mpr (hqL.comp (Filter.tendsto_add_atTop_nat k))
    exact (hcont.tendsto _).comp hz
  have hJ : ∀ n, pathValue d0 lam gam theta beta (minPrice m0 q n) (price p0 q n)
      (fun k => q (n + k)) = J pbar d0 lam gam theta beta (minPrice m0 q n) (price p0 q n) :=
    fun n => (tail_optimal hst m0 p0 hm hp q hq n).2
  have hle : ∀ r : ℕ → Set.Icc (0:ℝ) pbar,
      pathValue d0 lam gam theta beta M L (fun k => (r k : ℝ)) ≤
        pathValue d0 lam gam theta beta M L (fun _ => L) := by
    intro r
    have hz : Filter.Tendsto (fun n => ((⟨minPrice m0 q n, hmP n⟩ : Set.Icc (0:ℝ) pbar),
        (⟨price p0 q n, hpP n⟩ : Set.Icc (0:ℝ) pbar), r)) Filter.atTop
        (nhds ((⟨M, hMP⟩ : Set.Icc (0:ℝ) pbar), (⟨L, hLP⟩ : Set.Icc (0:ℝ) pbar), r)) :=
      (tendsto_subtype_rng.mpr hM).prodMk_nhds
        ((tendsto_subtype_rng.mpr hx).prodMk_nhds tendsto_const_nhds)
    have hR := (hcont.tendsto _).comp hz
    refine le_of_tendsto_of_tendsto' hR hT (fun n => ?_)
    simp only [Function.comp]
    rw [hJ n]
    exact pathValue_le_J hst _ _ (hmP n) (hpP n) _ (fun k => (r k).2)
  have : Nonempty (ℕ → Set.Icc (0:ℝ) pbar) := ⟨fun _ => ⟨L, hLP⟩⟩
  refine ⟨hMP, hLP, fun _ => hLP, le_antisymm ?_ (ciSup_le hle)⟩
  exact pathValue_le_J hst M L hMP hLP _ (fun _ => hLP)


/-! ### F. Necessary conditions at a steady state (one-sided perturbations of a constant path) -/

lemma exists_right_gt {V : ℝ → ℝ} {v a : ℝ} (h : HasDerivAt V v a) (hv : 0 < v) (δ : ℝ)
    (hδ : 0 < δ) : ∃ c, a < c ∧ c < a + δ ∧ V a < V c := by
  have hT := h.tendsto_slope_zero_right
  have h1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t⁻¹ • (V (a + t) - V a) :=
    hT.eventually (Ioi_mem_nhds hv)
  have h2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t ∈ Set.Ioo (0:ℝ) δ :=
    Ioo_mem_nhdsGT hδ
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  refine ⟨a + t, by linarith [ht2.1], by linarith [ht2.2], ?_⟩
  rw [smul_eq_mul] at ht1
  have htp : 0 < t := ht2.1
  have := (mul_pos_iff_of_pos_left (inv_pos.mpr htp)).mp ht1
  linarith

lemma exists_left_gt {V : ℝ → ℝ} {v a : ℝ} (h : HasDerivAt V v a) (hv : v < 0) (δ : ℝ)
    (hδ : 0 < δ) : ∃ c, a - δ < c ∧ c < a ∧ V a < V c := by
  have hT := h.tendsto_slope_zero_left
  have h1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Iio 0), t⁻¹ • (V (a + t) - V a) < 0 :=
    hT.eventually (Iio_mem_nhds hv)
  have h2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Iio 0), t ∈ Set.Ioo (-δ) 0 :=
    Ioo_mem_nhdsLT (by linarith)
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  refine ⟨a + t, by linarith [ht2.1], by linarith [ht2.2], ?_⟩
  rw [smul_eq_mul] at ht1
  have htn : t < 0 := ht2.2
  have hi : t⁻¹ < 0 := inv_lt_zero.mpr htn
  by_contra hc
  push_neg at hc
  have : 0 ≤ t⁻¹ * (V (a + t) - V a) := mul_nonneg_of_nonpos_of_nonpos hi.le (by linarith)
  linarith

lemma minPrice_const (a c : ℝ) : ∀ n, minPrice (min a c) (fun _ => c) n = min a c := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show min (minPrice (min a c) (fun _ => c) n) c = min a c
    rw [ih, min_assoc, min_self]

lemma constPath_value {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m p c : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (hp : p ∈ Set.Icc (0:ℝ) pbar) (hc : c ∈ Set.Icc (0:ℝ) pbar) :
    pathValue d0 lam gam theta beta m p (fun _ => c) =
      profit d0 lam gam c (theta * m + (1 - theta) * p) +
        beta / (1 - beta) * profit d0 lam gam c (theta * min m c + (1 - theta) * c) := by
  rw [pathValue_shift hst m p (fun _ => c) hm hp (fun _ => hc)]
  have hr0 : refPrice theta m p (fun _ => c) 0 = theta * m + (1 - theta) * p := rfl
  rw [hr0]
  congr 1
  have hterm : ∀ n, beta ^ n * profit d0 lam gam ((fun _ : ℕ => c) n)
      (refPrice theta (min m c) c (fun _ => c) n) =
      beta ^ n * profit d0 lam gam c (theta * min m c + (1 - theta) * c) := by
    intro n
    have hpr : price c (fun _ => c) n = c := by cases n <;> rfl
    simp only [refPrice, minPrice_const, hpr]
  have hb0 := hst.beta_pos
  have hb1 := hst.beta_lt_one
  simp only [pathValue]
  rw [tsum_congr hterm, tsum_mul_right, tsum_geometric_of_lt_one hb0.le hb1]
  field_simp

lemma profit_below (d0 : ℝ → ℝ) (lam gam r y : ℝ) (h : y ≤ r) :
    profit d0 lam gam y r = baseProfit d0 y + gam * (r - y) * y := by
  rw [profit_eq, max_eq_right (by linarith : y - r ≤ 0), max_eq_left (by linarith : 0 ≤ r - y)]
  ring

lemma deriv_strictAnti {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) :
    StrictAntiOn (deriv (baseProfit d0)) (Set.Icc (0:ℝ) pbar) :=
  hst.assumption1.strictConcave.strictAntiOn_deriv hst.differentiable

/-- The value of the constant path `c ≥ max(r0, m)` from state `(m, p)`, as a smooth function. -/
noncomputable def Vup (d0 : ℝ → ℝ) (lam theta beta m p : ℝ) (c : ℝ) : ℝ :=
  (baseProfit d0 c - lam * (c - (theta * m + (1 - theta) * p)) * c) +
    beta / (1 - beta) * (baseProfit d0 c - lam * (c - (theta * m + (1 - theta) * c)) * c)

lemma Vup_eq {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m p c : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (hp : p ∈ Set.Icc (0:ℝ) pbar) (hc : c ∈ Set.Icc (0:ℝ) pbar)
    (hcm : m ≤ c) (hcr : theta * m + (1 - theta) * p ≤ c) :
    pathValue d0 lam gam theta beta m p (fun _ => c) = Vup d0 lam theta beta m p c := by
  rw [constPath_value hst m p c hm hp hc, min_eq_left hcm, profit_above _ _ _ _ _ hcr,
    profit_above]
  · rfl
  · have := hst.theta_nonneg; have := hst.theta_le_one; nlinarith

lemma Vup_hasDeriv {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) pbar) :
    HasDerivAt (Vup d0 lam theta beta m p)
      ((deriv (baseProfit d0) p - lam * (2 * p - (theta * m + (1 - theta) * p))) +
        beta / (1 - beta) * (deriv (baseProfit d0) p - lam * theta * (2 * p - m))) p := by
  have h0 : HasDerivAt (baseProfit d0) (deriv (baseProfit d0) p) p :=
    (hst.differentiable p hp).hasDerivAt
  have hA : HasDerivAt (fun c : ℝ => lam * (c - (theta * m + (1 - theta) * p)) * c)
      (lam * (2 * p - (theta * m + (1 - theta) * p))) p := by
    have := (((hasDerivAt_id' p).sub_const (theta * m + (1 - theta) * p)).const_mul lam).mul
      (hasDerivAt_id' p)
    exact this.congr_deriv (by ring)
  have hB : HasDerivAt (fun c : ℝ => lam * (c - (theta * m + (1 - theta) * c)) * c)
      (lam * theta * (2 * p - m)) p := by
    have h1 : HasDerivAt (fun c : ℝ => c - (theta * m + (1 - theta) * c)) theta p := by
      have := (hasDerivAt_id' p).sub (((hasDerivAt_id' p).const_mul (1 - theta)).const_add
        (theta * m))
      exact this.congr_deriv (by ring)
    have := (h1.const_mul lam).mul (hasDerivAt_id' p)
    exact this.congr_deriv (by ring)
  exact (h0.sub hA).add ((h0.sub hB).const_mul (beta / (1 - beta)))

/-- `(1 - β) V'(p)` equals the eq12 expression. -/
lemma Vup_deriv_eq (d0 : ℝ → ℝ) (lam theta beta m p D : ℝ) (hb : beta < 1) :
    ((D - lam * (2 * p - (theta * m + (1 - theta) * p))) +
        beta / (1 - beta) * (D - lam * theta * (2 * p - m))) * (1 - beta) =
      D - lam * (2 - (1 - theta) * (1 + beta)) * p + lam * theta * m := by
  have : (1 - beta) ≠ 0 := by linarith
  field_simp
  ring

/-- Right perturbation at a steady state `(m, p)`, `p < pbar`: the eq12 expression is `≤ 0`. -/
lemma steady_right {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m p : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (hp : p ∈ Set.Icc (0:ℝ) pbar) (hmp : m ≤ p) (hpb : p < pbar)
    (hopt : IsOptimalPath pbar d0 lam gam theta beta m p (fun _ => p)) :
    deriv (baseProfit d0) p - lam * (2 * p - (theta * m + (1 - theta) * p)) +
        beta / (1 - beta) * (deriv (baseProfit d0) p - lam * theta * (2 * p - m)) ≤ 0 := by
  have ht0 := hst.theta_nonneg; have ht1 := hst.theta_le_one
  by_contra hpos
  push_neg at hpos
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_right_gt (Vup_hasDeriv hst m p hp) hpos (pbar - p)
    (by linarith)
  have hcP : c ∈ Set.Icc (0:ℝ) pbar := ⟨by linarith [hp.1], by linarith⟩
  have hr0 : theta * m + (1 - theta) * p ≤ c := by nlinarith
  have e1 := Vup_eq hst m p c hm hp hcP (by linarith) hr0
  have e2 := Vup_eq hst m p p hm hp hp hmp (by nlinarith)
  have hle := pathValue_le_J hst m p hm hp (fun _ => c) (fun _ => hcP)
  rw [← hopt.2, e1, e2] at hle
  linarith

/-- Left perturbation at a steady state `(m, p)` with `m < p`: the eq12 expression is `≥ 0`. -/
lemma steady_left {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (htp : 0 < theta) (m p : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (hp : p ∈ Set.Icc (0:ℝ) pbar) (hmp : m < p)
    (hopt : IsOptimalPath pbar d0 lam gam theta beta m p (fun _ => p)) :
    0 ≤ deriv (baseProfit d0) p - lam * (2 * p - (theta * m + (1 - theta) * p)) +
        beta / (1 - beta) * (deriv (baseProfit d0) p - lam * theta * (2 * p - m)) := by
  have ht0 := htp; have ht1 := hst.theta_le_one
  by_contra hneg
  push_neg at hneg
  have hgap : 0 < p - (theta * m + (1 - theta) * p) := by nlinarith
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_left_gt (Vup_hasDeriv hst m p hp) hneg _ hgap
  have hcP : c ∈ Set.Icc (0:ℝ) pbar := ⟨by nlinarith [hm.1], by linarith [hp.2]⟩
  have hr0 : theta * m + (1 - theta) * p ≤ c := by linarith
  have hcm : m ≤ c := by nlinarith
  have e1 := Vup_eq hst m p c hm hp hcP hcm hr0
  have e2 := Vup_eq hst m p p hm hp hp hmp.le (by nlinarith)
  have hle := pathValue_le_J hst m p hm hp (fun _ => c) (fun _ => hcP)
  rw [← hopt.2, e1, e2] at hle
  linarith

lemma deriv_pbar_nonpos {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (hpb : 0 < pbar) :
    deriv (baseProfit d0) pbar ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have hpbP : pbar ∈ Set.Icc (0:ℝ) pbar := ⟨hpb.le, le_refl _⟩
  have h0 : HasDerivAt (fun x => -baseProfit d0 x) (-deriv (baseProfit d0) pbar) pbar :=
    (hst.differentiable pbar hpbP).hasDerivAt.neg
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_left_gt h0 (by linarith) pbar hpb
  have hz : baseProfit d0 pbar = 0 := by
    simp [baseProfit, hst.assumption1.demand_pbar]
  have hcP : c ∈ Set.Icc (0:ℝ) pbar := ⟨by linarith, hc2.le⟩
  have hnn : 0 ≤ baseProfit d0 c := mul_nonneg hcP.1 (hst.assumption1.nonneg c hcP)
  have h3 : -baseProfit d0 pbar < -baseProfit d0 c := hc3
  linarith

/-- F1: at a steady state `(m, p)` with `m < p`, eq12 holds. -/
theorem steady_eq12 {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (htp : 0 < theta) (m p : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (hp : p ∈ Set.Icc (0:ℝ) pbar) (hmp : m < p)
    (hopt : IsOptimalPath pbar d0 lam gam theta beta m p (fun _ => p)) :
    eq12 d0 lam theta beta m p := by
  have hb1 := hst.beta_lt_one; have hb0 := hst.beta_pos
  have ht0 := htp; have ht1 := hst.theta_le_one
  have hlam : 0 < lam := lt_of_lt_of_le hst.gam_pos hst.gam_le_lam
  have hE := Vup_deriv_eq d0 lam theta beta m p (deriv (baseProfit d0) p) hb1
  have hL := steady_left hst htp m p hm hp hmp hopt
  unfold eq12
  have h1b : 0 < 1 - beta := by linarith
  rcases lt_or_eq_of_le hp.2 with hlt | heq
  · have hR := steady_right hst m p hm hp hmp.le hlt hopt
    have : deriv (baseProfit d0) p - lam * (2 * p - (theta * m + (1 - theta) * p)) +
        beta / (1 - beta) * (deriv (baseProfit d0) p - lam * theta * (2 * p - m)) = 0 :=
      le_antisymm hR hL
    rw [this, zero_mul] at hE
    linarith
  · exfalso
    have hpb : 0 < pbar := by linarith [hm.1]
    have hd := deriv_pbar_nonpos hst hpb
    rw [heq] at hE hL
    have h0 := mul_nonneg hL h1b.le
    rw [hE] at h0
    have hk : theta < 2 - (1 - theta) * (1 + beta) := by nlinarith
    have hmpb : m < pbar := by linarith
    have : lam * theta * m < lam * (2 - (1 - theta) * (1 + beta)) * pbar := by
      have h1 : lam * theta * m ≤ lam * theta * pbar :=
        mul_le_mul_of_nonneg_left hmpb.le (by positivity)
      have h2 : lam * theta * pbar < lam * (2 - (1 - theta) * (1 + beta)) * pbar := by
        have := mul_lt_mul_of_pos_left hk hlam
        exact mul_lt_mul_of_pos_right this hpb
      linarith
    linarith

/-- F2: at a diagonal steady state `(m, m)`, `s ≤ m`. -/
theorem steady_diag_ge_s {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s) (m : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar)
    (hopt : IsOptimalPath pbar d0 lam gam theta beta m m (fun _ => m)) : s ≤ m := by
  by_contra hlt
  push_neg at hlt
  have hb1 := hst.beta_lt_one
  have hR := steady_right hst m m hm hm le_rfl (lt_of_lt_of_le hlt hs.1.2) hopt
  have hE := Vup_deriv_eq d0 lam theta beta m m (deriv (baseProfit d0) m) hb1
  have h0 := mul_nonpos_of_nonpos_of_nonneg hR (by linarith : (0:ℝ) ≤ 1 - beta)
  rw [hE] at h0
  have hsa := deriv_strictAnti hst hm hs.1 hlt
  have h9 := hs.2
  unfold eq9 at h9
  have hlam : 0 ≤ lam := (hst.gam_pos.le.trans hst.gam_le_lam)
  have hk : 0 ≤ lam * (1 - beta * (1 - theta)) := by
    have := hst.theta_nonneg; have := hst.theta_le_one; have := hst.beta_pos
    apply mul_nonneg hlam; nlinarith
  have := mul_le_mul_of_nonneg_left hlt.le hk
  nlinarith

/-- F3: at a diagonal steady state `(m, m)`, `m ≤ S`. -/
theorem steady_diag_le_S {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (S : ℝ)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S) (m : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar)
    (hopt : IsOptimalPath pbar d0 lam gam theta beta m m (fun _ => m)) : m ≤ S := by
  by_contra hlt
  push_neg at hlt
  have hb1 := hst.beta_lt_one; have hb0 := hst.beta_pos
  have hg := hst.gam_pos
  set W : ℝ → ℝ := fun c => baseProfit d0 c + gam * (m - c) * c + beta / (1 - beta) * baseProfit d0 c
    with hW
  have h0 : HasDerivAt (baseProfit d0) (deriv (baseProfit d0) m) m :=
    (hst.differentiable m hm).hasDerivAt
  have hA : HasDerivAt (fun c : ℝ => gam * (m - c) * c) (gam * (m - 2 * m)) m := by
    have := (((hasDerivAt_id' m).const_sub m).const_mul gam).mul (hasDerivAt_id' m)
    exact this.congr_deriv (by ring)
  have hWd : HasDerivAt W (deriv (baseProfit d0) m + gam * (m - 2 * m) +
      beta / (1 - beta) * deriv (baseProfit d0) m) m :=
    (h0.add hA).add (h0.const_mul _)
  have hsa := deriv_strictAnti hst hS.1 hm hlt
  have h10 := hS.2
  unfold eq10 at h10
  have hneg : deriv (baseProfit d0) m + gam * (m - 2 * m) +
      beta / (1 - beta) * deriv (baseProfit d0) m < 0 := by
    have hid : (deriv (baseProfit d0) m + gam * (m - 2 * m) +
        beta / (1 - beta) * deriv (baseProfit d0) m) * (1 - beta) =
        deriv (baseProfit d0) m - gam * (1 - beta) * m := by
      have : (1 - beta) ≠ 0 := by linarith
      field_simp; ring
    have hk : gam * (1 - beta) * S < gam * (1 - beta) * m :=
      mul_lt_mul_of_pos_left hlt (mul_pos hg (by linarith))
    by_contra hc; push_neg at hc
    have := mul_nonneg hc (by linarith : (0:ℝ) ≤ 1 - beta)
    rw [hid] at this
    linarith
  have hm0 : 0 < m := lt_of_le_of_lt hS.1.1 hlt
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_left_gt hWd hneg m hm0
  have hcP : c ∈ Set.Icc (0:ℝ) pbar := ⟨by linarith, by linarith [hm.2]⟩
  have hvc : pathValue d0 lam gam theta beta m m (fun _ => c) = W c := by
    rw [constPath_value hst m m c hm hm hcP, min_eq_right hc2.le]
    have : theta * m + (1 - theta) * m = m := by ring
    have h2 : theta * c + (1 - theta) * c = c := by ring
    rw [this, h2, profit_below _ _ _ _ _ hc2.le, profit_below _ _ _ _ _ le_rfl]
    simp only [hW]; ring
  have hvm : pathValue d0 lam gam theta beta m m (fun _ => m) = W m := by
    rw [constPath_value hst m m m hm hm hm, min_self]
    have : theta * m + (1 - theta) * m = m := by ring
    rw [this, profit_below _ _ _ _ _ le_rfl]
    simp only [hW]; ring
  have hle := pathValue_le_J hst m m hm hm (fun _ => c) (fun _ => hcP)
  rw [← hopt.2, hvc, hvm] at hle
  linarith


/-! ### G. Case (c) via the auxiliary problem `lam := gam, theta := 0` -/

lemma opt_theta0 {pbar : ℝ} {d0 : ℝ → ℝ} {gam beta : ℝ} (m m' p : ℝ) (q : ℕ → ℝ) :
    IsOptimalPath pbar d0 gam gam 0 beta m p q ↔ IsOptimalPath pbar d0 gam gam 0 beta m' p q := by
  simp only [IsOptimalPath, J, pathValue, refPrice, zero_mul, zero_add, sub_zero, one_mul]

lemma minPrice_frozen (m0 : ℝ) (q : ℕ → ℝ) (K : ℕ) (hge : ∀ n, n < K → m0 ≤ q n) :
    ∀ n, n ≤ K → minPrice m0 q n = m0 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    show min (minPrice m0 q n) (q n) = m0
    rw [ih (by omega)]
    exact min_eq_left (hge n (by omega))

lemma monotone_price {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (htl : theta < 1) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) (hge : ∀ n, m0 ≤ q n) :
    Monotone (price p0 q) ∨ Antitone (price p0 q) := by
  have hmin : ∀ n, minPrice m0 q n = m0 := fun n =>
    minPrice_frozen m0 q n (fun k _ => hge k) n le_rfl
  apply plateau
  intro t u htu
  have h1 := step_max hst m0 p0 hm hp q hq t (q u) (hq.1 u)
  have h2 := step_max hst m0 p0 hm hp q hq u (q t) (hq.1 t)
  simp only [hmin, min_eq_left (hge u), min_eq_left (hge t)] at h1 h2
  exact argmax_mono hst htl m0 _ _ (q t) (q u) htu (hq.1 t) (hq.1 u) _ _ h1 h2

lemma aux_limit_le_S {pbar : ℝ} {d0 : ℝ → ℝ} {gam beta : ℝ}
    (hst : Std0 pbar d0 gam gam 0 beta) (S : ℝ)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S) (m p : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (hp : p ∈ Set.Icc (0:ℝ) pbar) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 gam gam 0 beta m p q) (L : ℝ)
    (hL : Filter.Tendsto q Filter.atTop (nhds L)) : L ≤ S := by
  have h0P : (0:ℝ) ∈ Set.Icc (0:ℝ) pbar := ⟨le_rfl, hm.1.trans hm.2⟩
  have hq0 := (opt_theta0 m 0 p q).mp hq
  have hmin : minPrice 0 q = fun _ => 0 := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih =>
      show min (minPrice 0 q n) (q n) = 0
      rw [ih]; exact min_eq_left (hq.1 n).1
  have hM : Filter.Tendsto (minPrice 0 q) Filter.atTop (nhds 0) := by
    rw [hmin]; exact tendsto_const_nhds
  obtain ⟨-, hLP, hopt⟩ := limit_steady hst 0 p h0P hp q hq0 0 L hL hM
  exact steady_diag_le_S hst S hS L hLP ((opt_theta0 0 L L _).mp hopt)

lemma aux_antitone {pbar : ℝ} {d0 : ℝ → ℝ} {gam beta : ℝ}
    (hst : Std0 pbar d0 gam gam 0 beta) (S : ℝ)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S) (m p : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (hp : p ∈ Set.Icc (0:ℝ) pbar) (hSp : S ≤ p) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 gam gam 0 beta m p q) : Antitone (price p q) := by
  have h0P : (0:ℝ) ∈ Set.Icc (0:ℝ) pbar := ⟨le_rfl, hm.1.trans hm.2⟩
  have hq0 := (opt_theta0 m 0 p q).mp hq
  rcases monotone_price hst zero_lt_one 0 p h0P hp q hq0 (fun n => (hq.1 n).1) with hmono | hanti
  · have hxP : ∀ n, price p q n ∈ Set.Icc (0:ℝ) pbar := price_mem p q hp hq.1
    have hbdd : BddAbove (Set.range (price p q)) := ⟨pbar, by rintro _ ⟨n, rfl⟩; exact (hxP n).2⟩
    have hT := tendsto_atTop_ciSup hmono hbdd
    have hT1 := hT.comp (Filter.tendsto_add_atTop_nat 1)
    have e : (price p q ∘ fun a => a + 1) = q := funext fun n => rfl
    rw [e] at hT1
    have hLS := aux_limit_le_S hst S hS m p hm hp q hq _ hT1
    have hle : ∀ n, price p q n ≤ ⨆ k, price p q k := fun n => le_ciSup hbdd n
    have hge : ∀ n, p ≤ price p q n := fun n => hmono (Nat.zero_le n)
    intro a b _
    have := hle a; have := hle b; have := hge a; have := hge b
    linarith
  · exact hanti

lemma psi_cmp (lam gam x r r' : ℝ) (hlg : gam ≤ lam) (hrr : r ≤ r') (hx : 0 ≤ x)
    (hg : 0 ≤ gam) :
    x * (-lam * max (x - r) 0 + gam * max (r - x) 0) ≤
      x * (-gam * max (x - r') 0 + gam * max (r' - x) 0) := by
  rw [psi_alt lam gam x r, psi_alt gam gam x r', sub_self, zero_mul, sub_zero]
  apply mul_le_mul_of_nonneg_left _ hx
  have h1 : 0 ≤ (lam - gam) * max (x - r) 0 := mul_nonneg (by linarith) (le_max_right _ _)
  have h2 : gam * (r - x) ≤ gam * (r' - x) := mul_le_mul_of_nonneg_left (by linarith) hg
  linarith

lemma minPrice_le_price (m p : ℝ) (q : ℕ → ℝ) (hmp : m ≤ p) :
    ∀ n, minPrice m q n ≤ price p q n := by
  intro n
  cases n with
  | zero => exact hmp
  | succ n => exact min_le_right _ _

lemma pathValue_le_aux {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m p : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (hp : p ∈ Set.Icc (0:ℝ) pbar) (hmp : m ≤ p)
    (q : ℕ → ℝ) (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) :
    pathValue d0 lam gam theta beta m p q ≤ pathValue d0 gam gam 0 beta m p q := by
  have h1 := term_summable hst m p q hm hp hq
  have h2 := term_summable hst.aux m p q hm hp hq
  have e1 : pathValue d0 lam gam theta beta m p q = ∑' n, term d0 lam gam theta beta m p q n := rfl
  have e2 : pathValue d0 gam gam 0 beta m p q = ∑' n, term d0 gam gam 0 beta m p q n := rfl
  rw [e1, e2]
  refine h1.tsum_le_tsum (fun n => ?_) h2
  unfold term
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hst.beta_pos.le n)
  rw [profit_eq, profit_eq]
  have hr : refPrice theta m p q n ≤ refPrice 0 m p q n := by
    have := minPrice_le_price m p q hmp n
    have ht0 := hst.theta_nonneg
    simp only [refPrice]
    nlinarith
  have := psi_cmp lam gam (q n) _ _ hst.gam_le_lam hr (hq n).1 hst.gam_pos.le
  linarith

lemma minPrice_eq_price_of_anti (m : ℝ) (q : ℕ → ℝ) (h : Antitone (price m q)) :
    ∀ n, minPrice m q n = price m q n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show min (minPrice m q n) (q n) = q n
    rw [ih]
    exact min_eq_right (h (Nat.le_succ n))

lemma pathValue_eq_aux (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (m : ℝ) (q : ℕ → ℝ) (h : Antitone (price m q)) :
    pathValue d0 lam gam theta beta m m q = pathValue d0 gam gam 0 beta m m q := by
  unfold pathValue
  refine tsum_congr (fun n => ?_)
  have hmn := minPrice_eq_price_of_anti m q h n
  have hle : q n ≤ price m q n := h (Nat.le_succ n)
  have r1 : refPrice theta m m q n = price m q n := by simp only [refPrice, hmn]; ring
  have r2 : refPrice 0 m m q n = price m q n := by simp only [refPrice, hmn]; ring
  rw [r1, r2, profit_below _ _ _ _ _ hle, profit_below _ _ _ _ _ hle]

/-- G2: from a diagonal state `(m, m)` with `m ≥ S` the optimal path is nonincreasing to `S`. -/
theorem diag_antitone {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (S : ℝ)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S) (m : ℝ)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (hSm : S ≤ m) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 lam gam theta beta m m q) :
    Antitone (price m q) ∧ Filter.Tendsto q Filter.atTop (nhds S) := by
  have ha := hst.aux
  obtain ⟨qs, hqs⟩ := exists_optimal ha m m hm hm
  have hqsA := aux_antitone ha S hS m m hm hm hSm qs hqs
  have h1 : pathValue d0 gam gam 0 beta m m qs ≤ pathValue d0 lam gam theta beta m m q := by
    rw [← pathValue_eq_aux d0 lam gam theta beta m qs hqsA, hq.2]
    exact pathValue_le_J hst m m hm hm qs hqs.1
  have h2 := pathValue_le_aux hst m m hm hm le_rfl q hq.1
  have h3 := pathValue_le_J ha m m hm hm q hq.1
  have hqA : IsOptimalPath pbar d0 gam gam 0 beta m m q :=
    ⟨hq.1, le_antisymm h3 (by have := hqs.2; linarith)⟩
  have hanti := aux_antitone ha S hS m m hm hm hSm q hqA
  refine ⟨hanti, ?_⟩
  have hqanti : Antitone q := fun a b hab => hanti (Nat.succ_le_succ hab)
  have hT := tendsto_atTop_ciInf hqanti ⟨0, by rintro _ ⟨n, rfl⟩; exact (hq.1 n).1⟩
  have hLS := aux_limit_le_S ha S hS m m hm hm q hqA _ hT
  have hSL : S ≤ ⨅ n, q n := by
    apply ge_of_tendsto' hT
    intro n
    have := optimal_ge_minS hst S hS m m hm hm le_rfl q hq n
    rwa [min_eq_right hSm] at this
  have hE : (⨅ n, q n) = S := le_antisymm hLS hSL
  rw [hE] at hT
  exact hT

lemma plateau_fin (x : ℕ → ℝ) (K : ℕ)
    (hP : ∀ t u, t ≤ K → u ≤ K → x t < x u → x (t + 1) ≤ x (u + 1))
    (hend : x (K + 1) < x K) : ∀ t, t ≤ K → x (t + 1) ≤ x t := by
  intro t htK
  by_contra hc
  push_neg at hc
  have inv : ∀ j, t + 1 + j ≤ K →
      ∃ w, w < K ∧ x w < x (t + 1 + j) ∧ x (t + 1 + j) ≤ x (w + 1) := by
    intro j
    induction j with
    | zero => intro h; exact ⟨t, by omega, by simpa using hc, by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨w, hwK, hw1, hw2⟩ := ih (by omega)
      have hstep : x (t + 1 + j) ≤ x (t + 1 + j + 1) :=
        hw2.trans (hP w _ hwK.le (by omega) hw1)
      have e : t + 1 + (j + 1) = t + 1 + j + 1 := by omega
      rcases lt_or_eq_of_le hstep with hlt | heq
      · refine ⟨t + 1 + j, by omega, ?_, ?_⟩
        · rw [e]; exact hlt
        · rw [e]
      · refine ⟨w, hwK, ?_, ?_⟩
        · rw [e, ← heq]; exact hw1
        · rw [e, ← heq]; exact hw2
  rcases Nat.eq_or_lt_of_le htK with rfl | hlt
  · linarith
  · obtain ⟨w, hwK, hw1, hw2⟩ := inv (K - (t + 1)) (by omega)
    have e : t + 1 + (K - (t + 1)) = K := by omega
    rw [e] at hw1 hw2
    have := hP w K hwK.le le_rfl hw1
    linarith

/-- G1: before the first price below `m0`, an optimal path is nonincreasing. -/
lemma head_antitone {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (hmp : m0 ≤ p0) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) (K : ℕ)
    (hge : ∀ n, n < K → m0 ≤ q n) (hK : q K < m0) :
    ∀ n, n < K → q (n + 1) ≤ q n := by
  have hmin := minPrice_frozen m0 q K hge
  rcases lt_or_eq_of_le hst.theta_le_one with htl | hte
  · have hP : ∀ t u, t ≤ K → u ≤ K → price p0 q t < price p0 q u →
        price p0 q (t + 1) ≤ price p0 q (u + 1) := by
      intro t u ht hu htu
      have h1 := step_max hst m0 p0 hm hp q hq t (q u) (hq.1 u)
      have h2 := step_max hst m0 p0 hm hp q hq u (q t) (hq.1 t)
      have e1 : minPrice m0 q (t + 1) = min m0 (q t) := by
        show min (minPrice m0 q t) (q t) = _
        rw [hmin t ht]
      have e2 : minPrice m0 q (u + 1) = min m0 (q u) := by
        show min (minPrice m0 q u) (q u) = _
        rw [hmin u hu]
      rw [hmin t ht, e1] at h1
      rw [hmin u hu, e2] at h2
      exact argmax_mono hst htl m0 _ _ (q t) (q u) htu (hq.1 t) (hq.1 u) _ _ h1 h2
    have hend : price p0 q (K + 1) < price p0 q K := by
      show q K < price p0 q K
      cases K with
      | zero => show q 0 < p0; linarith
      | succ k => show q (k + 1) < q k; linarith [hge k (by omega)]
    intro n hn
    exact plateau_fin _ K hP hend (n + 1) hn
  · subst hte
    have key : ∀ n k, n < K → k < K → q n = q k := by
      intro n k hn hk
      by_contra hne
      have hgn := hge n hn
      have hgk := hge k hk
      have h1 := step_max hst m0 p0 hm hp q hq n (q k) (hq.1 k)
      have h2 := step_max hst m0 p0 hm hp q hq k (q n) (hq.1 n)
      set c := (q n + q k) / 2 with hc
      have hcP : c ∈ Set.Icc (0:ℝ) pbar :=
        ⟨by linarith [(hq.1 n).1, (hq.1 k).1], by linarith [(hq.1 n).2, (hq.1 k).2]⟩
      have hcm : m0 ≤ c := by linarith
      have h3 := step_max hst m0 p0 hm hp q hq n c hcP
      have e1 : minPrice m0 q (n + 1) = m0 := hmin (n + 1) (by omega)
      have e2 : minPrice m0 q (k + 1) = m0 := hmin (k + 1) (by omega)
      simp only [hmin n hn.le, hmin k hk.le, e1, e2, min_eq_left hgk, min_eq_left hgn,
        min_eq_left hcm, one_mul, sub_self, zero_mul, add_zero] at h1 h2 h3
      rw [J_theta_one pbar d0 lam gam beta m0 (q k) (q n)] at h1 h2
      rw [J_theta_one pbar d0 lam gam beta m0 c (q n)] at h3
      rw [profit_above d0 lam gam m0 _ hgn, profit_above d0 lam gam m0 _ hgk] at h1 h2
      rw [profit_above d0 lam gam m0 _ hgn, profit_above d0 lam gam m0 _ hcm] at h3
      have hsc := hst.assumption1.strictConcave.2 (hq.1 n) (hq.1 k) hne
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hsc
      have hce : 1 / 2 * q n + 1 / 2 * q k = c := by rw [hc]; ring
      rw [hce] at hsc
      have hl := hst.gam_pos.trans_le hst.gam_le_lam
      have hq2 : lam * (c - m0) * c ≤ (lam * (q n - m0) * q n + lam * (q k - m0) * q k) / 2 := by
        have e : (lam * (q n - m0) * q n + lam * (q k - m0) * q k) / 2 - lam * (c - m0) * c =
            lam * (q n - q k) ^ 2 / 4 := by rw [hc]; ring
        nlinarith [mul_nonneg hl.le (sq_nonneg (q n - q k))]
      linarith
    intro n hn
    rcases Nat.lt_or_ge (n + 1) K with h | h
    · rw [key (n + 1) n h hn]
    · have e : n + 1 = K := by omega
      rw [e]
      linarith [hge n hn]

lemma eq12_contra {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m L : ℝ) (hm : m ∈ Set.Icc (0:ℝ) pbar)
    (hL : L ∈ Set.Icc (0:ℝ) pbar) (hmL : m < L)
    (hg9 : deriv (baseProfit d0) m ≤ lam * (1 - beta * (1 - theta)) * m)
    (h12 : eq12 d0 lam theta beta m L) : False := by
  unfold eq12 at h12
  have hsa := deriv_strictAnti hst hm hL hmL
  have hlam : 0 < lam := lt_of_lt_of_le hst.gam_pos hst.gam_le_lam
  have ht0 := hst.theta_nonneg; have ht1 := hst.theta_le_one
  have hb0 := hst.beta_pos; have hb1 := hst.beta_lt_one
  have hK : 0 < 2 - (1 - theta) * (1 + beta) := by nlinarith
  have := mul_lt_mul_of_pos_left hmL (mul_pos hlam hK)
  linarith

lemma g9_le_of_ge {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (a m : ℝ) (ha : a ∈ Set.Icc (0:ℝ) pbar)
    (hm : m ∈ Set.Icc (0:ℝ) pbar) (ham : a ≤ m) (k : ℝ) (hk : 0 ≤ k)
    (hk2 : k ≤ lam * (1 - beta * (1 - theta)))
    (hd : deriv (baseProfit d0) a = k * a) :
    deriv (baseProfit d0) m ≤ lam * (1 - beta * (1 - theta)) * m := by
  have h1 := deriv_antitone hst ha hm ham
  have h2 : k * a ≤ k * m := mul_le_mul_of_nonneg_left ham hk
  have h3 : k * m ≤ lam * (1 - beta * (1 - theta)) * m := mul_le_mul_of_nonneg_right hk2 hm.1
  linarith

lemma k10_le_k9 {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) :
    0 ≤ gam * (1 - beta) ∧ gam * (1 - beta) ≤ lam * (1 - beta * (1 - theta)) := by
  have ht0 := hst.theta_nonneg; have ht1 := hst.theta_le_one
  have hb0 := hst.beta_pos; have hb1 := hst.beta_lt_one
  have hg := hst.gam_pos; have hgl := hst.gam_le_lam
  refine ⟨mul_nonneg hg.le (by linarith), ?_⟩
  have h1 : gam * (1 - beta) ≤ lam * (1 - beta) := mul_le_mul_of_nonneg_right hgl (by linarith)
  have h2 : lam * (1 - beta) ≤ lam * (1 - beta * (1 - theta)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  linarith

lemma s_le_S {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s) (S : ℝ)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S) : s ≤ S := by
  by_contra h
  push_neg at h
  have hsa := deriv_strictAnti hst hS.1 hs.1 h
  have h9 := hs.2; have h10 := hS.2
  unfold eq9 at h9; unfold eq10 at h10
  obtain ⟨hk0, hk⟩ := k10_le_k9 hst
  have h1 : gam * (1 - beta) * S ≤ gam * (1 - beta) * s := mul_le_mul_of_nonneg_left h.le hk0
  have h2 : gam * (1 - beta) * s ≤ lam * (1 - beta * (1 - theta)) * s :=
    mul_le_mul_of_nonneg_right hk hs.1.1
  linarith

lemma tendsto_of_mono {pbar : ℝ} (q : ℕ → ℝ) (h : Monotone q ∨ Antitone q)
    (hq : ∀ n, q n ∈ Set.Icc (0:ℝ) pbar) : ∃ L, Filter.Tendsto q Filter.atTop (nhds L) := by
  rcases h with h | h
  · exact ⟨_, tendsto_atTop_ciSup h ⟨pbar, by rintro _ ⟨n, rfl⟩; exact (hq n).2⟩⟩
  · exact ⟨_, tendsto_atTop_ciInf h ⟨0, by rintro _ ⟨n, rfl⟩; exact (hq n).1⟩⟩

lemma frozen_limit {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (m0 p0 : ℝ)
    (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (q : ℕ → ℝ)
    (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) (hge : ∀ n, m0 ≤ q n) :
    ∃ L, L ∈ Set.Icc (0:ℝ) pbar ∧ m0 ≤ L ∧ Filter.Tendsto q Filter.atTop (nhds L) ∧
      IsOptimalPath pbar d0 lam gam theta beta m0 L (fun _ => L) := by
  obtain ⟨L, hL⟩ := tendsto_of_mono q (monotone_frozen hst m0 p0 hm hp q hq hge) hq.1
  have hmin : minPrice m0 q = fun _ => m0 :=
    funext fun n => minPrice_frozen m0 q n (fun k _ => hge k) n le_rfl
  have hM : Filter.Tendsto (minPrice m0 q) Filter.atTop (nhds m0) := by
    rw [hmin]; exact tendsto_const_nhds
  obtain ⟨-, hLP, hopt⟩ := limit_steady hst m0 p0 hm hp q hq m0 L hL hM
  exact ⟨L, hLP, ge_of_tendsto' hL hge, hL, hopt⟩

/-- Case (c): `m0 ≥ S` gives a nonincreasing optimal path converging to `S`. -/
theorem case_c {pbar : ℝ} {d0 : ℝ → ℝ} {lam gam theta beta : ℝ}
    (hst : Std0 pbar d0 lam gam theta beta) (htp : 0 < theta) (S : ℝ)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 : ℝ) (hm : m0 ∈ Set.Icc (0:ℝ) pbar) (hp : p0 ∈ Set.Icc (0:ℝ) pbar) (hmp : m0 ≤ p0)
    (hSm : S ≤ m0) (q : ℕ → ℝ) (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) :
    Antitone q ∧ Filter.Tendsto q Filter.atTop (nhds S) := by
  by_cases hex : ∃ k, q k < m0
  · classical
    have hK : q (Nat.find hex) < m0 := Nat.find_spec hex
    have hge : ∀ n, n < Nat.find hex → m0 ≤ q n := fun n hn => not_lt.mp (Nat.find_min hex hn)
    set K := Nat.find hex with hKdef
    have hhead := head_antitone hst m0 p0 hm hp hmp q hq K hge hK
    have hmK : minPrice m0 q (K + 1) = q K := by
      show min (minPrice m0 q K) (q K) = q K
      rw [minPrice_frozen m0 q K hge K le_rfl]
      exact min_eq_right hK.le
    have htail := tail_optimal hst m0 p0 hm hp q hq (K + 1)
    rw [hmK] at htail
    have hSK : S ≤ q K := by
      have := optimal_ge_minS hst S hS m0 p0 hm hp hmp q hq K
      rwa [min_eq_right hSm] at this
    obtain ⟨hA, hT⟩ := diag_antitone hst S hS (q K) (hq.1 K) hSK _ htail
    refine ⟨antitone_nat_of_succ_le (fun n => ?_), ?_⟩
    · rcases Nat.lt_or_ge n K with h | h
      · exact hhead n h
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
        have := hA (Nat.le_succ j)
        cases j with
        | zero =>
          change q (K + 1 + 0) ≤ q K at this
          simpa using this
        | succ i =>
          change q (K + 1 + (i + 1)) ≤ q (K + 1 + i) at this
          have e1 : K + (i + 1) + 1 = K + 1 + (i + 1) := by omega
          have e2 : K + (i + 1) = K + 1 + i := by omega
          rw [e1, e2]
          exact this
    · have e : (fun n => q (n + (K + 1))) = fun k => q (K + 1 + k) :=
        funext fun n => by rw [add_comm]
      rw [← Filter.tendsto_add_atTop_iff_nat (K + 1), e]
      exact hT
  · push_neg at hex
    obtain ⟨L, hLP, hmL, hL, hopt⟩ := frozen_limit hst m0 p0 hm hp q hq hex
    obtain ⟨hk0, hk⟩ := k10_le_k9 hst
    have hg9 := g9_le_of_ge hst S m0 hS.1 hm hSm _ hk0 hk (by have := hS.2; unfold eq10 at this; linarith)
    have hLeq : L = m0 := by
      rcases lt_or_eq_of_le hmL with hlt | heq
      · exact (eq12_contra hst m0 L hm hLP hlt hg9 (steady_eq12 hst htp m0 L hm hLP hlt hopt)).elim
      · exact heq.symm
    rw [hLeq] at hopt hL
    have hm0S : m0 = S := le_antisymm (steady_diag_le_S hst S hS m0 hm hopt) hSm
    refine ⟨?_, by rw [← hm0S]; exact hL⟩
    rcases monotone_frozen hst m0 p0 hm hp q hq hex with hmono | hanti
    · intro a b _
      have h1 := hmono.ge_of_tendsto hL a
      have h2 := hmono.ge_of_tendsto hL b
      linarith [hex a, hex b]
    · exact hanti

end PEP3

/-! ## The target -/

open PeakEndPricing.Convergence in
theorem solution (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 : ℝ) (hm0 : m0 ∈ Set.Icc (0 : ℝ) pbar) (hp0 : p0 ∈ Set.Icc (0 : ℝ) pbar) (hmp : m0 ≤ p0) :
    (∃ q : ℕ → ℝ, IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) ∧
    ∀ q : ℕ → ℝ, IsOptimalPath pbar d0 lam gam theta beta m0 p0 q →
      (Monotone q ∨ Antitone q) ∧
      (m0 ∈ Set.Icc (0 : ℝ) s → ∃ x ∈ Set.Icc (0 : ℝ) pbar,
        eq12 d0 lam theta beta m0 x ∧ Filter.Tendsto q Filter.atTop (nhds x)) ∧
      (m0 ∈ Set.Icc s S → Filter.Tendsto q Filter.atTop (nhds m0)) ∧
      (m0 ∈ Set.Icc S pbar → Filter.Tendsto q Filter.atTop (nhds S)) := by
  have h0 := PEP3.Std0.of hst
  have htp := hst.theta_pos
  refine ⟨PEP3.exists_optimal h0 m0 p0 hm0 hp0, fun q hq => ?_⟩
  have hsS := PEP3.s_le_S h0 s hs S hS
  by_cases hmS : m0 ≤ S
  · have hge : ∀ n, m0 ≤ q n := fun n => by
      have := PEP3.optimal_ge_minS h0 S hS m0 p0 hm0 hp0 hmp q hq n
      rwa [min_eq_left hmS] at this
    obtain ⟨L, hLP, hmL, hT, hopt⟩ := PEP3.frozen_limit h0 m0 p0 hm0 hp0 q hq hge
    have hLm : s ≤ m0 → L = m0 := by
      intro hsm
      rcases lt_or_eq_of_le hmL with hlt | heq
      · exfalso
        have hk : 0 ≤ lam * (1 - beta * (1 - theta)) := (PEP3.k10_le_k9 h0).1.trans (PEP3.k10_le_k9 h0).2
        have hg9 := PEP3.g9_le_of_ge h0 s m0 hs.1 hm0 hsm _ hk le_rfl
          (by have := hs.2; unfold eq9 at this; linarith)
        exact PEP3.eq12_contra h0 m0 L hm0 hLP hlt hg9 (PEP3.steady_eq12 h0 htp m0 L hm0 hLP hlt hopt)
      · exact heq.symm
    refine ⟨PEP3.monotone_frozen h0 m0 p0 hm0 hp0 q hq hge, ?_, ?_, ?_⟩
    · intro hma
      rcases lt_or_eq_of_le hmL with hlt | heq
      · exact ⟨L, hLP, PEP3.steady_eq12 h0 htp m0 L hm0 hLP hlt hopt, hT⟩
      · rw [← heq] at hopt hT
        have hsm := PEP3.steady_diag_ge_s h0 s hs m0 hm0 hopt
        have hms : m0 = s := le_antisymm hma.2 hsm
        refine ⟨m0, hm0, ?_, hT⟩
        have h9 := hs.2
        unfold eq9 at h9
        rw [← hms] at h9
        unfold eq12
        linear_combination h9
    · intro hmb
      rw [← hLm hmb.1]; exact hT
    · intro hmc
      have hmS' : m0 = S := le_antisymm hmS hmc.1
      rw [← hmS', ← hLm (hsS.trans hmc.1)]; exact hT
  · push_neg at hmS
    obtain ⟨hA, hT⟩ := PEP3.case_c h0 htp S hS m0 p0 hm0 hp0 hmp hmS.le q hq
    refine ⟨Or.inr hA, ?_, ?_, fun _ => hT⟩
    · intro hma; exfalso; linarith [hma.2]
    · intro hmb; exfalso; linarith [hmb.2]
