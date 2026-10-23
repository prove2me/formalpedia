-- Prove2me | solution 1 for RefMNLPricing.Gap.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T09:55:25.871129+00:00
-- url     : https://prove2.me/submissions/72f73a1b-9a6f-422b-9558-d28e1ad3b3b3

import Mathlib
import Definitions.Def_RefMNLPricing_Gap_Model

set_option autoImplicit false

namespace P062929a0

open RefMNLPricing.Myopic

lemma rev_eq {n : ℕ} (a b cp cm p r : Fin n → ℝ) :
    revenue a b cp cm p r =
      (∑ i, p i * Real.exp (util a b cp cm p r i)) /
        (1 + ∑ k, Real.exp (util a b cp cm p r k)) := by
  unfold revenue share
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_div_assoc]

lemma denom_pos {n : ℕ} (a b cp cm p r : Fin n → ℝ) :
    0 < 1 + ∑ k, Real.exp (util a b cp cm p r k) := by
  have : 0 ≤ ∑ k, Real.exp (util a b cp cm p r k) :=
    Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
  linarith

lemma rev_nonneg {n : ℕ} (a b cp cm p r : Fin n → ℝ) (pH : ℝ) (hp : InBox pH p) :
    0 ≤ revenue a b cp cm p r := by
  rw [rev_eq]
  apply div_nonneg _ (denom_pos a b cp cm p r).le
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i).1 (Real.exp_pos _).le

lemma rev_le {n : ℕ} (a b cp cm p r : Fin n → ℝ) (pH : ℝ) (hpH : 0 ≤ pH) (hp : InBox pH p) :
    revenue a b cp cm p r ≤ pH := by
  rw [rev_eq, div_le_iff₀ (denom_pos a b cp cm p r)]
  have h1 : ∑ i, p i * Real.exp (util a b cp cm p r i) ≤
      ∑ i, pH * Real.exp (util a b cp cm p r i) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hp i).2 (Real.exp_pos _).le
  rw [← Finset.mul_sum] at h1
  nlinarith

/-- At a box maximiser every price is at least the optimal revenue. -/
lemma price_ge_rev {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ) (r p : Fin n → ℝ)
    (hp : InBox pH p)
    (hmax : ∀ q, InBox pH q → revenue a b cp cm q r ≤ revenue a b cp cm p r)
    (j : Fin n) : revenue a b cp cm p r ≤ p j := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ∑ k ∈ Finset.univ.erase j,
      p k * Real.exp (util a b cp cm p r k) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 + ∑ k ∈ Finset.univ.erase j,
      Real.exp (util a b cp cm p r k) := ⟨_, rfl⟩
  have hMpos : 0 < M := by
    have : 0 ≤ ∑ k ∈ Finset.univ.erase j, Real.exp (util a b cp cm p r k) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    linarith
  have hN0 : 0 ≤ N := by
    rw [hN]; exact Finset.sum_nonneg fun k _ => mul_nonneg (hp k).1 (Real.exp_pos _).le
  have hNM : N ≤ pH * M := by
    have h1 : N ≤ ∑ k ∈ Finset.univ.erase j, pH * Real.exp (util a b cp cm p r k) := by
      rw [hN]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hp k).2 (Real.exp_pos _).le
    rw [← Finset.mul_sum] at h1
    have hpH : 0 ≤ pH := le_trans (hp j).1 (hp j).2
    rw [hM]; nlinarith
  have key : ∀ q : Fin n → ℝ, (∀ k, k ≠ j → q k = p k) →
      revenue a b cp cm q r = (q j * Real.exp (util a b cp cm q r j) + N) /
        (Real.exp (util a b cp cm q r j) + M) := by
    intro q hq
    have hu : ∀ k, k ≠ j → util a b cp cm q r k = util a b cp cm p r k := by
      intro k hk; simp only [util, hq k hk]
    rw [rev_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have h1 : ∑ k ∈ Finset.univ.erase j, q k * Real.exp (util a b cp cm q r k) = N := by
      rw [hN]
      apply Finset.sum_congr rfl; intro k hk
      rw [hq k (Finset.ne_of_mem_erase hk), hu k (Finset.ne_of_mem_erase hk)]
    have h2 : ∑ k ∈ Finset.univ.erase j, Real.exp (util a b cp cm q r k) =
        ∑ k ∈ Finset.univ.erase j, Real.exp (util a b cp cm p r k) := by
      apply Finset.sum_congr rfl; intro k hk
      rw [hu k (Finset.ne_of_mem_erase hk)]
    rw [h1, h2, hM]; ring_nf
  have hRp := key p (fun _ _ => rfl)
  have hE := Real.exp_pos (util a b cp cm p r j)
  have hRlt : revenue a b cp cm p r * M < N := by
    have hd : 0 < Real.exp (util a b cp cm p r j) + M := by linarith
    have h3 : revenue a b cp cm p r * (Real.exp (util a b cp cm p r j) + M) =
        p j * Real.exp (util a b cp cm p r j) + N := by
      rw [hRp, div_mul_cancel₀ _ hd.ne']
    nlinarith
  set x := N / M with hx
  have hx0 : 0 ≤ x := div_nonneg hN0 hMpos.le
  have hxH : x ≤ pH := by rw [hx, div_le_iff₀ hMpos]; linarith
  let q : Fin n → ℝ := Function.update p j x
  have hqbox : InBox pH q := by
    intro k
    simp only [q, Function.update_apply]
    split_ifs
    · exact ⟨hx0, hxH⟩
    · exact hp k
  have hqk : ∀ k, k ≠ j → q k = p k := by
    intro k hk; simp [q, Function.update_apply, hk]
  have hqj : q j = x := by simp [q]
  have hrq := key q hqk
  rw [hqj] at hrq
  have hE' := Real.exp_pos (util a b cp cm q r j)
  have hrq' : revenue a b cp cm q r = x := by
    rw [hrq, div_eq_iff (by linarith)]
    rw [hx]; field_simp
  have hlt2 : revenue a b cp cm p r < x := by
    rw [hx, lt_div_iff₀ hMpos]; exact hRlt
  have := hmax q hqbox
  linarith

/-- Utility comparison after lowering the price by `δ` and moving the reference. -/
lemma util_shift (a0 b0 cp0 cm0 p0 r r' δ : ℝ) (hb : 0 < b0) (hcp : 0 ≤ cp0) (hcm : 0 ≤ cm0)
    (hδ : 0 ≤ δ) (h1 : cp0 * (r - r') ≤ δ * (b0 + cp0)) (h2 : cm0 * (r - r') ≤ δ * (b0 + cm0)) :
    a0 - b0 * p0 + cp0 * max (r - p0) 0 - cm0 * max (p0 - r) 0 ≤
      a0 - b0 * (p0 - δ) + cp0 * max (r' - (p0 - δ)) 0 - cm0 * max ((p0 - δ) - r') 0 := by
  rcases le_total (r' - (p0 - δ)) 0 with h3 | h3 <;>
    rcases le_total (r - p0) 0 with h4 | h4
  · rw [max_eq_right h3, max_eq_left (by linarith : (0:ℝ) ≤ p0 - δ - r'), max_eq_right h4,
      max_eq_left (by linarith : (0:ℝ) ≤ p0 - r)]
    nlinarith
  · rw [max_eq_right h3, max_eq_left (by linarith : (0:ℝ) ≤ p0 - δ - r'), max_eq_left h4,
      max_eq_right (by linarith : p0 - r ≤ 0)]
    -- s = r - p0 ≥ 0, u = p0 - δ - r' ≥ 0
    have k1 : cp0 * ((r - p0) + (p0 - δ - r')) ≤ b0 * δ := by nlinarith
    have k2 : cm0 * ((r - p0) + (p0 - δ - r')) ≤ b0 * δ := by nlinarith
    have hs : 0 ≤ r - p0 := h4
    have hu : 0 ≤ p0 - δ - r' := by linarith
    have hbd : 0 ≤ b0 * δ := mul_nonneg hb.le hδ
    rcases eq_or_lt_of_le (add_nonneg hs hu) with h5 | h5
    · have e1 : r - p0 = 0 := by linarith
      have e2 : p0 - δ - r' = 0 := by linarith
      rw [e1, e2] at *; nlinarith
    · have : ((r - p0) + (p0 - δ - r')) * (cp0 * (r - p0) - cm0 * 0 + cm0 * (p0 - δ - r')) ≤
          ((r - p0) + (p0 - δ - r')) * (b0 * δ) := by
        nlinarith [mul_le_mul_of_nonneg_left k1 hs, mul_le_mul_of_nonneg_left k2 hu]
      have := le_of_mul_le_mul_left this h5
      nlinarith
  · rw [max_eq_left h3, max_eq_right (by linarith : p0 - δ - r' ≤ 0), max_eq_right h4,
      max_eq_left (by linarith : (0:ℝ) ≤ p0 - r)]
    nlinarith [mul_nonneg hcp h3, mul_nonneg hcm (by linarith : (0:ℝ) ≤ p0 - r),
      mul_nonneg hb.le hδ]
  · rw [max_eq_left h3, max_eq_right (by linarith : p0 - δ - r' ≤ 0), max_eq_left h4,
      max_eq_right (by linarith : p0 - r ≤ 0)]
    nlinarith

lemma omega_nonneg {n : ℕ} (b cp cm : Fin n → ℝ) (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) :
    0 ≤ RefMNLPricing.Gap.omega b cp cm := by
  unfold RefMNLPricing.Gap.omega
  exact Real.iSup_nonneg fun i =>
    le_max_of_le_left (div_nonneg (hcp i) (by linarith [hb i, hcp i]))

lemma omega_ge {n : ℕ} (b cp cm : Fin n → ℝ) (i : Fin n) :
    max (cp i / (b i + cp i)) (cm i / (b i + cm i)) ≤ RefMNLPricing.Gap.omega b cp cm := by
  unfold RefMNLPricing.Gap.omega
  exact le_ciSup (f := fun i => max (cp i / (b i + cp i)) (cm i / (b i + cm i)))
    (Set.finite_range _).bddAbove i

/-- One-period comparison. -/
lemma key {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (r r' p0 q : Fin n → ℝ) (K : ℝ) (hK : 0 ≤ K) (hrr : ∀ i, r i - r' i ≤ K)
    (hp0 : InBox pH p0)
    (hmax0 : ∀ p, InBox pH p → revenue a b cp cm p r ≤ revenue a b cp cm p0 r)
    (hmaxq : ∀ p, InBox pH p → revenue a b cp cm p r' ≤ revenue a b cp cm q r')
    (hq : InBox pH q) :
    revenue a b cp cm p0 r ≤
      revenue a b cp cm q r' + RefMNLPricing.Gap.omega b cp cm * K := by
  set ω := RefMNLPricing.Gap.omega b cp cm with hωdef
  have hω0 : 0 ≤ ω := omega_nonneg b cp cm hb hcp
  have hωK : 0 ≤ ω * K := mul_nonneg hω0 hK
  set R := revenue a b cp cm p0 r with hRdef
  by_cases hc : R - ω * K ≤ 0
  · have := rev_nonneg a b cp cm q r' pH hq
    linarith
  push_neg at hc
  have hA : ∀ j, R ≤ p0 j := price_ge_rev a b cp cm pH r p0 hp0 hmax0
  let p' : Fin n → ℝ := fun i => p0 i - ω * K
  have hp'box : InBox pH p' := by
    intro i
    constructor
    · show 0 ≤ p0 i - ω * K
      linarith [hA i]
    · show p0 i - ω * K ≤ pH
      linarith [(hp0 i).2]
  have hEle : ∀ i, Real.exp (util a b cp cm p0 r i) ≤ Real.exp (util a b cp cm p' r' i) := by
    intro i
    apply Real.exp_le_exp.mpr
    have hbc1 : 0 < b i + cp i := by linarith [hb i, hcp i]
    have hbc2 : 0 < b i + cm i := by linarith [hb i, hcm i]
    have hw := omega_ge b cp cm i
    have w1 : cp i ≤ ω * (b i + cp i) := by
      have := le_trans (le_max_left _ _) hw
      rwa [div_le_iff₀ hbc1] at this
    have w2 : cm i ≤ ω * (b i + cm i) := by
      have := le_trans (le_max_right _ _) hw
      rwa [div_le_iff₀ hbc2] at this
    have e1 : cp i * (r i - r' i) ≤ ω * K * (b i + cp i) := by
      have := mul_le_mul_of_nonneg_left (hrr i) (hcp i)
      have := mul_le_mul_of_nonneg_right w1 hK
      nlinarith
    have e2 : cm i * (r i - r' i) ≤ ω * K * (b i + cm i) := by
      have := mul_le_mul_of_nonneg_left (hrr i) (hcm i)
      have := mul_le_mul_of_nonneg_right w2 hK
      nlinarith
    exact util_shift (a i) (b i) (cp i) (cm i) (p0 i) (r i) (r' i) (ω * K) (hb i) (hcp i) (hcm i)
      hωK e1 e2
  have hge : R - ω * K ≤ revenue a b cp cm p' r' := by
    rw [rev_eq a b cp cm p' r', le_div_iff₀ (denom_pos a b cp cm p' r')]
    have s4 : R * (1 + ∑ k, Real.exp (util a b cp cm p0 r k)) =
        ∑ i, p0 i * Real.exp (util a b cp cm p0 r i) := by
      rw [hRdef, rev_eq, div_mul_cancel₀ _ (denom_pos a b cp cm p0 r).ne']
    have s1 : ∑ i, (p0 i - R) * Real.exp (util a b cp cm p0 r i) ≤
        ∑ i, (p0 i - R) * Real.exp (util a b cp cm p' r' i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hEle i) (sub_nonneg.mpr (hA i))
    have s2 : ∑ i, (p0 i - R) * Real.exp (util a b cp cm p' r' i) =
        ∑ i, p' i * Real.exp (util a b cp cm p' r' i) -
          (R - ω * K) * ∑ i, Real.exp (util a b cp cm p' r' i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [p']; ring
    have s3 : ∑ i, (p0 i - R) * Real.exp (util a b cp cm p0 r i) =
        ∑ i, p0 i * Real.exp (util a b cp cm p0 r i) -
          R * ∑ i, Real.exp (util a b cp cm p0 r i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    nlinarith
  have := hmaxq p' hp'box
  linarith

lemma conv_mem (α pH x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) pH)
    (hy : y ∈ Set.Icc (0 : ℝ) pH) : α * x + (1 - α) * y ∈ Set.Icc (0 : ℝ) pH := by
  have h1 : 0 ≤ 1 - α := by linarith [hα.2]
  constructor
  · have := mul_nonneg hα.1 hx.1
    have := mul_nonneg h1 hy.1
    linarith
  · have := mul_le_mul_of_nonneg_left hx.2 hα.1
    have := mul_le_mul_of_nonneg_left hy.2 h1
    nlinarith

end P062929a0

set_option maxHeartbeats 1000000 in
open RefMNLPricing.Gap in
theorem solution {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : IsMyopicSel a b cp cm pH pm)
    (r₀ : Fin n → ℝ) (hr₀ : RefMNLPricing.Myopic.InBox pH r₀) :
    0 ≤ optValue a b cp cm α β pH r₀ - myopicValue a b cp cm α β pm r₀ ∧
      optValue a b cp cm α β pH r₀ - myopicValue a b cp cm α β pm r₀ ≤
        β * (1 - α) / ((1 - α * β) * (1 - β)) * omega b cp cm * pH := by
  classical
  obtain ⟨hα0, hα1⟩ := hα
  obtain ⟨hβ0, hβ1⟩ := hβ
  have h1α : 0 ≤ 1 - α := by linarith
  set ω := omega b cp cm with hωdef
  have hω0 : 0 ≤ ω := P062929a0.omega_nonneg b cp cm hb hcp
  set m := RefMNLPricing.Myopic.myopicRef pm α r₀ with hmdef
  have hm_box : ∀ t, RefMNLPricing.Myopic.InBox pH (m t) := by
    intro t
    induction t with
    | zero => exact hr₀
    | succ t ih =>
      intro i
      show α * m t i + (1 - α) * pm (m t) i ∈ Set.Icc (0 : ℝ) pH
      exact P062929a0.conv_mem α pH _ _ ⟨hα0, hα1⟩ (ih i) ((hpm (m t) ih).1 i)
  have hrefPath : ∀ t, refPath α r₀ (fun t => pm (m t)) t = m t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext i
      show α * refPath α r₀ (fun t => pm (m t)) t i + (1 - α) * pm (m t) i =
        α * m t i + (1 - α) * pm (m t) i
      rw [ih]
  have hVm : myopicValue a b cp cm α β pm r₀ =
      ∑' t, β ^ t * RefMNLPricing.Myopic.revenue a b cp cm (pm (m t)) (m t) := by
    unfold myopicValue disc
    refine tsum_congr fun t => ?_
    rw [hrefPath t]
  -- the Karlin objects
  let L : (Fin n → ℝ) → (Fin n → Set.Icc (0 : ℝ) pH) → ℝ := fun r p =>
    RefMNLPricing.Myopic.revenue a b cp cm (fun i => (p i : ℝ)) r
  let T : (Fin n → Set.Icc (0 : ℝ) pH) → (Fin n → ℝ) → (Fin n → ℝ) := fun p r =>
    fun i => α * r i + (1 - α) * (p i : ℝ)
  have hopt : optValue a b cp cm α β pH r₀ =
      ⨆ s : ℕ → Fin n → Set.Icc (0 : ℝ) pH,
        KarlinDP.Deterministic.totalYield L T (fun _ => β) r₀ s := rfl
  have hweight : ∀ (s : ℕ → Fin n → Set.Icc (0 : ℝ) pH) (t : ℕ),
      KarlinDP.Deterministic.weight (fun _ => β) s t = β ^ t := by
    intro s t
    unfold KarlinDP.Deterministic.weight
    simp [Finset.prod_const, Finset.card_range]
  have hgeom : Summable (fun t : ℕ => β ^ t) := summable_geometric_of_lt_one hβ0 hβ1
  have hαβ0 : 0 ≤ α * β := mul_nonneg hα0 hβ0
  have hαβ1 : α * β < 1 := by nlinarith
  have hgeom2 : Summable (fun t : ℕ => (α * β) ^ t) := summable_geometric_of_lt_one hαβ0 hαβ1
  have hg : Summable (fun t => β ^ t * RefMNLPricing.Myopic.revenue a b cp cm (pm (m t)) (m t)) := by
    refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_) (hgeom.mul_left pH)
    · exact mul_nonneg (pow_nonneg hβ0 t)
        (P062929a0.rev_nonneg a b cp cm _ _ pH (hpm (m t) (hm_box t)).1)
    · have := P062929a0.rev_le a b cp cm (pm (m t)) (m t) pH hpH.le (hpm (m t) (hm_box t)).1
      have hb0 := pow_nonneg hβ0 t
      nlinarith
  -- the bound for every strategy
  have hbound : ∀ s : ℕ → Fin n → Set.Icc (0 : ℝ) pH,
      KarlinDP.Deterministic.totalYield L T (fun _ => β) r₀ s ≤
        myopicValue a b cp cm α β pm r₀ + ω * pH * ((1 - β)⁻¹ - (1 - α * β)⁻¹) := by
    intro s
    set tr := KarlinDP.Deterministic.trajectory T r₀ s with htr
    have htr_box : ∀ t, RefMNLPricing.Myopic.InBox pH (tr t) := by
      intro t
      induction t with
      | zero => exact hr₀
      | succ t ih =>
        intro i
        show α * tr t i + (1 - α) * (s t i : ℝ) ∈ Set.Icc (0 : ℝ) pH
        exact P062929a0.conv_mem α pH _ _ ⟨hα0, hα1⟩ (ih i) (s t i).2
    have hgap : ∀ t i, tr t i - m t i ≤ (1 - α ^ t) * pH := by
      intro t
      induction t with
      | zero => intro i; simp [htr, hmdef, KarlinDP.Deterministic.trajectory,
          RefMNLPricing.Myopic.myopicRef]
      | succ t ih =>
        intro i
        show α * tr t i + (1 - α) * (s t i : ℝ) - (α * m t i + (1 - α) * pm (m t) i) ≤
          (1 - α ^ (t + 1)) * pH
        have e1 := mul_le_mul_of_nonneg_left (ih i) hα0
        have hs := (s t i).2.2
        have hp0 := ((hpm (m t) (hm_box t)).1 i).1
        have e2 : (1 - α) * ((s t i : ℝ) - pm (m t) i) ≤ (1 - α) * pH :=
          mul_le_mul_of_nonneg_left (by linarith) h1α
        rw [pow_succ]
        nlinarith
    have hstep : ∀ t, L (tr t) (s t) * KarlinDP.Deterministic.weight (fun _ => β) s t ≤
        β ^ t * RefMNLPricing.Myopic.revenue a b cp cm (pm (m t)) (m t) +
          ω * pH * (β ^ t - (α * β) ^ t) := by
      intro t
      rw [hweight]
      have hK : 0 ≤ (1 - α ^ t) * pH := mul_nonneg (by linarith [pow_le_one₀ hα0 hα1 (n := t)]) hpH.le
      have h1 : L (tr t) (s t) ≤ RefMNLPricing.Myopic.revenue a b cp cm (pm (tr t)) (tr t) :=
        (hpm (tr t) (htr_box t)).2 _ (fun i => (s t i).2)
      have h2 := P062929a0.key a b cp cm pH hb hcp hcm (tr t) (m t) (pm (tr t)) (pm (m t))
        ((1 - α ^ t) * pH) hK (hgap t) (hpm (tr t) (htr_box t)).1 (hpm (tr t) (htr_box t)).2
        (hpm (m t) (hm_box t)).2 (hpm (m t) (hm_box t)).1
      have hbt := pow_nonneg hβ0 t
      have e : ω * pH * (β ^ t - (α * β) ^ t) = β ^ t * (ω * ((1 - α ^ t) * pH)) := by
        rw [mul_pow]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hbt
      nlinarith
    have hf : Summable (fun t => L (tr t) (s t) * KarlinDP.Deterministic.weight (fun _ => β) s t) := by
      refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_) (hgeom.mul_left pH)
      · rw [hweight]
        exact mul_nonneg (P062929a0.rev_nonneg a b cp cm _ _ pH (fun i => (s t i).2))
          (pow_nonneg hβ0 t)
      · rw [hweight]
        have := P062929a0.rev_le a b cp cm (fun i => (s t i : ℝ)) (tr t) pH hpH.le
          (fun i => (s t i).2)
        have hb0 := pow_nonneg hβ0 t
        show L (tr t) (s t) * β ^ t ≤ pH * β ^ t
        nlinarith
    have hR : Summable (fun t => β ^ t * RefMNLPricing.Myopic.revenue a b cp cm (pm (m t)) (m t) +
        ω * pH * (β ^ t - (α * β) ^ t)) :=
      hg.add ((hgeom.sub hgeom2).mul_left _)
    have hle := Summable.tsum_le_tsum hstep hf hR
    unfold KarlinDP.Deterministic.totalYield
    rw [hVm]
    refine le_trans hle (le_of_eq ?_)
    rw [Summable.tsum_add hg ((hgeom.sub hgeom2).mul_left _), tsum_mul_left,
      Summable.tsum_sub hgeom hgeom2, tsum_geometric_of_lt_one hβ0 hβ1,
      tsum_geometric_of_lt_one hαβ0 hαβ1]
  have hbdd : BddAbove (Set.range fun s : ℕ → Fin n → Set.Icc (0 : ℝ) pH =>
      KarlinDP.Deterministic.totalYield L T (fun _ => β) r₀ s) := by
    refine ⟨myopicValue a b cp cm α β pm r₀ + ω * pH * ((1 - β)⁻¹ - (1 - α * β)⁻¹), ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hbound s
  have : Nonempty (Set.Icc (0 : ℝ) pH) := ⟨⟨0, le_refl _, hpH.le⟩⟩
  have hup : optValue a b cp cm α β pH r₀ ≤
      myopicValue a b cp cm α β pm r₀ + ω * pH * ((1 - β)⁻¹ - (1 - α * β)⁻¹) := by
    rw [hopt]
    exact ciSup_le hbound
  -- the myopic strategy is admissible
  let sm : ℕ → Fin n → Set.Icc (0 : ℝ) pH := fun t i =>
    ⟨pm (m t) i, (hpm (m t) (hm_box t)).1 i⟩
  have htrm : ∀ t, KarlinDP.Deterministic.trajectory T r₀ sm t = m t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext i
      show α * KarlinDP.Deterministic.trajectory T r₀ sm t i + (1 - α) * pm (m t) i =
        α * m t i + (1 - α) * pm (m t) i
      rw [ih]
  have hlow : myopicValue a b cp cm α β pm r₀ ≤ optValue a b cp cm α β pH r₀ := by
    rw [hopt]
    refine le_trans (le_of_eq ?_) (le_ciSup hbdd sm)
    rw [hVm]
    unfold KarlinDP.Deterministic.totalYield
    refine tsum_congr fun t => ?_
    rw [hweight, htrm t, mul_comm]
  have hconst : ω * pH * ((1 - β)⁻¹ - (1 - α * β)⁻¹) =
      β * (1 - α) / ((1 - α * β) * (1 - β)) * ω * pH := by
    have h1 : (1 - β) ≠ 0 := by linarith
    have h2 : (1 - α * β) ≠ 0 := by linarith
    have h3 : (1 - β * α) ≠ 0 := by linarith
    field_simp
    ring
  constructor
  · linarith
  · rw [← hconst]; linarith
