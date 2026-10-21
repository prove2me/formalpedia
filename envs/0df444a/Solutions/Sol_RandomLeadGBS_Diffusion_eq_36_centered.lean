-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.eq_36_centered
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:55:09.742153+00:00
-- url     : https://prove2.me/submissions/5a75e0e1-b39d-4b35-95f9-26246c58beee

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_4_centered
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_8_centered
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_5_centered

open Filter Topology MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open RandomLeadGBS.Diffusion

namespace GBSEq14

/-- Summing a summable family over one level `{s | s.1 = k}` of `ℤ × ℕ`. -/
lemma level_sum (g : State → ℝ) (hg : Summable g) (k : ℤ) :
    ∑' s : State, (if s.1 = k then g s else 0) = ∑' z : ℕ, g (k, z) := by
  have hs : Summable (fun s : State => if s.1 = k then g s else 0) := by
    refine Summable.of_norm_bounded hg.abs (fun s => ?_)
    split_ifs <;> simp
  rw [Summable.tsum_prod hs]
  have : (fun y : ℤ => ∑' z : ℕ, (if (y, z).1 = k then g (y, z) else 0)) =
      fun y => if y = k then ∑' z : ℕ, g (k, z) else 0 := by
    funext y
    by_cases hy : y = k
    · subst hy; simp
    · simp [hy]
  rw [this, tsum_ite_eq]

/-- Row sums of the rate matrix against a test function. -/
lemma row (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    (fun s' => rate P r s s' * h s') =
      fun s' => (if s' = afterCustomer P r s then r * h (afterCustomer P r s) else 0) +
        (if s' = afterItem P r s then P.β * (s.2 : ℝ) * h (afterItem P r s) else 0) := by
  funext s'
  simp only [rate, add_mul]
  congr 1
  · split_ifs with h1
    · subst h1; rfl
    · simp
  · by_cases h1 : s' = afterItem P r s
    · subst h1
      by_cases hz : 1 ≤ s.2
      · simp [hz]
      · have : s.2 = 0 := by omega
        simp [this]
    · simp [h1]

lemma row_summable (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    Summable (fun s' => rate P r s s' * h s') := by
  rw [row]
  exact (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all)).add
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all))

lemma row_tsum (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    ∑' s', rate P r s s' * h s' =
      r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s) := by
  rw [row, Summable.tsum_add
    (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all))
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all)),
    tsum_ite_eq, tsum_ite_eq]

lemma rate_nonneg (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (s s' : State) :
    0 ≤ rate P r s s' := by
  unfold rate
  apply add_nonneg
  · split_ifs <;> linarith
  · split_ifs
    · positivity
    · rfl

/-- The flux identity: for a bounded test function `h`, stationarity gives
`E[ r h(after customer) + β Z h(after item) ] = E[(r + β Z) h]`. -/
lemma flux (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (p : State → ℝ)
    (hp : IsStationary P r p) (h : State → ℝ) (hh : ∀ s, |h s| ≤ 1) :
    ∑' s, p s * (r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s)) =
      ∑' s, p s * exitRate P r s * h s := by
  obtain ⟨hnn, _hsum, _hone, hsumx, hbal⟩ := hp
  -- summability of the double family
  have hG : Summable (fun x : State × State => p x.1 * rate P r x.1 x.2) := by
    refine (summable_prod_of_nonneg (fun x => mul_nonneg (hnn _) (rate_nonneg P r hr hβ _ _))).mpr
      ⟨fun s => ?_, ?_⟩
    · simpa using (row_summable P r s (fun _ => 1)).mul_left (p s)
    · have : (fun s : State => ∑' s' : State, p (s, s').1 * rate P r (s, s').1 (s, s').2) =
          fun s => p s * exitRate P r s := by
        funext s
        simp only
        rw [tsum_mul_left]
        have := row_tsum P r s (fun _ => 1)
        simp only [mul_one] at this
        rw [this, exitRate]
      rw [this]; exact hsumx
  have hF : Summable (Function.uncurry (fun s s' : State => p s * rate P r s s' * h s')) := by
    refine Summable.of_norm_bounded hG (fun x => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hnn _), abs_of_nonneg (rate_nonneg P r hr hβ _ _)]
    have := hh x.2
    have h0 : 0 ≤ p x.1 * rate P r x.1 x.2 := mul_nonneg (hnn _) (rate_nonneg P r hr hβ _ _)
    nlinarith
  symm
  calc ∑' s, p s * exitRate P r s * h s
      = ∑' s', (∑' s, p s * rate P r s s') * h s' := by
        congr 1; funext s'; rw [hbal s']
    _ = ∑' s', ∑' s, p s * rate P r s s' * h s' := by
        congr 1; funext s'; rw [tsum_mul_right]
    _ = ∑' s, ∑' s', p s * rate P r s s' * h s' := hF.tsum_comm
    _ = ∑' s, p s * (r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s)) := by
        congr 1; funext s
        rw [← row_tsum, ← tsum_mul_left]
        congr 1; funext s'; ring

end GBSEq14

open GBSEq14

theorem eq14g (P : Params) (hP : P.Standing) (r : ℝ) (hr : 0 < r)
    (p : State → ℝ) (hp : IsStationary P r p) :
    Summable (fun s : State => p s * (s.2 : ℝ)) ∧
    P.β * ∑' s : State, p s * (s.2 : ℝ) = r := by
  obtain ⟨hβ, -, -, -, -⟩ := hP
  have hp' := hp
  obtain ⟨hnn, hsum, hone, hsumx, _hbal⟩ := hp'
  have hsZ : Summable (fun s : State => p s * (s.2 : ℝ)) := by
    have : (fun s : State => p s * (s.2 : ℝ)) =
        fun s => (p s * exitRate P r s - r * p s) / P.β := by
      funext s; simp only [exitRate]; field_simp; ring
    rw [this]; exact (hsumx.sub (hsum.mul_left r)).div_const _
  -- level quantities
  set m : ℤ → ℝ := fun k => ∑' z : ℕ, p (k, z) with hm
  set w : ℤ → ℝ := fun k => ∑' z : ℕ, p (k, z) * (z : ℝ) with hw
  have hlev : ∀ k : ℤ, r * m (k + 1) + P.β * w (k - 1) = r * m k + P.β * w k := by
    intro k
    have hfl := flux P r hr hβ p hp (fun s => if s.1 = k then 1 else 0)
      (fun s => by split_ifs <;> simp)
    have hL : (fun s : State => p s * (r * (if (afterCustomer P r s).1 = k then (1:ℝ) else 0) +
        P.β * (s.2 : ℝ) * (if (afterItem P r s).1 = k then (1:ℝ) else 0))) =
        fun s => (if s.1 = k + 1 then r * p s else 0) +
          (if s.1 = k - 1 then P.β * (p s * (s.2 : ℝ)) else 0) := by
      funext s
      have e1 : (afterCustomer P r s).1 = s.1 - 1 := rfl
      have e2 : (afterItem P r s).1 = s.1 + 1 := rfl
      simp only [e1, e2]
      split_ifs <;> first | (exfalso; omega) | ring
    have hR : (fun s : State => p s * exitRate P r s * (if s.1 = k then (1:ℝ) else 0)) =
        fun s => (if s.1 = k then r * p s else 0) +
          (if s.1 = k then P.β * (p s * (s.2 : ℝ)) else 0) := by
      funext s
      simp only [exitRate]
      split_ifs <;> ring
    rw [hL, hR] at hfl
    have s1 : ∀ k' : ℤ, Summable (fun s : State => if s.1 = k' then r * p s else 0) := by
      intro k'
      refine Summable.of_norm_bounded ((hsum.mul_left r).abs) (fun s => ?_)
      split_ifs <;> simp <;> positivity
    have s2 : ∀ k' : ℤ, Summable (fun s : State =>
        if s.1 = k' then P.β * (p s * (s.2 : ℝ)) else 0) := by
      intro k'
      refine Summable.of_norm_bounded ((hsZ.mul_left P.β).abs) (fun s => ?_)
      split_ifs <;> simp <;> positivity
    rw [Summable.tsum_add (s1 _) (s2 _), Summable.tsum_add (s1 _) (s2 _),
      level_sum _ (hsum.mul_left r), level_sum _ (hsum.mul_left r),
      level_sum _ (hsZ.mul_left P.β), level_sum _ (hsZ.mul_left P.β)] at hfl
    simp only [tsum_mul_left] at hfl
    simpa [hm, hw] using hfl
  -- φ k = β w k - r m (k+1) is constant
  set φ : ℤ → ℝ := fun k => P.β * w k - r * m (k + 1) with hφ
  have hstep : ∀ k : ℤ, φ k = φ (k - 1) := by
    intro k
    have := hlev k
    simp only [hφ, sub_add_cancel]; linarith
  have hconst : ∀ k : ℤ, φ k = φ 0 := by
    intro k
    induction k using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [hstep (k + 1)]; simpa using ih
    | pred k ih => have := hstep (-(k:ℤ)); linarith
  have hpnn : 0 ≤ p := fun s => hnn s
  have hsm : Summable m := ((summable_prod_of_nonneg hpnn).mp hsum).2
  have hsw : Summable w := by
    have h0 : 0 ≤ (fun s : State => p s * (s.2 : ℝ)) := fun s => mul_nonneg (hnn s) (by positivity)
    exact ((summable_prod_of_nonneg h0).mp hsZ).2
  have hsm1 : Summable (fun k : ℤ => r * m (k + 1)) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr (hsm.mul_left r)
  have hsφ : Summable φ := (hsw.mul_left P.β).sub hsm1
  have hφ0 : φ 0 = 0 := by
    have : Summable (fun _ : ℤ => φ 0) := by
      have : φ = fun _ => φ 0 := funext hconst
      rwa [this] at hsφ
    exact (summable_const_iff (φ 0)).mp this
  have hab : ∀ k, P.β * w k = r * m (k + 1) := by
    intro k; have := hconst k; rw [hφ0] at this; simp only [hφ] at this; linarith
  refine ⟨hsZ, ?_⟩
  rw [Summable.tsum_prod hsZ, ← tsum_mul_left]
  have : (fun k : ℤ => P.β * ∑' z : ℕ, p (k, z) * (z : ℝ)) = fun k => r * m (k + 1) := by
    funext k; exact hab k
  rw [this]
  have h1 : ∑' k : ℤ, r * m (k + 1) = ∑' k : ℤ, r * m k :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (fun k => r * m k)
  rw [h1, tsum_mul_left]
  have : ∑' k : ℤ, m k = 1 := by
    rw [← hone, Summable.tsum_prod hsum]
  rw [this, mul_one]


theorem eq19g (P : Params) (hP : P.Standing) (r : ℝ) (hr : 0 < r)
    (p : ℤ → ℝ) (hp : IsArtStationary P r p) :
    Summable (fun j : ℤ => p j * (artZ P r j : ℝ)) ∧
    P.β * ∑' j : ℤ, p j * (artZ P r j : ℝ) = r := by
  obtain ⟨hβ, -, -, -, -⟩ := hP
  obtain ⟨_hnn, hsum, hone, hsumx, hbal⟩ := hp
  set Z : ℤ → ℝ := fun j => (artZ P r j : ℝ) with hZ
  -- a j : up-flux, b j : down-flux
  set a : ℤ → ℝ := fun j => p j * (P.β * Z j) with ha
  set b : ℤ → ℝ := fun j => p j * r with hb
  have hsa : Summable a := by
    have : a = fun j => p j * artExitRate P r j - p j * r := by
      funext j; simp only [ha, artExitRate, hZ]; ring
    rw [this]; exact hsumx.sub (hsum.mul_right r)
  have hsZ : Summable (fun j : ℤ => p j * Z j) := by
    have : (fun j : ℤ => p j * Z j) = fun j => a j / P.β := by
      funext j; simp only [ha]; field_simp
    rw [this]; exact hsa.div_const _
  -- balance equation in flux form
  have hbal' : ∀ j' : ℤ, b (j' + 1) + a (j' - 1) = b j' + a j' := by
    intro j'
    have h := hbal j'
    have hfun : (fun j => p j * artRate P r j j') =
        fun j => (if j = j' + 1 then b (j' + 1) else 0) + (if j = j' - 1 then a (j' - 1) else 0) := by
      funext j
      simp only [artRate, mul_add]
      congr 1
      · by_cases h1 : j = j' + 1
        · subst h1; simp [hb]
        · have : ¬ j' = j - 1 := by omega
          simp [h1, this]
      · by_cases h1 : j = j' - 1
        · subst h1; simp [ha, hZ]
        · have : ¬ j' = j + 1 := by omega
          simp [h1, this]
    rw [hfun, Summable.tsum_add (summable_of_ne_finset_zero (s := {j' + 1}) (by intro j hj; simp_all))
      (summable_of_ne_finset_zero (s := {j' - 1}) (by intro j hj; simp_all)),
      tsum_ite_eq, tsum_ite_eq] at h
    rw [h]; simp only [ha, hb, artExitRate, hZ]; ring
  -- φ j = a j - b (j+1) is constant
  set φ : ℤ → ℝ := fun j => a j - b (j + 1) with hφ
  have hstep : ∀ j : ℤ, φ j = φ (j - 1) := by
    intro j
    have := hbal' j
    simp only [hφ, sub_add_cancel]; linarith
  have hconst : ∀ j : ℤ, φ j = φ 0 := by
    intro j
    induction j using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [hstep (k + 1)]; simpa using ih
    | pred k ih => have := hstep (-(k:ℤ)); linarith
  have hsb1 : Summable (fun j : ℤ => b (j + 1)) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr (hsum.mul_right r)
  have hsφ : Summable φ := hsa.sub hsb1
  have hφ0 : φ 0 = 0 := by
    have : Summable (fun _ : ℤ => φ 0) := by
      have : φ = fun _ => φ 0 := funext hconst
      rwa [this] at hsφ
    exact (summable_const_iff (φ 0)).mp this
  have hab : ∀ j, a j = b (j + 1) := by
    intro j; have := hconst j; rw [hφ0] at this; simp only [hφ] at this; linarith
  refine ⟨hsZ, ?_⟩
  rw [← tsum_mul_left]
  have : (fun j => P.β * (p j * Z j)) = fun j => b (j + 1) := by
    funext j; rw [← hab j]; simp only [ha]; ring
  rw [this]
  have h1 : ∑' j : ℤ, b (j + 1) = ∑' j : ℤ, b j :=
    (Equiv.addRight (1 : ℤ)).tsum_eq b
  rw [h1]; simp only [hb]; rw [tsum_mul_right, hone, one_mul]


theorem eq31g (P : Params) (hP : P.Standing) :
    ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, ∀ (p : State → ℝ) (q : ℤ → ℝ),
      IsStationary P r p → IsArtStationary P r q →
      Summable (fun j : ℤ => q j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ)) ∧
      Summable (fun s : State => p s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ)) ∧
      ∑' j : ℤ, q j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ) -
        ∑' s : State, p s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ) ≤ C := by
  obtain ⟨C, hC, r₀, h4⟩ := lemma_4_centered P hP
  refine ⟨C, hC, max r₀ 1, fun r hr p q hp hq => ?_⟩
  have hr0 : r ≥ r₀ := le_trans (le_max_left _ _) hr
  have hrpos : 0 < r := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hr)
  have hβ : 0 < P.β := hP.1
  obtain ⟨hsD, _hsDt, hDle, hDtC⟩ := h4 r hr0 p hp
  obtain ⟨hsZ, hZ⟩ := eq14g P hP r hrpos p hp
  obtain ⟨hsZh, hZh⟩ := eq19g P hP r hrpos q hq
  -- the artificial in-transit level is the integer ceiling of the truncated target
  have hart : (fun j : ℤ => q j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ)) =
      fun j => q j * (artZ P r j : ℝ) := by
    funext j
    have h0 : 0 ≤ truncTarget P r j := le_max_right _ _
    simp only [artZ]
    rw [← Int.natCast_ceil_eq_ceil h0, Int.cast_natCast]
  -- for the GBS chain, ⌈T⌉ = Z − D
  have hgbs : (fun s : State => p s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ)) =
      fun s => p s * (s.2 : ℝ) - p s * gapD P r s := by
    funext s; simp only [gapD]; ring
  rw [hart, hgbs]
  refine ⟨hsZh, hsZ.sub hsD, ?_⟩
  rw [Summable.tsum_sub hsZ hsD]
  have e1 : ∑' j : ℤ, q j * (artZ P r j : ℝ) = r / P.β := by
    field_simp; linarith [hZh]
  have e2 : ∑' s : State, p s * (s.2 : ℝ) = r / P.β := by
    field_simp; linarith [hZ]
  rw [e1, e2]
  linarith


namespace GBSCor6

lemma half_mean (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ x, max (-x) 0 ∂(gaussianReal 0 v) = √((v : ℝ) / (2 * π)) := by
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have h1 : ∫ x, gaussianPDFReal 0 v x * max (-x) 0 = ∫ x, gaussianPDFReal 0 v x * max x 0 := by
    rw [← integral_neg_eq_self (fun x => gaussianPDFReal 0 v x * max (-x) 0)]
    congr 1; funext x
    simp only [neg_neg, gaussianPDFReal, sub_zero, even_two, Even.neg_pow]
  rw [h1]
  have h2 : ∫ x, gaussianPDFReal 0 v x * max x 0 =
      ∫ x in Ioi (0 : ℝ), (√(2 * π * v))⁻¹ * (x ^ (1 : ℝ) * rexp (-(1 / (2 * v)) * x ^ (2 : ℝ))) := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; funext x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (mem_Ioi.mpr hx)]
      simp only [gaussianPDFReal, sub_zero, rpow_one, max_eq_left hx.le]
      rw [show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
      have e : -x ^ 2 / (2 * (v : ℝ)) = -(1 / (2 * v)) * x ^ 2 := by ring
      rw [e]; ring
    · rw [indicator_of_notMem (by simpa using hx)]
      simp [max_eq_right (not_lt.mp hx)]
  rw [h2, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by positivity)]
  have e1 : (-((1 : ℝ) + 1) / 2) = -1 := by norm_num
  have e2 : (((1 : ℝ) + 1) / 2) = 1 := by norm_num
  rw [e1, e2, Real.Gamma_one, Real.rpow_neg_one]
  have hπ : 0 < π := Real.pi_pos
  have hs : 0 < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  rw [show ((v : ℝ) / (2 * π)) = ((√(2 * π * v))⁻¹ * v) ^ 2 by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]; field_simp]
  rw [Real.sqrt_sq (by positivity)]
  field_simp


/-- The truncated negative part `x ↦ min (x⁻) c` as a bounded continuous function. -/
noncomputable def phi (c : ℝ) (hc : 0 ≤ c) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (max (-x) 0) c, (continuous_neg.max continuous_const).min continuous_const⟩ c
    (by
      intro x y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have hx0 : 0 ≤ min (max (-x) 0) c := le_min (le_max_right _ _) hc
      have hy0 : 0 ≤ min (max (-y) 0) c := le_min (le_max_right _ _) hc
      have hxc : min (max (-x) 0) c ≤ c := min_le_right _ _
      have hyc : min (max (-y) 0) c ≤ c := min_le_right _ _
      rw [abs_le]; constructor <;> linarith)

lemma phi_apply (c : ℝ) (hc : 0 ≤ c) (x : ℝ) : phi c hc x = min (max (-x) 0) c := rfl

/-- `(-c - x)⁺ = x⁻ - min (x⁻) c` for `c ≥ 0`. -/
lemma split (c : ℝ) (hc : 0 ≤ c) (x : ℝ) :
    max (-c - x) 0 = max (-x) 0 - min (max (-x) 0) c := by
  rcases le_total (-x) 0 with h | h
  · rw [max_eq_right (by linarith), max_eq_right h, min_eq_left hc]; ring
  · rw [max_eq_left h]
    rcases le_total (-x) c with h' | h'
    · rw [min_eq_left h', max_eq_right (by linarith)]; ring
    · rw [min_eq_right h', max_eq_left (by linarith)]; ring

end GBSCor6

open GBSCor6

theorem cor6g (P : Params) (hP : P.Standing) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, ∀ p : ℤ → ℝ, IsArtStationary P r p →
      Summable (fun j : ℤ => p j * max (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0) ∧
      ∑' j : ℤ, p j * max (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0 ≤ ε := by
  intro ε hε
  obtain ⟨hex, hlim⟩ := lemma_5_centered P hP
  obtain ⟨hβ, hγ, -⟩ := hP
  have hγr : (1 : ℝ) ≤ P.γ := by exact_mod_cast hγ
  have hβγ : 0 < P.β * P.γ := by positivity
  set v : ℝ≥0 := (1 / (P.β * P.γ)).toNNReal with hvdef
  have hvval : (v : ℝ) = 1 / (P.β * P.γ) := Real.coe_toNNReal _ (by positivity)
  have hv : v ≠ 0 := by
    intro h0
    have : (v : ℝ) = 0 := by rw [h0]; rfl
    rw [hvval] at this
    have : 0 < 1 / (P.β * P.γ) := by positivity
    linarith
  set N := gaussianReal 0 v with hN
  set K : ℝ := (2 * π * P.β * P.γ) ^ (-(1 / 2 : ℝ)) with hKdef
  have hπ : 0 < π := Real.pi_pos
  have hK : ∫ x, max (-x) 0 ∂N = K := by
    rw [hN, half_mean v hv, hvval, hKdef]
    rw [show 1 / (P.β * P.γ) / (2 * π) = (2 * π * P.β * P.γ)⁻¹ by field_simp]
    rw [Real.sqrt_inv, Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hid : Integrable (fun x : ℝ => x) N :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))
  have hNint : Integrable (fun x : ℝ => max (-x) 0) N := hid.neg_part
  -- monotone convergence of the truncations
  have hmc : Tendsto (fun n : ℕ => ∫ x, min (max (-x) 0) (n : ℝ) ∂N) atTop (𝓝 K) := by
    rw [← hK]
    apply integral_tendsto_of_tendsto_of_monotone
    · intro n
      refine Integrable.of_bound
        ((continuous_neg.max continuous_const).min continuous_const).aestronglyMeasurable
        (n : ℝ) (Eventually.of_forall fun x => ?_)
      have h0 : 0 ≤ min (max (-x) 0) (n : ℝ) := le_min (le_max_right _ _) (Nat.cast_nonneg n)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact min_le_right _ _
    · exact hNint
    · exact Eventually.of_forall fun x m n hmn => min_le_min le_rfl (by exact_mod_cast hmn)
    · refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
      obtain ⟨N0, hN0⟩ := exists_nat_ge (max (-x) 0)
      filter_upwards [eventually_ge_atTop N0] with n hn
      have : max (-x) 0 ≤ (n : ℝ) := le_trans hN0 (by exact_mod_cast hn)
      rw [min_eq_left this]
  obtain ⟨n, hn1, hnK⟩ : ∃ n : ℕ, 1 ≤ n ∧ K - ε / 2 < ∫ x, min (max (-x) 0) (n : ℝ) ∂N := by
    have h1 := hmc.eventually (lt_mem_nhds (by linarith : K - ε / 2 < K))
    obtain ⟨n, hn⟩ := (h1.and (eventually_ge_atTop 1)).exists
    exact ⟨n, hn.2, hn.1⟩
  set c : ℝ := (n : ℝ) with hcdef
  have hc1 : (1 : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast hn1
  have hc0 : (0 : ℝ) ≤ c := by linarith
  refine ⟨c, by linarith, ?_⟩
  by_contra hbad
  push Not at hbad
  classical
  let Bad : ℝ → (ℤ → ℝ) → Prop := fun r p => IsArtStationary P r p ∧
    (Summable (fun j : ℤ => p j * max (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0) →
      ε < ∑' j : ℤ, p j * max (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0)
  let pf : ℝ → ℤ → ℝ := fun r =>
    if h : ∃ p, Bad r p then h.choose else if h' : 0 < r then (hex r h').choose else fun _ => 0
  have hpf_stat : ∀ r, 0 < r → IsArtStationary P r (pf r) := by
    intro r hr
    simp only [pf]
    split_ifs with h
    · exact h.choose_spec.1
    · exact (hex r hr).choose_spec
  have hpf_bad : ∀ r, (∃ p, Bad r p) → Bad r (pf r) := by
    intro r h
    simp only [pf, dif_pos h]
    exact h.choose_spec
  have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  obtain ⟨hw, -, hneg⟩ := hlim pf (by filter_upwards [hpos] with r hr using hpf_stat r hr)
  have hφ := hw (phi c hc0)
  simp only [phi_apply] at hφ
  have hev : ∀ᶠ r in atTop,
      Summable (fun j : ℤ => pf r j * max (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0) ∧
      ∑' j : ℤ, pf r j * max (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0 < ε := by
    have h1 : ∀ᶠ r in atTop, 0 < ∑' j : ℤ, pf r j * max (-(((j : ℝ) - P.xs r) / Real.sqrt r)) 0 :=
      hneg.eventually (lt_mem_nhds hKpos)
    have h2 : ∀ᶠ r in atTop, (∑' j : ℤ, pf r j * max (-(((j : ℝ) - P.xs r) / Real.sqrt r)) 0) -
        (∑' j : ℤ, pf r j * min (max (-(((j : ℝ) - P.xs r) / Real.sqrt r)) 0) c) < ε := by
      have := hneg.sub hφ
      exact this.eventually (gt_mem_nhds (by linarith))
    filter_upwards [h1, h2, hpos] with r h1 h2 hr
    have hnn : ∀ j, 0 ≤ pf r j := (hpf_stat r hr).1
    have hs1 : Summable (fun j : ℤ => pf r j * max (-(((j : ℝ) - P.xs r) / Real.sqrt r)) 0) := by
      by_contra hns
      rw [tsum_eq_zero_of_not_summable hns] at h1
      exact lt_irrefl _ h1
    have hs2 : Summable (fun j : ℤ => pf r j * min (max (-(((j : ℝ) - P.xs r) / Real.sqrt r)) 0) c) := by
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hnn j) (le_min (le_max_right _ _) hc0))
        (fun j => ?_) ((hpf_stat r hr).2.1.mul_right c)
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hnn j)
    have heq : (fun j : ℤ => pf r j * max (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0) =
        fun j => pf r j * max (-(((j : ℝ) - P.xs r) / Real.sqrt r)) 0 -
          pf r j * min (max (-(((j : ℝ) - P.xs r) / Real.sqrt r)) 0) c := by
      funext j
      rw [show -c - ((j : ℝ) - P.xs r) / Real.sqrt r = -c - (((j : ℝ) - P.xs r) / Real.sqrt r) by ring,
        split c hc0, mul_sub]
    rw [heq]
    exact ⟨hs1.sub hs2, by rw [Summable.tsum_sub hs1 hs2]; exact h2⟩
  have hfreq : ∃ᶠ r in atTop, ∃ p, Bad r p := by
    rw [frequently_atTop]
    intro r₀
    obtain ⟨r, hr, p, hp, hp2⟩ := hbad r₀
    exact ⟨r, hr, p, hp, hp2⟩
  obtain ⟨r, ⟨hS, hlt⟩, hb⟩ := (hev.and_frequently hfreq).exists
  have := (hpf_bad r hb).2 hS
  linarith


namespace GBSEq36

/-! ### Support of a stationary distribution -/

lemma orderStep_ge (P : Params) (r : ℝ) (y : ℤ) (z : ℕ) :
    ⌈truncTarget P r y⌉ ≤ ((orderStep P r y z : ℕ) : ℤ) := by
  simp only [orderStep]
  rw [Int.ceil_sub_natCast]
  have h := Int.self_le_toNat (⌈truncTarget P r y⌉ - (z : ℤ))
  push_cast
  omega

/-- A stationary distribution vanishes on states with `Z < ⌈T(Y)⌉` (they are never entered). -/
lemma support (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (p : State → ℝ)
    (hp : IsStationary P r p) (s : State) (hs : ((s.2 : ℕ) : ℤ) < ⌈truncTarget P r s.1⌉) :
    p s = 0 := by
  have hb := hp.2.2.2.2 s
  have h0 : ∀ s0 : State, p s0 * rate P r s0 s = 0 := by
    intro s0
    have : rate P r s0 s = 0 := by
      unfold rate
      rw [if_neg, if_neg]
      · simp
      · rintro ⟨-, h⟩
        have := orderStep_ge P r (s0.1 + 1) (s0.2 - 1)
        rw [h] at hs
        simp only [afterItem] at hs
        omega
      · intro h
        have := orderStep_ge P r (s0.1 - 1) s0.2
        rw [h] at hs
        simp only [afterCustomer] at hs
        omega
    rw [this, mul_zero]
  simp only [h0, tsum_zero] at hb
  have hpos : 0 < exitRate P r s := by
    unfold exitRate; positivity
  rcases mul_eq_zero.mp hb.symm with h | h
  · exact h
  · linarith

/-! ### Tail-sum formula on `ℤ`-valued observables -/

lemma tail {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (y : ι → ℤ) :
    ∑' i, ENNReal.ofReal (w i * ((y i).toNat : ℝ)) =
      ∑' k : ℕ, ENNReal.ofReal (∑' i, if (k : ℤ) < y i then w i else 0) := by
  have h1 : ∀ i, ENNReal.ofReal (w i * ((y i).toNat : ℝ)) =
      ∑' k : ℕ, if (k : ℤ) < y i then ENNReal.ofReal (w i) else 0 := by
    intro i
    rw [tsum_eq_sum (s := Finset.range (y i).toNat)]
    · rw [Finset.sum_congr rfl (fun k hk => if_pos (Int.lt_toNat.mp (Finset.mem_range.mp hk)))]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (hw i),
        ENNReal.ofReal_natCast, mul_comm]
    · intro k hk
      rw [if_neg]
      intro h
      exact hk (Finset.mem_range.mpr (Int.lt_toNat.mpr h))
  rw [tsum_congr h1, ENNReal.tsum_comm]
  congr 1; funext k
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by split_ifs; exact hw i; exact le_rfl)
    (Summable.of_nonneg_of_le (fun i => by split_ifs; exact hw i; exact le_rfl)
      (fun i => by split_ifs; exact le_rfl; exact hw i) hs)]
  congr 1; funext i
  split_ifs <;> simp

lemma summable_of_ofReal {ι : Type*} (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (h : ∑' i, ENNReal.ofReal (f i) ≠ ⊤) : Summable f := by
  have := ENNReal.summable_toReal h
  simpa [ENNReal.toReal_ofReal (hf _)] using this

lemma tsum_le_of_ofReal {ι κ : Type*} (f : ι → ℝ) (g : κ → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hsg : Summable g) (h : ∑' i, ENNReal.ofReal (f i) ≤ ∑' i, ENNReal.ofReal (g i)) :
    Summable f ∧ ∑' i, f i ≤ ∑' i, g i := by
  have hsf : Summable f := summable_of_ofReal f hf
    (ne_top_of_le_ne_top (by rw [← ENNReal.ofReal_tsum_of_nonneg hg hsg]; exact ENNReal.ofReal_ne_top) h)
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hsf, ← ENNReal.ofReal_tsum_of_nonneg hg hsg] at h
  exact ⟨hsf, (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hg)).mp h⟩

lemma ind_summable {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (c : ι → Prop) [DecidablePred c] : Summable (fun i => if c i then w i else 0) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs; exact hw i; exact le_rfl)
    (fun i => by split_ifs; exact le_rfl; exact hw i) hs

/-- Upper tails: `Ŷ ≤st Y` gives `E Ŷ⁺ ≤ E Y⁺`. -/
lemma pos_cmp (p : State → ℝ) (q : ℤ → ℝ) (hpn : ∀ s, 0 ≤ p s) (hps : Summable p)
    (hqn : ∀ j, 0 ≤ q j) (hqs : Summable q)
    (h8 : ∀ x : ℝ, ∑' j : ℤ, (if x < (j : ℝ) then q j else 0) ≤
      ∑' s : State, (if x < (s.1 : ℝ) then p s else 0))
    (hsp : Summable (fun s : State => p s * ((s.1.toNat : ℕ) : ℝ))) :
    Summable (fun j : ℤ => q j * ((j.toNat : ℕ) : ℝ)) ∧
      ∑' j : ℤ, q j * ((j.toNat : ℕ) : ℝ) ≤ ∑' s : State, p s * ((s.1.toNat : ℕ) : ℝ) := by
  apply tsum_le_of_ofReal _ _ (fun j => mul_nonneg (hqn j) (Nat.cast_nonneg _))
    (fun s => mul_nonneg (hpn s) (Nat.cast_nonneg _)) hsp
  rw [tail q hqn hqs (fun j => j), tail p hpn hps (fun s => s.1)]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  have := h8 (k : ℝ)
  have e1 : ∀ j : ℤ, ((k : ℝ) < (j : ℝ)) = ((k : ℤ) < j) := fun j => by
    apply propext; constructor <;> intro h <;> exact_mod_cast h
  simp only [e1] at this
  exact this

/-- Lower tails: `Ŷ ≤st Y` gives `E Y⁻ ≤ E Ŷ⁻`. -/
lemma neg_cmp (p : State → ℝ) (q : ℤ → ℝ) (hpn : ∀ s, 0 ≤ p s) (hps : Summable p)
    (hp1 : ∑' s, p s = 1)
    (hqn : ∀ j, 0 ≤ q j) (hqs : Summable q) (hq1 : ∑' j, q j = 1)
    (h8 : ∀ x : ℝ, ∑' j : ℤ, (if x < (j : ℝ) then q j else 0) ≤
      ∑' s : State, (if x < (s.1 : ℝ) then p s else 0))
    (hsq : Summable (fun j : ℤ => q j * (((-j).toNat : ℕ) : ℝ))) :
    Summable (fun s : State => p s * (((-s.1).toNat : ℕ) : ℝ)) ∧
      ∑' s : State, p s * (((-s.1).toNat : ℕ) : ℝ) ≤ ∑' j : ℤ, q j * (((-j).toNat : ℕ) : ℝ) := by
  apply tsum_le_of_ofReal _ _ (fun s => mul_nonneg (hpn s) (Nat.cast_nonneg _))
    (fun j => mul_nonneg (hqn j) (Nat.cast_nonneg _)) hsq
  rw [tail p hpn hps (fun s => -s.1), tail q hqn hqs (fun j => -j)]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  have := h8 (-(k : ℝ) - 1)
  -- complement form
  have cp : ∀ s : State, (if (k : ℤ) < -s.1 then p s else 0) =
      p s - (if -(k : ℝ) - 1 < (s.1 : ℝ) then p s else 0) := by
    intro s
    by_cases h : (k : ℤ) < -s.1
    · have : ¬ (-(k : ℝ) - 1 < (s.1 : ℝ)) := by
        intro h'
        have : -(k : ℤ) - 1 < s.1 := by exact_mod_cast h'
        omega
      rw [if_pos h, if_neg this]; ring
    · have : (-(k : ℝ) - 1 < (s.1 : ℝ)) := by
        have : -(k : ℤ) - 1 < s.1 := by omega
        exact_mod_cast this
      rw [if_neg h, if_pos this]; ring
  have cq : ∀ j : ℤ, (if (k : ℤ) < -j then q j else 0) =
      q j - (if -(k : ℝ) - 1 < (j : ℝ) then q j else 0) := by
    intro j
    by_cases h : (k : ℤ) < -j
    · have : ¬ (-(k : ℝ) - 1 < (j : ℝ)) := by
        intro h'
        have : -(k : ℤ) - 1 < j := by exact_mod_cast h'
        omega
      rw [if_pos h, if_neg this]; ring
    · have : (-(k : ℝ) - 1 < (j : ℝ)) := by
        have : -(k : ℤ) - 1 < j := by omega
        exact_mod_cast this
      rw [if_neg h, if_pos this]; ring
  rw [tsum_congr cp, tsum_congr cq, Summable.tsum_sub hps (ind_summable p hpn hps _),
    Summable.tsum_sub hqs (ind_summable q hqn hqs _), hp1, hq1]
  linarith

/-! ### Pointwise facts about the truncated target -/

lemma T_nonneg (P : Params) (r : ℝ) (y : ℤ) : 0 ≤ truncTarget P r y := le_max_right _ _

lemma T_le (P : Params) (r : ℝ) (hM : 0 ≤ Xstar P r + P.f r) (y : ℤ) :
    truncTarget P r y ≤ Xstar P r + P.f r :=
  max_le (min_le_right _ _) hM

noncomputable def Xp (P : Params) (r : ℝ) : ℝ := Xstar P r + (P.γ : ℝ) * P.xs r
noncomputable def fe (P : Params) (r : ℝ) : ℝ := P.f r - (P.γ : ℝ) * P.xs r

lemma target_eq (P : Params) (r : ℝ) (y : ℤ) :
    target P r y = Xp P r - (P.γ : ℝ) * y := by
  simp [target, Xp]; ring

lemma up_bound (P : Params) (r : ℝ) (y : ℤ) :
    (P.γ : ℝ) * y ≤ Xp P r - truncTarget P r y + max ((P.γ : ℝ) * y - Xp P r) 0 := by
  have ht := target_eq P r y
  unfold truncTarget
  rw [ht]
  rcases le_total 0 (Xp P r - (P.γ : ℝ) * y) with h | h
  · have : max (min (Xp P r - (P.γ : ℝ) * y) (Xstar P r + P.f r)) 0 ≤
        Xp P r - (P.γ : ℝ) * y :=
      max_le (min_le_left _ _) h
    have := le_max_right ((P.γ : ℝ) * y - Xp P r) 0
    linarith
  · have : max (min (Xp P r - (P.γ : ℝ) * y) (Xstar P r + P.f r)) 0 = 0 :=
      max_eq_right (le_trans (min_le_left _ _) h)
    rw [this]
    have := le_max_left ((P.γ : ℝ) * y - Xp P r) 0
    linarith

lemma low_bound (P : Params) (r : ℝ) (hM : 0 ≤ Xstar P r + P.f r)
    (y : ℤ) :
    Xp P r - truncTarget P r y - max (-fe P r - (P.γ : ℝ) * y) 0 ≤ (P.γ : ℝ) * y := by
  have ht := target_eq P r y
  unfold truncTarget
  rw [ht]
  have e : Xstar P r + P.f r = Xp P r + fe P r := by unfold Xp fe; ring
  rcases le_total (Xp P r - (P.γ : ℝ) * y) (Xstar P r + P.f r) with h | h
  · rw [min_eq_left h]
    have := le_max_left (Xp P r - (P.γ : ℝ) * y) 0
    have := le_max_right (-fe P r - (P.γ : ℝ) * y) 0
    linarith
  · rw [min_eq_right h, max_eq_left hM]
    have := le_max_left (-fe P r - (P.γ : ℝ) * y) 0
    linarith

lemma gapDt_lower (P : Params) (r : ℝ) (s : State) :
    (P.γ : ℝ) * s.1 - Xp P r - 1 ≤ gapDt P r s := by
  unfold gapDt
  have h1 := Int.ceil_lt_add_one (min (truncTarget P r s.1) (target P r s.1))
  have h2 := min_le_right (truncTarget P r s.1) (target P r s.1)
  simp only [target_eq P r s.1] at h1 h2 ⊢
  have : (0 : ℝ) ≤ s.2 := Nat.cast_nonneg _
  linarith

lemma gapDt_nonneg (P : Params) (r : ℝ) (s : State)
    (hs : ⌈truncTarget P r s.1⌉ ≤ ((s.2 : ℕ) : ℤ)) : 0 ≤ gapDt P r s := by
  unfold gapDt
  have h1 : ⌈min (truncTarget P r s.1) (target P r s.1)⌉ ≤ ⌈truncTarget P r s.1⌉ :=
    Int.ceil_mono (min_le_left _ _)
  have : ⌈min (truncTarget P r s.1) (target P r s.1)⌉ ≤ ((s.2 : ℕ) : ℤ) := le_trans h1 hs
  have : ((⌈min (truncTarget P r s.1) (target P r s.1)⌉ : ℤ) : ℝ) ≤ ((((s.2 : ℕ) : ℤ)) : ℝ) := by
    exact_mod_cast this
  push_cast at this
  linarith

lemma int_split (y : ℤ) : (y : ℝ) = ((y.toNat : ℕ) : ℝ) - (((-y).toNat : ℕ) : ℝ) := by
  have := Int.toNat_sub_toNat_neg y
  have h : ((((y.toNat : ℕ) : ℤ) - (((-y).toNat : ℕ) : ℤ) : ℤ) : ℝ) = (y : ℝ) := by
    rw [this]
  push_cast at h
  linarith

lemma toNat_le_max (y : ℤ) : ((y.toNat : ℕ) : ℝ) = max (y : ℝ) 0 := by
  rcases le_total 0 y with h | h
  · rw [max_eq_left (by exact_mod_cast h)]
    have : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg h
    exact_mod_cast this
  · rw [max_eq_right (by exact_mod_cast h)]
    simp [Int.toNat_eq_zero.mpr h]

lemma toNat_neg_eq (y : ℤ) : (((-y).toNat : ℕ) : ℝ) = max (-(y : ℝ)) 0 := by
  rw [toNat_le_max]; push_cast; rfl

end GBSEq36

open GBSEq36

theorem solution (P : Params) (hP : P.Standing)
    (p : ℝ → State → ℝ) (hp : ∀ᶠ r in atTop, IsStationary P r (p r))
    (q : ℝ → ℤ → ℝ) (hq : ∀ᶠ r in atTop, IsArtStationary P r (q r)) :
    (∀ᶠ r in atTop, Summable (fun s : State => p r s * (s.1 : ℝ)) ∧
      Summable (fun j : ℤ => q r j * (j : ℝ))) ∧
    Tendsto (fun r => ∑' s : State, p r s * ((s.1 : ℝ) / Real.sqrt r) -
      ∑' j : ℤ, q r j * ((j : ℝ) / Real.sqrt r)) atTop (𝓝 0) := by
  have hP' := hP
  obtain ⟨hβ, hγ, hfpos, -, hfsqrt⟩ := hP'
  have hγr : (1 : ℝ) ≤ P.γ := by exact_mod_cast hγ
  obtain ⟨C4, hC4, r4, h4⟩ := lemma_4_centered P hP
  obtain ⟨C31, hC31, r31, h31⟩ := eq31g P hP
  have h6 := cor6g P hP
  obtain ⟨c1, hc1, r6, h6'⟩ := h6 1 one_pos
  have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  /- The core estimate at a fixed large `r`. -/
  have key : ∀ r : ℝ, 0 < r → r ≥ r4 → r ≥ r31 → r ≥ r6 →
      IsStationary P r (p r) → IsArtStationary P r (q r) →
      Summable (fun s : State => p r s * (s.1 : ℝ)) ∧ Summable (fun j : ℤ => q r j * (j : ℝ)) ∧
      0 ≤ ∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ) ∧
      (P.γ : ℝ) * (∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ)) ≤
        C31 + C4 + 2 + ∑' j : ℤ, q r j * max (-fe P r - (P.γ : ℝ) * j) 0 ∧
      Summable (fun j : ℤ => q r j * max (-fe P r - (P.γ : ℝ) * j) 0) := by
    intro r hr hr4 hr31 hr6 hpr hqr
    set pr := p r with hpr_def
    set qr := q r with hqr_def
    have hXs := le_abs_self (Xp P r)
    have hXa := abs_nonneg (Xp P r)
    have hM : 0 ≤ Xstar P r + P.f r := by have := hfpos r; unfold Xstar; positivity
    have hpr' := hpr
    have hqr' := hqr
    obtain ⟨hpn, hps, hp1, -, -⟩ := hpr'
    obtain ⟨hqn, hqs, hq1, -, -⟩ := hqr'
    obtain ⟨hsD, hsDt, -, hDtC⟩ := h4 r hr4 pr hpr
    obtain ⟨hsTq, hsTp, h31r⟩ := h31 r hr31 pr qr hpr hqr
    obtain ⟨hs6, -⟩ := h6' r hr6 qr hqr
    have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    -- (1) E Y⁺ < ∞ from the gap D̃
    have hsYp : Summable (fun s : State => pr s * ((s.1.toNat : ℕ) : ℝ)) := by
      refine Summable.of_nonneg_of_le (fun s => mul_nonneg (hpn s) (Nat.cast_nonneg _))
        (fun s => ?_) (hsDt.add (hps.mul_right (|Xp P r| + 1)))
      by_cases hz : ((s.2 : ℕ) : ℤ) < ⌈truncTarget P r s.1⌉
      · rw [support P r hr hβ pr hpr s hz]; simp
      · push Not at hz
        have h0 := gapDt_nonneg P r s hz
        have h1 := gapDt_lower P r s
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ (hpn s)
        rw [toNat_le_max]
        apply max_le
        · have : (s.1 : ℝ) ≤ (P.γ : ℝ) * s.1 ∨ (s.1 : ℝ) < 0 := by
            rcases le_or_gt 0 (s.1 : ℝ) with h | h
            · left; nlinarith
            · right; exact h
          rcases this with h | h <;> linarith
        · linarith
    -- (2) E Ŷ⁻ < ∞ from Corollary 6
    have hsQn : Summable (fun j : ℤ => qr j * (((-j).toNat : ℕ) : ℝ)) := by
      have hb : Summable (fun j : ℤ =>
          Real.sqrt r * (qr j * max (-c1 - ((j : ℝ) - P.xs r) / Real.sqrt r) 0) + Real.sqrt r * c1 * qr j
            + |P.xs r| * qr j) :=
        ((hs6.mul_left _).add (hqs.mul_left _)).add (hqs.mul_left _)
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hqn j) (Nat.cast_nonneg _))
        (fun j => ?_) hb
      rw [toNat_neg_eq]
      have h1 : max (-(j : ℝ)) 0 ≤ Real.sqrt r * max (-c1 - ((j : ℝ) - P.xs r) / Real.sqrt r) 0 +
          Real.sqrt r * c1 + |P.xs r| := by
        have hxa := le_abs_self (P.xs r)
        have hxa' := abs_nonneg (P.xs r)
        apply max_le
        · have : -c1 - ((j : ℝ) - P.xs r) / Real.sqrt r ≤ max (-c1 - ((j : ℝ) - P.xs r) / Real.sqrt r) 0 :=
            le_max_left _ _
          have e : Real.sqrt r * (-c1 - ((j : ℝ) - P.xs r) / Real.sqrt r) =
              -(Real.sqrt r * c1) - j + P.xs r := by
            field_simp; ring
          have k := mul_le_mul_of_nonneg_left this hsqrt.le
          have k2 := neg_le_abs (P.xs r)
          linarith
        · have := le_max_right (-c1 - ((j : ℝ) - P.xs r) / Real.sqrt r) 0
          positivity
      have := mul_le_mul_of_nonneg_left h1 (hqn j)
      nlinarith
    -- (3) tail comparisons from Lemma 8
    obtain ⟨h8a, -⟩ := lemma_8_centered P hP r hr pr hpr qr hqr
    obtain ⟨hsQp, hQpY⟩ := pos_cmp pr qr hpn hps hqn hqs h8a hsYp
    obtain ⟨hsYn, hYnQ⟩ := neg_cmp pr qr hpn hps hp1 hqn hqs hq1 h8a hsQn
    have eY : (fun s : State => pr s * (s.1 : ℝ)) =
        fun s => pr s * ((s.1.toNat : ℕ) : ℝ) - pr s * (((-s.1).toNat : ℕ) : ℝ) := by
      funext s; rw [int_split s.1]; ring
    have eQ : (fun j : ℤ => qr j * (j : ℝ)) =
        fun j => qr j * ((j.toNat : ℕ) : ℝ) - qr j * (((-j).toNat : ℕ) : ℝ) := by
      funext j; rw [int_split j]; ring
    have hsY : Summable (fun s : State => pr s * (s.1 : ℝ)) := by rw [eY]; exact hsYp.sub hsYn
    have hsQ : Summable (fun j : ℤ => qr j * (j : ℝ)) := by rw [eQ]; exact hsQp.sub hsQn
    have hlow : 0 ≤ ∑' s : State, pr s * (s.1 : ℝ) - ∑' j : ℤ, qr j * (j : ℝ) := by
      rw [eY, eQ, Summable.tsum_sub hsYp hsYn, Summable.tsum_sub hsQp hsQn]
      linarith
    -- (4) the error term of the artificial chain is summable
    have hsE : Summable (fun j : ℤ => qr j * max (-fe P r - (P.γ : ℝ) * j) 0) := by
      refine Summable.of_nonneg_of_le
        (fun j => mul_nonneg (hqn j) (le_max_right _ _)) (fun j => ?_)
        ((hsQn.mul_left (P.γ : ℝ)).add (hqs.mul_left |fe P r|))
      rw [toNat_neg_eq]
      have : max (-fe P r - (P.γ : ℝ) * j) 0 ≤ (P.γ : ℝ) * max (-(j : ℝ)) 0 + |fe P r| := by
        have hγ0 : (0 : ℝ) ≤ P.γ := Nat.cast_nonneg _
        have hfa := neg_abs_le (fe P r)
        have hfa' := abs_nonneg (fe P r)
        apply max_le
        · have := le_max_left (-(j : ℝ)) 0
          nlinarith
        · have := le_max_right (-(j : ℝ)) 0
          positivity
      have := mul_le_mul_of_nonneg_left this (hqn j)
      linarith
    -- (5) upper bound for the GBS chain: γ E Y ≤ X∗ − E T + E D̃ + 1
    have hsT : Summable (fun s : State => pr s * truncTarget P r s.1) :=
      Summable.of_nonneg_of_le (fun s => mul_nonneg (hpn s) (T_nonneg P r _))
        (fun s => mul_le_mul_of_nonneg_left (T_le P r hM _) (hpn s))
        (hps.mul_right (Xstar P r + P.f r))
    have hsTh : Summable (fun j : ℤ => qr j * truncTarget P r j) :=
      Summable.of_nonneg_of_le (fun j => mul_nonneg (hqn j) (T_nonneg P r _))
        (fun j => mul_le_mul_of_nonneg_left (T_le P r hM _) (hqn j))
        (hqs.mul_right (Xstar P r + P.f r))
    have hup : (P.γ : ℝ) * ∑' s : State, pr s * (s.1 : ℝ) ≤
        Xp P r - ∑' s : State, pr s * truncTarget P r s.1 + ∑' s, pr s * gapDt P r s + 1 := by
      have hpt : ∀ s : State, (P.γ : ℝ) * (pr s * (s.1 : ℝ)) ≤
          Xp P r * pr s - pr s * truncTarget P r s.1 + pr s * gapDt P r s + pr s := by
        intro s
        by_cases hz : ((s.2 : ℕ) : ℤ) < ⌈truncTarget P r s.1⌉
        · rw [support P r hr hβ pr hpr s hz]; simp
        · push Not at hz
          have h0 := gapDt_nonneg P r s hz
          have h1 := gapDt_lower P r s
          have h2 := up_bound P r s.1
          have h3 : max ((P.γ : ℝ) * s.1 - Xp P r) 0 ≤ gapDt P r s + 1 :=
            max_le (by linarith) (by linarith)
          have := mul_le_mul_of_nonneg_left (le_trans h2 (by linarith :
            Xp P r - truncTarget P r s.1 + max ((P.γ : ℝ) * s.1 - Xp P r) 0 ≤
              Xp P r - truncTarget P r s.1 + (gapDt P r s + 1))) (hpn s)
          nlinarith
      have := Summable.tsum_le_tsum hpt (hsY.mul_left _)
        ((((hps.mul_left (Xp P r)).sub hsT).add hsDt).add hps)
      rw [tsum_mul_left, Summable.tsum_add (((hps.mul_left (Xp P r)).sub hsT).add hsDt) hps,
        Summable.tsum_add ((hps.mul_left (Xp P r)).sub hsT) hsDt,
        Summable.tsum_sub (hps.mul_left (Xp P r)) hsT, tsum_mul_left, hp1] at this
      linarith
    -- (6) lower bound for the artificial chain
    have hlo : Xp P r - ∑' j : ℤ, qr j * truncTarget P r j -
        ∑' j : ℤ, qr j * max (-fe P r - (P.γ : ℝ) * j) 0 ≤
        (P.γ : ℝ) * ∑' j : ℤ, qr j * (j : ℝ) := by
      have hpt : ∀ j : ℤ, Xp P r * qr j - qr j * truncTarget P r j -
          qr j * max (-fe P r - (P.γ : ℝ) * j) 0 ≤ (P.γ : ℝ) * (qr j * (j : ℝ)) := by
        intro j
        have := mul_le_mul_of_nonneg_left (low_bound P r hM j) (hqn j)
        nlinarith
      have := Summable.tsum_le_tsum hpt (((hqs.mul_left (Xp P r)).sub hsTh).sub hsE)
        (hsQ.mul_left _)
      rw [tsum_mul_left, Summable.tsum_sub ((hqs.mul_left (Xp P r)).sub hsTh) hsE,
        Summable.tsum_sub (hqs.mul_left (Xp P r)) hsTh, tsum_mul_left, hq1] at this
      linarith
    -- (7) T versus ⌈T⌉
    have hTq : ∑' j : ℤ, qr j * truncTarget P r j ≤
        ∑' j : ℤ, qr j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ) :=
      Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (Int.le_ceil _) (hqn j))
        hsTh hsTq
    have hTp : ∑' s : State, pr s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ) - 1 ≤
        ∑' s : State, pr s * truncTarget P r s.1 := by
      have := Summable.tsum_le_tsum
        (fun s : State => (by
          have h := Int.ceil_lt_add_one (truncTarget P r s.1)
          have := mul_le_mul_of_nonneg_left h.le (hpn s)
          linarith : pr s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ) ≤
            pr s * truncTarget P r s.1 + pr s))
        hsTp (hsT.add hps)
      rw [Summable.tsum_add hsT hps, hp1] at this
      linarith
    refine ⟨hsY, hsQ, hlow, ?_, hsE⟩
    rw [mul_sub]
    linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hpos, hp, hq, eventually_ge_atTop r4, eventually_ge_atTop r31,
      eventually_ge_atTop r6] with r hr hpr hqr h4r h31r h6r
    obtain ⟨a, b, -⟩ := key r hr h4r h31r h6r hpr hqr
    exact ⟨a, b⟩
  · -- the scaled difference tends to zero
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [hpos, hp, hq, eventually_ge_atTop r4, eventually_ge_atTop r31,
        eventually_ge_atTop r6] with r hr hpr hqr h4r h31r h6r
      obtain ⟨hsY, hsQ, hlow, -⟩ := key r hr h4r h31r h6r hpr hqr
      have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      have e : ∑' s : State, p r s * ((s.1 : ℝ) / Real.sqrt r) -
          ∑' j : ℤ, q r j * ((j : ℝ) / Real.sqrt r) =
          (∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ)) / Real.sqrt r := by
        simp only [mul_div_assoc']
        rw [tsum_div_const, tsum_div_const, sub_div]
      rw [e]
      have := div_nonneg hlow hsqrt.le
      linarith
    · intro a ha
      -- choose ε = a/3 in Corollary 6
      obtain ⟨c, hc, r6', h6c⟩ := h6 (a / 3) (by linarith)
      have hγpos : (0 : ℝ) < P.γ := by linarith
      have hf_big : ∀ᶠ r in atTop, c * (P.γ : ℝ) ≤ P.f r / Real.sqrt r :=
        hfsqrt.eventually (eventually_ge_atTop _)
      have hC : Tendsto (fun r => (C31 + C4 + 2) / ((P.γ : ℝ) * Real.sqrt r)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.const_mul_atTop hγpos)
      have hC' : ∀ᶠ r in atTop, (C31 + C4 + 2) / ((P.γ : ℝ) * Real.sqrt r) < a / 3 :=
        hC.eventually (gt_mem_nhds (by linarith))
      filter_upwards [hpos, hp, hq, eventually_ge_atTop r4, eventually_ge_atTop r31,
        eventually_ge_atTop r6, eventually_ge_atTop r6', hf_big, hC'] with
        r hr hpr hqr h4r h31r h6r h6r' hfr hCr
      obtain ⟨hsY, hsQ, hlow, hupb, hsE⟩ := key r hr h4r h31r h6r hpr hqr
      obtain ⟨hs6, h6le⟩ := h6c r h6r' (q r) hqr
      have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      have hqn := hqr.1
      -- the error term is at most γ √r · a/3
      have hE : ∑' j : ℤ, q r j * max (-fe P r - (P.γ : ℝ) * j) 0 ≤
          (P.γ : ℝ) * Real.sqrt r * (a / 3) := by
        have hfr' : c * (P.γ : ℝ) * Real.sqrt r ≤ P.f r := by
          rw [le_div_iff₀ hsqrt] at hfr; linarith
        have hpt : ∀ j : ℤ, q r j * max (-fe P r - (P.γ : ℝ) * j) 0 ≤
            (P.γ : ℝ) * Real.sqrt r * (q r j * max (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0) := by
          intro j
          have : max (-fe P r - (P.γ : ℝ) * j) 0 ≤
              (P.γ : ℝ) * Real.sqrt r * max (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0 := by
            apply max_le
            · have h1 := le_max_left (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0
              have e : (P.γ : ℝ) * Real.sqrt r * (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) =
                  -(c * (P.γ : ℝ) * Real.sqrt r) - (P.γ : ℝ) * j + (P.γ : ℝ) * P.xs r := by
                field_simp; ring
              have efe : fe P r = P.f r - (P.γ : ℝ) * P.xs r := rfl
              have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (P.γ : ℝ) * Real.sqrt r)
              linarith
            · have := le_max_right (-c - ((j : ℝ) - P.xs r) / Real.sqrt r) 0
              positivity
          have := mul_le_mul_of_nonneg_left this (hqn j)
          linarith
        have := Summable.tsum_le_tsum hpt hsE (hs6.mul_left _)
        rw [tsum_mul_left] at this
        have h3 := mul_le_mul_of_nonneg_left h6le (by positivity : (0 : ℝ) ≤ (P.γ : ℝ) * Real.sqrt r)
        linarith
      have e : ∑' s : State, p r s * ((s.1 : ℝ) / Real.sqrt r) -
          ∑' j : ℤ, q r j * ((j : ℝ) / Real.sqrt r) =
          (∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ)) / Real.sqrt r := by
        simp only [mul_div_assoc']
        rw [tsum_div_const, tsum_div_const, sub_div]
      rw [e, div_lt_iff₀ hsqrt]
      set Δ := ∑' s : State, p r s * (s.1 : ℝ) - ∑' j : ℤ, q r j * (j : ℝ)
      have hCr' : C31 + C4 + 2 < a / 3 * ((P.γ : ℝ) * Real.sqrt r) := by
        rw [div_lt_iff₀ (by positivity)] at hCr; linarith
      have : (P.γ : ℝ) * Δ < (P.γ : ℝ) * (a * Real.sqrt r) := by nlinarith
      exact lt_of_mul_lt_mul_left this hγpos.le
