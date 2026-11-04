-- Prove2me | solution 1 for SelfishMiningRuin.ValueFn.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:31:08.290031+00:00
-- url     : https://prove2.me/submissions/da3d3346-b43d-4061-9e7b-b935705e12c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Model
import Definitions.Def_SelfishMiningRuin_ValueFn_Formula
import Theorems.Thm_SelfishMiningRuin_ValueFn_equation_29
import Theorems.Thm_SelfishMiningRuin_ValueFn_equations_39_40
import Theorems.Thm_SelfishMiningRuin_ValueFn_Vhat_linear_bound

set_option autoImplicit false

namespace SMRSol31

open SelfishMiningRuin.ValueFn Filter Topology

/-- Comparison lemma: a solution of `c g' + β g = h` with `g 0 = 0` and `h ≤ β m`
stays below `m`. -/
lemma cmp_upper (g g' h : ℝ → ℝ) (c β m U : ℝ) (hc : 0 < c) (hβ : 0 < β) (hm : 0 ≤ m)
    (hU : 0 ≤ U) (hcont : ContinuousOn g (Set.Icc 0 U))
    (hder : ∀ v ∈ Set.Ioo 0 U, HasDerivAt g (g' v) v)
    (heq : ∀ v ∈ Set.Ioo 0 U, c * g' v + β * g v = h v)
    (hh : ∀ v ∈ Set.Ioo 0 U, h v ≤ β * m) (h0 : g 0 = 0) : g U ≤ m := by
  set ψ : ℝ → ℝ := fun v => Real.exp (β / c * v) * (g v - m) with hψ
  have hψd : ∀ v ∈ Set.Ioo 0 U, HasDerivAt ψ
      (Real.exp (β / c * v) * (β / c) * (g v - m) + Real.exp (β / c * v) * g' v) v := by
    intro v hv
    have h1 : HasDerivAt (fun v => Real.exp (β / c * v)) (Real.exp (β / c * v) * (β / c)) v := by
      have := ((hasDerivAt_id' v).const_mul (β / c)).exp
      simpa using this
    exact h1.mul ((hder v hv).sub_const m)
  have hanti : AntitoneOn ψ (Set.Icc 0 U) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 U)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (hcont.sub continuousOn_const)
    · rw [interior_Icc]
      intro v hv
      exact (hψd v hv).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hψd v hv).deriv]
      have e1 := heq v hv
      have e2 := hh v hv
      have hpos : 0 < Real.exp (β / c * v) := Real.exp_pos _
      have : Real.exp (β / c * v) * (β / c) * (g v - m) + Real.exp (β / c * v) * g' v
          = Real.exp (β / c * v) / c * (β * g v + c * g' v - β * m) := by
        field_simp
        ring
      rw [this]
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      linarith
  have key := hanti (Set.left_mem_Icc.mpr hU) (Set.right_mem_Icc.mpr hU) hU
  simp only [ψ, h0, mul_zero, Real.exp_zero, one_mul, zero_sub] at key
  by_contra hcon
  push Not at hcon
  have : 0 < Real.exp (β / c * U) * (g U - m) := mul_pos (Real.exp_pos _) (by linarith)
  linarith

lemma cmp_abs (g g' h : ℝ → ℝ) (c β m U : ℝ) (hc : 0 < c) (hβ : 0 < β) (hm : 0 ≤ m)
    (hU : 0 ≤ U) (hcont : ContinuousOn g (Set.Icc 0 U))
    (hder : ∀ v ∈ Set.Ioo 0 U, HasDerivAt g (g' v) v)
    (heq : ∀ v ∈ Set.Ioo 0 U, c * g' v + β * g v = h v)
    (hh : ∀ v ∈ Set.Ioo 0 U, |h v| ≤ β * m) (h0 : g 0 = 0) : |g U| ≤ m := by
  rw [abs_le]
  constructor
  · have := cmp_upper (fun v => -g v) (fun v => -g' v) (fun v => -h v) c β m U hc hβ hm hU
      hcont.neg (fun v hv => (hder v hv).neg)
      (fun v hv => by have := heq v hv; linarith)
      (fun v hv => by have := hh v hv; have := neg_abs_le (h v); linarith)
      (by simp [h0])
    linarith
  · exact cmp_upper g g' h c β m U hc hβ hm hU hcont hder heq
      (fun v hv => le_trans (le_abs_self _) (hh v hv)) h0

/-- Uniqueness for the homogeneous advanced system with linear growth. -/
lemma uniq (lam c b t p q : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (D0 D1 Df d0 d1 df : ℝ → ℝ)
    (hc0 : ContinuousOn D0 (Set.Ici 0)) (hc1 : ContinuousOn D1 (Set.Ici 0))
    (hcf : ContinuousOn Df (Set.Ici 0))
    (hd0 : ∀ v, 0 < v → HasDerivAt D0 (d0 v) v)
    (hd1 : ∀ v, 0 < v → HasDerivAt D1 (d1 v) v)
    (hdf : ∀ v, 0 < v → HasDerivAt Df (df v) v)
    (h00 : D0 0 = 0) (h10 : D1 0 = 0) (hf0 : Df 0 = 0)
    (heq0 : ∀ v, 0 < v → c * d0 v + (lam * p + 1 / t) * D0 v - lam * p * D1 v = 0)
    (heq1 : ∀ v, 0 < v → c * d1 v + (lam + 1 / t) * D1 v - lam * p * D0 (v + 2 * b) -
      lam * (1 - p) * Df v = 0)
    (heqf : ∀ v, 0 < v → c * df v + (lam + 1 / t) * Df v - lam * p * D0 (v + 2 * b) -
      lam * (1 - p) * q * D0 (v + b) - lam * (1 - p) * (1 - q) * D0 v = 0)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ u, 0 ≤ u → |D0 u| ≤ K * (1 + u) ∧ |D1 u| ≤ K * (1 + u) ∧ |Df u| ≤ K * (1 + u)) :
    ∀ u, 0 ≤ u → D0 u = 0 := by
  set β := lam + 1 / t with hβ
  have hβpos : 0 < β := by positivity
  set θ := lam / β with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hβpos]
    have : 0 < 1 / t := by positivity
    linarith
  have hβθ : β * θ = lam := by rw [hθ]; field_simp
  let B : ℕ → ℝ → ℝ := fun n u => K * θ ^ n * (1 + u + 2 * b * n)
  have hBmono : ∀ n (x y : ℝ), x ≤ y → B n x ≤ B n y := by
    intro n x y hxy
    simp only [B]
    have : 0 ≤ K * θ ^ n := by positivity
    nlinarith
  have hBnn : ∀ n (x : ℝ), 0 ≤ x → 0 ≤ B n x := by
    intro n x hx
    simp only [B]
    positivity
  have claim : ∀ n : ℕ, ∀ u, 0 ≤ u → |D0 u| ≤ B n u ∧ |D1 u| ≤ B n u ∧ |Df u| ≤ B n u := by
    intro n
    induction n with
    | zero =>
      intro u hu
      simpa [B] using hK u hu
    | succ n ih =>
      intro u hu
      set M := B n (u + 2 * b) with hM
      have hMnn : 0 ≤ M := hBnn n _ (by linarith)
      have hBM : θ * M = B (n + 1) u := by
        simp only [hM, B]
        push_cast
        ring
      have bnd : ∀ w, 0 ≤ w → w ≤ u + 2 * b →
          |D0 w| ≤ M ∧ |D1 w| ≤ M ∧ |Df w| ≤ M := by
        intro w hw hwu
        obtain ⟨a1, a2, a3⟩ := ih w hw
        have := hBmono n w (u + 2 * b) hwu
        exact ⟨a1.trans this, a2.trans this, a3.trans this⟩
      have hm : 0 ≤ θ * M := by positivity
      rw [← hBM]
      refine ⟨?_, ?_, ?_⟩
      · apply cmp_abs D0 d0 (fun v => lam * p * D1 v + lam * (1 - p) * D0 v) c β (θ * M) u
          hc hβpos hm hu (hc0.mono (fun x hx => hx.1))
          (fun v hv => hd0 v hv.1)
          (fun v hv => by have := heq0 v hv.1; simp only [hβ]; linarith) _ h00
        intro v hv
        obtain ⟨a1, a2, -⟩ := bnd v hv.1.le (by linarith [hv.2])
        rw [← mul_assoc, hβθ]
        calc |lam * p * D1 v + lam * (1 - p) * D0 v|
            ≤ |lam * p * D1 v| + |lam * (1 - p) * D0 v| := abs_add_le _ _
          _ = lam * p * |D1 v| + lam * (1 - p) * |D0 v| := by
            rw [abs_mul (lam * p), abs_mul (lam * (1 - p)), abs_of_pos (by positivity : 0 < lam * p),
              abs_of_pos (by nlinarith : 0 < lam * (1 - p))]
          _ ≤ lam * p * M + lam * (1 - p) * M := by
            gcongr
          _ = lam * M := by ring
      · apply cmp_abs D1 d1 (fun v => lam * p * D0 (v + 2 * b) + lam * (1 - p) * Df v)
          c β (θ * M) u
          hc hβpos hm hu (hc1.mono (fun x hx => hx.1))
          (fun v hv => hd1 v hv.1)
          (fun v hv => by have := heq1 v hv.1; simp only [hβ]; linarith) _ h10
        intro v hv
        obtain ⟨a1, -, -⟩ := bnd (v + 2 * b) (by linarith [hv.1]) (by linarith [hv.2])
        obtain ⟨-, -, a3⟩ := bnd v hv.1.le (by linarith [hv.2])
        rw [← mul_assoc, hβθ]
        calc |lam * p * D0 (v + 2 * b) + lam * (1 - p) * Df v|
            ≤ |lam * p * D0 (v + 2 * b)| + |lam * (1 - p) * Df v| := abs_add_le _ _
          _ = lam * p * |D0 (v + 2 * b)| + lam * (1 - p) * |Df v| := by
            rw [abs_mul (lam * p), abs_mul (lam * (1 - p)), abs_of_pos (by positivity : 0 < lam * p),
              abs_of_pos (by nlinarith : 0 < lam * (1 - p))]
          _ ≤ lam * p * M + lam * (1 - p) * M := by
            gcongr
          _ = lam * M := by ring
      · apply cmp_abs Df df (fun v => lam * p * D0 (v + 2 * b) + lam * (1 - p) * q * D0 (v + b)
            + lam * (1 - p) * (1 - q) * D0 v)
          c β (θ * M) u
          hc hβpos hm hu (hcf.mono (fun x hx => hx.1))
          (fun v hv => hdf v hv.1)
          (fun v hv => by have := heqf v hv.1; simp only [hβ]; linarith) _ hf0
        intro v hv
        obtain ⟨a1, -, -⟩ := bnd (v + 2 * b) (by linarith [hv.1]) (by linarith [hv.2])
        obtain ⟨a2, -, -⟩ := bnd (v + b) (by linarith [hv.1]) (by linarith [hv.2])
        obtain ⟨a3, -, -⟩ := bnd v hv.1.le (by linarith [hv.2])
        rw [← mul_assoc, hβθ]
        have w1 : 0 < lam * p := by positivity
        have w2 : 0 ≤ lam * (1 - p) * q := by
          have : 0 < lam * (1 - p) := by nlinarith
          positivity
        have w3 : 0 ≤ lam * (1 - p) * (1 - q) := by
          have : 0 < lam * (1 - p) := by nlinarith
          have : 0 ≤ 1 - q := by linarith
          positivity
        calc |lam * p * D0 (v + 2 * b) + lam * (1 - p) * q * D0 (v + b)
              + lam * (1 - p) * (1 - q) * D0 v|
            ≤ |lam * p * D0 (v + 2 * b) + lam * (1 - p) * q * D0 (v + b)|
              + |lam * (1 - p) * (1 - q) * D0 v| := abs_add_le _ _
          _ ≤ |lam * p * D0 (v + 2 * b)| + |lam * (1 - p) * q * D0 (v + b)|
              + |lam * (1 - p) * (1 - q) * D0 v| := by gcongr; exact abs_add_le _ _
          _ = lam * p * |D0 (v + 2 * b)| + lam * (1 - p) * q * |D0 (v + b)|
              + lam * (1 - p) * (1 - q) * |D0 v| := by
            rw [abs_mul (lam * p), abs_mul (lam * (1 - p) * q), abs_mul (lam * (1 - p) * (1 - q)),
              abs_of_pos w1, abs_of_nonneg w2, abs_of_nonneg w3]
          _ ≤ lam * p * M + lam * (1 - p) * q * M + lam * (1 - p) * (1 - q) * M := by
            gcongr
          _ = lam * M := by ring
  intro u hu
  have hlim : Tendsto (fun n : ℕ => B n u) atTop (𝓝 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
    have h2 := tendsto_self_mul_const_pow_of_lt_one hθ0 hθ1
    have := (h1.const_mul (K * (1 + u))).add (h2.const_mul (2 * b * K))
    simp only [mul_zero, add_zero] at this
    refine this.congr (fun n => ?_)
    simp only [B]
    ring
  have hle : |D0 u| ≤ 0 := ge_of_tendsto' hlim (fun n => (claim n u hu).1)
  exact abs_nonpos_iff.mp hle

/-- Exponential-trigonometric building block. -/
noncomputable def ef (A r B C a w : ℝ) (u : ℝ) : ℝ :=
  A * Real.exp (r * u) + Real.exp (a * u) * (B * Real.cos (w * u) + C * Real.sin (w * u))

lemma ef_hasDerivAt (A r B C a w u : ℝ) :
    HasDerivAt (ef A r B C a w) (ef (A * r) r (a * B + w * C) (a * C - w * B) a w u) u := by
  have h1 : HasDerivAt (fun u => Real.exp (r * u)) (Real.exp (r * u) * r) u := by
    simpa using ((hasDerivAt_id' u).const_mul r).exp
  have h2 : HasDerivAt (fun u => Real.exp (a * u)) (Real.exp (a * u) * a) u := by
    simpa using ((hasDerivAt_id' u).const_mul a).exp
  have h3 : HasDerivAt (fun u => Real.cos (w * u)) (-Real.sin (w * u) * w) u := by
    simpa using ((hasDerivAt_id' u).const_mul w).cos
  have h4 : HasDerivAt (fun u => Real.sin (w * u)) (Real.cos (w * u) * w) u := by
    simpa using ((hasDerivAt_id' u).const_mul w).sin
  have := (h1.const_mul A).add (h2.mul ((h3.const_mul B).add (h4.const_mul C)))
  refine this.congr_deriv ?_
  simp only [ef, Pi.add_apply]
  ring

lemma ef_bound (A r B C a w u : ℝ) (hr : r ≤ 0) (ha : a ≤ 0) (hu : 0 ≤ u) :
    |ef A r B C a w u| ≤ |A| + |B| + |C| := by
  have e1 : |Real.exp (r * u)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have e2 : |Real.exp (a * u)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have e3 : |B * Real.cos (w * u) + C * Real.sin (w * u)| ≤ |B| + |C| := by
    calc _ ≤ |B * Real.cos (w * u)| + |C * Real.sin (w * u)| := abs_add_le _ _
      _ ≤ |B| * 1 + |C| * 1 := by
        rw [abs_mul, abs_mul]
        gcongr
        · exact Real.abs_cos_le_one _
        · exact Real.abs_sin_le_one _
      _ = |B| + |C| := by ring
  unfold ef
  calc _ ≤ |A * Real.exp (r * u)| + |Real.exp (a * u) * (B * Real.cos (w * u) + C * Real.sin (w * u))| :=
        abs_add_le _ _
    _ ≤ |A| * 1 + 1 * (|B| + |C|) := by
        rw [abs_mul, abs_mul]
        gcongr
    _ = |A| + |B| + |C| := by ring

/-- Linear growth on the half-line. -/
def LG (f : ℝ → ℝ) : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ u, 0 ≤ u → |f u| ≤ K * (1 + u)

lemma LG.add {f g : ℝ → ℝ} (hf : LG f) (hg : LG g) : LG (fun u => f u + g u) := by
  obtain ⟨K1, hK1, h1⟩ := hf
  obtain ⟨K2, hK2, h2⟩ := hg
  refine ⟨K1 + K2, by positivity, fun u hu => ?_⟩
  calc |f u + g u| ≤ |f u| + |g u| := abs_add_le _ _
    _ ≤ K1 * (1 + u) + K2 * (1 + u) := add_le_add (h1 u hu) (h2 u hu)
    _ = (K1 + K2) * (1 + u) := by ring

lemma LG.smul {f : ℝ → ℝ} (k : ℝ) (hf : LG f) : LG (fun u => k * f u) := by
  obtain ⟨K1, hK1, h1⟩ := hf
  refine ⟨|k| * K1, by positivity, fun u hu => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h1 u hu) (abs_nonneg k)

lemma LG.sub {f g : ℝ → ℝ} (hf : LG f) (hg : LG g) : LG (fun u => f u - g u) := by
  have := hf.add (hg.smul (-1))
  simp only [neg_mul, one_mul, ← sub_eq_add_neg] at this
  exact this

lemma LG.shift {f : ℝ → ℝ} (d : ℝ) (hd : 0 ≤ d) (hf : LG f) : LG (fun u => f (u + d)) := by
  obtain ⟨K1, hK1, h1⟩ := hf
  refine ⟨K1 * (1 + d), by positivity, fun u hu => ?_⟩
  calc |f (u + d)| ≤ K1 * (1 + (u + d)) := h1 _ (by linarith)
    _ ≤ K1 * (1 + d) * (1 + u) := by
        have : 1 + (u + d) ≤ (1 + d) * (1 + u) := by nlinarith
        calc K1 * (1 + (u + d)) ≤ K1 * ((1 + d) * (1 + u)) := mul_le_mul_of_nonneg_left this hK1
          _ = _ := by ring

lemma LG.of_bdd {f : ℝ → ℝ} (M : ℝ) (hf : ∀ u, 0 ≤ u → |f u| ≤ M) : LG f := by
  refine ⟨|M|, abs_nonneg _, fun u hu => ?_⟩
  calc |f u| ≤ M := hf u hu
    _ ≤ |M| := le_abs_self _
    _ ≤ |M| * (1 + u) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)

lemma LG.id : LG (fun u => u) := by
  refine ⟨1, zero_le_one, fun u hu => ?_⟩
  rw [abs_of_nonneg hu]
  linarith

lemma LG.ef (A r B C a w : ℝ) (hr : r ≤ 0) (ha : a ≤ 0) : LG (ef A r B C a w) :=
  LG.of_bdd _ (fun u hu => ef_bound A r B C a w u hr ha hu)

lemma LG.const (k : ℝ) : LG (fun _ => k) := LG.of_bdd |k| (fun _ _ => le_refl _)

lemma cwa0 (V : ℝ → ℝ) (K : ℝ) (hV0 : V 0 = 0) (hK : ∀ u, 0 ≤ u → |V u| ≤ K * u) :
    ContinuousWithinAt V (Set.Ici 0) 0 := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (|K| + 1), by positivity, fun {x} hx hdist => ?_⟩
  have hx0 : (0:ℝ) ≤ x := hx
  rw [Real.dist_eq, hV0, sub_zero]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0, lt_div_iff₀ (by positivity)] at hdist
  calc |V x| ≤ K * x := hK x hx0
    _ ≤ |K| * x := mul_le_mul_of_nonneg_right (le_abs_self K) hx0
    _ ≤ (|K| + 1) * x := by nlinarith
    _ < ε := by linarith

lemma ef_chain (A r B C a w : ℝ) (hr : r ≤ 0) (ha : a ≤ 0) :
    ∃ g1 g2 g3 : ℝ → ℝ, (∀ u, HasDerivAt (ef A r B C a w) (g1 u) u) ∧
      (∀ u, HasDerivAt g1 (g2 u) u) ∧ (∀ u, HasDerivAt g2 (g3 u) u) ∧
      LG g1 ∧ LG g2 ∧ LG g3 :=
  ⟨_, _, _, ef_hasDerivAt A r B C a w, ef_hasDerivAt _ r _ _ a w, ef_hasDerivAt _ r _ _ a w,
    LG.ef _ r _ _ a w hr ha, LG.ef _ r _ _ a w hr ha, LG.ef _ r _ _ a w hr ha⟩

end SMRSol31

open SelfishMiningRuin.ValueFn SMRSol31

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (W : ℕ → Ω → ℝ)
    (ξ ζ : ℕ → Ω → Bool) (lam c b t p q rho1 rho2 rho3 A1 A2 A3 : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprim : Primitives P lam p q W ξ ζ)
    (hrho3 : rho3 ≠ 0)
    (hroots : {rho : ℂ | rho.re < 0 ∧ charFun lam c b t p q rho = 0} =
      {(rho1 : ℂ), Complex.mk rho2 rho3, Complex.mk rho2 (-rho3)})
    (hA : System23 lam c b t p q rho1 rho2 rho3 A1 A2 A3) :
    ∀ u : ℝ, 0 ≤ u →
      Vhat P W ξ ζ c b u t St.zero =
        closedForm lam c b t p q rho1 rho2 rho3 A1 A2 A3 u := by
  have hm1 : (rho1 : ℂ) ∈ {rho : ℂ | rho.re < 0 ∧ charFun lam c b t p q rho = 0} := by
    rw [hroots]; simp
  have hm2 : Complex.mk rho2 rho3 ∈ {rho : ℂ | rho.re < 0 ∧ charFun lam c b t p q rho = 0} := by
    rw [hroots]; simp
  obtain ⟨hr1, hch1⟩ := hm1
  obtain ⟨hr2, hch2⟩ := hm2
  simp only [Complex.ofReal_re] at hr1
  change rho2 < 0 at hr2
  have h3940 := equations_39_40 lam c b t p q rho1 rho2 rho3 A1 A2 A3 hlam hc hb ht hp0 hp1
    hq0 hq1 hch1 hch2
  dsimp only at h3940
  obtain ⟨hE32, hbc⟩ := h3940
  obtain ⟨hF00, hdF00, hd2F00⟩ := hbc.mpr hA
  obtain ⟨h1, h2, h3, hh1, hh2, hh3, L1, L2, L3⟩ := ef_chain A1 rho1 A2 A3 rho2 rho3 hr1.le hr2.le
  obtain ⟨F0, hF0⟩ : ∃ F : ℝ → ℝ, F = fun u => ef A1 rho1 A2 A3 rho2 rho3 u + u +
      Cconst lam c b t p q := ⟨_, rfl⟩
  have hF0eq : closedForm lam c b t p q rho1 rho2 rho3 A1 A2 A3 = F0 := by
    rw [hF0]; rfl
  rw [hF0eq] at hE32 hF00 hdF00 hd2F00
  have hF0d : ∀ u, HasDerivAt F0 (h1 u + 1) u := by
    intro u; rw [hF0]
    exact ((hh1 u).add (hasDerivAt_id' u)).add_const _
  have hD1 : deriv F0 = fun u => h1 u + 1 := funext fun u => (hF0d u).deriv
  have hD2 : iteratedDeriv 2 F0 = h2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hD1]
    funext u; exact ((hh2 u).add_const 1).deriv
  have hD3 : iteratedDeriv 3 F0 = h3 := by
    rw [iteratedDeriv_succ, hD2]
    funext u; exact (hh3 u).deriv
  rw [hD1] at hdF00
  rw [hD2] at hd2F00
  simp only at hdF00
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hp00 : p ≠ 0 := hp0.ne'
  have hp10 : 1 - p ≠ 0 := by linarith
  have hp10' : p - 1 ≠ 0 := by linarith
  have ht0 : t ≠ 0 := ht.ne'
  have hc0 : c ≠ 0 := hc.ne'
  -- the other two closed-form value functions
  obtain ⟨F1, hF1⟩ : ∃ F : ℝ → ℝ, F = fun u =>
      (c * (h1 u + 1) + (lam * p + 1 / t) * F0 u - u / t) / (lam * p) := ⟨_, rfl⟩
  obtain ⟨F1d, hF1d⟩ : ∃ F : ℝ → ℝ, F = fun u =>
      (c * h2 u + (lam * p + 1 / t) * (h1 u + 1) - 1 / t) / (lam * p) := ⟨_, rfl⟩
  obtain ⟨F1dd, hF1dd⟩ : ∃ F : ℝ → ℝ, F = fun u =>
      (c * h3 u + (lam * p + 1 / t) * h2 u) / (lam * p) := ⟨_, rfl⟩
  obtain ⟨Ff, hFf⟩ : ∃ F : ℝ → ℝ, F = fun u =>
      (c * F1d u + (lam + 1 / t) * F1 u - lam * p * F0 (u + 2 * b) - u / t) /
        (lam * (1 - p)) := ⟨_, rfl⟩
  obtain ⟨Ffd, hFfd⟩ : ∃ F : ℝ → ℝ, F = fun u =>
      (c * F1dd u + (lam + 1 / t) * F1d u - lam * p * (h1 (u + 2 * b) + 1) - 1 / t) /
        (lam * (1 - p)) := ⟨_, rfl⟩
  have hF1der : ∀ u, HasDerivAt F1 (F1d u) u := by
    intro u; rw [hF1, hF1d]
    exact (((((hh2 u).add_const 1).const_mul c).add ((hF0d u).const_mul _)).sub
      ((hasDerivAt_id' u).div_const t)).div_const _
  have hF1dder : ∀ u, HasDerivAt F1d (F1dd u) u := by
    intro u; rw [hF1d, hF1dd]
    have := ((((hh3 u).const_mul c).add (((hh2 u).add_const 1).const_mul (lam * p + 1 / t))).sub_const
      (1 / t)).div_const (lam * p)
    exact this
  have hFfder : ∀ u, HasDerivAt Ff (Ffd u) u := by
    intro u; rw [hFf, hFfd]
    have e1 : HasDerivAt (fun u => F0 (u + 2 * b)) (h1 (u + 2 * b) + 1) u :=
      HasDerivAt.comp_add_const u (2 * b) (hF0d (u + 2 * b))
    exact (((((hF1dder u).const_mul c).add ((hF1der u).const_mul _)).sub
      (e1.const_mul _)).sub ((hasDerivAt_id' u).div_const t)).div_const _
  -- the system for the closed forms
  have S1 : ∀ u, c * (h1 u + 1) + (lam * p + 1 / t) * F0 u - lam * p * F1 u - u / t = 0 := by
    intro u; rw [hF1]; field_simp; ring
  have S2 : ∀ u, c * F1d u + (lam + 1 / t) * F1 u - lam * p * F0 (u + 2 * b) -
      lam * (1 - p) * Ff u - u / t = 0 := by
    intro u; rw [hFf]; field_simp; ring
  have S3 : ∀ u, c * Ffd u + (lam + 1 / t) * Ff u - lam * p * F0 (u + 2 * b) -
      lam * (1 - p) * q * F0 (u + b) - lam * (1 - p) * (1 - q) * F0 u - u / t = 0 := by
    intro u
    have hE := hE32 u
    simp only [E32, hD1, hD2, hD3] at hE
    rw [← hE]
    simp only [hFfd, hFf, hF1dd, hF1d, hF1, D1, D2, D3, D4, D5, D6, D7]
    field_simp
    ring
  -- boundary values
  have B1 : F1 0 = 0 := by rw [hF1]; simp [hdF00, hF00]
  have B2 : Ff 0 = 0 := by
    have : c * F1d 0 = lam * p * F0 (2 * b) := by
      rw [hF1d]; simp only [hdF00, hd2F00]; field_simp; ring
    rw [hFf]; simp only [zero_add, B1, zero_div, mul_zero, add_zero, sub_zero, this, sub_self]
  -- linear growth of the closed forms
  have LF0 : LG F0 := by rw [hF0]; exact ((LG.ef _ _ _ _ _ _ hr1.le hr2.le).add LG.id).add (LG.const _)
  have LF1 : LG F1 := by
    have e : F1 = fun u => (1 / (lam * p)) * ((c * (h1 u + 1) + (lam * p + 1 / t) * F0 u) -
        (1 / t) * u) := by rw [hF1]; funext u; ring
    rw [e]
    exact LG.smul _ (LG.sub (LG.add (LG.smul c (L1.add (LG.const 1))) (LG.smul _ LF0))
      (LG.smul _ LG.id))
  have LF1d : LG F1d := by
    have e : F1d = fun u => (1 / (lam * p)) * ((c * h2 u + (lam * p + 1 / t) * (h1 u + 1)) -
        1 / t) := by rw [hF1d]; funext u; ring
    rw [e]
    exact LG.smul _ (LG.sub (LG.add (LG.smul c L2) (LG.smul _ (L1.add (LG.const 1))))
      (LG.const _))
  have LFf : LG Ff := by
    have e : Ff = fun u => (1 / (lam * (1 - p))) * ((c * F1d u + (lam + 1 / t) * F1 u -
        lam * p * F0 (u + 2 * b)) - (1 / t) * u) := by rw [hFf]; funext u; ring
    rw [e]
    exact LG.smul _ (LG.sub (LG.sub (LG.add (LG.smul c LF1d) (LG.smul _ LF1))
      (LG.smul _ (LG.shift (2 * b) (by linarith) LF0))) (LG.smul _ LG.id))
  -- the stochastic value functions
  have h29 := equation_29 P W ξ ζ lam c b t p q hlam hc hb ht hp0 hp1 hq0 hq1 hprim
  dsimp only at h29
  obtain ⟨hV00, hV10, hVf0, hV⟩ := h29
  obtain ⟨Kv, hKv⟩ := Vhat_linear_bound P W ξ ζ lam c b t p q hlam hc hb ht hp0 hp1 hq0 hq1 hprim
  obtain ⟨K0, hK0, hK0b⟩ := LF0
  obtain ⟨K1, hK1, hK1b⟩ := LF1
  obtain ⟨Kf, hKf, hKfb⟩ := LFf
  have contV : ∀ z : St, Vhat P W ξ ζ c b 0 t z = 0 →
      (∀ v, 0 < v → ContinuousAt (fun u => Vhat P W ξ ζ c b u t z) v) →
      ContinuousOn (fun u => Vhat P W ξ ζ c b u t z) (Set.Ici 0) := by
    intro z hz0 hzc v hv
    rcases (show (0:ℝ) ≤ v from hv).eq_or_lt with h | h
    · subst h
      exact cwa0 (fun u => Vhat P W ξ ζ c b u t z) Kv hz0 (fun u hu => hKv z u hu)
    · exact (hzc v h).continuousWithinAt
  have cV0 := contV St.zero hV00 (fun v hv => (hV v hv).1.1.continuousAt)
  have cV1 := contV St.one hV10 (fun v hv => (hV v hv).1.2.1.continuousAt)
  have cVf := contV St.fork hVf0 (fun v hv => (hV v hv).1.2.2.continuousAt)
  have key := uniq lam c b t p q hlam hc hb ht hp0 hp1 hq0 hq1
    (fun u => Vhat P W ξ ζ c b u t St.zero - F0 u)
    (fun u => Vhat P W ξ ζ c b u t St.one - F1 u)
    (fun u => Vhat P W ξ ζ c b u t St.fork - Ff u)
    (fun v => deriv (fun u => Vhat P W ξ ζ c b u t St.zero) v - (h1 v + 1))
    (fun v => deriv (fun u => Vhat P W ξ ζ c b u t St.one) v - F1d v)
    (fun v => deriv (fun u => Vhat P W ξ ζ c b u t St.fork) v - Ffd v)
    (cV0.sub (fun v _ => (hF0d v).continuousAt.continuousWithinAt))
    (cV1.sub (fun v _ => (hF1der v).continuousAt.continuousWithinAt))
    (cVf.sub (fun v _ => (hFfder v).continuousAt.continuousWithinAt))
    (fun v hv => (hV v hv).1.1.sub (hF0d v))
    (fun v hv => (hV v hv).1.2.1.sub (hF1der v))
    (fun v hv => (hV v hv).1.2.2.sub (hFfder v))
    (by simp [hV00, hF00]) (by simp [hV10, B1]) (by simp [hVf0, B2])
    (fun v hv => by
      have e := (hV v hv).2.1
      have s := S1 v
      linear_combination -e - s)
    (fun v hv => by
      have e := (hV v hv).2.2.1
      have s := S2 v
      linear_combination -e - s)
    (fun v hv => by
      have e := (hV v hv).2.2.2
      have s := S3 v
      linear_combination -e - s)
    (|Kv| + K0 + K1 + Kf) (by positivity)
    (by
      intro u hu
      have hv : ∀ z, |Vhat P W ξ ζ c b u t z| ≤ |Kv| * (1 + u) := by
        intro z
        calc _ ≤ Kv * u := hKv z u hu
          _ ≤ |Kv| * u := mul_le_mul_of_nonneg_right (le_abs_self _) hu
          _ ≤ |Kv| * (1 + u) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      have a0 := hK0b u hu
      have a1 := hK1b u hu
      have af := hKfb u hu
      have hu1 : 0 ≤ 1 + u := by linarith
      refine ⟨?_, ?_, ?_⟩
      · calc _ ≤ |Vhat P W ξ ζ c b u t St.zero| + |F0 u| := abs_sub _ _
          _ ≤ |Kv| * (1 + u) + K0 * (1 + u) := add_le_add (hv _) a0
          _ ≤ (|Kv| + K0 + K1 + Kf) * (1 + u) := by nlinarith
      · calc _ ≤ |Vhat P W ξ ζ c b u t St.one| + |F1 u| := abs_sub _ _
          _ ≤ |Kv| * (1 + u) + K1 * (1 + u) := add_le_add (hv _) a1
          _ ≤ (|Kv| + K0 + K1 + Kf) * (1 + u) := by nlinarith
      · calc _ ≤ |Vhat P W ξ ζ c b u t St.fork| + |Ff u| := abs_sub _ _
          _ ≤ |Kv| * (1 + u) + Kf * (1 + u) := add_le_add (hv _) af
          _ ≤ (|Kv| + K0 + K1 + Kf) * (1 + u) := by nlinarith)
  intro u hu
  have := key u hu
  rw [hF0eq]
  linarith
