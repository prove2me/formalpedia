-- Prove2me | solution 1 for SupplyChainTheory.shang_song_bounds_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:11:22.590352+00:00
-- url     : https://prove2.me/submissions/5df44f78-72ac-4ce2-8882-281b9a729dd2

import Definitions.Def_SupplyChainTheory_multiechelon

open MeasureTheory

namespace SupplyChainTheory

/-- Lipschitz-type regularity of a real function. -/
def LipR (f : ℝ → ℝ) : Prop := ∃ K : ℝ, ∀ x y, |f x - f y| ≤ K * |x - y|

lemma LipR.add {f g : ℝ → ℝ} (hf : LipR f) (hg : LipR g) : LipR (fun x => f x + g x) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨L, hL⟩ := hg
  refine ⟨K + L, fun x y => ?_⟩
  have h1 := hK x y
  have h2 := hL x y
  calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
    _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
    _ ≤ (K + L) * |x - y| := by linarith

lemma LipR.sub {f g : ℝ → ℝ} (hf : LipR f) (hg : LipR g) : LipR (fun x => f x - g x) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨L, hL⟩ := hg
  refine ⟨K + L, fun x y => ?_⟩
  have h1 := hK x y
  have h2 := hL x y
  calc |f x - g x - (f y - g y)| = |(f x - f y) - (g x - g y)| := by ring_nf
    _ ≤ |f x - f y| + |g x - g y| := abs_sub _ _
    _ ≤ (K + L) * |x - y| := by linarith

lemma LipR.const_mul (c : ℝ) {f : ℝ → ℝ} (hf : LipR f) : LipR (fun x => c * f x) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨|c| * K, fun x y => ?_⟩
  have h1 := hK x y
  calc |c * f x - c * f y| = |c| * |f x - f y| := by rw [← mul_sub, abs_mul]
    _ ≤ |c| * (K * |x - y|) := by gcongr
    _ = |c| * K * |x - y| := by ring

lemma LipR.const (c : ℝ) : LipR (fun _ => c) := ⟨0, fun x y => by simp⟩

lemma LipR.id : LipR (fun x => x) := ⟨1, fun x y => by simp⟩

lemma LipR.comp_sub (y : ℝ) : LipR (fun d : ℝ => y - d) := ⟨1, fun x z => by
  have : y - x - (y - z) = -(x - z) := by ring
  rw [this, abs_neg]; simp⟩

lemma LipR.comp_lin {f : ℝ → ℝ} (hf : LipR f) (y : ℝ) : LipR (fun d => f (y - d)) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨K, fun x z => ?_⟩
  have := hK (y - x) (y - z)
  have e : |y - x - (y - z)| = |x - z| := by
    rw [show y - x - (y - z) = -(x - z) by ring, abs_neg]
  rwa [e] at this

lemma LipR.comp_min (S : ℝ) {f : ℝ → ℝ} (hf : LipR f) : LipR (fun x => f (min S x)) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨K, fun x y => ?_⟩
  refine (hK _ _).trans ?_
  have hK0 : 0 ≤ K := by
    have := hK 0 1
    have h2 : (0:ℝ) ≤ |f 0 - f 1| := abs_nonneg _
    simp at this
    linarith
  apply mul_le_mul_of_nonneg_left _ hK0
  rw [abs_le]
  constructor <;> rcases le_total S x with h1 | h1 <;> rcases le_total S y with h2 | h2 <;>
    simp [min_eq_left, min_eq_right, h1, h2] <;>
    first
    | (have := le_abs_self (x - y); have := neg_abs_le (x - y); linarith)
    | skip

lemma LipR.max0 : LipR (fun x : ℝ => max x 0) := ⟨1, fun x y => by
  have := abs_max_sub_max_le_abs x y 0
  simpa using this⟩

lemma LipR.cont {f : ℝ → ℝ} (hf : LipR f) : Continuous f := by
  obtain ⟨K, hK⟩ := hf
  have : LipschitzWith (Real.toNNReal K) f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [Real.dist_eq, Real.coe_toNNReal'] using (hK x y).trans (by
      gcongr; exact le_max_left _ _)
  exact this.continuous

lemma LipR.integrable {f : ℝ → ℝ} (hf : LipR f) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (y : ℝ) : Integrable (fun d => f (y - d)) μ := by
  obtain ⟨K, hK⟩ := hf
  have hc := (LipR.cont ⟨K, hK⟩).comp (continuous_const.sub continuous_id : Continuous fun d : ℝ => y - d)
  refine Integrable.mono' (g := fun d => |f y| + |K| * |d|) ?_ hc.aestronglyMeasurable ?_
  · exact (integrable_const _).add (hμ.norm.const_mul _)
  · refine Filter.Eventually.of_forall (fun d => ?_)
    have h := hK (y - d) y
    have : |f (y - d)| ≤ |f y| + |f (y - d) - f y| := by
      calc |f (y - d)| = |f y + (f (y - d) - f y)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h3 : |y - d - y| = |d| := by rw [show y - d - y = -d by ring, abs_neg]
    rw [h3] at h
    simp only [Real.norm_eq_abs]
    nlinarith [le_abs_self K, abs_nonneg d]

/-- The "shifted expectation" operator. -/
noncomputable def Tm (μ : Measure ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ d, f (y - d) ∂μ

lemma Tm_lip {f : ℝ → ℝ} (hf : LipR f) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) : LipR (Tm μ f) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨K, fun x y => ?_⟩
  unfold Tm
  have i1 := LipR.integrable ⟨K, hK⟩ μ hμ x
  have i2 := LipR.integrable ⟨K, hK⟩ μ hμ y
  rw [← integral_sub i1 i2]
  have : |∫ d, (f (x - d) - f (y - d)) ∂μ| ≤ ∫ d, |f (x - d) - f (y - d)| ∂μ := by
    simpa using norm_integral_le_integral_norm (μ := μ) (fun d => f (x - d) - f (y - d))
  refine this.trans ?_
  have : ∫ d, |f (x - d) - f (y - d)| ∂μ ≤ ∫ d, K * |x - y| ∂μ := by
    apply integral_mono (i1.sub i2).abs (integrable_const _)
    intro d
    have := hK (x - d) (y - d)
    simpa using this
  simpa using this

lemma Tm_mono {f : ℝ → ℝ} (hf : LipR f) (hm : Monotone f) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) : Monotone (Tm μ f) := by
  intro x y hxy
  unfold Tm
  exact integral_mono (hf.integrable μ hμ x) (hf.integrable μ hμ y) (fun d => hm (by linarith))

lemma Tm_conv {f : ℝ → ℝ} (hf : LipR f) (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) (y : ℝ) :
    Tm (μ.conv ν) f y = Tm ν (Tm μ f) y := by
  obtain ⟨K, hK⟩ := hf
  have hfc := LipR.cont ⟨K, hK⟩
  unfold Tm
  unfold Measure.conv
  rw [integral_map (by fun_prop) (by
    exact (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)]
  have hint : Integrable (fun z : ℝ × ℝ => f (y - (z.1 + z.2))) (μ.prod ν) := by
    refine Integrable.mono' (g := fun z : ℝ × ℝ => |f y| + |K| * (|z.1| + |z.2|)) ?_ ?_ ?_
    · exact (integrable_const _).add (((hμ.norm.comp_fst ν).add (hν.norm.comp_snd μ)).const_mul _)
    · exact (hfc.comp (continuous_const.sub (continuous_fst.add continuous_snd))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z => ?_)
      have h := hK (y - (z.1 + z.2)) y
      have : |f (y - (z.1 + z.2))| ≤ |f y| + |f (y - (z.1 + z.2)) - f y| := by
        calc |f (y - (z.1 + z.2))| = |f y + (f (y - (z.1 + z.2)) - f y)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have h3 : |y - (z.1 + z.2) - y| ≤ |z.1| + |z.2| := by
        rw [show y - (z.1 + z.2) - y = -(z.1 + z.2) by ring, abs_neg]; exact abs_add_le _ _
      have hK0 : 0 ≤ |K| := abs_nonneg _
      simp only [Real.norm_eq_abs]
      nlinarith [le_abs_self K, abs_nonneg z.1, abs_nonneg z.2, mul_le_mul_of_nonneg_left h3 hK0,
        mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg (y - (z.1 + z.2) - y))]
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
  simp only [Tm]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  show f (y - (a + b)) = f (y - b - a)
  congr 1; ring


lemma Tm_lin {g : ℝ → ℝ} (hg : LipR g) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (a y : ℝ) :
    Tm μ (fun z => a * z + g z) y = a * (y - ∫ d, d ∂μ) + Tm μ g y := by
  unfold Tm
  have i1 : Integrable (fun d => a * (y - d)) μ :=
    (LipR.integrable (LipR.const_mul a LipR.id) μ hμ y)
  rw [integral_add i1 (hg.integrable μ hμ y), integral_const_mul, integral_sub (integrable_const _) hμ]
  simp

lemma Tm_const (μ : Measure ℝ) [IsProbabilityMeasure μ] (c y : ℝ) : Tm μ (fun _ => c) y = c := by
  simp [Tm]

lemma Tm_nonneg {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) (μ : Measure ℝ) (y : ℝ) : 0 ≤ Tm μ g y :=
  integral_nonneg (fun d => hg _)

lemma Tm_add {f g : ℝ → ℝ} (hf : LipR f) (hg : LipR g) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Tm μ (fun z => f z + g z) y = Tm μ f y + Tm μ g y :=
  integral_add (hf.integrable μ hμ y) (hg.integrable μ hμ y)

lemma Tm_sub {f g : ℝ → ℝ} (hf : LipR f) (hg : LipR g) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Tm μ (fun z => f z - g z) y = Tm μ f y - Tm μ g y :=
  integral_sub (hf.integrable μ hμ y) (hg.integrable μ hμ y)

lemma Tm_cmul {f : ℝ → ℝ} (c : ℝ) (μ : Measure ℝ) (y : ℝ) :
    Tm μ (fun z => c * f z) y = c * Tm μ f y := integral_const_mul _ _

lemma Tm_mono' {f g : ℝ → ℝ} (hf : LipR f) (hg : LipR g) (hfg : ∀ x, f x ≤ g x)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (y : ℝ) : Tm μ f y ≤ Tm μ g y :=
  integral_mono (hf.integrable μ hμ y) (hg.integrable μ hμ y) (fun d => hfg _)

lemma Tm_convex {f : ℝ → ℝ} (hf : LipR f) (hc : ConvexOn ℝ Set.univ f) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ) :
    ConvexOn ℝ Set.univ (Tm μ f) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Tm]
  have i1 := hf.integrable μ hμ x
  have i2 := hf.integrable μ hμ y
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul a) (i2.const_mul b)]
  apply integral_mono ((LipR.integrable hf μ hμ _)) ((i1.const_mul a).add (i2.const_mul b))
  intro d
  have := hc.2 (Set.mem_univ (x - d)) (Set.mem_univ (y - d)) ha hb hab
  simp only [smul_eq_mul] at this
  have e : a * x + b * y - d = a * (x - d) + b * (y - d) := by
    have : d = (a + b) * d := by rw [hab]; ring
    nlinarith
  show f (a * x + b * y - d) ≤ a * f (x - d) + b * f (y - d)
  rw [e]
  exact this

lemma tildeLaw_prob (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)] :
    ∀ k, IsProbabilityMeasure (tildeLaw D k)
  | 0 => by
    show IsProbabilityMeasure (Measure.dirac (0:ℝ))
    infer_instance
  | k + 1 => by
    haveI := tildeLaw_prob D k
    show IsProbabilityMeasure ((tildeLaw D k).conv (D (k + 1)))
    infer_instance

lemma tildeLaw_int (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) :
    ∀ k, Integrable (fun x : ℝ => x) (tildeLaw D k)
  | 0 => by
    show Integrable (fun x : ℝ => x) (Measure.dirac (0:ℝ))
    exact integrable_dirac (by simp)
  | k + 1 => by
    haveI := tildeLaw_prob D k
    have ih := tildeLaw_int D hD k
    show Integrable (fun x : ℝ => x) ((tildeLaw D k).conv (D (k + 1)))
    unfold Measure.conv
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact (ih.comp_fst (D (k+1))).add ((hD (k+1)).comp_snd (tildeLaw D k))

lemma tildeLaw_mean (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (k : ℕ) :
    ∫ s, s ∂(tildeLaw D (k + 1)) = ∫ s, s ∂(tildeLaw D k) + ∫ d, d ∂(D (k + 1)) := by
  haveI := tildeLaw_prob D k
  have h := Tm_conv (f := fun z => (-1) * z) (LipR.const_mul (-1) LipR.id) (tildeLaw D k) (D (k+1))
    (tildeLaw_int D hD k) (hD (k+1)) 0
  unfold Tm at h
  have e1 : ∫ d, (-1) * (0 - d) ∂(tildeLaw D k).conv (D (k+1)) = ∫ s, s ∂(tildeLaw D (k + 1)) := by
    congr 1; ext d; ring
  rw [e1] at h
  rw [show tildeLaw D (k+1) = (tildeLaw D k).conv (D (k+1)) from rfl] at *
  rw [h]
  have e2 : ∀ b : ℝ, ∫ a, (-1) * (0 - b - a) ∂(tildeLaw D k) = b + ∫ s, s ∂(tildeLaw D k) := by
    intro b
    have : ∀ a : ℝ, (-1) * (0 - b - a) = b + a := fun a => by ring
    simp_rw [this]
    rw [integral_add (integrable_const _) (tildeLaw_int D hD k)]
    simp
  simp_rw [e2]
  rw [integral_add (hD (k+1)) (integrable_const _)]
  simp; ring

/-- `E[(D̃_k - x)^+]`. -/
noncomputable def Nf (D : ℕ → Measure ℝ) (k : ℕ) : ℝ → ℝ :=
  Tm (tildeLaw D k) (fun z => max (-z) 0)

lemma LipR.neg_max0 : LipR (fun z : ℝ => max (-z) 0) := by
  have := LipR.max0.comp_lin 0
  obtain ⟨K, hK⟩ := this
  refine ⟨K, fun x y => ?_⟩
  simpa using hK x y

lemma Nf_zero (D : ℕ → Measure ℝ) (x : ℝ) : Nf D 0 x = max (-x) 0 := by
  simp [Nf, Tm, tildeLaw]

lemma Nf_succ (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (k : ℕ) (y : ℝ) :
    Nf D (k + 1) y = Tm (D (k + 1)) (Nf D k) y := by
  haveI := tildeLaw_prob D k
  unfold Nf
  exact Tm_conv LipR.neg_max0 _ _ (tildeLaw_int D hD k) (hD (k+1)) y

lemma Nf_lip (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (k : ℕ) : LipR (Nf D k) := by
  haveI := tildeLaw_prob D k
  exact Tm_lip LipR.neg_max0 _ (tildeLaw_int D hD k)

lemma Nf_nonneg (D : ℕ → Measure ℝ) (k : ℕ) (x : ℝ) : 0 ≤ Nf D k x :=
  Tm_nonneg (fun z => le_max_right _ _) _ _

lemma Nf_anti (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (k : ℕ) : Antitone (Nf D k) := by
  haveI := tildeLaw_prob D k
  intro x y hxy
  unfold Nf Tm
  exact integral_mono (LipR.neg_max0.integrable _ (tildeLaw_int D hD k) y)
    (LipR.neg_max0.integrable _ (tildeLaw_int D hD k) x) (fun d => by
      simp only; apply max_le_max _ le_rfl; linarith)

lemma Nf_convex (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (k : ℕ) : ConvexOn ℝ Set.univ (Nf D k) := by
  induction k with
  | zero =>
    have : Nf D 0 = fun x => max (-x) 0 := funext (Nf_zero D)
    rw [this]
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    apply max_le
    · have h1 := le_max_left (-x) 0
      have h2 := le_max_left (-y) 0
      nlinarith
    · have h1 := le_max_right (-x) 0
      have h2 := le_max_right (-y) 0
      nlinarith
  | succ k ih =>
    have : Nf D (k+1) = Tm (D (k+1)) (Nf D k) := funext (Nf_succ D hD k)
    rw [this]
    exact Tm_convex (Nf_lip D hD k) ih _ (hD (k+1))

lemma Em_nonneg (μ : Measure ℝ) (h0 : μ (Set.Iio 0) = 0) : 0 ≤ ∫ d, d ∂μ := by
  apply integral_nonneg_of_ae
  rw [Filter.EventuallyLE, ae_iff]
  have : {a : ℝ | ¬ (0 ≤ a)} = Set.Iio 0 := by ext a; simp
  simp only [Pi.zero_apply, this]
  exact h0

/-- `x + N_k(x)` is monotone and nonnegative. -/
lemma Nf_id_prop (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (hD0 : ∀ j, D j (Set.Iio 0) = 0) (k : ℕ) :
    Monotone (fun x => x + Nf D k x) ∧ ∀ x, 0 ≤ x + Nf D k x := by
  induction k with
  | zero =>
    have : ∀ x, x + Nf D 0 x = max x 0 := by
      intro x; rw [Nf_zero]
      rcases le_total x 0 with h | h
      · simp [h]
      · simp [h]
    simp_rw [this]
    exact ⟨fun x y h => max_le_max h le_rfl, fun x => le_max_right _ _⟩
  | succ k ih =>
    have e : ∀ y, y + Nf D (k+1) y = Tm (D (k+1)) (fun z => 1 * z + Nf D k z) y
        + ∫ d, d ∂(D (k+1)) := by
      intro y
      rw [Tm_lin (Nf_lip D hD k) _ (hD (k+1)), Nf_succ D hD k]
      ring
    have e' : (fun y => y + Nf D (k+1) y) = fun y => Tm (D (k+1)) (fun z => 1 * z + Nf D k z) y
        + ∫ d, d ∂(D (k+1)) := funext e
    have hl : LipR (fun z => 1 * z + Nf D k z) := (LipR.const_mul 1 LipR.id).add (Nf_lip D hD k)
    refine ⟨?_, ?_⟩
    · rw [e']
      intro x y hxy
      have := Tm_mono hl (fun a b hab => by simpa using ih.1 hab) _ (hD (k+1)) hxy
      simp only
      linarith
    · intro x
      rw [e]
      have := Tm_nonneg (g := fun z => 1 * z + Nf D k z) (fun z => by simpa using ih.2 z) (D (k+1)) x
      have := Em_nonneg (D (k+1)) (hD0 (k+1))
      linarith


lemma Nf_succ_id (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (k : ℕ) (y : ℝ) :
    y + Nf D (k+1) y = Tm (D (k+1)) (fun z => 1 * z + Nf D k z) y + ∫ d, d ∂(D (k+1)) := by
  rw [Tm_lin (Nf_lip D hD k) _ (hD (k+1)), Nf_succ D hD k]
  ring

lemma Tm_comb {f g : ℝ → ℝ} (hf : LipR f) (hg : LipR g) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (a b c d y : ℝ) :
    Tm μ (fun z => a * z + b + c * f z + d * g z) y
      = a * (y - ∫ d, d ∂μ) + b + c * Tm μ f y + d * Tm μ g y := by
  have h1 : LipR (fun z => b + c * f z + d * g z) :=
    ((LipR.const b).add (hf.const_mul c)).add (hg.const_mul d)
  have e : (fun z => a * z + b + c * f z + d * g z) = fun z => a * z + (b + c * f z + d * g z) := by
    funext z; ring
  rw [e, Tm_lin h1 μ hμ,
    Tm_add ((LipR.const b).add (hf.const_mul c)) (hg.const_mul d) μ hμ,
    Tm_add (LipR.const b) (hf.const_mul c) μ hμ, Tm_const, Tm_cmul, Tm_cmul]
  ring

noncomputable def Hs (h : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 k, h i
noncomputable def cc (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (k : ℕ) : ℝ := p + localHolding N h (k + 1)
noncomputable def Ek (D : ℕ → Measure ℝ) (k : ℕ) : ℝ := ∫ d, d ∂(D k)

lemma Hs_succ (h : ℕ → ℝ) (k : ℕ) : Hs h (k+1) = Hs h k + h (k+1) := by
  unfold Hs; exact Finset.sum_Icc_succ_top (by omega) _

lemma Hs_nonneg {h : ℕ → ℝ} (hh : ∀ j, 0 ≤ h j) (k : ℕ) : 0 ≤ Hs h k :=
  Finset.sum_nonneg (fun i _ => hh i)

lemma loc_nonneg {h : ℕ → ℝ} (hh : ∀ j, 0 ≤ h j) (N j : ℕ) : 0 ≤ localHolding N h j :=
  Finset.sum_nonneg (fun i _ => hh i)

lemma cc_nonneg {h : ℕ → ℝ} {p : ℝ} (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (N k : ℕ) :
    0 ≤ cc N h p k := add_nonneg hp (loc_nonneg hh _ _)

lemma cc_step {N : ℕ} {h : ℕ → ℝ} {p : ℝ} {k : ℕ} (hk : k + 1 ≤ N) :
    cc N h p k = h (k+1) + cc N h p (k+1) := by
  unfold cc localHolding
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hk, Finset.sum_insert (by simp)]
  ring

lemma csG_succ (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) (k : ℕ) (y : ℝ) :
    csG N h p D S (k+1) y = Tm (D (k+1)) (fun z => h (k+1) * z + csBar N h p D S k z) y := by
  simp [csG, csHat, Tm]

lemma csBar_succ (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    csBar N h p D S (k+1) x = csG N h p D S (k+1) (min (S (k+1)) x) := by
  rw [csG_succ]; rfl

lemma csBar_zero (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) (x : ℝ) :
    csBar N h p D S 0 x = cc N h p 0 * Nf D 0 x := by
  rw [Nf_zero]; rfl

lemma csBar_lip (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (S : ℕ → ℝ) :
    ∀ k, LipR (csBar N h p D S k) ∧ LipR (csG N h p D S (k+1))
  | 0 => by
    have h0 : LipR (csBar N h p D S 0) := by
      have : csBar N h p D S 0 = fun x => (cc N h p 0) * max (-x) 0 := by
        funext x; rw [csBar_zero, Nf_zero]
      rw [this]; exact LipR.const_mul _ LipR.neg_max0
    refine ⟨h0, ?_⟩
    have : csG N h p D S (0+1) = Tm (D (0+1)) (fun z => h (0+1) * z + csBar N h p D S 0 z) :=
      funext (csG_succ N h p D S 0)
    rw [this]
    exact Tm_lip ((LipR.const_mul _ LipR.id).add h0) _ (hD _)
  | k + 1 => by
    have ih := (csBar_lip N h p D hD S k).2
    have h0 : LipR (csBar N h p D S (k+1)) := by
      have : csBar N h p D S (k+1) = fun x => csG N h p D S (k+1) (min (S (k+1)) x) :=
        funext (csBar_succ N h p D S k)
      rw [this]; exact LipR.comp_min _ ih
    refine ⟨h0, ?_⟩
    have : csG N h p D S (k+1+1) = Tm (D (k+1+1)) (fun z => h (k+1+1) * z + csBar N h p D S (k+1) z) :=
      funext (csG_succ N h p D S (k+1))
    rw [this]
    exact Tm_lip ((LipR.const_mul _ LipR.id).add h0) _ (hD _)


noncomputable def Uf (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Hs h k * (x - Ek D k) + (Hs h k + cc N h p k) * Nf D k x

noncomputable def Lf (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  h k * (x - Ek D k) + (h k + cc N h p k) * Nf D k x

structure Inv (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) (k : ℕ) : Prop where
  pl : ∀ x, cc N h p k * Nf D k x ≤ csBar N h p D S k x
  ml : Monotone (fun x => csBar N h p D S k x - cc N h p k * Nf D k x)
  pu : ∀ x, csBar N h p D S k x ≤ Uf N h p D k x
  mu : Monotone (fun x => Uf N h p D k x - csBar N h p D S k x)

lemma Uf_convex (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (k : ℕ) :
    ConvexOn ℝ Set.univ (Uf N h p D k) := by
  have hco : 0 ≤ Hs h k + cc N h p k := add_nonneg (Hs_nonneg hh k) (cc_nonneg hh hp N k)
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hN := (Nf_convex D hD k).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hN ⊢
  have hb' : b = 1 - a := by linarith
  subst hb'
  unfold Uf
  nlinarith [mul_le_mul_of_nonneg_left hN hco]

lemma Uf_quasi (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (k : ℕ)
    {s a b : ℝ} (hsa : s ≤ a) (hab : a ≤ b) (hsb : Uf N h p D k s ≤ Uf N h p D k b) :
    Uf N h p D k a ≤ Uf N h p D k b := by
  have := (Uf_convex N h p D hD hh hp k).le_on_segment (Set.mem_univ s) (Set.mem_univ b)
    (show a ∈ segment ℝ s b by rw [segment_eq_Icc (hsa.trans hab)]; exact ⟨hsa, hab⟩)
  rwa [max_eq_right hsb] at this

section step
variable (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
  (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (S : ℕ → ℝ)
include hD

lemma csG_split (k : ℕ) (y : ℝ) :
    csG N h p D S (k+1) y = h (k+1) * (y - Ek D (k+1)) + Tm (D (k+1)) (csBar N h p D S k) y := by
  rw [csG_succ, Tm_lin (csBar_lip N h p D hD S k).1 _ (hD _)]; rfl

lemma lower_diff (k : ℕ) (hk : k + 1 ≤ N) (y : ℝ) :
    csG N h p D S (k+1) y - Lf N h p D (k+1) y
      = Tm (D (k+1)) (fun z => csBar N h p D S k z - cc N h p k * Nf D k z) y := by
  rw [Tm_sub (csBar_lip N h p D hD S k).1 (LipR.const_mul _ (Nf_lip D hD k)) _ (hD _),
    Tm_cmul, csG_split N h p D hD S k y]
  unfold Lf
  rw [cc_step hk, ← Nf_succ D hD k]
  unfold Ek
  ring

lemma upper_diff (k : ℕ) (hk : k + 1 ≤ N) (y : ℝ) :
    Uf N h p D (k+1) y - csG N h p D S (k+1) y
      = Tm (D (k+1)) (fun z => Uf N h p D k z - csBar N h p D S k z) y + Hs h k * Ek D k := by
  have hc := Tm_comb (Nf_lip D hD k) (csBar_lip N h p D hD S k).1 (D (k+1)) (hD _)
    (Hs h k) (-(Hs h k * Ek D k)) (Hs h k + cc N h p k) (-1) y
  have fe : (fun z => Uf N h p D k z - csBar N h p D S k z)
      = fun z => Hs h k * z + -(Hs h k * Ek D k) + (Hs h k + cc N h p k) * Nf D k z
          + (-1) * csBar N h p D S k z := by
    funext z; unfold Uf; ring
  rw [fe, hc, csG_split N h p D hD S k y]
  unfold Uf
  rw [Hs_succ, cc_step hk, ← Nf_succ D hD k]
  unfold Ek
  ring

end step


section step2
variable (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
  (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (S : ℕ → ℝ)
include hD

lemma facts_lower (k : ℕ) (hk : k + 1 ≤ N) (I : Inv N h p D S k) :
    (∀ y, Lf N h p D (k+1) y ≤ csG N h p D S (k+1) y) ∧
    Monotone (fun y => csG N h p D S (k+1) y - Lf N h p D (k+1) y) := by
  have hl : LipR (fun z => csBar N h p D S k z - cc N h p k * Nf D k z) :=
    (csBar_lip N h p D hD S k).1.sub (LipR.const_mul _ (Nf_lip D hD k))
  constructor
  · intro y
    have := Tm_nonneg (g := fun z => csBar N h p D S k z - cc N h p k * Nf D k z)
      (fun z => sub_nonneg.2 (I.pl z)) (D (k+1)) y
    rw [← lower_diff N h p D hD S k hk y] at this
    linarith
  · intro x y hxy
    simp only [lower_diff N h p D hD S k hk]
    exact Tm_mono hl I.ml (D (k+1)) (hD (k+1)) hxy

lemma facts_upper (hh : ∀ j, 0 ≤ h j) (k : ℕ) (hk : k + 1 ≤ N) (hD0 : ∀ j, D j (Set.Iio 0) = 0)
    (I : Inv N h p D S k) :
    (∀ y, csG N h p D S (k+1) y ≤ Uf N h p D (k+1) y) ∧
    Monotone (fun y => Uf N h p D (k+1) y - csG N h p D S (k+1) y) := by
  have hl : LipR (fun z => Uf N h p D k z - csBar N h p D S k z) := by
    unfold Uf
    exact (((LipR.const_mul _ (LipR.id.sub (LipR.const _)))).add
      (LipR.const_mul _ (Nf_lip D hD k))).sub (csBar_lip N h p D hD S k).1
  have hE := Em_nonneg (D k) (hD0 k)
  have hH := Hs_nonneg hh k
  constructor
  · intro y
    have := Tm_nonneg (g := fun z => Uf N h p D k z - csBar N h p D S k z)
      (fun z => sub_nonneg.2 (I.pu z)) (D (k+1)) y
    have h2 := upper_diff N h p D hD S k hk y
    have h3 : 0 ≤ Hs h k * Ek D k := mul_nonneg hH hE
    linarith
  · intro x y hxy
    simp only [upper_diff N h p D hD S k hk]
    have := Tm_mono hl I.mu (D (k+1)) (hD (k+1)) hxy
    linarith

lemma inv_succ (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (hD0 : ∀ j, D j (Set.Iio 0) = 0)
    (k : ℕ) (hk : k + 1 ≤ N) (I : Inv N h p D S k)
    (hmin : ∀ y, csG N h p D S (k+1) (S (k+1)) ≤ csG N h p D S (k+1) y) :
    Inv N h p D S (k+1) := by
  obtain ⟨hL1, hL2⟩ := facts_lower N h p D hD S k hk I
  obtain ⟨hU1, hU2⟩ := facts_upper N h p D hD S hh k hk hD0 I
  have hc1 : 0 ≤ cc N h p (k+1) := cc_nonneg hh hp N (k+1)
  have hh' : 0 ≤ h (k+1) := hh (k+1)
  have hNid := Nf_id_prop D hD hD0 (k+1)
  have hq0 : ∀ y, 0 ≤ y + Nf D (k+1) y - Ek D (k+1) := by
    intro y
    have h1 := Nf_succ_id D hD k y
    have h2 := Tm_nonneg (g := fun z => 1 * z + Nf D k z)
      (fun z => by simpa using (Nf_id_prop D hD hD0 k).2 z) (D (k+1)) y
    unfold Ek
    linarith
  have hFq_eq : ∀ y, csG N h p D S (k+1) y - cc N h p (k+1) * Nf D (k+1) y
      = (csG N h p D S (k+1) y - Lf N h p D (k+1) y)
        + h (k+1) * (y + Nf D (k+1) y - Ek D (k+1)) := by
    intro y; unfold Lf; ring
  have hFq_nonneg : ∀ y, 0 ≤ csG N h p D S (k+1) y - cc N h p (k+1) * Nf D (k+1) y := by
    intro y
    rw [hFq_eq]
    have := hL1 y
    have := mul_nonneg hh' (hq0 y)
    linarith
  have hFq_mono : Monotone (fun y => csG N h p D S (k+1) y - cc N h p (k+1) * Nf D (k+1) y) := by
    intro x y hxy
    simp only [hFq_eq]
    have h1 := hL2 hxy
    have h2 := hNid.1 hxy
    simp only at h1 h2
    have := mul_le_mul_of_nonneg_left (show x + Nf D (k+1) x - Ek D (k+1) ≤ y + Nf D (k+1) y - Ek D (k+1)
      by linarith) hh'
    linarith
  have hθ : Monotone (fun x => Nf D (k+1) (min (S (k+1)) x) - Nf D (k+1) x) := by
    have ha := Nf_anti D hD (k+1)
    intro x y hxy
    simp only
    rcases le_total y (S (k+1)) with h1 | h1
    · rw [min_eq_right h1, min_eq_right (hxy.trans h1)]; simp
    · rcases le_total x (S (k+1)) with h2 | h2
      · rw [min_eq_right h2, min_eq_left h1]
        have := ha h1
        have := ha (min_le_left (S (k+1)) y)
        simp only [sub_self]
        have := ha h1
        linarith
      · rw [min_eq_left h2, min_eq_left h1]
        have := ha hxy
        linarith
  have hFmin : ∀ x, csG N h p D S (k+1) (min (S (k+1)) x) ≤ csG N h p D S (k+1) x := by
    intro x
    rcases le_total x (S (k+1)) with hx | hx
    · rw [min_eq_right hx]
    · rw [min_eq_left hx]; exact hmin x
  have hUb : ∀ b, S (k+1) ≤ b →
      Uf N h p D (k+1) (S (k+1)) ≤ Uf N h p D (k+1) b := by
    intro b hb
    have := hU2 hb
    have := hmin b
    simp only at *
    linarith
  have hUmono : ∀ a b, S (k+1) ≤ a → a ≤ b → Uf N h p D (k+1) a ≤ Uf N h p D (k+1) b :=
    fun a b hsa hab => Uf_quasi N h p D hD hh hp (k+1) hsa hab (hUb b (hsa.trans hab))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [csBar_succ]
    have h1 := hFq_nonneg (min (S (k+1)) x)
    have h2 := Nf_anti D hD (k+1) (min_le_right (S (k+1)) x)
    have := mul_nonneg hc1 (sub_nonneg.2 h2)
    nlinarith
  · intro x y hxy
    simp only [csBar_succ]
    have h1 := hFq_mono (min_le_min (le_refl (S (k+1))) hxy)
    have h2 := mul_le_mul_of_nonneg_left (hθ hxy) hc1
    simp only at h1 h2
    nlinarith
  · intro x
    rw [csBar_succ]
    exact (hFmin x).trans (hU1 x)
  · intro x x' hxx'
    simp only [csBar_succ]
    rcases le_total x' (S (k+1)) with h1 | h1
    · rw [min_eq_right h1, min_eq_right (hxx'.trans h1)]; exact hU2 hxx'
    · rcases le_total x (S (k+1)) with h2 | h2
      · rw [min_eq_right h2, min_eq_left h1]
        have := hU2 h2
        have := hUmono (S (k+1)) x' le_rfl h1
        simp only at *
        linarith
      · rw [min_eq_left h2, min_eq_left h1]
        have := hUmono x x' h2 hxx'
        linarith

lemma inv_all (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (hD0 : ∀ j, D j (Set.Iio 0) = 0)
    (hS : CSSequential N h p D S) : ∀ k, k ≤ N → Inv N h p D S k := by
  intro k
  induction k with
  | zero =>
    intro _
    have hH : Hs h 0 = 0 := by simp [Hs]
    have e : ∀ x, csBar N h p D S 0 x = cc N h p 0 * Nf D 0 x := csBar_zero N h p D S
    refine ⟨fun x => (e x).ge, ?_, ?_, ?_⟩
    · intro x y _; simp only [e]; simp
    · intro x; rw [e]; unfold Uf; rw [hH]; simp
    · intro x y _; simp only [e]; unfold Uf; rw [hH]; simp
  | succ k ih =>
    intro hk
    refine inv_succ N h p D hD S hh hp hD0 k hk (ih (by omega)) ?_
    intro y
    exact hS (k+1) (Finset.mem_Icc.2 ⟨by omega, hk⟩) y

end step2


lemma tilde_mean_sum (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) :
    ∀ j, ∫ s, s ∂(tildeLaw D j) = ∑ i ∈ Finset.Icc 1 j, Ek D i
  | 0 => by simp [tildeLaw]
  | j + 1 => by
    rw [tildeLaw_mean D hD j, tilde_mean_sum D hD j, Finset.sum_Icc_succ_top (by omega)]
    rfl

lemma nv_form (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (a b : ℝ) (j : ℕ) (y : ℝ) :
    nvCostOf a b (tildeLaw D j) y
      = a * (y - ∑ i ∈ Finset.Icc 1 j, Ek D i) + (a + b) * Nf D j y := by
  haveI := tildeLaw_prob D j
  have hpt : ∀ d : ℝ, a * max (y - d) 0 + b * max (d - y) 0
      = a * (y - d) + (a + b) * max (-(y - d)) 0 := by
    intro d
    rcases le_total (y - d) 0 with h1 | h1
    · have e1 : max (y - d) 0 = 0 := max_eq_right h1
      have e2 : max (d - y) 0 = d - y := max_eq_left (by linarith)
      have e3 : max (-(y - d)) 0 = d - y := by rw [neg_sub]; exact e2
      rw [e1, e2, e3]; ring
    · have e1 : max (y - d) 0 = y - d := max_eq_left h1
      have e2 : max (d - y) 0 = 0 := max_eq_right (by linarith)
      have e3 : max (-(y - d)) 0 = 0 := by rw [neg_sub]; exact e2
      rw [e1, e2, e3]; ring
  have : nvCostOf a b (tildeLaw D j) y
      = Tm (tildeLaw D j) (fun z => a * z + (a + b) * max (-z) 0) y := by
    unfold nvCostOf Tm
    exact integral_congr_ae (Filter.Eventually.of_forall (fun d => hpt d))
  rw [this, Tm_lin (LipR.const_mul _ LipR.neg_max0) _ (tildeLaw_int D hD j), Tm_cmul,
    tilde_mean_sum D hD j]
  rfl

lemma pipe_eq (D : ℕ → Measure ℝ) {j : ℕ} (hj : 1 ≤ j) :
    ∑ i ∈ Finset.Icc 1 j, Ek D i = pipelineMean D j + Ek D j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  unfold pipelineMean
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top (by omega)]
  rfl

lemma ssLower_eq (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) {j : ℕ} (hj : 1 ≤ j) (y : ℝ) :
    ssLower N h p D j y = Lf N h p D j y := by
  unfold ssLower Lf
  rw [nv_form D hD, pipe_eq D hj]
  unfold cc
  ring

lemma ssUpper_eq (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) {j : ℕ} (hj : 1 ≤ j) (y : ℝ) :
    ssUpper N h p D j y = Uf N h p D j y := by
  unfold ssUpper Uf
  rw [nv_form D hD, pipe_eq D hj]
  unfold cc Hs
  ring

lemma exists_min_aff (D : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (D j)]
    (hD : ∀ j, Integrable (fun x : ℝ => x) (D j)) (hD0 : ∀ j, D j (Set.Iio 0) = 0)
    (j : ℕ) {α c e : ℝ} (hα : 0 < α) (hc : 0 < c) :
    ∃ y0, ∀ y, α * (y0 - e) + (α + c) * Nf D j y0 ≤ α * (y - e) + (α + c) * Nf D j y := by
  have hcont : Continuous (fun x => α * (x - e) + (α + c) * Nf D j x) :=
    (((LipR.const_mul α (LipR.id.sub (LipR.const e))).add
      (LipR.const_mul (α + c) (Nf_lip D hD j)))).cont
  apply hcont.exists_forall_le
  rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
  have hN := fun x => Nf_nonneg D j x
  have hP := fun x => (Nf_id_prop D hD hD0 j).2 x
  constructor
  · rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_le_atBot (-(b + α * e) / c)] with x hx
    have h1 : c * (-(b + α * e) / c) = -(b + α * e) := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hx hc.le
    rw [h1] at h2
    have h3 := hP x
    nlinarith [mul_nonneg (by linarith : 0 ≤ α + c) h3]
  · rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (e + b / α)] with x hx
    have : b ≤ α * (x - e) := by
      have := (div_le_iff₀ hα).1 (show b / α ≤ x - e by linarith)
      linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ α + c) (hN x)]


theorem shang_song_core (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hD0 : ∀ j, D j (Set.Iio 0) = 0)
    (hh : ∀ j, 0 < h j) (hp : 0 < p) (Sstar : ℕ → ℝ) (hS : CSSequential N h p D Sstar)
    (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    (∀ y, ssLower N h p D j y ≤ csG N h p D Sstar j y
        ∧ csG N h p D Sstar j y ≤ ssUpper N h p D j y)
      ∧ ∃ Sl Su : ℝ, IsMinOn (ssUpper N h p D j) Set.univ Sl
          ∧ IsMinOn (ssLower N h p D j) Set.univ Su ∧ Sl ≤ Sstar j ∧ Sstar j ≤ Su := by
  have hh0 : ∀ j, 0 ≤ h j := fun j => (hh j).le
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have I := inv_all N h p D hD Sstar hh0 hp.le hD0 hS k (by omega)
  obtain ⟨hL1, hL2⟩ := facts_lower N h p D hD Sstar k hjN I
  obtain ⟨hU1, hU2⟩ := facts_upper N h p D hD Sstar hh0 k hjN hD0 I
  have hmin : ∀ y, csG N h p D Sstar (k+1) (Sstar (k+1)) ≤ csG N h p D Sstar (k+1) y :=
    fun y => hS (k+1) (Finset.mem_Icc.2 ⟨hj1, hjN⟩) y
  have eL : ssLower N h p D (k+1) = Lf N h p D (k+1) := funext (ssLower_eq N h p D hD hj1)
  have eU : ssUpper N h p D (k+1) = Uf N h p D (k+1) := funext (ssUpper_eq N h p D hD hj1)
  rw [eL, eU]
  refine ⟨fun y => ⟨hL1 y, hU1 y⟩, ?_⟩
  have hHs : 0 < Hs h (k+1) := by
    unfold Hs
    exact Finset.sum_pos (fun i _ => hh i) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hcc : 0 < cc N h p (k+1) := add_pos_of_pos_of_nonneg hp (loc_nonneg hh0 _ _)
  obtain ⟨y0, hy0⟩ := exists_min_aff D hD hD0 (k+1) (e := Ek D (k+1)) hHs hcc
  obtain ⟨y1, hy1⟩ := exists_min_aff D hD hD0 (k+1) (e := Ek D (k+1)) (hh (k+1)) hcc
  have hU0 : ∀ y, Uf N h p D (k+1) y0 ≤ Uf N h p D (k+1) y := fun y => hy0 y
  have hL0 : ∀ y, Lf N h p D (k+1) y1 ≤ Lf N h p D (k+1) y := fun y => hy1 y
  set s := Sstar (k+1) with hs
  have hUb : ∀ b, s ≤ b → Uf N h p D (k+1) s ≤ Uf N h p D (k+1) b := by
    intro b hb
    have := hU2 hb
    have := hmin b
    simp only at *
    linarith
  have hLb : ∀ b, b ≤ s → Lf N h p D (k+1) s ≤ Lf N h p D (k+1) b := by
    intro b hb
    have := hL2 hb
    have := hmin b
    simp only at *
    linarith
  refine ⟨if y0 ≤ s then y0 else s, if s ≤ y1 then y1 else s, ?_, ?_, ?_, ?_⟩
  · rw [isMinOn_iff]
    intro y _
    split_ifs with h1
    · exact hU0 y
    · exact (hUb y0 (not_le.1 h1).le).trans (hU0 y)
  · rw [isMinOn_iff]
    intro y _
    split_ifs with h1
    · exact hL0 y
    · exact (hLb y1 (not_le.1 h1).le).trans (hL0 y)
  · split_ifs with h1
    · exact h1
    · exact le_rfl
  · split_ifs with h1
    · exact h1
    · exact le_rfl

end SupplyChainTheory

open SupplyChainTheory


theorem solution (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hD0 : ∀ j, D j (Set.Iio 0) = 0)
    (hh : ∀ j, 0 < h j) (hp : 0 < p) (Sstar : ℕ → ℝ) (hS : CSSequential N h p D Sstar)
    (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    (∀ y, ssLower N h p D j y ≤ csG N h p D Sstar j y
        ∧ csG N h p D Sstar j y ≤ ssUpper N h p D j y)
      ∧ ∃ Sl Su : ℝ, IsMinOn (ssUpper N h p D j) Set.univ Sl
          ∧ IsMinOn (ssLower N h p D j) Set.univ Su ∧ Sl ≤ Sstar j ∧ Sstar j ≤ Su := by
  exact shang_song_core N h p D hD hD0 hh hp Sstar hS j hj1 hjN
