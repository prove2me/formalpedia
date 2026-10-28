-- Prove2me | solution 1 for PenaltyLag.Rate.corollary_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T05:17:40.786589+00:00
-- url     : https://prove2.me/submissions/38773f1a-6137-4175-b200-dd3579074c1d

import Mathlib
import Definitions.Def_PenaltyLag_Rate_Basic

set_option autoImplicit false

open Filter Topology

namespace PLRate53

open PenaltyLag.Rate

/-! ### Scalar facts about one penalty term `a * (theta (y + 2 r t)^2 - y^2)`, `a = 1/(4r)`. -/

lemma theta_nonneg (t : ℝ) : 0 ≤ theta t := le_max_left _ _

lemma term_ge (r a y z t : ℝ) (ha : a * (4 * r) = 1) (ha0 : 0 < a) (hz : 0 ≤ z) :
    z * t - a * (z - y) ^ 2 ≤ a * (theta (y + 2 * r * t) ^ 2 - y ^ 2) := by
  unfold theta
  rcases le_total 0 (y + 2 * r * t) with h | h
  · rw [max_eq_right h]
    have e : a * ((y + 2 * r * t) ^ 2 - y ^ 2) - (z * t - a * (z - y) ^ 2)
        = a * (z - y - 2 * r * t) ^ 2 := by linear_combination (z * t) * ha
    nlinarith [mul_nonneg ha0.le (sq_nonneg (z - y - 2 * r * t))]
  · rw [max_eq_left h]
    have e : a * ((0:ℝ) ^ 2 - y ^ 2) - (z * t - a * (z - y) ^ 2)
        = a * z * (z - 2 * y - 4 * r * t) := by linear_combination (z * t) * ha
    have h2 : 0 ≤ z - 2 * y - 4 * r * t := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha0.le hz) h2]

lemma term_le0 (r a y t : ℝ) (hr : 0 < r) (ha0 : 0 < a) (ht : t ≤ 0) :
    a * (theta (y + 2 * r * t) ^ 2 - y ^ 2) ≤ 0 := by
  have key : theta (y + 2 * r * t) ^ 2 ≤ y ^ 2 := by
    unfold theta
    rcases le_total 0 (y + 2 * r * t) with h | h
    · rw [max_eq_right h]
      have h1 : 0 ≤ -(r * t) := by nlinarith
      nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ 2 * y + 2 * r * t)]
    · rw [max_eq_left h]; nlinarith [sq_nonneg y]
  exact mul_nonpos_of_nonneg_of_nonpos ha0.le (by linarith)

lemma term_exact (r a y t : ℝ) (ha : a * (4 * r) = 1) :
    a * (theta (y + 2 * r * t) ^ 2 - y ^ 2)
      = theta (y + 2 * r * t) * t - a * (theta (y + 2 * r * t) - y) ^ 2 := by
  unfold theta
  rcases le_total 0 (y + 2 * r * t) with h | h
  · rw [max_eq_right h]; linear_combination (y * t + 2 * r * t ^ 2) * ha
  · rw [max_eq_left h]; ring

lemma term_lin (r a y yb t : ℝ) (ha : a * (4 * r) = 1) (ha0 : 0 < a) :
    a * (theta (yb + 2 * r * t) ^ 2 - yb ^ 2)
      + 2 * a * (theta (yb + 2 * r * t) - yb) * (y - yb) - a * (y - yb) ^ 2
      ≤ a * (theta (y + 2 * r * t) ^ 2 - y ^ 2) := by
  have h1 := term_ge r a y (theta (yb + 2 * r * t)) t ha ha0 (theta_nonneg _)
  have h2 := term_exact r a yb t ha
  rw [h2]
  have e : theta (yb + 2 * r * t) * t - a * (theta (yb + 2 * r * t) - yb) ^ 2
      + 2 * a * (theta (yb + 2 * r * t) - yb) * (y - yb) - a * (y - yb) ^ 2
      = theta (yb + 2 * r * t) * t - a * (theta (yb + 2 * r * t) - y) ^ 2 := by ring
  linarith

lemma term_sq (r a yb t : ℝ) (ha : a * (4 * r) = 1) (ha0 : 0 < a) (hyb : 0 ≤ yb) :
    r * (2 * a * (theta (yb + 2 * r * t) - yb)) ^ 2
      ≤ a * (theta (yb + 2 * r * t) ^ 2 - yb ^ 2) - yb * t := by
  unfold theta
  rcases le_total 0 (yb + 2 * r * t) with h | h
  · rw [max_eq_right h]
    have e : a * ((yb + 2 * r * t) ^ 2 - yb ^ 2) - yb * t
        - r * (2 * a * (yb + 2 * r * t - yb)) ^ 2 = 0 := by
      linear_combination (yb * t - 4 * a * r ^ 2 * t ^ 2) * ha
    linarith
  · rw [max_eq_left h]
    have e1 : 2 * a * (yb + 2 * r * t) = 2 * a * yb + t := by linear_combination t * ha
    have h1 : 2 * a * yb + t ≤ 0 := by
      rw [← e1]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    have e2 : a * ((0:ℝ) ^ 2 - yb ^ 2) - yb * t - r * (2 * a * (0 - yb)) ^ 2
        = -yb * (2 * a * yb + t) := by
      linear_combination (-a * yb ^ 2) * ha
    nlinarith [mul_nonneg hyb (neg_nonneg.2 h1)]

/-- Convexity of `t ↦ theta (c + 2 r t)^2` composed with a convex inequality. -/
lemma theta_sq_conv (c r u v w α β : ℝ) (hr : 0 < r) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β = 1) (hw : w ≤ α * u + β * v) :
    theta (c + 2 * r * w) ^ 2
      ≤ α * theta (c + 2 * r * u) ^ 2 + β * theta (c + 2 * r * v) ^ 2 := by
  set p := theta (c + 2 * r * u)
  set q := theta (c + 2 * r * v)
  have hp : 0 ≤ p := theta_nonneg _
  have hq : 0 ≤ q := theta_nonneg _
  have hpA : c + 2 * r * u ≤ p := le_max_right _ _
  have hqB : c + 2 * r * v ≤ q := le_max_right _ _
  have h1 : theta (c + 2 * r * w) ≤ α * p + β * q := by
    unfold theta
    apply max_le (by positivity)
    have : c + 2 * r * w ≤ c + 2 * r * (α * u + β * v) := by nlinarith
    have e : c + 2 * r * (α * u + β * v) = α * (c + 2 * r * u) + β * (c + 2 * r * v) := by
      linear_combination (-c) * hαβ
    nlinarith [mul_le_mul_of_nonneg_left hpA hα, mul_le_mul_of_nonneg_left hqB hβ]
  have h0 : 0 ≤ theta (c + 2 * r * w) := theta_nonneg _
  have h2 : theta (c + 2 * r * w) ^ 2 ≤ (α * p + β * q) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have hb : β = 1 - α := by linarith
  subst hb
  nlinarith [mul_nonneg (mul_nonneg hα hβ) (sq_nonneg (p - q))]

/-! ### Sums. -/

lemma Lr_eq {n m : ℕ} (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ) (x : Pt n) (y : Mult m) :
    Lr f₀ f r x y = f₀ x + ∑ i, (1 / (4 * r)) * (theta (y i + 2 * r * f i x) ^ 2 - y i ^ 2) := by
  unfold Lr; rw [Finset.mul_sum]

lemma normsq_sub {m : ℕ} (y yb : Mult m) : ‖y - yb‖ ^ 2 = ∑ i, (y i - yb i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp

lemma a_facts (r : ℝ) (hr : 0 < r) : 1 / (4 * r) * (4 * r) = 1 ∧ 0 < 1 / (4 * r) :=
  ⟨one_div_mul_cancel (by positivity), by positivity⟩

lemma Lr_ge_ell {n m : ℕ} (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ) (hr : 0 < r)
    (x : Pt n) (y yb : Mult m) (hyb : ∀ i, 0 ≤ yb i) :
    f₀ x + ∑ i, yb i * f i x - 1 / (4 * r) * ‖y - yb‖ ^ 2 ≤ Lr f₀ f r x y := by
  obtain ⟨ha, ha0⟩ := a_facts r hr
  rw [Lr_eq, normsq_sub]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    term_ge r (1 / (4 * r)) (y i) (yb i) (f i x) ha ha0 (hyb i))
  have e : ∀ i, yb i * f i x - 1 / (4 * r) * (yb i - y i) ^ 2
      = yb i * f i x - 1 / (4 * r) * (y i - yb i) ^ 2 := fun i => by ring
  simp only [e] at hs
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  linarith

lemma Lr_le_f0 {n m : ℕ} (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ) (hr : 0 < r)
    (x : Pt n) (y : Mult m) (hx : ∀ i, f i x ≤ 0) : Lr f₀ f r x y ≤ f₀ x := by
  obtain ⟨_, ha0⟩ := a_facts r hr
  rw [Lr_eq]
  have := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) =>
    term_le0 r (1 / (4 * r)) (y i) (f i x) hr ha0 (hx i))
  linarith

/-- `G x i = (theta (ȳᵢ + 2 r fᵢ x) - ȳᵢ) / (2r)`, the y-gradient of `L_r(x, ·)` at `ȳ`. -/
noncomputable def G {n m : ℕ} (f : Fin m → Pt n → ℝ) (r : ℝ) (yb : Mult m) (x : Pt n)
    (i : Fin m) : ℝ :=
  2 * (1 / (4 * r)) * (theta (yb i + 2 * r * f i x) - yb i)

lemma Lr_lin {n m : ℕ} (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ) (hr : 0 < r)
    (x : Pt n) (y yb : Mult m) :
    Lr f₀ f r x yb + ∑ i, G f r yb x i * (y i - yb i) - 1 / (4 * r) * ‖y - yb‖ ^ 2
      ≤ Lr f₀ f r x y := by
  obtain ⟨ha, ha0⟩ := a_facts r hr
  rw [Lr_eq, Lr_eq, normsq_sub]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    term_lin r (1 / (4 * r)) (y i) (yb i) (f i x) ha ha0)
  simp only [G, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs ⊢
  linarith

lemma Lr_sq {n m : ℕ} (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (r : ℝ) (hr : 0 < r)
    (x : Pt n) (yb : Mult m) (hyb : ∀ i, 0 ≤ yb i) :
    r * ∑ i, G f r yb x i ^ 2 ≤ Lr f₀ f r x yb - (f₀ x + ∑ i, yb i * f i x) := by
  obtain ⟨ha, ha0⟩ := a_facts r hr
  rw [Lr_eq]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    term_sq r (1 / (4 * r)) (yb i) (f i x) ha ha0 (hyb i))
  rw [Finset.sum_sub_distrib] at hs
  rw [Finset.mul_sum]
  simp only [G]
  linarith

lemma Lr_convex {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ)
    (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i)) (r : ℝ) (hr : 0 < r) (y : Mult m) :
    ConvexOn ℝ X (fun x => Lr f₀ f r x y) := by
  refine ⟨hf₀.1, fun a ha b hb α β hα hβ hαβ => ?_⟩
  obtain ⟨_, hc⟩ := a_facts r hr
  simp only [Lr_eq, smul_eq_mul]
  have h0 := hf₀.2 ha hb hα hβ hαβ
  simp only [smul_eq_mul] at h0
  have hs : ∑ i, 1 / (4 * r) * (theta (y i + 2 * r * f i (α • a + β • b)) ^ 2 - y i ^ 2)
      ≤ α * ∑ i, 1 / (4 * r) * (theta (y i + 2 * r * f i a) ^ 2 - y i ^ 2)
          + β * ∑ i, 1 / (4 * r) * (theta (y i + 2 * r * f i b) ^ 2 - y i ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hi := (hf i).2 ha hb hα hβ hαβ
    simp only [smul_eq_mul] at hi
    have := theta_sq_conv (y i) r (f i a) (f i b) (f i (α • a + β • b)) α β hr hα hβ hαβ hi
    have e : α * (1 / (4 * r) * (theta (y i + 2 * r * f i a) ^ 2 - y i ^ 2))
          + β * (1 / (4 * r) * (theta (y i + 2 * r * f i b) ^ 2 - y i ^ 2))
        = 1 / (4 * r) * ((α * theta (y i + 2 * r * f i a) ^ 2
            + β * theta (y i + 2 * r * f i b) ^ 2) - y i ^ 2) := by
      linear_combination (-(1 / (4 * r)) * y i ^ 2) * hαβ
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  nlinarith [hs, h0]


/-! ### Second-order Taylor bound. -/

noncomputable def dualSymm (n : ℕ) : StrongDual ℝ (Pt n) →L[ℝ] Pt n where
  toFun φ := (InnerProductSpace.toDual ℝ (Pt n)).symm φ
  map_add' a b := map_add _ a b
  map_smul' c φ := by simp
  cont := (InnerProductSpace.toDual ℝ (Pt n)).symm.continuous

lemma fderiv_eq_inner {n : ℕ} (g : Pt n → ℝ) (w z : Pt n) :
    fderiv ℝ g w z = inner ℝ (gradient g w) z := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

lemma hess_smul {n : ℕ} (g : Pt n → ℝ) (x u : Pt n) (t : ℝ) :
    hessForm g x (t • u) = t ^ 2 * hessForm g x u := by
  unfold hessForm
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring

lemma tendsto_add_left {n : ℕ} (x : Pt n) : Tendsto (fun h : Pt n => x + h) (𝓝 0) (𝓝 x) := by
  have := (continuous_add_left x).tendsto (0 : Pt n)
  simpa using this

lemma taylor2 {n : ℕ} (g : Pt n → ℝ) (x : Pt n) (U : Set (Pt n)) (hU : U ∈ 𝓝 x)
    (hg : ContDiffOn ℝ 2 g U) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 (0 : Pt n),
      |g (x + z) - g x - fderiv ℝ g x z - hessForm g x z / 2| ≤ ε * ‖z‖ ^ 2 := by
  have hcd : ContDiffAt ℝ 2 g x := hg.contDiffAt hU
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ g) x := hcd.fderiv_right (by norm_num)
  have hgrad : DifferentiableAt ℝ (gradient g) x := by
    have e : gradient g = fun w => dualSymm n (fderiv ℝ g w) := rfl
    rw [e]
    exact (dualSymm n).differentiableAt.comp x (hfd.differentiableAt one_ne_zero)
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hgrad.hasFDerivAt).def hε
  have hdiff : ∀ᶠ w in 𝓝 x, HasFDerivAt g (fderiv ℝ g w) w := by
    filter_upwards [eventually_mem_nhds_iff.2 hU] with w hw
    exact ((hg.contDiffAt hw).differentiableAt (by norm_num)).hasFDerivAt
  have hdiff' := (tendsto_add_left x).eventually hdiff
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hlo.and hdiff')
  refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun z hz => ?_⟩
  have hz' : ‖z‖ < δ := by simpa using hz
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, dist (t • z) 0 < δ := by
    intro t ht
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [norm_nonneg z, ht.2]
  have hk : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt
      (fun t : ℝ => g (x + t • z) - t * fderiv ℝ g x z - t ^ 2 / 2 * hessForm g x z)
      (fderiv ℝ g (x + t • z) z - fderiv ℝ g x z - t * hessForm g x z) (Set.Icc 0 1) t := by
    intro t ht
    have hg' := (hball (hseg t ht)).2
    have hline : HasDerivAt (fun s : ℝ => x + s • z) z t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_add x
    have h1 := hg'.comp_hasDerivAt t hline
    have h2 := (hasDerivAt_id t).mul_const (fderiv ℝ g x z)
    have h3 := ((hasDerivAt_pow 2 t).div_const 2).mul_const (hessForm g x z)
    have h4 := (h1.sub h2).sub h3
    have e : fderiv ℝ g (x + t • z) z - fderiv ℝ g x z - t * hessForm g x z
        = fderiv ℝ g (x + t • z) z - 1 * fderiv ℝ g x z
          - ((2:ℕ):ℝ) * t ^ (2 - 1) / 2 * hessForm g x z := by norm_num <;> ring
    rw [e]
    exact h4.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖fderiv ℝ g (x + t • z) z - fderiv ℝ g x z - t * hessForm g x z‖ ≤ ε * ‖z‖ ^ 2 := by
    intro t ht
    have hb := (hball (hseg t (Set.Ico_subset_Icc_self ht))).1
    have e : fderiv ℝ g (x + t • z) z - fderiv ℝ g x z - t * hessForm g x z
        = inner ℝ (gradient g (x + t • z) - gradient g x - fderiv ℝ (gradient g) x (t • z)) z := by
      rw [inner_sub_left, inner_sub_left, map_smul, real_inner_smul_left, ← fderiv_eq_inner,
        ← fderiv_eq_inner, hessForm, real_inner_comm]
    rw [e, Real.norm_eq_abs]
    calc |inner ℝ (gradient g (x + t • z) - gradient g x - fderiv ℝ (gradient g) x (t • z)) z|
        ≤ ‖gradient g (x + t • z) - gradient g x - fderiv ℝ (gradient g) x (t • z)‖ * ‖z‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ (ε * ‖t • z‖) * ‖z‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ ε * ‖z‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        have : t * ‖z‖ ≤ ‖z‖ := by nlinarith [norm_nonneg z, ht.2.le]
        calc ε * (t * ‖z‖) * ‖z‖ ≤ ε * ‖z‖ * ‖z‖ := by gcongr
          _ = ε * ‖z‖ ^ 2 := by ring
  have hfin := norm_image_sub_le_of_norm_deriv_le_segment_01' hk hbound
  rw [Real.norm_eq_abs] at hfin
  convert hfin using 2
  simp only [one_smul, zero_smul, add_zero]
  ring

lemma exists_pos_smul {n : ℕ} (u : Pt n) (P : Pt n → Prop) (h : ∀ᶠ z in 𝓝 (0:Pt n), P z) :
    ∃ t : ℝ, 0 < t ∧ P (t • u) := by
  have ht : Tendsto (fun t : ℝ => t • u) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t • u) (𝓝 0) (𝓝 ((0:ℝ) • u)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, h1, h2⟩ := ((ht.eventually h).and eventually_mem_nhdsWithin).exists
  exact ⟨t, h2, h1⟩

lemma sum_lin4 {m : ℕ} (c a b d e : Fin m → ℝ) :
    ∑ i, c i * (a i - b i - d i - e i / 2)
      = ∑ i, c i * a i - ∑ i, c i * b i - ∑ i, c i * d i - (∑ i, c i * e i) / 2 := by
  rw [Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Local quadratic growth of `L_r(·, ȳ)` at `x̄`. -/

set_option maxHeartbeats 1000000 in
lemma local_growth {n m : ℕ} (X : Set (Pt n)) (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ)
    (xbar : Pt n) (ybar : Mult m) (hA : Sec5Assumptions X f₀ f xbar ybar) (r : ℝ) (hr : 0 < r) :
    ∃ μ > 0, ∀ᶠ z in 𝓝 (0 : Pt n),
      xbar + z ∈ X ∧ f₀ xbar + μ * ‖z‖ ^ 2 ≤ Lr f₀ f r (xbar + z) ybar := by
  classical
  obtain ⟨U, hU, h0U, hiU⟩ := hA.smooth
  set I := activeSet f xbar with hIdef
  have hyb : ∀ i, 0 ≤ ybar i := fun i => (hA.kuhnTucker.1 i).1
  have hXn : X ∈ 𝓝 xbar := mem_interior_iff_mem_nhds.1 hA.interior_mem
  have hXev : ∀ᶠ z in 𝓝 (0:Pt n), xbar + z ∈ X := (tendsto_add_left xbar).eventually hXn
  have hd : ∀ g : Pt n → ℝ, ContDiffOn ℝ 2 g U → HasFDerivAt g (fderiv ℝ g xbar) xbar :=
    fun g hg => ((hg.contDiffAt hU).differentiableAt (by norm_num)).hasFDerivAt
  have hcs : ∑ i, ybar i * f i xbar = 0 :=
    Finset.sum_eq_zero fun i _ => (hA.kuhnTucker.1 i).2.2
  have hact : ∀ i ∈ I, f i xbar = 0 := by
    intro i hi; simpa [hIdef, activeSet] using hi
  have hinact : ∀ i, i ∉ I → ybar i = 0 := by
    intro i hi
    have hne : f i xbar ≠ 0 := by simpa [hIdef, activeSet] using hi
    rcases mul_eq_zero.1 (hA.kuhnTucker.1 i).2.2 with h | h
    · exact h
    · exact absurd h hne
  have hpos : ∀ i ∈ I, 0 < ybar i := fun i hi =>
    lt_of_le_of_ne (hyb i) (Ne.symm (hA.strictComp i hi))
  -- first-order condition
  have hlin : ∀ z, fderiv ℝ f₀ xbar z + ∑ i, ybar i * fderiv ℝ (f i) xbar z = 0 := by
    have hD : HasFDerivAt (fun x => f₀ x + ∑ i, ybar i * f i x)
        (fderiv ℝ f₀ xbar + ∑ i, ybar i • fderiv ℝ (f i) xbar) xbar :=
      (hd f₀ h0U).add (HasFDerivAt.fun_sum fun i _ => (hd (f i) (hiU i)).const_mul (ybar i))
    have hmin' : IsLocalMin (fun x => f₀ x + ∑ i, ybar i * f i x) xbar :=
      Filter.eventually_of_mem hXn fun x hx => hA.kuhnTucker.2.2 x hx
    have h0 := hmin'.hasFDerivAt_eq_zero hD
    intro z
    have := congrArg (fun L : Pt n →L[ℝ] ℝ => L z) h0
    simpa using this
  -- the Lagrangian Hessian form
  set H : Pt n → ℝ := fun u => hessForm f₀ xbar u + ∑ i, ybar i * hessForm (f i) xbar u with hH
  have hHform : ∀ u, Hform f₀ f I xbar ybar u = H u := by
    intro u
    simp only [Hform, hH]
    congr 1
    exact Finset.sum_subset (Finset.subset_univ I) fun i _ hi => by rw [hinact i hi, zero_mul]
  have hHs : ∀ (t : ℝ) u, H (t • u) = t ^ 2 * H u := by
    intro t u
    simp only [hH, hess_smul]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  set S := ∑ i, ybar i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hyb i
  have hell : ∀ ε > 0, ∀ᶠ z in 𝓝 (0:Pt n),
      |(f₀ (xbar + z) + ∑ i, ybar i * f i (xbar + z)) - f₀ xbar - H z / 2|
        ≤ ε * (1 + S) * ‖z‖ ^ 2 := by
    intro ε hε
    filter_upwards [taylor2 f₀ xbar U hU h0U ε hε,
      Filter.eventually_all.2 fun i => taylor2 (f i) xbar U hU (hiU i) ε hε] with z h0 hi
    have hlz := hlin z
    have hsum : |∑ i, ybar i * (f i (xbar + z) - f i xbar - fderiv ℝ (f i) xbar z
        - hessForm (f i) xbar z / 2)| ≤ S * (ε * ‖z‖ ^ 2) := by
      calc _ ≤ ∑ i, |ybar i * (f i (xbar + z) - f i xbar - fderiv ℝ (f i) xbar z
              - hessForm (f i) xbar z / 2)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ybar i * (ε * ‖z‖ ^ 2) := Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_of_nonneg (hyb i)]
              exact mul_le_mul_of_nonneg_left (hi i) (hyb i)
        _ = S * (ε * ‖z‖ ^ 2) := by rw [hS, Finset.sum_mul]
    have h4 := sum_lin4 (fun i => ybar i) (fun i => f i (xbar + z)) (fun i => f i xbar)
      (fun i => fderiv ℝ (f i) xbar z) (fun i => hessForm (f i) xbar z)
    simp only at h4
    have e : (f₀ (xbar + z) + ∑ i, ybar i * f i (xbar + z)) - f₀ xbar - H z / 2
        = (f₀ (xbar + z) - f₀ xbar - fderiv ℝ f₀ xbar z - hessForm f₀ xbar z / 2)
          + ∑ i, ybar i * (f i (xbar + z) - f i xbar - fderiv ℝ (f i) xbar z
              - hessForm (f i) xbar z / 2) := by
      rw [h4]; simp only [hH]; linarith [hcs, hlz]
    rw [e]
    calc _ ≤ |f₀ (xbar + z) - f₀ xbar - fderiv ℝ f₀ xbar z - hessForm f₀ xbar z / 2|
          + |∑ i, ybar i * (f i (xbar + z) - f i xbar - fderiv ℝ (f i) xbar z
              - hessForm (f i) xbar z / 2)| := abs_add_le _ _
      _ ≤ ε * ‖z‖ ^ 2 + S * (ε * ‖z‖ ^ 2) := add_le_add h0 hsum
      _ = ε * (1 + S) * ‖z‖ ^ 2 := by ring
  -- Hessian of the Lagrangian is positive semidefinite (x̄ minimizes it on a neighbourhood)
  have hH0 : ∀ u, 0 ≤ H u := by
    intro u
    by_contra hneg
    push_neg at hneg
    set ε := -H u / (4 * (1 + S) * (‖u‖ ^ 2 + 1)) with hεdef
    have hden : 0 < 4 * (1 + S) * (‖u‖ ^ 2 + 1) := by positivity
    have hε : 0 < ε := div_pos (by linarith) hden
    have hεe : ε * (4 * (1 + S) * (‖u‖ ^ 2 + 1)) = -H u := div_mul_cancel₀ _ hden.ne'
    obtain ⟨t, ht, hP⟩ := exists_pos_smul u _ ((hell ε hε).and hXev)
    have hm := hA.kuhnTucker.2.2 _ hP.2
    rw [hcs, add_zero] at hm
    have h1 := (abs_le.1 hP.1).2
    rw [hHs, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h1
    have hT : 0 < t ^ 2 := by positivity
    have hq : ε * (1 + S) * ‖u‖ ^ 2 ≤ -H u / 4 := by
      have : ε * (1 + S) * ‖u‖ ^ 2 ≤ ε * (1 + S) * (‖u‖ ^ 2 + 1) := by
        have : 0 ≤ ε * (1 + S) := by positivity
        nlinarith
      linarith
    have h2 : ε * (1 + S) * (t * ‖u‖) ^ 2 ≤ t ^ 2 * (-H u / 4) := by
      rw [mul_pow, ← mul_assoc, mul_comm (ε * (1 + S)) (t ^ 2), mul_assoc]
      exact mul_le_mul_of_nonneg_left hq hT.le
    nlinarith
  -- the quadratic model Q
  set Q : Pt n → ℝ := fun u => H u / 2 + r / 2 * ∑ i ∈ I, (fderiv ℝ (f i) xbar u) ^ 2 with hQ
  have hQs : ∀ (t : ℝ) u, Q (t • u) = t ^ 2 * Q u := by
    intro t u
    simp only [hQ, hHs, map_smul, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    ring
  have hQ0 : Q 0 = 0 := by
    have := hQs 0 0
    simpa using this
  have hQc : Continuous Q := by
    simp only [hQ, hH, hessForm]
    fun_prop
  have hQpos : ∀ u : Pt n, u ≠ 0 → 0 < Q u := by
    intro u hu
    by_cases hall : ∀ i ∈ I, fderiv ℝ (f i) xbar u = 0
    · have hso := hA.secondOrder u hu (fun i hi => by
        rw [real_inner_comm, ← fderiv_eq_inner]; exact hall i hi)
      rw [← hIdef, hHform] at hso
      have h0 : ∑ i ∈ I, (fderiv ℝ (f i) xbar u) ^ 2 = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hall i hi]; ring
      simp only [hQ]; rw [h0]; linarith
    · push_neg at hall
      obtain ⟨i, hi, hne⟩ := hall
      have hs : 0 < ∑ j ∈ I, (fderiv ℝ (f j) xbar u) ^ 2 :=
        lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne)))
          (Finset.single_le_sum (f := fun j => (fderiv ℝ (f j) xbar u) ^ 2)
            (fun j _ => sq_nonneg _) hi)
      simp only [hQ]
      nlinarith [hH0 u]
  obtain ⟨lam, hlam, hQlb⟩ : ∃ lam > 0, ∀ u : Pt n, lam * ‖u‖ ^ 2 ≤ Q u := by
    by_cases hne : (Metric.sphere (0:Pt n) 1).Nonempty
    · obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0:Pt n) 1).exists_isMinOn hne hQc.continuousOn
      have hu0n : ‖u0‖ = 1 := by simpa using hu0
      have hu0ne : u0 ≠ 0 := by
        intro h; rw [h, norm_zero] at hu0n; norm_num at hu0n
      refine ⟨Q u0, hQpos u0 hu0ne, fun u => ?_⟩
      rcases eq_or_ne u 0 with rfl | hu
      · simp [hQ0]
      · have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
        have hv : ‖u‖⁻¹ • u ∈ Metric.sphere (0:Pt n) 1 := by
          simp [norm_smul, hnu.ne']
        have h1 := isMinOn_iff.1 hmin _ hv
        rw [hQs] at h1
        have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖u‖)
        calc Q u0 * ‖u‖ ^ 2 ≤ ‖u‖⁻¹ ^ 2 * Q u * ‖u‖ ^ 2 := h2
          _ = Q u := by field_simp
    · refine ⟨1, one_pos, fun u => ?_⟩
      have hu : u = 0 := by
        by_contra hu
        exact hne ⟨‖u‖⁻¹ • u, by simp [norm_smul, (norm_pos_iff.2 hu).ne']⟩
      subst hu; simp [hQ0]
  -- assemble
  set ε1 := Real.sqrt (lam / (4 * r * (m + 1))) with hε1def
  have hε1 : 0 < ε1 := Real.sqrt_pos.2 (by positivity)
  have hε1sq : ε1 ^ 2 = lam / (4 * r * (m + 1)) := Real.sq_sqrt (by positivity)
  have hfo : ∀ᶠ z in 𝓝 (0:Pt n), ∀ i,
      |f i (xbar + z) - f i xbar - fderiv ℝ (f i) xbar z| ≤ ε1 * ‖z‖ := by
    refine Filter.eventually_all.2 fun i => ?_
    have := (hasFDerivAt_iff_isLittleO_nhds_zero.1 (hd (f i) (hiU i))).def hε1
    filter_upwards [this] with z hz
    simpa [Real.norm_eq_abs] using hz
  have hactev : ∀ᶠ z in 𝓝 (0:Pt n), ∀ i ∈ I, 0 < ybar i + 2 * r * f i (xbar + z) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hc : ContinuousAt (fun x => ybar i + 2 * r * f i x) xbar :=
      continuousAt_const.add (continuousAt_const.mul (hd (f i) (hiU i)).continuousAt)
    have h0 : (fun _ : Pt n => (0:ℝ)) xbar < (fun x => ybar i + 2 * r * f i x) xbar := by
      simp [hact i hi, hpos i hi]
    exact (tendsto_add_left xbar).eventually (continuousAt_const.eventually_lt hc h0)
  have hεpos : 0 < lam / (4 * (1 + S)) := by positivity
  refine ⟨lam / 2, by positivity, ?_⟩
  filter_upwards [hXev, hell _ hεpos, hfo, hactev] with z hzX hl hf1 hac
  refine ⟨hzX, ?_⟩
  have hl' := (abs_le.1 hl).1
  have hεS : lam / (4 * (1 + S)) * (1 + S) = lam / 4 := by field_simp
  rw [hεS] at hl'
  have hsq := Lr_sq f₀ f r hr (xbar + z) ybar hyb
  have hGeq : ∀ i ∈ I, G f r ybar (xbar + z) i = f i (xbar + z) := by
    intro i hi
    simp only [G, theta]
    rw [max_eq_right (hac i hi).le]
    field_simp
    ring
  have hGI : ∑ i ∈ I, f i (xbar + z) ^ 2 ≤ ∑ i, G f r ybar (xbar + z) i ^ 2 := by
    calc ∑ i ∈ I, f i (xbar + z) ^ 2 = ∑ i ∈ I, G f r ybar (xbar + z) i ^ 2 :=
          Finset.sum_congr rfl fun i hi => by rw [hGeq i hi]
      _ ≤ ∑ i, G f r ybar (xbar + z) i ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => sq_nonneg _
  have hterm : ∀ i ∈ I, (fderiv ℝ (f i) xbar z) ^ 2 / 2 - (ε1 * ‖z‖) ^ 2 ≤ f i (xbar + z) ^ 2 := by
    intro i hi
    have h1 := hf1 i
    rw [hact i hi, sub_zero] at h1
    set e := f i (xbar + z) - fderiv ℝ (f i) xbar z
    have he : e ^ 2 ≤ (ε1 * ‖z‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have : f i (xbar + z) = fderiv ℝ (f i) xbar z + e := by simp [e]
    rw [this]
    nlinarith [sq_nonneg (fderiv ℝ (f i) xbar z + 2 * e)]
  have hsumI : ∑ i ∈ I, (fderiv ℝ (f i) xbar z) ^ 2 / 2 - (I.card : ℝ) * (ε1 * ‖z‖) ^ 2
      ≤ ∑ i ∈ I, f i (xbar + z) ^ 2 := by
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hcard : (I.card : ℝ) ≤ m := by
    have := Finset.card_le_univ I
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hQz := hQlb z
  simp only [hQ] at hQz
  have hdiv : ∑ i ∈ I, (fderiv ℝ (f i) xbar z) ^ 2 / 2
      = (∑ i ∈ I, (fderiv ℝ (f i) xbar z) ^ 2) / 2 := by rw [Finset.sum_div]
  rw [hdiv] at hsumI
  have hc1 : r * ((I.card : ℝ) * (ε1 * ‖z‖) ^ 2) ≤ lam / 4 * ‖z‖ ^ 2 := by
    rw [mul_pow, hε1sq]
    have hm1 : (I.card : ℝ) ≤ m + 1 := by linarith
    have hz2 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
    have : r * ((I.card : ℝ) * (lam / (4 * r * (m + 1)) * ‖z‖ ^ 2))
        = (I.card : ℝ) / (m + 1) * (lam / 4 * ‖z‖ ^ 2) := by
      field_simp
    rw [this]
    have hfr : (I.card : ℝ) / (m + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hm1
    have : 0 ≤ lam / 4 * ‖z‖ ^ 2 := by positivity
    nlinarith
  nlinarith [hsq, hGI, hsumI, hl', hQz, hc1]

end PLRate53

open Filter Topology PenaltyLag.Rate in
theorem solution
    {n m : ℕ} (X : Set (Pt n)) (hX : Convex ℝ X)
    (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : Pt n) (ybar : Mult m) (hA : Sec5Assumptions X f₀ f xbar ybar)
    (r : ℝ) (hr : 0 < r)
    (y : ℕ → Mult m) (hyb : Bornology.IsBounded (Set.range y)) (hymax : IsMaximizing X f₀ f r y)
    (x : ℕ → Pt n) (hxX : ∀ k, x k ∈ X)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 0))
    (h47 : ∀ k, (Lr f₀ f r (x k) (y k) : EReal) - gr X f₀ f r (y k) ≤ (α k : EReal))
    (q : ℝ) (hq : 0 < q)
    (h518 : ∀ᶠ k in atTop,
      (α k : EReal) ≤ (q : EReal) * ((⨆ y' : Mult m, gr X f₀ f r y') - gr X f₀ f r (y k))) :
    ∃ s : ℝ, 0 < s ∧ ∀ᶠ k in atTop, ‖x k - xbar‖ ≤ s * ‖y k - ybar‖ := by
  classical
  obtain ⟨μ, hμ, hloc⟩ := PLRate53.local_growth X f₀ f xbar ybar hA r hr
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hloc
  have hyb0 : ∀ i, 0 ≤ ybar i := fun i => (hA.kuhnTucker.1 i).1
  have hxbX : xbar ∈ X := hA.optimal.1
  have hfeas : ∀ i, f i xbar ≤ 0 := hA.optimal.2.1
  have hcs : ∑ i, ybar i * f i xbar = 0 :=
    Finset.sum_eq_zero fun i _ => (hA.kuhnTucker.1 i).2.2
  have hell : ∀ z ∈ X, f₀ xbar ≤ f₀ z + ∑ i, ybar i * f i z := by
    intro z hz; have := hA.kuhnTucker.2.2 z hz; rw [hcs, add_zero] at this; exact this
  set F := f₀ xbar with hF
  obtain ⟨ha, ha0⟩ := PLRate53.a_facts r hr
  set a := 1 / (4 * r) with hadef
  have hphib : Lr f₀ f r xbar ybar ≤ F := PLRate53.Lr_le_f0 f₀ f r hr xbar ybar hfeas
  set δ' := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  -- growth of φ = L_r(·, ȳ) on X
  have hgrowth1 : ∀ z ∈ X, ‖z - xbar‖ ≤ δ' → μ * ‖z - xbar‖ ^ 2 ≤ Lr f₀ f r z ybar - F := by
    intro z hz hd
    have h := (hball (show dist (z - xbar) 0 < δ by
      rw [dist_zero_right]; linarith)).2
    rw [add_sub_cancel] at h
    linarith
  have hgrowth2 : ∀ z ∈ X, δ' ≤ ‖z - xbar‖ → μ * δ' * ‖z - xbar‖ ≤ Lr f₀ f r z ybar - F := by
    intro z hz hd
    set d := ‖z - xbar‖
    have hd0 : 0 < d := lt_of_lt_of_le hδ'0 hd
    set l := δ' / d with hl
    have hl0 : 0 < l := div_pos hδ'0 hd0
    have hl1 : l ≤ 1 := (div_le_one hd0).2 hd
    have hconv := (PLRate53.Lr_convex X f₀ f hf₀ hf r hr ybar).2 hxbX hz
      (by linarith : (0:ℝ) ≤ 1 - l) hl0.le (by ring)
    simp only [smul_eq_mul] at hconv
    have hw : (1 - l) • xbar + l • z = xbar + l • (z - xbar) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have hnorm : ‖l • (z - xbar)‖ = δ' := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0, hl, div_mul_cancel₀ _ hd0.ne']
    have h := (hball (show dist (l • (z - xbar)) 0 < δ by
      rw [dist_zero_right, hnorm]; linarith)).2
    rw [← hw, hnorm] at h
    -- F + μ δ'^2 ≤ φ(w) ≤ (1-l) φ(x̄) + l φ(z)
    have h2 : l * (μ * δ' * d) ≤ l * (Lr f₀ f r z ybar - F) := by
      have e : l * (μ * δ' * d) = μ * δ' ^ 2 := by rw [hl]; field_simp
      rw [e]; nlinarith
    exact le_of_mul_le_mul_left h2 hl0
  -- bounded multipliers
  obtain ⟨C0, hC0⟩ := isBounded_iff_forall_norm_le.1 hyb
  set R := C0 + ‖ybar‖ with hR
  have hRk : ∀ k, ‖y k - ybar‖ ≤ R := fun k =>
    (norm_sub_le _ _).trans (by linarith [hC0 _ ⟨k, rfl⟩])
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hRk 0)
  -- bounds on g_r
  have hgrUB : ∀ y', gr X f₀ f r y' ≤ (F : EReal) := by
    intro y'
    exact (iInf₂_le xbar hxbX).trans (EReal.coe_le_coe_iff.2
      (PLRate53.Lr_le_f0 f₀ f r hr xbar y' hfeas))
  have hgrLB : ∀ y', ((F - a * ‖y' - ybar‖ ^ 2 : ℝ) : EReal) ≤ gr X f₀ f r y' := by
    intro y'
    refine le_iInf₂ fun z hz => EReal.coe_le_coe_iff.2 ?_
    have := PLRate53.Lr_ge_ell f₀ f r hr z y' ybar hyb0
    linarith [hell z hz]
  have hsupUB : (⨆ y' : Mult m, gr X f₀ f r y') ≤ (F : EReal) := iSup_le hgrUB
  set K := 2 * (q + 3) * a with hK
  have hkey : ∀ᶠ k in atTop, Lr f₀ f r (x k) ybar - F ≤ K * ‖y k - ybar‖ ^ 2 := by
    filter_upwards [h518] with k hk
    set ρ := ‖y k - ybar‖ with hρ
    have hgS : gr X f₀ f r (y k) ≤ ⨆ y' : Mult m, gr X f₀ f r y' :=
      le_iSup (fun y' => gr X f₀ f r y') (y k)
    have hLB := hgrLB (y k)
    have hUB := hgrUB (y k)
    have hgbot : gr X f₀ f r (y k) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hLB
    have hgtop : gr X f₀ f r (y k) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top F) hUB
    have hSbot : (⨆ y' : Mult m, gr X f₀ f r y') ≠ ⊥ := ne_bot_of_le_ne_bot hgbot hgS
    have hStop : (⨆ y' : Mult m, gr X f₀ f r y') ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top F) hsupUB
    obtain ⟨gv, hgv⟩ : ∃ v : ℝ, gr X f₀ f r (y k) = v :=
      ⟨_, (EReal.coe_toReal hgtop hgbot).symm⟩
    obtain ⟨sv, hsv⟩ : ∃ v : ℝ, (⨆ y' : Mult m, gr X f₀ f r y') = v :=
      ⟨_, (EReal.coe_toReal hStop hSbot).symm⟩
    have h1 := h47 k
    rw [hgv, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h1
    rw [hsv, hgv, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hk
    rw [hgv, EReal.coe_le_coe_iff] at hLB
    rw [hgv, hsv, EReal.coe_le_coe_iff] at hgS
    have hSU := hsupUB
    rw [hsv, EReal.coe_le_coe_iff] at hSU
    -- L(x_k, y_k) ≤ F + q a ρ²
    have hL : Lr f₀ f r (x k) (y k) ≤ F + q * (a * ρ ^ 2) := by
      have : α k ≤ q * (F - gv) := by
        have : q * (sv - gv) ≤ q * (F - gv) :=
          mul_le_mul_of_nonneg_left (by linarith) hq.le
        linarith
      have : q * (F - gv) ≤ q * (a * ρ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hq.le
      have : 0 ≤ q * (F - gv) := mul_nonneg hq.le (by linarith)
      linarith
    have hlin := PLRate53.Lr_lin f₀ f r hr (x k) (y k) ybar
    have hsq := PLRate53.Lr_sq f₀ f r hr (x k) ybar hyb0
    have hellk := hell (x k) (hxX k)
    -- AM-GM on the cross term
    have hcross : -(∑ i, PLRate53.G f r ybar (x k) i * (y k i - ybar i))
        ≤ r / 2 * ∑ i, PLRate53.G f r ybar (x k) i ^ 2 + 2 * a * ρ ^ 2 := by
      rw [hρ, PLRate53.normsq_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      set Gi := PLRate53.G f r ybar (x k) i
      set di := y k i - ybar i
      have e : 2 * r * (r / 2 * Gi ^ 2 + 2 * a * di ^ 2 + Gi * di) = (r * Gi + di) ^ 2 := by
        linear_combination di ^ 2 * ha
      have : 0 ≤ r / 2 * Gi ^ 2 + 2 * a * di ^ 2 + Gi * di := by
        have h2 : 0 ≤ 2 * r * (r / 2 * Gi ^ 2 + 2 * a * di ^ 2 + Gi * di) := by
          rw [e]; positivity
        exact nonneg_of_mul_nonneg_right (by linarith) (by linarith : (0:ℝ) < 2 * r) |> fun h => h
      linarith
    nlinarith [hlin, hsq, hellk, hcross, hL]
  -- conclusion
  set s := K / μ + 1 + K * R / (μ * δ') with hs
  have hK0 : 0 ≤ K := by positivity
  have hs1 : 1 ≤ s := by
    have : 0 ≤ K / μ := by positivity
    have : 0 ≤ K * R / (μ * δ') := by positivity
    linarith
  refine ⟨s, by linarith, ?_⟩
  filter_upwards [hkey] with k hk
  set d := ‖x k - xbar‖
  set ρ := ‖y k - ybar‖
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  rcases le_total d δ' with hd | hd
  · have h1 := hgrowth1 (x k) (hxX k) hd
    have h2 : μ * d ^ 2 ≤ K * ρ ^ 2 := le_trans h1 hk
    have h3 : d ^ 2 ≤ (s * ρ) ^ 2 := by
      have hKμ : K ≤ μ * (K / μ) := by rw [mul_div_cancel₀ _ hμ.ne']
      have hss : K / μ ≤ s ^ 2 := by nlinarith [(by positivity : (0:ℝ) ≤ K * R / (μ * δ'))]
      have : μ * d ^ 2 ≤ μ * (s ^ 2 * ρ ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hss (sq_nonneg ρ)]
      rw [mul_pow]
      exact le_of_mul_le_mul_left this hμ
    exact (pow_le_pow_iff_left₀ hd0 (by positivity) two_ne_zero).1 h3
  · have h1 := hgrowth2 (x k) (hxX k) hd
    have h2 : μ * δ' * d ≤ K * R * ρ := by
      have := le_trans h1 hk
      have : K * ρ ^ 2 ≤ K * R * ρ := by
        have := mul_le_mul_of_nonneg_left (hRk k) (mul_nonneg hK0 hρ0)
        nlinarith
      linarith
    have h3 : d ≤ K * R / (μ * δ') * ρ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have : K * R / (μ * δ') * ρ ≤ s * ρ := by
      apply mul_le_mul_of_nonneg_right _ hρ0
      have : 0 ≤ K / μ := by positivity
      linarith
    linarith
