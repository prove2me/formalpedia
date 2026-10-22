-- Prove2me | solution 1 for RelSmoothFOM.DualAvg.eq_36
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:09:12.631981+00:00
-- url     : https://prove2.me/submissions/eafd20d2-7e4d-4c24-9fad-40b642919b21

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

set_option autoImplicit false
open RelSmoothFOM.DualAvg Filter Topology

section RDGrelint
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma rdg_mem_relint {Q : Set E} {x : E} (hx : x ∈ intrinsicInterior ℝ Q) :
    x ∈ affineSpan ℝ Q ∧ ∃ ε > 0, ∀ z ∈ affineSpan ℝ Q, dist z x < ε → z ∈ Q := by
  rw [mem_intrinsicInterior] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y.2, ?_⟩
  rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy) with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, fun z hz hzd => ?_⟩
  have : (⟨z, hz⟩ : affineSpan ℝ Q) ∈ Metric.ball y ε := by
    simpa [Metric.mem_ball, Subtype.dist_eq] using hzd
  exact hball this

lemma rdg_relint_of {Q : Set E} {x : E} (hxA : x ∈ affineSpan ℝ Q) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ z ∈ affineSpan ℝ Q, dist z x < ε → z ∈ Q) : x ∈ intrinsicInterior ℝ Q := by
  rw [mem_intrinsicInterior]
  refine ⟨⟨x, hxA⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds]
  refine Metric.mem_nhds_iff.2 ⟨ε, hε, fun z hz => ?_⟩
  have hz' : dist (z : E) x < ε := by simpa [Metric.mem_ball, Subtype.dist_eq] using hz
  exact h z z.2 hz'

lemma rdg_combo {Q : Set E} (hQ : Convex ℝ Q) {x y : E} (hx : x ∈ intrinsicInterior ℝ Q)
    (hy : y ∈ Q) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ intrinsicInterior ℝ Q := by
  obtain ⟨hxA, ε, hε, hball⟩ := rdg_mem_relint hx
  have hyA : y ∈ affineSpan ℝ Q := subset_affineSpan ℝ Q hy
  have hwA : a • x + b • y ∈ affineSpan ℝ Q := by
    have h1 := AffineMap.lineMap_mem (k := ℝ) a hyA hxA
    have hb' : b = 1 - a := by linarith
    subst hb'
    rw [AffineMap.lineMap_apply] at h1
    simp only [vsub_eq_sub, vadd_eq_add] at h1
    convert h1 using 1
    module
  refine rdg_relint_of hwA (mul_pos ha hε) fun z hz hzd => ?_
  set w := a • x + b • y with hw
  have hzw : z - w ∈ (affineSpan ℝ Q).direction := AffineSubspace.vsub_mem_direction hz hwA
  have hx'A : x + a⁻¹ • (z - w) ∈ affineSpan ℝ Q := by
    have := AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ a⁻¹ hzw) hxA
    rwa [vadd_eq_add, add_comm] at this
  have hd : dist (x + a⁻¹ • (z - w)) x < ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha.le),
      inv_mul_lt_iff₀ ha]
    rwa [dist_eq_norm] at hzd
  have hx'Q := hball _ hx'A hd
  have hz_eq : z = a • (x + a⁻¹ • (z - w)) + b • y := by
    have : a • (a⁻¹ • (z - w)) = z - w := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    rw [smul_add, this, hw]
    abel
  rw [hz_eq]
  exact hQ hx'Q hy ha.le hb hab

lemma rdg_relint_convex {Q : Set E} (hQ : Convex ℝ Q) : Convex ℝ (intrinsicInterior ℝ Q) := by
  intro x hx y hy a b ha hb hab
  rcases ha.eq_or_lt with rfl | hpos
  · have : b = 1 := by linarith
    subst this
    simpa using hy
  · exact rdg_combo hQ hx (intrinsicInterior_subset hy) hpos hb hab

lemma rdg_path {x0 x : E} :
    Tendsto (fun t : ℝ => t • x0 + (1 - t) • x) (𝓝[>] 0) (𝓝 x) := by
  have hc : Continuous (fun t : ℝ => t • x0 + (1 - t) • x) := by fun_prop
  have h2 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  simpa using h2

lemma rdg_path_mem {Q : Set E} (hQ : Convex ℝ Q) {x0 x : E} (hx0 : x0 ∈ intrinsicInterior ℝ Q)
    (hx : x ∈ Q) : ∀ᶠ t in 𝓝[>] (0:ℝ), t • x0 + (1 - t) • x ∈ intrinsicInterior ℝ Q := by
  filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  exact rdg_combo hQ hx0 hx ht.1 (by linarith [ht.2]) (by ring)

lemma rdg_ext {Q : Set E} (hQ : Convex ℝ Q) {φ : E → ℝ} (hd : ∀ x ∈ Q, DifferentiableAt ℝ φ x)
    (hineq : ∀ x ∈ intrinsicInterior ℝ Q, ∀ y ∈ intrinsicInterior ℝ Q,
      φ x + fderiv ℝ φ x (y - x) ≤ φ y) :
    ∀ x ∈ Q, ∀ y ∈ Q, φ x + fderiv ℝ φ x (y - x) ≤ φ y := by
  have hRQ : intrinsicInterior ℝ Q ⊆ Q := intrinsicInterior_subset
  have hRc : Convex ℝ (intrinsicInterior ℝ Q) := rdg_relint_convex hQ
  have hconvR : ∀ x ∈ intrinsicInterior ℝ Q, ∀ y ∈ intrinsicInterior ℝ Q, ∀ a b : ℝ, 0 ≤ a →
      0 ≤ b → a + b = 1 → φ (a • x + b • y) ≤ a * φ x + b * φ y := by
    intro x hx y hy a b ha hb hab
    have hz : a • x + b • y ∈ intrinsicInterior ℝ Q := hRc hx hy ha hb hab
    have h1 := hineq _ hz x hx
    have h2 := hineq _ hz y hy
    have e1 : x - (a • x + b • y) = b • (x - y) := by
      obtain rfl : a = 1 - b := by linarith
      module
    have e2 : y - (a • x + b • y) = (-a) • (x - y) := by
      obtain rfl : b = 1 - a := by linarith
      module
    rw [e1, map_smul, smul_eq_mul] at h1
    rw [e2, map_smul, smul_eq_mul] at h2
    have m1 := mul_le_mul_of_nonneg_left h1 ha
    have m2 := mul_le_mul_of_nonneg_left h2 hb
    have m3 : φ (a • x + b • y) = (a + b) * φ (a • x + b • y) := by rw [hab, one_mul]
    nlinarith
  have hconvQ : ∀ x ∈ Q, ∀ y ∈ Q, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      φ (a • x + b • y) ≤ a * φ x + b * φ y := by
    intro x hx y hy a b ha hb hab
    obtain ⟨x0, hx0⟩ := Set.Nonempty.intrinsicInterior hQ ⟨x, hx⟩
    have hxs : Tendsto (fun t : ℝ => t • x0 + (1 - t) • x) (𝓝[>] 0) (𝓝 x) := rdg_path
    have hys : Tendsto (fun t : ℝ => t • x0 + (1 - t) • y) (𝓝[>] 0) (𝓝 y) := rdg_path
    have hz : Tendsto (fun t : ℝ => a • (t • x0 + (1 - t) • x) + b • (t • x0 + (1 - t) • y))
        (𝓝[>] 0) (𝓝 (a • x + b • y)) := (hxs.const_smul a).add (hys.const_smul b)
    have hzQ : a • x + b • y ∈ Q := hQ hx hy ha hb hab
    have c1 := ((hd _ hzQ).continuousAt.tendsto).comp hz
    have c2 := ((hd x hx).continuousAt.tendsto).comp hxs
    have c3 := ((hd y hy).continuousAt.tendsto).comp hys
    refine le_of_tendsto_of_tendsto c1 ((c2.const_mul a).add (c3.const_mul b)) ?_
    filter_upwards [rdg_path_mem hQ hx0 hx, rdg_path_mem hQ hx0 hy] with t h1 h2
    exact hconvR _ h1 _ h2 a b ha hb hab
  intro p hp u hu
  have hline : HasDerivAt (fun t : ℝ => φ (p + t • (u - p))) (fderiv ℝ φ p (u - p)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p + t • (u - p)) (u - p) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (u - p)).const_add p
    have h2 : HasFDerivAt φ (fderiv ℝ φ p) (p + (0:ℝ) • (u - p)) := by
      simpa using (hd p hp).hasFDerivAt
    exact h2.comp_hasDerivAt (0:ℝ) h1
  have hslope := hline.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ),
      t⁻¹ • (φ (p + (0 + t) • (u - p)) - φ (p + (0:ℝ) • (u - p))) ≤ φ u - φ p := by
    filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    have h3 := hconvQ p hp u hu (1 - t) t (by linarith [ht.2]) ht.1.le (by ring)
    have e : (1 - t) • p + t • u = p + t • (u - p) := by module
    rw [e] at h3
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht.1]
    nlinarith
  have := le_of_tendsto hslope hev
  linarith

lemma rdg_ext_comb {Q : Set E} (hQ : Convex ℝ Q) {f h : E → ℝ}
    (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (a c : ℝ)
    (hineq : ∀ x ∈ intrinsicInterior ℝ Q, ∀ y ∈ intrinsicInterior ℝ Q,
      0 ≤ a * (f y - f x - fderiv ℝ f x (y - x)) + c * (h y - h x - fderiv ℝ h x (y - x))) :
    ∀ x ∈ Q, ∀ y ∈ Q,
      0 ≤ a * (f y - f x - fderiv ℝ f x (y - x)) + c * (h y - h x - fderiv ℝ h x (y - x)) := by
  have hder : ∀ x ∈ Q, HasFDerivAt (fun w => a * f w + c * h w)
      (a • fderiv ℝ f x + c • fderiv ℝ h x) x := fun x hx =>
    ((hfd x hx).hasFDerivAt.const_mul a).add ((hhd x hx).hasFDerivAt.const_mul c)
  have key := rdg_ext hQ (φ := fun w => a * f w + c * h w)
    (fun x hx => (hder x hx).differentiableAt) (by
      intro x hx y hy
      have hxQ := intrinsicInterior_subset hx
      rw [(hder x hxQ).fderiv]
      have := hineq x hx y hy
      simp only [add_apply, smul_apply, smul_eq_mul]
      nlinarith)
  intro x hx y hy
  have := key x hx y hy
  rw [(hder x hx).fderiv] at this
  simp only [add_apply, smul_apply, smul_eq_mul] at this
  nlinarith

end RDGrelint

section RDGrun
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma rdg_sc_ext {Q : Set E} (hQ : Convex ℝ Q) {f h : E → ℝ}
    (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x)
    {μ : ℝ} (hsc : IsRelStronglyConvex Q f h μ) :
    ∀ x ∈ Q, ∀ y ∈ Q, f x + fderiv ℝ f x (y - x) + μ * bregman h y x ≤ f y := by
  have := rdg_ext_comb hQ hfd hhd 1 (-μ) (by
    intro x hx y hy
    have := hsc x hx y hy
    simp only [bregman] at this
    nlinarith)
  intro x hx y hy
  have := this x hx y hy
  simp only [bregman]
  nlinarith

lemma rdg_sm_ext {Q : Set E} (hQ : Convex ℝ Q) {f h : E → ℝ}
    (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x)
    {L : ℝ} (hsm : IsRelSmooth Q f h L) :
    ∀ x ∈ Q, ∀ y ∈ Q, f y ≤ f x + fderiv ℝ f x (y - x) + L * bregman h y x := by
  have := rdg_ext_comb hQ hfd hhd (-1) L (by
    intro x hx y hy
    have := hsm x hx y hy
    simp only [bregman] at this
    nlinarith)
  intro x hx y hy
  have := this x hx y hy
  simp only [bregman]
  nlinarith

lemma rdg_xmem {Q : Set E} {f h : E → ℝ} {L μ : ℝ} {x : ℕ → E}
    (hrun : IsDualAveragingRun Q f h L μ x) (k : ℕ) : x k ∈ Q := by
  cases k with
  | zero => exact hrun.1
  | succ k => exact (hrun.2.2.2 k).1

lemma rdg_min {Q : Set E} {f h : E → ℝ} {L μ : ℝ} {x : ℕ → E}
    (hrun : IsDualAveragingRun Q f h L μ x) (k : ℕ) :
    ∀ u ∈ Q, daModel f h L μ x k (x k) ≤ daModel f h L μ x k u := by
  cases k with
  | zero =>
    intro w hw
    have := hrun.2.2.1 w hw
    simpa [daModel] using this
  | succ k => exact fun w hw => (hrun.2.2.2 k).2 w hw

lemma rdg_wpos {L μ : ℝ} (hμL : μ < L) (hμ : 0 ≤ μ) (k : ℕ) : 0 < daWeight L μ k := by
  have hd : 0 < L - μ := by linarith
  have hL : 0 < L := by linarith
  unfold daWeight; positivity

lemma rdg_c {L μ : ℝ} (hμL : μ < L) (hμ : 0 ≤ μ) (k : ℕ) :
    1 + μ * daSum L μ k = (L - μ) * daWeight L μ k := by
  have hd : 0 < L - μ := by linarith
  have hstep : ∀ j : ℕ, daSum L μ (j + 1) = daSum L μ j + daWeight L μ j := by
    intro j; simp [daSum, Finset.sum_range_succ]
  have key : ∀ j : ℕ, 1 + μ * daSum L μ j = (L / (L - μ)) ^ j := by
    intro j
    induction j with
    | zero => simp [daSum]
    | succ j ih =>
      rw [hstep, mul_add, ← add_assoc, ih, daWeight, pow_succ]
      field_simp
      ring
  rw [key k, daWeight]
  field_simp

lemma rdg_model_succ {f h : E → ℝ} {L μ : ℝ} {x : ℕ → E} (k : ℕ) (u : E) :
    daModel f h L μ x (k + 1) u = daModel f h L μ x k u + daWeight L μ k *
      (f (x k) + fderiv ℝ f (x k) (u - x k) + μ * bregman h u (x k)) := by
  simp only [daModel, Finset.sum_range_succ]
  ring

theorem rdg_eq35
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L)
    (x : ℕ → E) (hrun : IsDualAveragingRun Q f h L μ x) :
    ∀ k : ℕ, ∀ u ∈ Q,
      (1 + μ * daSum L μ k) * bregman h u (x k) = bregman (daModel f h L μ x k) u (x k) ∧
      bregman (daModel f h L μ x k) u (x k) ≤
        daModel f h L μ x k u - daModel f h L μ x k (x k) := by
  intro k u hu
  have hxk : x k ∈ Q := by
    cases k with
    | zero => exact hrun.1
    | succ k => exact (hrun.2.2.2 k).1
  have hdh : DifferentiableAt ℝ h (x k) := hhd _ hxk
  have hmin : IsMinOn (daModel f h L μ x k) Q (x k) := by
    cases k with
    | zero =>
      intro w hw
      have := hrun.2.2.1 w hw
      simpa [daModel] using this
    | succ k => exact fun w hw => (hrun.2.2.2 k).2 w hw
  set G : E →L[ℝ] ℝ := fderiv ℝ h (x k) + ∑ i ∈ Finset.range k, daWeight L μ i •
        (fderiv ℝ f (x i) + μ • (fderiv ℝ h (x k) - fderiv ℝ h (x i))) with hG
  have hψ : HasFDerivAt (daModel f h L μ x k) G (x k) := by
    unfold daModel
    simp only [bregman]
    refine hdh.hasFDerivAt.add ?_
    apply HasFDerivAt.fun_sum
    intro i _
    have h1 : HasFDerivAt (fun w : E => fderiv ℝ f (x i) (w - x i)) (fderiv ℝ f (x i)) (x k) := by
      have := ((fderiv ℝ f (x i)).hasFDerivAt (x := x k)).sub_const (fderiv ℝ f (x i) (x i))
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [map_sub])
    have h2 : HasFDerivAt (fun w : E => fderiv ℝ h (x i) (w - x i)) (fderiv ℝ h (x i)) (x k) := by
      have := ((fderiv ℝ h (x i)).hasFDerivAt (x := x k)).sub_const (fderiv ℝ h (x i) (x i))
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [map_sub])
    have := (((hasFDerivAt_const (f (x i)) (x k)).add h1).add
      (((hdh.hasFDerivAt.sub_const (h (x i))).sub h2).const_mul μ)).const_mul (daWeight L μ i)
    refine HasFDerivAt.congr_of_eventuallyEq (this.congr_fderiv ?_)
      (Filter.Eventually.of_forall fun y => ?_)
    · simp
    · simp only [Pi.add_apply, Pi.sub_apply]
  have hnn : 0 ≤ G (u - x k) :=
    hmin.localize.hasFDerivWithinAt_nonneg hψ.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hQ.segment_subset hxk hu))
  have hbreg : bregman (daModel f h L μ x k) u (x k) =
      daModel f h L μ x k u - daModel f h L μ x k (x k) - G (u - x k) := by
    unfold bregman
    rw [hψ.fderiv]
  refine ⟨?_, ?_⟩
  · rw [hbreg]
    have hGe : G (u - x k) = fderiv ℝ h (x k) (u - x k) + ∑ i ∈ Finset.range k, daWeight L μ i *
        (fderiv ℝ f (x i) (u - x k) + μ * (fderiv ℝ h (x k) (u - x k) - fderiv ℝ h (x i) (u - x k))) := by
      simp only [hG, add_apply, sum_apply,
        smul_apply, sub_apply, smul_eq_mul]
    have hterm : ∀ i ∈ Finset.range k,
        daWeight L μ i * (f (x i) + fderiv ℝ f (x i) (u - x i) + μ * bregman h u (x i)) -
          daWeight L μ i * (f (x i) + fderiv ℝ f (x i) (x k - x i) + μ * bregman h (x k) (x i)) -
          daWeight L μ i * (fderiv ℝ f (x i) (u - x k) +
            μ * (fderiv ℝ h (x k) (u - x k) - fderiv ℝ h (x i) (u - x k))) =
        daWeight L μ i * μ * bregman h u (x k) := by
      intro i _
      unfold bregman
      simp only [map_sub]
      ring
    have hsum : ∑ i ∈ Finset.range k, daWeight L μ i * (f (x i) + fderiv ℝ f (x i) (u - x i) +
          μ * bregman h u (x i)) -
        ∑ i ∈ Finset.range k, daWeight L μ i * (f (x i) + fderiv ℝ f (x i) (x k - x i) +
          μ * bregman h (x k) (x i)) -
        ∑ i ∈ Finset.range k, daWeight L μ i *
          (fderiv ℝ f (x i) (u - x k) + μ * (fderiv ℝ h (x k) (u - x k) - fderiv ℝ h (x i) (u - x k))) =
        μ * daSum L μ k * bregman h u (x k) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm]
      unfold daSum
      rw [mul_comm μ, Finset.sum_mul, Finset.sum_mul]
    have hBh : bregman h u (x k) = h u - h (x k) - fderiv ℝ h (x k) (u - x k) := rfl
    have hu1 : daModel f h L μ x k u = h u + ∑ i ∈ Finset.range k, daWeight L μ i *
        (f (x i) + fderiv ℝ f (x i) (u - x i) + μ * bregman h u (x i)) := rfl
    have hu2 : daModel f h L μ x k (x k) = h (x k) + ∑ i ∈ Finset.range k, daWeight L μ i *
        (f (x i) + fderiv ℝ f (x i) (x k - x i) + μ * bregman h (x k) (x i)) := rfl
    rw [hGe, hu1, hu2]
    rw [hBh] at hsum ⊢
    linarith
  · rw [hbreg]
    linarith


lemma rdg_step {Q : Set E} (hQ : Convex ℝ Q)
    {f h : E → ℝ} (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    {L μ : ℝ} (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L)
    {x : ℕ → E} (hrun : IsDualAveragingRun Q f h L μ x) (k : ℕ) :
    daModel f h L μ x (k + 1) (x (k + 1)) ≥
      daModel f h L μ x k (x k) + daWeight L μ k * f (x (k + 1)) := by
  have hk := rdg_xmem hrun k
  have hk1 := rdg_xmem hrun (k + 1)
  have e35 := rdg_eq35 Q hQ f h hfd hfc hhd hhc L μ hμ hμL x hrun k (x (k + 1)) hk1
  have hsmk := rdg_sm_ext hQ hfd hhd hsm (x k) hk (x (k + 1)) hk1
  have hsucc := rdg_model_succ (f := f) (h := h) (L := L) (μ := μ) (x := x) k (x (k + 1))
  have hc := rdg_c hμL hμ k
  have ha := rdg_wpos hμL hμ k
  have key : (L - μ) * daWeight L μ k * bregman h (x (k + 1)) (x k) ≤
      daModel f h L μ x k (x (k + 1)) - daModel f h L μ x k (x k) := by
    have h2 := e35.2
    rw [← e35.1, hc] at h2
    exact h2
  have hm := mul_le_mul_of_nonneg_left hsmk ha.le
  rw [ge_iff_le, hsucc]
  nlinarith

lemma rdg_eq34 {Q : Set E} (hQ : Convex ℝ Q)
    {f h : E → ℝ} (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x)
    {L μ : ℝ} (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsc : IsRelStronglyConvex Q f h μ)
    {x : ℕ → E} (hrun : IsDualAveragingRun Q f h L μ x) (k : ℕ) (u : E) (hu : u ∈ Q) :
    daModel f h L μ x k (x k) ≤ h u + daSum L μ k * f u := by
  refine (rdg_min hrun k u hu).trans ?_
  unfold daModel daSum
  rw [Finset.sum_mul]
  have : ∑ i ∈ Finset.range k, daWeight L μ i *
      (f (x i) + fderiv ℝ f (x i) (u - x i) + μ * bregman h u (x i)) ≤
      ∑ i ∈ Finset.range k, daWeight L μ i * f u :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (by have := rdg_sc_ext hQ hfd hhd hsc (x i) (rdg_xmem hrun i) u hu; linarith)
      (rdg_wpos hμL hμ i).le
  linarith

end RDGrun

theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q)
    (f h : E → ℝ) (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsDualAveragingRun Q f h L μ x) :
    ∀ k : ℕ, ∀ u ∈ Q,
      ∑ i ∈ Finset.range k, daWeight L μ i * f (x (i + 1)) ≤ daModel f h L μ x k (x k) ∧
      daModel f h L μ x k (x k) ≤ h u + daSum L μ k * f u := by
  have hlow : ∀ k : ℕ, ∑ i ∈ Finset.range k, daWeight L μ i * f (x (i + 1)) ≤
      daModel f h L μ x k (x k) := by
    intro k
    induction k with
    | zero => simp [daModel, hrun.2.1]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have := rdg_step hQ hfd hfc hhd hhc hμ hμL hsm hrun k
      linarith
  exact fun k u hu => ⟨hlow k, rdg_eq34 hQ hfd hhd hμ hμL hsc hrun k u hu⟩
