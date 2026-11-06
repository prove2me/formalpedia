-- Prove2me | solution 1 for ProductFraming.Nest.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:17:58.258133+00:00
-- url     : https://prove2.me/submissions/889084ef-f576-4f12-b3db-e33b7e875afe

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

open MeasureTheory ProbabilityTheory Set Real

namespace PFNExpAux

lemma integral_expMeasure {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂(expMeasure r) = ∫ x in Ioi 0, r * exp (-(r * x)) * f x := by
  show ∫ x, f x ∂(volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal 1 r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_gammaPDFReal 1 r).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  congr 1
  ext x
  simp only [smul_eq_mul, indicator]
  rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hr x)]
  unfold gammaPDFReal
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (mem_Ici.mpr h1) h2
  · exact absurd (mem_Ici.mp h2) h1
  · simp

lemma ae_nonneg_expMeasure (r : ℝ) : ∀ᵐ w ∂(expMeasure r), 0 ≤ w := by
  rw [ae_iff]
  simp only [not_le]
  show expMeasure r (Iio 0) = 0
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0) (fun x hx => gammaPDF_of_neg hx)]
  simp

/-- `E[min(Z, w)] = (1 - e^{-r w}) / r` for `Z` exponential with rate `r` and `w ≥ 0`. -/
lemma integral_min_expMeasure {r : ℝ} (hr : 0 < r) {w : ℝ} (hw : 0 ≤ w) :
    ∫ z, min z w ∂(expMeasure r) = (1 - exp (-(r * w))) / r := by
  rw [integral_expMeasure hr]
  have hint1 : IntegrableOn (fun z => r * exp (-(r * z)) * min z w) (Ioc 0 w) := by
    apply ContinuousOn.integrableOn_Icc ?_ |>.mono_set Ioc_subset_Icc_self
    fun_prop
  have hint2 : IntegrableOn (fun z => r * exp (-(r * z)) * min z w) (Ioi w) := by
    have : IntegrableOn (fun z => r * w * exp (-r * z)) (Ioi w) :=
      (exp_neg_integrableOn_Ioi w hr).const_mul (r * w)
    refine this.congr_fun (fun z hz => ?_) measurableSet_Ioi
    simp only
    rw [min_eq_right (le_of_lt (mem_Ioi.mp hz))]
    ring_nf
  rw [← Ioc_union_Ioi_eq_Ioi hw, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    hint1 hint2]
  have h1 : ∫ z in Ioc 0 w, r * exp (-(r * z)) * min z w
      = ∫ z in Ioc 0 w, r * z * exp (-(r * z)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    simp only
    rw [min_eq_left hz.2]; ring
  have h2 : ∫ z in Ioi w, r * exp (-(r * z)) * min z w
      = ∫ z in Ioi w, (r * w) * exp ((-r) * z) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    simp only
    rw [min_eq_right (le_of_lt (mem_Ioi.mp hz))]; ring_nf
  rw [h1, h2, integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  rw [← intervalIntegral.integral_of_le hw]
  have hderiv : ∀ x ∈ uIcc 0 w, HasDerivAt (fun z => -z * exp (-(r * z)) - exp (-(r * z)) / r)
      (r * x * exp (-(r * x))) x := by
    intro x _
    have he : HasDerivAt (fun z => exp (-(r * z))) (exp (-(r * x)) * (-r)) x := by
      have := ((hasDerivAt_id x).const_mul r).neg.exp
      simpa using this
    have := ((hasDerivAt_neg x).mul he).sub (he.div_const r)
    have h' := this.congr_deriv (show _ = r * x * exp (-(r * x)) by field_simp; ring)
    exact h'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  field_simp
  ring_nf
  rw [Real.exp_zero]; ring

/-- `E[Z] = 1/r` for `Z` exponential with rate `r`. -/
lemma integral_id_expMeasure {r : ℝ} (hr : 0 < r) : ∫ z, z ∂(expMeasure r) = r⁻¹ := by
  rw [integral_expMeasure hr]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.Gamma_two, mul_one] at h
  simp only [Real.rpow_one] at h
  have : ∫ z in Ioi (0 : ℝ), r * exp (-(r * z)) * z = r * ∫ z in Ioi (0 : ℝ), z * exp (-(r * z)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z _; simp only; ring
  rw [this, h]
  norm_num [Real.rpow_two, div_pow]
  field_simp

lemma integrable_id_expMeasure {r : ℝ} (hr : 0 < r) : Integrable (fun z : ℝ => z) (expMeasure r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_id_expMeasure hr]
  exact (inv_pos.mpr hr).ne'

end PFNExpAux

open Finset ProductFraming.Nest

namespace PFNL7Aux

lemma sum_Icc_split (f : ℕ → ℝ) {x m : ℕ} (h : x ≤ m) :
    ∑ y ∈ Finset.Icc x m, f y = f x + ∑ y ∈ Finset.Icc (x + 1) m, f y := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc h, sum_insert]
  simp

lemma tail_succ (m : ℕ) (lam : ℕ → ℝ) {x : ℕ} (h : x ≤ m) :
    tail m lam x = lam x + tail m lam (x + 1) := by
  unfold tail; exact sum_Icc_split lam h

lemma tail_nonneg (m : ℕ) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) {z : ℕ} (hz : 1 ≤ z) :
    0 ≤ tail m lam z := by
  unfold tail
  apply sum_nonneg
  intro y hy
  rw [Finset.mem_Icc] at hy
  exact hlam.1 y (Finset.mem_Icc.mpr ⟨by omega, hy.2⟩)

lemma tail_anti (m : ℕ) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) {z w : ℕ} (hz : 1 ≤ z)
    (hzw : z ≤ w) : tail m lam w ≤ tail m lam z := by
  unfold tail
  apply sum_le_sum_of_subset_of_nonneg
  · intro y hy; rw [Finset.mem_Icc] at hy ⊢; omega
  · intro y hy _
    rw [Finset.mem_Icc] at hy
    exact hlam.1 y (Finset.mem_Icc.mpr ⟨by omega, hy.2⟩)

lemma A_eq_B (m : ℕ) (lam : ℕ → ℝ) :
    ∀ d x, x + d = m + 1 →
      ∑ y ∈ Finset.Icc x m, lam y * ((y : ℝ) - x + 1) = ∑ z ∈ Finset.Icc x m, tail m lam z := by
  intro d
  induction d with
  | zero =>
    intro x hx
    have : Finset.Icc x m = ∅ := by ext y; simp; omega
    simp [this]
  | succ d ih =>
    intro x hx
    have hxm : x ≤ m := by omega
    have ih' := ih (x + 1) (by omega)
    rw [sum_Icc_split _ hxm, sum_Icc_split _ hxm, ← ih', tail_succ m lam hxm]
    unfold tail
    rw [show lam x * ((x : ℝ) - x + 1) = lam x by ring, add_assoc, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl; intro i _; push_cast; ring

lemma q_eq (m : ℕ) (lam : ℕ → ℝ) (x : ℕ) :
    q m lam x = (∑ z ∈ Finset.Icc x m, tail m lam z) / tail m lam x := by
  unfold q
  by_cases hx : x ≤ m + 1
  · rw [A_eq_B m lam (m + 1 - x) x (by omega)]
  · have : Finset.Icc x m = ∅ := by ext y; simp; omega
    simp [this]

/-- `B(j) = E[(X - j + 1)^+] = ∑_{z ≥ j} Λ(z)`. -/
noncomputable def B (m : ℕ) (lam : ℕ → ℝ) (j : ℕ) : ℝ := ∑ z ∈ Finset.Icc j m, tail m lam z

lemma B_one (m : ℕ) (lam : ℕ → ℝ) : B m lam 1 = mean m lam := by
  unfold B
  rw [← A_eq_B m lam m 1 (by omega), mean]
  apply sum_congr rfl; intro y _; push_cast; ring

lemma B_nonneg (m : ℕ) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ B m lam j := by
  unfold B; apply sum_nonneg; intro z hz
  exact tail_nonneg m lam hlam (le_trans hj (Finset.mem_Icc.mp hz).1)

lemma B_le_tail (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 m) : B m lam j ≤ mean m lam * tail m lam j := by
  have hq := hA3 j hj
  rw [q_eq, q_eq] at hq
  have ht1 : tail m lam 1 = 1 := hlam.2
  rw [ht1, div_one] at hq
  change B m lam j / tail m lam j ≤ B m lam 1 at hq
  rw [B_one] at hq
  rw [Finset.mem_Icc] at hj
  rcases (tail_nonneg m lam hlam hj.1).lt_or_eq with hpos | hzero
  · rw [div_le_iff₀ hpos] at hq; linarith
  · have : B m lam j = 0 := by
      unfold B
      apply sum_eq_zero
      intro z hz
      rw [Finset.mem_Icc] at hz
      have h1 := tail_anti m lam hlam (z := j) (w := z) hj.1 hz.1
      have h2 := tail_nonneg m lam hlam (z := z) (by omega)
      linarith
    rw [this, ← hzero]; simp

lemma B_succ (m : ℕ) (lam : ℕ → ℝ) {j : ℕ} (hj : j ≤ m) :
    B m lam j = tail m lam j + B m lam (j + 1) := by
  unfold B; exact sum_Icc_split _ hj

lemma B_geom (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam)
    (hμ : 1 ≤ mean m lam) :
    ∀ k, k < m → B m lam (k + 1) ≤ mean m lam * (1 - 1 / mean m lam) ^ k := by
  have hμpos : 0 < mean m lam := by linarith
  have hρ : 0 ≤ 1 - 1 / mean m lam := by
    rw [sub_nonneg, div_le_one hμpos]; exact hμ
  intro k
  induction k with
  | zero => intro _; rw [B_one]; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hsplit := B_succ m lam (j := k + 1) (by omega)
    have hle := B_le_tail m hm lam hlam hA3 (j := k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hB0 := B_nonneg m lam hlam (j := k + 1) (by omega)
    -- `B(k+2) = B(k+1) - Λ(k+1) ≤ (1 - 1/μ) B(k+1)`
    have h1 : B m lam (k + 1 + 1) ≤ (1 - 1 / mean m lam) * B m lam (k + 1) := by
      have : B m lam (k + 1) / mean m lam ≤ tail m lam (k + 1) := by
        rw [div_le_iff₀ hμpos]; linarith
      have h2 : (1 - 1 / mean m lam) * B m lam (k + 1) = B m lam (k + 1) - B m lam (k + 1) / mean m lam := by
        ring
      rw [h2]; linarith
    calc B m lam (k + 1 + 1) ≤ (1 - 1 / mean m lam) * B m lam (k + 1) := h1
      _ ≤ (1 - 1 / mean m lam) * (mean m lam * (1 - 1 / mean m lam) ^ k) :=
          mul_le_mul_of_nonneg_left ih' hρ
      _ = mean m lam * (1 - 1 / mean m lam) ^ (k + 1) := by ring

open PFNExpAux in
/-- The stop-loss comparison: `E[(X - t)^+] ≤ E[(Z - t)^+]` for every real `t`. -/
lemma hinge (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam)
    (hμ : 1 ≤ mean m lam) (t : ℝ) :
    ∑ x ∈ Finset.Icc 1 m, lam x * max ((x : ℝ) - t) 0 ≤
      ∫ z, max (z - t) 0 ∂(expMeasure (mean m lam)⁻¹) := by
  set μ := mean m lam with hμdef
  have hμpos : 0 < μ := by linarith
  have hr : 0 < μ⁻¹ := inv_pos.mpr hμpos
  haveI := isProbabilityMeasure_expMeasure hr
  have hid := integrable_id_expMeasure hr
  rcases le_or_gt t 0 with ht | ht
  · -- both sides equal `μ - t`
    have hL : ∑ x ∈ Finset.Icc 1 m, lam x * max ((x : ℝ) - t) 0 = μ - t := by
      have : ∑ x ∈ Finset.Icc 1 m, lam x * max ((x : ℝ) - t) 0
          = ∑ x ∈ Finset.Icc 1 m, (lam x * (x : ℝ) - t * lam x) := by
        apply sum_congr rfl; intro x hx
        have : (1 : ℝ) ≤ x := by exact_mod_cast (Finset.mem_Icc.mp hx).1
        rw [max_eq_left (by linarith)]; ring
      rw [this, sum_sub_distrib, ← mul_sum, hlam.2, hμdef, mean]; ring
    have hR : ∫ z, max (z - t) 0 ∂(expMeasure μ⁻¹) = μ - t := by
      have : ∫ z, max (z - t) 0 ∂(expMeasure μ⁻¹) = ∫ z, (z - t) ∂(expMeasure μ⁻¹) := by
        apply integral_congr_ae
        filter_upwards [ae_nonneg_expMeasure μ⁻¹] with z hz
        exact max_eq_left (by linarith)
      rw [this, integral_sub hid (integrable_const t), integral_id_expMeasure hr, inv_inv]
      simp
    rw [hL, hR]
  · -- `t > 0`: the right side is `μ e^{-t/μ}`
    have hR : ∫ z, max (z - t) 0 ∂(expMeasure μ⁻¹) = μ * exp (-(μ⁻¹ * t)) := by
      have : ∫ z, max (z - t) 0 ∂(expMeasure μ⁻¹) = ∫ z, (z - min z t) ∂(expMeasure μ⁻¹) := by
        apply integral_congr_ae
        filter_upwards with z
        rcases le_total z t with h | h
        · rw [min_eq_left h, max_eq_right (by linarith)]; ring
        · rw [min_eq_right h, max_eq_left (by linarith)]
      have hmin_int : Integrable (fun z : ℝ => min z t) (expMeasure μ⁻¹) :=
        hid.inf (integrable_const t)
      rw [this, integral_sub hid hmin_int, integral_id_expMeasure hr,
        integral_min_expMeasure hr ht.le, inv_inv]
      field_simp
      ring
    rw [hR]
    set k := ⌊t⌋₊ with hk
    have hk1 : (k : ℝ) ≤ t := Nat.floor_le ht.le
    have hk2 : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
    rcases le_or_gt m k with hmk | hmk
    · -- no page beyond `t`
      have : ∑ x ∈ Finset.Icc 1 m, lam x * max ((x : ℝ) - t) 0 = 0 := by
        apply sum_eq_zero; intro x hx
        have : (x : ℝ) ≤ k := by exact_mod_cast le_trans (Finset.mem_Icc.mp hx).2 hmk
        rw [max_eq_right (by linarith)]; ring
      rw [this]; positivity
    · set s := t - k with hs
      have hs0 : 0 ≤ s := by linarith
      have hs1 : s < 1 := by linarith
      -- the left side is `B(k+1) - s Λ(k+1)`
      have hL : ∑ x ∈ Finset.Icc 1 m, lam x * max ((x : ℝ) - t) 0
          = B m lam (k + 1) - s * tail m lam (k + 1) := by
        have hsub : ∑ x ∈ Finset.Icc (k + 1) m, lam x * max ((x : ℝ) - t) 0
            = ∑ x ∈ Finset.Icc 1 m, lam x * max ((x : ℝ) - t) 0 := by
          apply sum_subset
          · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
          · intro x hx hx'
            rw [Finset.mem_Icc] at hx hx'
            have : (x : ℝ) ≤ k := by exact_mod_cast (by omega : x ≤ k)
            rw [max_eq_right (by linarith)]; ring
        rw [← hsub]
        unfold B
        rw [← A_eq_B m lam (m - k) (k + 1) (by omega), tail, mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro x hx
        have : ((k + 1 : ℕ) : ℝ) ≤ x := by exact_mod_cast (Finset.mem_Icc.mp hx).1
        push_cast at this
        rw [max_eq_left (by linarith)]
        push_cast; ring
      rw [hL]
      have hB := B_geom m hm lam hlam hA3 hμ k hmk
      have hBt := B_le_tail m hm lam hlam hA3 (j := k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hB0 := B_nonneg m lam hlam (j := k + 1) (by omega)
      have hρ0 : 0 ≤ 1 - 1 / μ := by rw [sub_nonneg, div_le_one hμpos]; exact hμ
      have hsμ : 0 ≤ 1 - s / μ := by rw [sub_nonneg, div_le_one hμpos]; linarith
      -- step 1: `B - sΛ ≤ B (1 - s/μ)`
      have h1 : B m lam (k + 1) - s * tail m lam (k + 1) ≤ B m lam (k + 1) * (1 - s / μ) := by
        have : B m lam (k + 1) / μ ≤ tail m lam (k + 1) := by
          rw [div_le_iff₀ hμpos]; linarith
        have h' : s * (B m lam (k + 1) / μ) ≤ s * tail m lam (k + 1) :=
          mul_le_mul_of_nonneg_left this hs0
        have : B m lam (k + 1) * (1 - s / μ) = B m lam (k + 1) - s * (B m lam (k + 1) / μ) := by ring
        linarith
      -- step 2: `(1 - 1/μ)^k ≤ e^{-k/μ}` and `1 - s/μ ≤ e^{-s/μ}`
      have he1 : 1 - 1 / μ ≤ exp (-(1 / μ)) := by linarith [add_one_le_exp (-(1 / μ))]
      have he2 : 1 - s / μ ≤ exp (-(s / μ)) := by linarith [add_one_le_exp (-(s / μ))]
      have hpow : (1 - 1 / μ) ^ k ≤ exp (-(1 / μ)) ^ k := pow_le_pow_left₀ hρ0 he1 k
      rw [← Real.exp_nat_mul] at hpow
      calc B m lam (k + 1) - s * tail m lam (k + 1) ≤ B m lam (k + 1) * (1 - s / μ) := h1
        _ ≤ μ * (1 - 1 / μ) ^ k * (1 - s / μ) := mul_le_mul_of_nonneg_right hB hsμ
        _ ≤ μ * exp (k * -(1 / μ)) * exp (-(s / μ)) := by
            apply mul_le_mul _ he2 hsμ (by positivity)
            exact mul_le_mul_of_nonneg_left hpow hμpos.le
        _ = μ * exp (-(μ⁻¹ * t)) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            rw [hs]; field_simp; ring

/-- A supporting line of a convex function at an interior point. -/
lemma support {g : ℝ → ℝ} (hg : ConvexOn ℝ (Ici 0) g) {j : ℝ} (hj : 0 < j) {y : ℝ} (hy : 0 ≤ y) :
    g j + derivWithin g (Ioi j) j * (y - j) ≤ g y := by
  have hjint : j ∈ interior (Ici (0 : ℝ)) := by rw [interior_Ici]; exact hj
  rcases lt_trichotomy y j with hlt | heq | hgt
  · have h1 := hg.slope_le_leftDeriv_of_mem_interior (mem_Ici.mpr hy) hjint hlt
    have h2 := hg.leftDeriv_le_rightDeriv_of_mem_interior hjint
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h1
    nlinarith
  · subst heq; simp
  · have h1 := hg.rightDeriv_le_slope_of_mem_interior hjint (mem_Ici.mpr hy) hgt
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
    linarith

open PFNExpAux in
lemma affine_bound (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam)
    (hμ : 1 ≤ mean m lam) (α σ : ℝ) (hσ : 0 ≤ σ) :
    ∑ x ∈ Finset.Icc 1 m, lam x * max (α + σ * x) 0 ≤
      ∫ z, max (α + σ * z) 0 ∂(expMeasure (mean m lam)⁻¹) := by
  have hμpos : 0 < mean m lam := by linarith
  have hr : 0 < (mean m lam)⁻¹ := inv_pos.mpr hμpos
  haveI := isProbabilityMeasure_expMeasure hr
  rcases hσ.lt_or_eq with hpos | hzero
  · have hrw : ∀ y : ℝ, max (α + σ * y) 0 = σ * max (y - (-α / σ)) 0 := by
      intro y
      have key : α + σ * y = σ * (y - (-α / σ)) := by field_simp; ring
      rw [key, mul_max_of_nonneg _ _ hpos.le, mul_zero]
    simp_rw [hrw]
    rw [integral_const_mul]
    have := hinge m hm lam hlam hA3 hμ (-α / σ)
    calc ∑ x ∈ Finset.Icc 1 m, lam x * (σ * max ((x : ℝ) - -α / σ) 0)
        = σ * ∑ x ∈ Finset.Icc 1 m, lam x * max ((x : ℝ) - -α / σ) 0 := by
          rw [mul_sum]; apply sum_congr rfl; intro x _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hpos.le
  · subst hzero
    simp only [zero_mul, add_zero]
    rw [← sum_mul, hlam.2, integral_const]
    simp

end PFNL7Aux

open PFNExpAux PFNL7Aux in
theorem solution (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam)
    (g : ℝ → ℝ) (hg_mono : MonotoneOn g (Set.Ici 0)) (hg_conv : ConvexOn ℝ (Set.Ici 0) g)
    (hg_int : Integrable g (expMeasure (mean m lam)⁻¹)) :
    ∑ x ∈ Icc 1 m, lam x * g (x : ℝ) ≤ ∫ z, g z ∂(expMeasure (mean m lam)⁻¹) := by
  set μ := mean m lam with hμdef
  have hμ : 1 ≤ μ := by
    rw [hμdef, mean, ← hlam.2]
    apply sum_le_sum
    intro y hy
    have : (1 : ℝ) ≤ y := by exact_mod_cast (Finset.mem_Icc.mp hy).1
    nlinarith [hlam.1 y hy]
  have hμpos : 0 < μ := by linarith
  have hr : 0 < μ⁻¹ := inv_pos.mpr hμpos
  haveI := isProbabilityMeasure_expMeasure hr
  have hid := integrable_id_expMeasure hr
  -- supporting lines at the nodes `j ≥ 1`
  set s : ℕ → ℝ := fun j => derivWithin g (Ioi (j : ℝ)) j with hs
  set ℓ : ℕ → ℝ → ℝ := fun j y => g j + s j * (y - j) with hℓ
  set d : ℕ → ℝ → ℝ := fun j y => ℓ (j + 1) y - ℓ j y with hd
  have hsup : ∀ j : ℕ, 1 ≤ j → ∀ y : ℝ, 0 ≤ y → ℓ j y ≤ g y := by
    intro j hj y hy
    exact support hg_conv (by exact_mod_cast hj) hy
  have hℓj : ∀ j : ℕ, ℓ j j = g j := by intro j; simp [hℓ]
  -- `d j` is affine with nonnegative slope, `≤ 0` left of `j`, `≥ 0` right of `j + 1`
  have hd_aff : ∀ j : ℕ, ∀ y a : ℝ, d j y = d j a + (s (j + 1) - s j) * (y - a) := by
    intro j y a; simp only [hd, hℓ]; ring
  have hdj : ∀ j : ℕ, 1 ≤ j → d j j ≤ 0 := by
    intro j hj
    have := hsup (j + 1) (by omega) j (Nat.cast_nonneg j)
    simp only [hd]; rw [hℓj]; linarith
  have hdj1 : ∀ j : ℕ, 1 ≤ j → 0 ≤ d j ((j : ℝ) + 1) := by
    intro j hj
    have := hsup j hj ((j : ℝ) + 1) (by positivity)
    have h2 : ℓ (j + 1) ((j : ℝ) + 1) = g ((j : ℝ) + 1) := by
      have := hℓj (j + 1); push_cast at this; exact this
    simp only [hd]; rw [h2]; linarith
  have hslope : ∀ j : ℕ, 1 ≤ j → 0 ≤ s (j + 1) - s j := by
    intro j hj
    have h1 := hdj j hj
    have h2 := hdj1 j hj
    have := hd_aff j ((j : ℝ) + 1) j
    nlinarith
  have hd_left : ∀ j : ℕ, 1 ≤ j → ∀ y : ℝ, y ≤ j → d j y ≤ 0 := by
    intro j hj y hy
    rw [hd_aff j y j]
    nlinarith [hdj j hj, hslope j hj]
  have hd_right : ∀ j : ℕ, 1 ≤ j → ∀ y : ℝ, (j : ℝ) + 1 ≤ y → 0 ≤ d j y := by
    intro j hj y hy
    rw [hd_aff j y ((j : ℝ) + 1)]
    nlinarith [hdj1 j hj, hslope j hj]
  -- the piecewise-linear minorant `H n = ℓ 1 + ∑_{j ∈ [1, n)} (d j)^+`
  set H : ℕ → ℝ → ℝ := fun n y => ℓ 1 y + ∑ j ∈ Finset.Ico 1 n, max (d j y) 0 with hH
  have hHsucc : ∀ n, 1 ≤ n → ∀ y, H (n + 1) y = H n y + max (d n y) 0 := by
    intro n hn y
    simp only [hH]
    rw [Finset.sum_Ico_succ_top hn]; ring
  have hinv : ∀ n, 1 ≤ n → (∀ y : ℝ, 0 ≤ y → H n y ≤ g y) ∧ (∀ y : ℝ, (n : ℝ) ≤ y → H n y = ℓ n y) ∧
      (∀ x : ℕ, 1 ≤ x → x ≤ n → H n x = g x) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      refine ⟨fun y hy => ?_, fun y _ => ?_, fun x hx1 hx2 => ?_⟩
      · simp only [hH, Finset.Ico_self, sum_empty, add_zero]; exact hsup 1 le_rfl y hy
      · simp [hH]
      · have : x = 1 := by omega
        subst this; simp [hH, hℓ]
    | succ n hn ih =>
      obtain ⟨ha, hb, hc⟩ := ih
      refine ⟨fun y hy => ?_, fun y hy => ?_, fun x hx1 hx2 => ?_⟩
      · rw [hHsucc n hn]
        rcases le_total y n with hyn | hyn
        · rw [max_eq_right (hd_left n hn y hyn), add_zero]; exact ha y hy
        · rw [hb y hyn]
          rcases le_total (d n y) 0 with h0 | h0
          · rw [max_eq_right h0, add_zero]; exact hsup n hn y hy
          · rw [max_eq_left h0]; simp only [hd]
            have := hsup (n + 1) (by omega) y hy
            linarith
      · push_cast at hy
        rw [hHsucc n hn, hb y (by linarith), max_eq_left (hd_right n hn y hy)]
        simp only [hd]; ring
      · rcases Nat.lt_or_ge x (n + 1) with hlt | hge
        · rw [hHsucc n hn, max_eq_right (hd_left n hn x (by exact_mod_cast (by omega : x ≤ n))),
            add_zero]
          exact hc x hx1 (by omega)
        · have : x = n + 1 := by omega
          subst this
          rw [hHsucc n hn]
          have := hb ((n + 1 : ℕ) : ℝ) (by push_cast; linarith)
          rw [this, max_eq_left (hd_right n hn _ (by push_cast; linarith))]
          have h2 := hℓj (n + 1)
          simp only [hd]
          linarith
  obtain ⟨hHa, _, hHc⟩ := hinv m hm
  -- integrability of the pieces
  have hℓint : ∀ j : ℕ, Integrable (ℓ j) (expMeasure μ⁻¹) := by
    intro j
    have : Integrable (fun y : ℝ => (g j - s j * j) + s j * y) (expMeasure μ⁻¹) :=
      (integrable_const _).add (hid.const_mul (s j))
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [hℓ]; ring
  have hdint : ∀ j : ℕ, Integrable (fun y => max (d j y) 0) (expMeasure μ⁻¹) := by
    intro j
    have : Integrable (d j) (expMeasure μ⁻¹) := (hℓint (j + 1)).sub (hℓint j)
    exact this.sup (integrable_const 0)
  have hHint : Integrable (H m) (expMeasure μ⁻¹) := by
    show Integrable (fun y => ℓ 1 y + ∑ j ∈ Finset.Ico 1 m, max (d j y) 0) (expMeasure μ⁻¹)
    exact (hℓint 1).add (integrable_finsetSum _ fun j _ => hdint j)
  -- the comparison for `H m`
  have hlin : ∑ x ∈ Finset.Icc 1 m, lam x * ℓ 1 x = ∫ y, ℓ 1 y ∂(expMeasure μ⁻¹) := by
    have hint : ∫ y, ℓ 1 y ∂(expMeasure μ⁻¹) = ∫ y, ((g 1 - s 1 * 1) + s 1 * y) ∂(expMeasure μ⁻¹) := by
      apply integral_congr_ae; filter_upwards with y; simp only [hℓ]; push_cast; ring
    rw [hint, integral_add (integrable_const _) (hid.const_mul _), integral_const_mul,
      integral_id_expMeasure hr, inv_inv, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have : ∑ x ∈ Finset.Icc 1 m, lam x * ℓ 1 x
        = (g 1 - s 1 * 1) * ∑ x ∈ Finset.Icc 1 m, lam x + s 1 * ∑ x ∈ Finset.Icc 1 m, lam x * x := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro x _; simp only [hℓ]; push_cast; ring
    rw [this, hlam.2, hμdef, mean]; ring
  have hdbound : ∀ j ∈ Finset.Ico 1 m, ∑ x ∈ Finset.Icc 1 m, lam x * max (d j x) 0 ≤
      ∫ y, max (d j y) 0 ∂(expMeasure μ⁻¹) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hrw : ∀ y : ℝ, d j y = (d j 0) + (s (j + 1) - s j) * y := by
      intro y; rw [hd_aff j y 0]; ring
    calc ∑ x ∈ Finset.Icc 1 m, lam x * max (d j x) 0
        = ∑ x ∈ Finset.Icc 1 m, lam x * max (d j 0 + (s (j + 1) - s j) * x) 0 :=
          sum_congr rfl (fun x _ => by rw [hrw x])
      _ ≤ ∫ y, max (d j 0 + (s (j + 1) - s j) * y) 0 ∂(expMeasure μ⁻¹) :=
          affine_bound m hm lam hlam hA3 hμ _ _ (hslope j hj1)
      _ = ∫ y, max (d j y) 0 ∂(expMeasure μ⁻¹) :=
          integral_congr_ae (ae_of_all _ fun y => by simp only; rw [← hrw y])
  have hHbound : ∑ x ∈ Finset.Icc 1 m, lam x * H m x ≤ ∫ y, H m y ∂(expMeasure μ⁻¹) := by
    have hsplit : ∑ x ∈ Finset.Icc 1 m, lam x * H m x
        = ∑ x ∈ Finset.Icc 1 m, lam x * ℓ 1 x +
          ∑ j ∈ Finset.Ico 1 m, ∑ x ∈ Finset.Icc 1 m, lam x * max (d j x) 0 := by
      have : ∀ x ∈ Finset.Icc 1 m, lam x * H m x
          = lam x * ℓ 1 x + ∑ j ∈ Finset.Ico 1 m, lam x * max (d j x) 0 := by
        intro x _
        show lam x * (ℓ 1 x + ∑ j ∈ Finset.Ico 1 m, max (d j x) 0) = _
        rw [mul_add, mul_sum]
      rw [sum_congr rfl this, sum_add_distrib, Finset.sum_comm]
    have hint : ∫ y, H m y ∂(expMeasure μ⁻¹) = ∫ y, ℓ 1 y ∂(expMeasure μ⁻¹) +
        ∑ j ∈ Finset.Ico 1 m, ∫ y, max (d j y) 0 ∂(expMeasure μ⁻¹) := by
      show ∫ y, (ℓ 1 y + ∑ j ∈ Finset.Ico 1 m, max (d j y) 0) ∂(expMeasure μ⁻¹) = _
      rw [integral_add (hℓint 1) (integrable_finsetSum _ fun j _ => hdint j),
        integral_finsetSum _ fun j _ => hdint j]
    rw [hsplit, hint, hlin]
    exact add_le_add le_rfl (sum_le_sum hdbound)
  calc ∑ x ∈ Icc 1 m, lam x * g (x : ℝ) = ∑ x ∈ Finset.Icc 1 m, lam x * H m x := by
        apply sum_congr rfl; intro x hx
        rw [hHc x (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2]
    _ ≤ ∫ y, H m y ∂(expMeasure μ⁻¹) := hHbound
    _ ≤ ∫ z, g z ∂(expMeasure μ⁻¹) := by
        apply integral_mono_ae hHint hg_int
        filter_upwards [ae_nonneg_expMeasure μ⁻¹] with y hy
        exact hHa y hy
