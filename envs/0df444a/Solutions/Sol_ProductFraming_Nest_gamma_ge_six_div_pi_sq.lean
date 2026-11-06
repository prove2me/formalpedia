-- Prove2me | solution 1 for ProductFraming.Nest.gamma_ge_six_div_pi_sq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:01:31.985952+00:00
-- url     : https://prove2.me/submissions/16cc08ea-880b-41c0-9b70-e84b319cca0b

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Definitions.Def_ProductFraming_Nest_Program
import Theorems.Thm_ProductFraming_Nest_corollary_6
import Theorems.Thm_ProductFraming_Nest_exponential_ratio_eq_pi_sq_div_six

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

end PFNExpAux

open Finset ProductFraming.Nest

namespace PFNGammaAux

/-- Downward induction from `y` to `1`. -/
lemma down {y : ℕ} (Q : ℕ → Prop) (h0 : 1 ≤ y → Q y)
    (hs : ∀ x, 1 ≤ x → x < y → Q (x + 1) → Q x) : ∀ x, 1 ≤ x → x ≤ y → Q x := by
  have : ∀ d x, x + d = y → 1 ≤ x → Q x := by
    intro d
    induction d with
    | zero => intro x hx h1; subst hx; exact h0 (by simpa using h1)
    | succ d ih =>
      intro x hx h1
      exact hs x h1 (by omega) (ih (x + 1) (by omega) (by omega))
  intro x h1 h2
  exact this (y - x) x (by omega) h1

lemma sum_Icc_split (f : ℕ → ℝ) {x m : ℕ} (h : x ≤ m) :
    ∑ y ∈ Finset.Icc x m, f y = f x + ∑ y ∈ Finset.Icc (x + 1) m, f y := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc h, sum_insert]
  simp

lemma tail_succ (m : ℕ) (lam : ℕ → ℝ) {x : ℕ} (h : x ≤ m) :
    tail m lam x = lam x + tail m lam (x + 1) := by
  unfold tail; exact sum_Icc_split lam h

lemma Emin_succ_sub (m : ℕ) (lam : ℕ → ℝ) (x : ℕ) :
    Emin m lam ((x + 1 : ℕ) : ℝ) = Emin m lam (x : ℝ) + tail m lam (x + 1) := by
  unfold Emin tail
  have hfil : (Finset.Icc 1 m).filter (fun y => x + 1 ≤ y) = Finset.Icc (x + 1) m := by
    ext y; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [← hfil, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  split_ifs with h
  · have h1 : ((x + 1 : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast h
    have h2 : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : x ≤ y)
    rw [min_eq_right h1, min_eq_right h2]; push_cast; ring
  · have h1 : (y : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : y ≤ x + 1)
    have h2 : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : y ≤ x)
    rw [min_eq_left h1, min_eq_left h2]; ring

lemma EminTail_tail (m : ℕ) (lam : ℕ → ℝ) (x : ℕ) :
    EminTail (tail m lam) x = Emin m lam (x : ℝ) := by
  induction x with
  | zero =>
    unfold EminTail Emin
    simp
  | succ k ih =>
    unfold EminTail at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih, Emin_succ_sub]

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

variable {m : ℕ} {L : ℕ → ℝ}

lemma L_anti (hL : Feasible6 m L) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ m) : L b ≤ L a := by
  have : ∀ d, ∀ b, b = a + d → b ≤ m → L b ≤ L a := by
    intro d
    induction d with
    | zero => intro b hb _; subst hb; exact le_refl _
    | succ d ih =>
      intro b hb hbm
      subst hb
      exact le_trans (hL.2.1 (a + d) (by omega) (by omega)) (ih (a + d) rfl (by omega))
  exact this (b - a) b (by omega) hb

lemma L_nonneg (hL : Feasible6 m L) {a : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) : 0 ≤ L a :=
  le_trans hL.2.2.1 (L_anti hL ha ham le_rfl)

lemma lamOf_nonneg (hL : Feasible6 m L) {x : ℕ} (hx : x ∈ Finset.Icc 1 m) : 0 ≤ lamOf m L x := by
  rw [Finset.mem_Icc] at hx
  unfold lamOf
  split_ifs with h
  · linarith [hL.2.1 x hx.1 (by omega)]
  · linarith [L_nonneg hL hx.1 hx.2]

lemma tail_lamOf (hL : Feasible6 m L) : ∀ x, 1 ≤ x → x ≤ m → tail m (lamOf m L) x = L x := by
  apply down (y := m) (fun x => tail m (lamOf m L) x = L x)
  · intro _
    unfold tail lamOf
    simp
  · intro x hx hxm ih
    rw [tail_succ _ _ hxm.le, ih]
    unfold lamOf
    rw [if_pos (by omega)]; ring

lemma EminTail_eq (hL : Feasible6 m L) {x : ℕ} (hx : x ≤ m) :
    Emin m (lamOf m L) (x : ℝ) = EminTail L x := by
  rw [← EminTail_tail]
  unfold EminTail
  apply sum_congr rfl
  intro y hy
  rw [Finset.mem_Icc] at hy
  exact tail_lamOf hL y hy.1 (by omega)

lemma pageLaw (hm : 1 ≤ m) (hL : Feasible6 m L) : IsPageLaw m (lamOf m L) := by
  refine ⟨fun x hx => lamOf_nonneg hL hx, ?_⟩
  have := tail_lamOf hL 1 le_rfl hm
  unfold tail at this
  rw [this, hL.1]

lemma nbue (hm : 1 ≤ m) (hL : Feasible6 m L) : IsNBUE m (lamOf m L) := by
  intro x hx
  rw [Finset.mem_Icc] at hx
  have hsum : ∀ a, 1 ≤ a → ∑ z ∈ Finset.Icc a m, tail m (lamOf m L) z = ∑ z ∈ Finset.Icc a m, L z := by
    intro a ha
    apply sum_congr rfl
    intro z hz
    rw [Finset.mem_Icc] at hz
    exact tail_lamOf hL z (by omega) hz.2
  rw [q_eq, q_eq, hsum x hx.1, hsum 1 le_rfl, tail_lamOf hL x hx.1 hx.2,
    tail_lamOf hL 1 le_rfl hm, hL.1, div_one]
  have hμ : 0 ≤ ∑ z ∈ Finset.Icc 1 m, L z := by
    apply sum_nonneg; intro z hz; rw [Finset.mem_Icc] at hz; exact L_nonneg hL hz.1 hz.2
  rcases Nat.lt_or_ge 1 x with h1 | h1
  · obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    have hc := hL.2.2.2 x' (by omega) (by omega)
    rcases (L_nonneg hL hx.1 hx.2).lt_or_eq with hpos | hzero
    · rw [div_le_iff₀ hpos]; linarith
    · rw [← hzero, div_zero]; exact hμ
  · have : x = 1 := by omega
    subst this
    rw [hL.1, div_one]

lemma mean_eq (hL : Feasible6 m L) : mean m (lamOf m L) = ∑ z ∈ Finset.Icc 1 m, L z := by
  have h := EminTail_eq hL (x := m) le_rfl
  unfold EminTail at h
  rw [← h]
  unfold mean Emin
  apply sum_congr rfl
  intro y hy
  rw [Finset.mem_Icc] at hy
  rw [min_eq_left (by exact_mod_cast hy.2)]

end PFNGammaAux

open PFNGammaAux PFNExpAux in
theorem solution (m : ℕ) (hm : 1 ≤ m) :
    ∀ U Λ : ℕ → ℝ, Feasible5 m U Λ → 6 / Real.pi ^ 2 ≤ J5 hm U Λ := by
  intro U L hF
  have hL := hF.1
  -- `E[min(X, x)] ≥ Λ(1) = 1 > 0`
  have hE : ∀ x ∈ Finset.Icc 1 m, 1 ≤ EminTail L x := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    unfold EminTail
    rw [sum_Icc_split _ hx.1, hL.1]
    have : 0 ≤ ∑ y ∈ Finset.Icc 2 x, L y := by
      apply sum_nonneg; intro y hy; rw [Finset.mem_Icc] at hy
      exact L_nonneg hL (by omega) (by omega)
    linarith
  -- weak duality: `1 = E[U(X)] ≤ J · E[X / E[min(X, Y) | X]]`
  set J := J5 hm U L with hJ
  have hUle : ∀ x ∈ Finset.Icc 1 m, lamOf m L x * U x ≤ J * (lamOf m L x * (x : ℝ) / EminTail L x) := by
    intro x hx
    have hEx := hE x hx
    have hx1 : (0 : ℝ) < x := by exact_mod_cast (Finset.mem_Icc.mp hx).1
    have hle : U x / (x : ℝ) * EminTail L x ≤ J :=
      Finset.le_sup' (fun x => U x / (x : ℝ) * EminTail L x) hx
    have hU : U x ≤ J * x / EminTail L x := by
      rw [le_div_iff₀ (by linarith)]
      have : U x / (x : ℝ) * EminTail L x * x = U x * EminTail L x := by field_simp
      nlinarith
    calc lamOf m L x * U x ≤ lamOf m L x * (J * x / EminTail L x) :=
          mul_le_mul_of_nonneg_left hU (lamOf_nonneg hL hx)
      _ = J * (lamOf m L x * (x : ℝ) / EminTail L x) := by ring
  have hdual : 1 ≤ J * ratio6 m L := by
    rw [← hF.2.2.2.1]
    unfold ratio6
    rw [mul_sum]
    exact sum_le_sum hUle
  -- `E[X / E[min(X, Y) | X]] ≤ π²/6` via Corollary 6 and the exponential computation
  have hpl := pageLaw hm hL
  have hnb := nbue hm hL
  have hc6 := corollary_6 m hm (lamOf m L) hpl hnb
  have hratio : ratio6 m L = ∑ x ∈ Finset.Icc 1 m, lamOf m L x * (x : ℝ) / Emin m (lamOf m L) (x : ℝ) := by
    unfold ratio6
    apply sum_congr rfl
    intro x hx
    rw [EminTail_eq hL (Finset.mem_Icc.mp hx).2]
  set μ := mean m (lamOf m L) with hμdef
  have hμ1 : 1 ≤ μ := by
    rw [hμdef, mean_eq hL]
    have := hE m (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩)
    unfold EminTail at this; exact this
  have hμpos : 0 < μ := by linarith
  have hr : 0 < μ⁻¹ := inv_pos.mpr hμpos
  have hint : ∫ w, w / (∫ z, min z w ∂(expMeasure μ⁻¹)) ∂(expMeasure μ⁻¹)
      = ∫ w, w / (μ * (1 - Real.exp (-w / μ))) ∂(expMeasure μ⁻¹) := by
    apply integral_congr_ae
    filter_upwards [ae_nonneg_expMeasure μ⁻¹] with w hw
    rw [integral_min_expMeasure hr hw]
    congr 1
    rw [div_inv_eq_mul, mul_comm]
    congr 3
    field_simp
  have hπ := exponential_ratio_eq_pi_sq_div_six μ hμpos
  have hr6 : ratio6 m L ≤ Real.pi ^ 2 / 6 := by
    rw [hratio, ← hπ, ← hint]; exact hc6
  have hr6nn : 0 ≤ ratio6 m L := by
    unfold ratio6
    apply sum_nonneg
    intro x hx
    exact div_nonneg (mul_nonneg (lamOf_nonneg hL hx) (Nat.cast_nonneg x))
      (by linarith [hE x hx])
  have hJnn : 0 ≤ J := by
    have hx1 : (1 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
    have := Finset.le_sup' (fun x => U x / (x : ℝ) * EminTail L x) hx1
    have h0 : 0 ≤ U 1 / ((1 : ℕ) : ℝ) * EminTail L 1 :=
      mul_nonneg (div_nonneg (hF.2.2.2.2 1 hx1) (Nat.cast_nonneg 1)) (by linarith [hE 1 hx1])
    exact le_trans h0 this
  have hpi : 0 < Real.pi ^ 2 := by positivity
  rw [div_le_iff₀ hpi]
  have : 1 * (Real.pi ^ 2 / 6) ≤ J * ratio6 m L * (Real.pi ^ 2 / 6) :=
    mul_le_mul_of_nonneg_right hdual (by positivity)
  have h2 : J * ratio6 m L ≤ J * (Real.pi ^ 2 / 6) := mul_le_mul_of_nonneg_left hr6 hJnn
  nlinarith
