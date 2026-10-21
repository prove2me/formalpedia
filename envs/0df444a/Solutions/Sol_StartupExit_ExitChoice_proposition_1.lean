-- Prove2me | solution 1 for StartupExit.ExitChoice.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T17:57:28.071902+00:00
-- url     : https://prove2.me/submissions/5657e0c1-1477-4ce7-a1a0-14cd709a606a

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model
import Theorems.Thm_StartupExit_ExitChoice_lemma_3

open StartupExit.ExitChoice

namespace SEP1Aux

/-- `G(·, k+2)` as a polynomial in `u = H x`. -/
noncomputable def Gp (k : ℕ) (u : ℝ) : ℝ := ((k:ℝ)+2) * u^(k+1) - ((k:ℝ)+1) * u^(k+2)

/-- antiderivative (in `u = H x`) of `(w+x) g(x, k+2)`. -/
noncomputable def Fp (w : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  (w-1) * Gp k u + 2*((k:ℝ)+1) * u^(k+2) - 2*((k:ℝ)+2)*((k:ℝ)+1)/((k:ℝ)+3) * u^(k+3)

lemma hasDerivAt_Gp (k : ℕ) (u : ℝ) :
    HasDerivAt (Gp k) (((k:ℝ)+2)*((k:ℝ)+1)*u^k*(1-u)) u := by
  have h1 := (hasDerivAt_pow (k+1) u).const_mul ((k:ℝ)+2)
  have h2 := (hasDerivAt_pow (k+2) u).const_mul ((k:ℝ)+1)
  have e : Gp k = fun y => ((k:ℝ)+2) * y^(k+1) - ((k:ℝ)+1) * y^(k+2) := rfl
  rw [e]
  refine (h1.sub h2).congr_deriv ?_
  rw [show k+1-1 = k by omega, show k+2-1 = k+1 by omega]; push_cast; ring

lemma hasDerivAt_Fp (w : ℝ) (k : ℕ) (u : ℝ) :
    HasDerivAt (Fp w k) ((w - 1 + 2*u)*(((k:ℝ)+2)*((k:ℝ)+1)*u^k*(1-u))) u := by
  have h1 := (hasDerivAt_Gp k u).const_mul (w-1)
  have h2 := (hasDerivAt_pow (k+2) u).const_mul (2*((k:ℝ)+1))
  have h3 := (hasDerivAt_pow (k+3) u).const_mul (2*((k:ℝ)+2)*((k:ℝ)+1)/((k:ℝ)+3))
  have e : Fp w k = fun y => (w-1) * Gp k y + 2*((k:ℝ)+1) * y^(k+2)
      - 2*((k:ℝ)+2)*((k:ℝ)+1)/((k:ℝ)+3) * y^(k+3) := rfl
  rw [e]
  refine ((h1.add h2).sub h3).congr_deriv ?_
  rw [show k+3-1 = k+2 by omega, show k+2-1 = k+1 by omega]
  have : ((k:ℝ)+3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma Gcdf_eq (k : ℕ) (x : ℝ) : Gcdf x (k+2) = Gp k (H x) := by
  unfold Gcdf Gp; push_cast; ring

lemma integral_eq (w : ℝ) (k : ℕ) (v : ℝ) :
    ∫ x in v..1, (w + x) * gdens x (k+2) = Fp w k 1 - Fp w k (H v) := by
  have hH : ∀ x, HasDerivAt H (1/2) x := by
    intro x
    have := ((hasDerivAt_id x).add_const (1:ℝ)).div_const 2
    have e : H = fun y => (id y + 1) / 2 := by funext y; simp [H]
    rw [e]; exact this
  have hd : ∀ x ∈ Set.uIcc v 1, HasDerivAt (fun x => Fp w k (H x)) ((w + x) * gdens x (k+2)) x := by
    intro x _
    have := (hasDerivAt_Fp w k (H x)).comp x (hH x)
    refine this.congr_deriv ?_
    unfold gdens H h
    rw [show k+2-2 = k by omega]
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp [H]
  · apply Continuous.intervalIntegrable
    unfold gdens H h
    fun_prop


lemma Gp_zero (k : ℕ) : Gp k 0 = 0 := by simp [Gp]
lemma Gp_one (k : ℕ) : Gp k 1 = 1 := by simp [Gp]; ring
lemma Fp_zero (w : ℝ) (k : ℕ) : Fp w k 0 = 0 := by simp [Fp, Gp]

lemma smono_of_hasDeriv {f f' : ℝ → ℝ} {a c : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Set.Ioo a c, 0 < f' x) : StrictMonoOn f (Set.Icc a c) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a c)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hf x).deriv]; exact hpos x hx

lemma santi_of_hasDeriv {f f' : ℝ → ℝ} {a c : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hneg : ∀ x ∈ Set.Ioo a c, f' x < 0) : StrictAntiOn f (Set.Icc a c) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a c)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hf x).deriv]; exact hneg x hx

/-- `G ≤ 1` on `[0,1]`. -/
lemma Gp_le_one (k : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : Gp k u ≤ 1 := by
  have hm : StrictMonoOn (Gp k) (Set.Icc 0 1) := by
    apply smono_of_hasDeriv (hasDerivAt_Gp k)
    intro x hx
    have := hx.1; have := hx.2
    have : 0 < x^k := by positivity
    have : (0:ℝ) < 1 - x := by linarith
    positivity
  rw [← Gp_one k]
  exact hm.monotoneOn ⟨h0, h1⟩ ⟨zero_le_one, le_rfl⟩ h1

section Abstract

variable (w A b : ℝ) (k : ℕ)

/-- `Π^F` as a function of `u = H(v*)` on the branch above the kink. -/
noncomputable def Phi (u : ℝ) : ℝ :=
  Fp w k 1 - Fp w k u + Gp k u * ((2*u + w - 1)/(A+b)) * A

noncomputable def Bq (u : ℝ) : ℝ :=
  A*u*(((k:ℝ)+2) - ((k:ℝ)+1)*u) - (b/2)*(2*u+w-1)*(((k:ℝ)+2)*((k:ℝ)+1))*(1-u)

noncomputable def Psi2 (u : ℝ) : ℝ := Phi w A b k u - A*((2*u + w - 1)/(A+b))

lemma hasDerivAt_Phi (hK : A + b ≠ 0) (u : ℝ) :
    HasDerivAt (Phi w A b k) (2/(A+b) * u^k * Bq w A b k u) u := by
  have hlin : HasDerivAt (fun y : ℝ => (2*y + w - 1)/(A+b)) (2/(A+b)) u := by
    have := ((((hasDerivAt_id u).const_mul (2:ℝ)).add_const w).sub_const 1).div_const (A+b)
    simpa using this
  have h := ((hasDerivAt_Fp w k u).const_sub (Fp w k 1)).add
    (((hasDerivAt_Gp k u).mul hlin).mul_const A)
  refine h.congr_deriv ?_
  unfold Bq Gp
  field_simp
  ring

lemma hasDerivAt_Psi2 (hK : A + b ≠ 0) (u : ℝ) :
    HasDerivAt (Psi2 w A b k)
      (2/(A+b) * (A * Gp k u - (b/2)*(2*u+w-1)*(((k:ℝ)+2)*((k:ℝ)+1)*u^k*(1-u)) - A)) u := by
  have hlin : HasDerivAt (fun y : ℝ => (2*y + w - 1)/(A+b)) (2/(A+b)) u := by
    have := ((((hasDerivAt_id u).const_mul (2:ℝ)).add_const w).sub_const 1).div_const (A+b)
    simpa using this
  have h := (hasDerivAt_Phi w A b k hK u).sub (hlin.const_mul A)
  refine h.congr_deriv ?_
  unfold Bq Gp
  field_simp
  ring

lemma Phi_zero : Phi w A b k 0 = Fp w k 1 := by simp [Phi, Gp_zero, Fp_zero]

lemma Psi2_one (hK : A + b ≠ 0) : Psi2 w A b k 1 = 0 := by
  simp only [Psi2, Phi, Gp_one]
  ring

lemma Bq_one : Bq w A b k 1 = A := by simp [Bq]; ring

lemma Bq_zero_neg (hw : 1 < w) (hb : 0 < b) : Bq w A b k 0 < 0 := by
  simp only [Bq]
  have : 0 < (b/2)*(2*0+w-1)*(((k:ℝ)+2)*((k:ℝ)+1))*(1-0) := by
    have : 0 < w - 1 := by linarith
    have : (0:ℝ) < (k:ℝ)+2 := by positivity
    have : (0:ℝ) < (k:ℝ)+1 := by positivity
    simp only [mul_zero, zero_add, sub_zero, mul_one]
    nlinarith [mul_pos (mul_pos (half_pos hb) this) (by positivity : (0:ℝ) < ((k:ℝ)+2)*((k:ℝ)+1))]
  linarith

/-- concavity: if `B ≥ 0` at `v` then `B > 0` on `(v, 1]`. -/
lemma Bq_pos_of (hb : 0 < b) (hbA : b*((k:ℝ)+2) < A) {v u : ℝ} (hv : 0 ≤ v) (hvu : v < u) (hu : u ≤ 1)
    (hBv : 0 ≤ Bq w A b k v) : 0 < Bq w A b k u := by
  have hA : 0 < A := by
    have : (0:ℝ) < b*((k:ℝ)+2) := by positivity
    linarith
  have hid : Bq w A b k u * (1 - v) = (1-u) * Bq w A b k v + (u - v) * Bq w A b k 1
      + ((k:ℝ)+1)*(A - b*((k:ℝ)+2)) * (u-v)*(1-u)*(1-v) := by
    unfold Bq; ring
  rw [Bq_one] at hid
  have h1 : 0 < (u - v) * A := mul_pos (by linarith) hA
  have h2 : 0 ≤ ((k:ℝ)+1)*(A - b*((k:ℝ)+2)) * (u-v)*(1-u)*(1-v) := by
    have : 0 ≤ 1 - u := by linarith
    have : 0 ≤ 1 - v := by linarith
    have : 0 ≤ u - v := by linarith
    have : 0 ≤ A - b*((k:ℝ)+2) := by linarith
    positivity
  have h3 : 0 ≤ (1-u) * Bq w A b k v := mul_nonneg (by linarith) hBv
  have h4 : 0 < Bq w A b k u * (1 - v) := by linarith
  have h5 : 0 < 1 - v := by linarith
  exact pos_of_mul_pos_left h4 h5.le


lemma Bq_pos_of_Phi_ge (hw : 1 < w) (hb : 0 < b) (hbA : b*((k:ℝ)+2) < A) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hP : Fp w k 1 ≤ Phi w A b k u) : 0 < Bq w A b k u := by
  have hK : 0 < A + b := by
    have : (0:ℝ) < b*((k:ℝ)+2) := by positivity
    linarith
  by_contra hB
  push_neg at hB
  have hanti : StrictAntiOn (Phi w A b k) (Set.Icc 0 u) := by
    apply santi_of_hasDeriv (hasDerivAt_Phi w A b k hK.ne')
    intro v hv
    have hBv : Bq w A b k v < 0 := by
      by_contra hc
      push_neg at hc
      have := Bq_pos_of w A b k hb hbA hv.1.le hv.2 hu1.le hc
      linarith
    have : 0 < 2/(A+b) * v^k := by have := hv.1; positivity
    exact mul_neg_of_pos_of_neg this hBv
  have := hanti ⟨le_rfl, hu0.le⟩ ⟨hu0.le, le_rfl⟩ hu0
  rw [Phi_zero] at this
  linarith

lemma Phi_smono (hb : 0 < b) (hbA : b*((k:ℝ)+2) < A) {u : ℝ}
    (hu0 : 0 ≤ u) (hB : 0 < Bq w A b k u) : StrictMonoOn (Phi w A b k) (Set.Icc u 1) := by
  have hK : 0 < A + b := by
    have : (0:ℝ) < b*((k:ℝ)+2) := by positivity
    linarith
  apply smono_of_hasDeriv (hasDerivAt_Phi w A b k hK.ne')
  intro v hv
  have hBv := Bq_pos_of w A b k hb hbA hu0 hv.1 hv.2.le hB.le
  have : 0 < 2/(A+b) * v^k := by have := hv.1; have : 0 < v := by linarith
                                 positivity
  positivity

lemma Psi2_santi (hw : 1 < w) (hb : 0 < b) (hbA : b*((k:ℝ)+2) < A) :
    StrictAntiOn (Psi2 w A b k) (Set.Icc 0 1) := by
  have hA : 0 < A := by
    have : (0:ℝ) < b*((k:ℝ)+2) := by positivity
    linarith
  have hK : 0 < A + b := by linarith
  apply santi_of_hasDeriv (hasDerivAt_Psi2 w A b k hK.ne')
  intro v hv
  have h1 := Gp_le_one k hv.1.le hv.2.le
  have h2 : 0 < (b/2)*(2*v+w-1)*(((k:ℝ)+2)*((k:ℝ)+1)*v^k*(1-v)) := by
    have := hv.1; have := hv.2; have : 0 < 1 - v := by linarith
    have : 0 < 2*v+w-1 := by linarith
    positivity
  have h3 : A * Gp k v ≤ A := by nlinarith
  have : A * Gp k v - (b/2)*(2*v+w-1)*(((k:ℝ)+2)*((k:ℝ)+1)*v^k*(1-v)) - A < 0 := by linarith
  exact mul_neg_of_pos_of_neg (by positivity) this

/-- `H(v*(t))` with `K = A + b`. -/
noncomputable def uu (t : ℝ) : ℝ := max ((t*(A+b) - w + 1)/2) 0

/-- `Π^F` as a function of `t = φ θ`. -/
noncomputable def ft (t : ℝ) : ℝ :=
  Fp w k 1 - Fp w k (uu w A b t) + Gp k (uu w A b t) * t * A

lemma ft_cont : Continuous (ft w A b k) := by
  unfold ft uu Fp Gp
  fun_prop

lemma ft_low (hK : 0 < A + b) {t : ℝ} (ht : t ≤ (w-1)/(A+b)) : ft w A b k t = Fp w k 1 := by
  have : uu w A b t = 0 := by
    unfold uu
    apply max_eq_right
    rw [le_div_iff₀ hK] at ht
    linarith
  simp [ft, this, Fp_zero, Gp_zero]

lemma ft_high (hK : 0 < A + b) {t : ℝ} (ht : (w-1)/(A+b) ≤ t) :
    ft w A b k t = Phi w A b k ((t*(A+b) - w + 1)/2) := by
  have hu : uu w A b t = (t*(A+b) - w + 1)/2 := by
    unfold uu
    apply max_eq_left
    rw [div_le_iff₀ hK] at ht
    linarith
  have ht' : (2*((t*(A+b) - w + 1)/2) + w - 1)/(A+b) = t := by
    field_simp; ring
  simp only [ft, Phi, hu, ht']


section TFacts
variable (hw : 1 < w) (hb : 0 < b) (hbA : b*((k:ℝ)+2) < A) (hAw : w ≤ A + b)
  (hK1 : A + b - w < 1)
include hw hb hbA hAw hK1

lemma posA : 0 < A := by
  have : (0:ℝ) < b*((k:ℝ)+2) := by positivity
  linarith

lemma posK : 0 < A + b := by have := posA w A b k hw hb hbA hAw hK1; linarith

lemma kink_pos : 0 < (w-1)/(A+b) := by
  have := posK w A b k hw hb hbA hAw hK1
  apply div_pos <;> linarith

lemma kink_lt_one : (w-1)/(A+b) < 1 := by
  have := posK w A b k hw hb hbA hAw hK1
  rw [div_lt_one this]; linarith

lemma ft_high' {t : ℝ} (ht : (w-1)/(A+b) ≤ t) :
    ft w A b k t - t * A = Psi2 w A b k ((t*(A+b) - w + 1)/2) := by
  have hK := posK w A b k hw hb hbA hAw hK1
  rw [ft_high w A b k hK ht, Psi2]
  have ht' : (2*((t*(A+b) - w + 1)/2) + w - 1)/(A+b) = t := by
    field_simp; ring
  rw [ht']; ring

lemma u_mem {t : ℝ} (ht0 : (w-1)/(A+b) ≤ t) (ht1 : t ≤ 1) :
    (t*(A+b) - w + 1)/2 ∈ Set.Icc (0:ℝ) 1 := by
  have hK := posK w A b k hw hb hbA hAw hK1
  rw [div_le_iff₀ hK] at ht0
  constructor
  · linarith
  · nlinarith

lemma ft_slope : StrictAntiOn (fun t => ft w A b k t - t * A) (Set.Icc 0 1) := by
  have hK := posK w A b k hw hb hbA hAw hK1
  have hA := posA w A b k hw hb hbA hAw hK1
  have hk0 := kink_pos w A b k hw hb hbA hAw hK1
  have hk1 := kink_lt_one w A b k hw hb hbA hAw hK1
  set kk := (w-1)/(A+b) with hkk
  have lo : StrictAntiOn (fun t => ft w A b k t - t * A) (Set.Icc 0 kk) := by
    intro t1 h1 t2 h2 hlt
    simp only
    rw [ft_low w A b k hK h1.2, ft_low w A b k hK h2.2]
    nlinarith
  have hi : StrictAntiOn (fun t => ft w A b k t - t * A) (Set.Icc kk 1) := by
    intro t1 h1 t2 h2 hlt
    simp only
    rw [ft_high' w A b k hw hb hbA hAw hK1 h1.1, ft_high' w A b k hw hb hbA hAw hK1 h2.1]
    apply Psi2_santi w A b k hw hb hbA (u_mem w A b k hw hb hbA hAw hK1 h1.1 h1.2)
      (u_mem w A b k hw hb hbA hAw hK1 h2.1 h2.2)
    have : t1 * (A+b) < t2 * (A+b) := mul_lt_mul_of_pos_right hlt hK
    linarith
  intro t1 h1 t2 h2 hlt
  rcases le_or_gt t2 kk with h2k | h2k
  · exact lo ⟨h1.1, by linarith⟩ ⟨h2.1, h2k⟩ hlt
  rcases le_or_gt t1 kk with h1k | h1k
  · have a1 := lo.antitoneOn ⟨h1.1, h1k⟩ ⟨hk0.le, le_rfl⟩ h1k
    have a2 := hi ⟨le_rfl, hk1.le⟩ ⟨h2k.le, h2.2⟩ h2k
    exact lt_of_lt_of_le a2 a1
  · exact hi ⟨h1k.le, h1.2⟩ ⟨h2k.le, h2.2⟩ hlt

lemma ft_one : A < ft w A b k 1 := by
  have hk1 := kink_lt_one w A b k hw hb hbA hAw hK1
  have hK := posK w A b k hw hb hbA hAw hK1
  have e := ft_high' w A b k hw hb hbA hAw hK1 (t := 1) hk1.le
  have hm := u_mem w A b k hw hb hbA hAw hK1 hk1.le le_rfl
  have hlt : (1*(A+b) - w + 1)/2 < 1 := by linarith
  have := Psi2_santi w A b k hw hb hbA hm ⟨zero_le_one, le_rfl⟩ hlt
  rw [Psi2_one w A b k hK.ne'] at this
  linarith


lemma ft_FE (hEA : Fp w k 1 < A) : ∃ θFE : ℝ, (w-1)/(A+b) < θFE ∧ θFE < Fp w k 1 / A ∧
    ft w A b k θFE = Fp w k 1 ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, ft w A b k t ≤ Fp w k 1 ↔ t ≤ θFE) ∧
    StrictMonoOn (ft w A b k) (Set.Icc θFE 1) := by
  have hK := posK w A b k hw hb hbA hAw hK1
  have hA := posA w A b k hw hb hbA hAw hK1
  have hk0 := kink_pos w A b k hw hb hbA hAw hK1
  have hk1 := kink_lt_one w A b k hw hb hbA hAw hK1
  set E := Fp w k 1 with hE
  have hEpos : 0 < E := by
    rw [hE]; simp only [Fp, Gp_one]
    have : (0:ℝ) < (k:ℝ)+3 := by positivity
    rw [show (1:ℝ)^(k+2) = 1 by simp, show (1:ℝ)^(k+3) = 1 by simp]
    have : 2*((k:ℝ)+1) - 2*((k:ℝ)+2)*((k:ℝ)+1)/((k:ℝ)+3) * 1 = 2*((k:ℝ)+1)/((k:ℝ)+3) := by
      field_simp; ring
    have : 0 < 2*((k:ℝ)+1)/((k:ℝ)+3) := by positivity
    nlinarith
  set kk := (w-1)/(A+b) with hkk
  set θt := E / A with hθt
  have hθt0 : 0 < θt := div_pos hEpos hA
  have hθt1 : θt < 1 := by rw [hθt, div_lt_one hA]; exact hEA
  have hθtA : θt * A = E := by rw [hθt]; field_simp
  have hsl := ft_slope w A b k hw hb hbA hAw hK1
  have h1 := ft_one w A b k hw hb hbA hAw hK1
  have hft : E < ft w A b k θt := by
    have := hsl ⟨hθt0.le, hθt1.le⟩ ⟨zero_le_one, le_rfl⟩ hθt1
    simp only at this
    linarith
  have hkθ : kk < θt := by
    by_contra hc; push_neg at hc
    rw [ft_low w A b k hK hc] at hft; linarith
  set uθ := (θt*(A+b) - w + 1)/2 with huθ
  have hkk' : kk * (A+b) = w - 1 := by rw [hkk]; field_simp
  have huθ0 : 0 < uθ := by
    have : kk * (A+b) < θt * (A+b) := mul_lt_mul_of_pos_right hkθ hK
    rw [huθ]; linarith
  have huθ1 : uθ < 1 := by
    have : θt * (A+b) < 1 * (A+b) := mul_lt_mul_of_pos_right hθt1 hK
    rw [huθ]; linarith
  have hPθ : E < Phi w A b k uθ := by rw [← ft_high w A b k hK hkθ.le]; exact hft
  have hcB : Continuous (Bq w A b k) := by unfold Bq; fun_prop
  have hcP : Continuous (Phi w A b k) := by unfold Phi Fp Gp; fun_prop
  have hB0 := Bq_zero_neg w A b k hw hb
  have hev : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), Bq w A b k x < 0 :=
    nhdsWithin_le_nhds (hcB.continuousAt.eventually_lt continuousAt_const hB0)
  obtain ⟨δ, hδ1, hδ2⟩ := (hev.and (Ioo_mem_nhdsGT huθ0)).exists
  have hPδ : Phi w A b k δ < E := by
    by_contra hc; push_neg at hc
    have := Bq_pos_of_Phi_ge w A b k hw hb hbA hδ2.1 (by linarith [hδ2.2]) hc
    linarith
  obtain ⟨u0, hu0m, hu0⟩ := intermediate_value_Icc hδ2.2.le hcP.continuousOn
    ⟨hPδ.le, hPθ.le⟩
  have hu0pos : 0 < u0 := lt_of_lt_of_le hδ2.1 hu0m.1
  have hu0lt : u0 < uθ := lt_of_le_of_ne hu0m.2 (by rintro rfl; linarith)
  have hBu0 : 0 < Bq w A b k u0 :=
    Bq_pos_of_Phi_ge w A b k hw hb hbA hu0pos (by linarith) hu0.ge
  have hmono := Phi_smono w A b k hb hbA hu0pos.le hBu0
  have hbelow : ∀ u, 0 < u → u < u0 → Phi w A b k u < E := by
    intro u hu hu'
    by_contra hc; push_neg at hc
    have hBu := Bq_pos_of_Phi_ge w A b k hw hb hbA hu (by linarith) hc
    have := Phi_smono w A b k hb hbA hu.le hBu ⟨le_rfl, by linarith⟩ ⟨hu'.le, by linarith⟩ hu'
    linarith
  set θFE := (2*u0 + w - 1)/(A+b) with hθFE
  have hθK : θFE * (A+b) = 2*u0 + w - 1 := by rw [hθFE]; field_simp
  have hθtK : θt * (A+b) = 2*uθ + w - 1 := by rw [huθ]; ring
  -- key monotone link between `t` and `u(t)`
  have link : ∀ t, (t*(A+b) - w + 1)/2 < u0 ↔ t < θFE := by
    intro t
    constructor
    · intro h; by_contra hc; push_neg at hc
      have := mul_le_mul_of_nonneg_right hc hK.le; linarith
    · intro h; have := mul_lt_mul_of_pos_right h hK; linarith
  have link' : ∀ t, (t*(A+b) - w + 1)/2 = u0 ↔ t = θFE := by
    intro t
    constructor
    · intro h
      have : t * (A+b) = θFE * (A+b) := by linarith
      exact mul_right_cancel₀ hK.ne' this
    · rintro rfl; linarith
  have hkFE : kk < θFE := by
    by_contra hc; push_neg at hc
    have := mul_le_mul_of_nonneg_right hc hK.le; linarith
  have hFEt : θFE < θt := by
    by_contra hc; push_neg at hc
    have := mul_le_mul_of_nonneg_right hc hK.le; linarith
  have huFE : (θFE*(A+b) - w + 1)/2 = u0 := (link' θFE).2 rfl
  refine ⟨θFE, hkFE, hFEt, ?_, ?_, ?_⟩
  · rw [ft_high w A b k hK hkFE.le, huFE, hu0]
  · intro t ht
    rcases le_or_gt t kk with htk | htk
    · rw [ft_low w A b k hK htk]
      exact ⟨fun _ => by linarith, fun _ => le_rfl⟩
    · rw [ft_high w A b k hK htk.le]
      have hum := u_mem w A b k hw hb hbA hAw hK1 htk.le ht.2
      have hupos : 0 < (t*(A+b) - w + 1)/2 := by
        have : kk * (A+b) < t * (A+b) := mul_lt_mul_of_pos_right htk hK
        linarith
      rcases lt_trichotomy ((t*(A+b) - w + 1)/2) u0 with hl | he | hg
      · exact ⟨fun _ => ((link t).1 hl).le, fun _ => (hbelow _ hupos hl).le⟩
      · rw [he, hu0]; exact ⟨fun _ => ((link' t).1 he).le, fun _ => le_rfl⟩
      · have hgt : E < Phi w A b k ((t*(A+b) - w + 1)/2) := by
          have := hmono ⟨le_rfl, by linarith⟩ ⟨hg.le, hum.2⟩ hg
          rw [hu0] at this; exact this
        constructor
        · intro h; linarith
        · intro h
          exfalso
          rcases h.lt_or_eq with h' | h'
          · have := (link t).2 h'; linarith
          · have := (link' t).2 h'; linarith
  · intro t1 h1 t2 h2 hlt
    have hk1' : kk ≤ t1 := by linarith [h1.1]
    have hk2' : kk ≤ t2 := by linarith [h2.1]
    rw [ft_high w A b k hK hk1', ft_high w A b k hK hk2']
    have m1 := u_mem w A b k hw hb hbA hAw hK1 hk1' h1.2
    have m2 := u_mem w A b k hw hb hbA hAw hK1 hk2' h2.2
    have g1 : u0 ≤ (t1*(A+b) - w + 1)/2 := by
      by_contra hc; push_neg at hc; have := (link t1).1 hc; linarith [h1.1]
    have g2 : u0 ≤ (t2*(A+b) - w + 1)/2 := by
      by_contra hc; push_neg at hc; have := (link t2).1 hc; linarith [h2.1]
    apply hmono ⟨g1, m1.2⟩ ⟨g2, m2.2⟩
    have := mul_lt_mul_of_pos_right hlt hK
    linarith

end TFacts

end Abstract


/-- the tie-broken choice expressed through an abstract `Π^F`-profile `f`. -/
noncomputable def chA (f : ℝ → ℝ) (E A : ℝ) (φ : ℝ → ℝ) (R c θ : ℝ) : Strategy :=
  if θ * A ≤ E ∧ f (φ (R - c) * θ) ≤ E then Strategy.early
  else if f (φ (R - c) * θ) ≤ θ * A then Strategy.late
  else Strategy.flexible

lemma mem01_mul {a c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hc : c ∈ Set.Icc (0:ℝ) 1) :
    a * c ∈ Set.Icc (0:ℝ) 1 :=
  ⟨mul_nonneg ha.1 hc.1, by nlinarith [ha.1, ha.2, hc.1, hc.2]⟩

theorem main_abstract (f : ℝ → ℝ) (hfc : Continuous f) (E A α Bd θFE : ℝ)
    (hE : 0 < E) (hEA : E < A)
    (hsl : StrictAntiOn (fun t => f t - t * A) (Set.Icc 0 1)) (h1 : A < f 1)
    (hFE0 : 0 < θFE) (hFEt : θFE < E / A) (hfFE : f θFE = E)
    (hiff : ∀ t ∈ Set.Icc (0:ℝ) 1, f t ≤ E ↔ t ≤ θFE)
    (hmono : StrictMonoOn f (Set.Icc θFE 1))
    (hBd : 0 < Bd) (hαFE : α / Bd < θFE)
    (φ : ℝ → ℝ) (R : ℝ) (hR : 0 < R) (hφ0 : φ 0 = 0) (hφR : φ R = 1)
    (hφm : StrictMonoOn φ (Set.Icc 0 R)) (hφc : ContinuousOn φ (Set.Icc 0 R)) :
    ∃ cl cu : ℝ, 0 < cl ∧ cl < cu ∧ cu < R ∧
      (∀ c ∈ Set.Ico 0 cl, ∃ θL : ℝ,
          α / (φ (R - c) * Bd) < θL ∧ θL < E / A ∧
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            chA f E A φ R c θ ≠ Strategy.late ∧
              (chA f E A φ R c θ = Strategy.flexible ↔ θL < θ)) ∧
      (∀ c ∈ Set.Ioo cl cu, ∃ θL θH : ℝ,
          E / A < θH ∧ θH < 1 ∧ θL < θH ∧
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            (θH ≤ θ → chA f E A φ R c θ = Strategy.late) ∧
            (θ < θH → chA f E A φ R c θ ≠ Strategy.late) ∧
            (θL < θ → θ < θH → chA f E A φ R c θ = Strategy.flexible) ∧
            (θ ≤ θL → chA f E A φ R c θ = Strategy.early)) ∧
      (∀ c ∈ Set.Icc cu R, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
          (θ ≤ E / A → chA f E A φ R c θ = Strategy.early) ∧
          (E / A < θ → chA f E A φ R c θ = Strategy.late)) := by
  have hA : 0 < A := by linarith
  set θt := E / A with hθt
  have hθt0 : 0 < θt := div_pos hE hA
  have hθt1 : θt < 1 := by rw [hθt, div_lt_one hA]; exact hEA
  have hθtA : θt * A = E := by rw [hθt]; field_simp
  have hleθt : ∀ θ, θ * A ≤ E ↔ θ ≤ θt := by
    intro θ; rw [hθt, le_div_iff₀ hA]
  have hFE1 : θFE < 1 := by linarith
  -- strict decrease of `D_φ(θ) = f(φθ) - θA`
  have Dm : ∀ p ∈ Set.Icc (0:ℝ) 1, StrictAntiOn (fun θ => f (p*θ) - θ*A) (Set.Icc 0 1) := by
    intro p hp θ1 h1' θ2 h2' hlt
    simp only
    rcases hp.1.eq_or_lt with h0 | h0
    · rw [← h0]; simp only [zero_mul]; nlinarith
    · have := hsl (mem01_mul hp h1') (mem01_mul hp h2') (mul_lt_mul_of_pos_left hlt h0)
      simp only at this
      nlinarith [mul_nonneg (sub_nonneg.2 hp.2) (sub_nonneg.2 hlt.le)]
  -- φ maps into [0,1]
  have hφI : ∀ c ∈ Set.Icc (0:ℝ) R, φ (R - c) ∈ Set.Icc (0:ℝ) 1 := by
    intro c hc
    have hs : R - c ∈ Set.Icc 0 R := ⟨by linarith [hc.2], by linarith [hc.1]⟩
    constructor
    · rw [← hφ0]; exact hφm.monotoneOn ⟨le_rfl, hR.le⟩ hs hs.1
    · rw [← hφR]; exact hφm.monotoneOn hs ⟨hR.le, le_rfl⟩ hs.2
  -- thresholds in φ-space
  set φu := θFE / θt with hφu
  have hφu0 : 0 < φu := div_pos hFE0 hθt0
  have hφu1 : φu < 1 := by rw [hφu, div_lt_one hθt0]; exact hFEt
  have hφuθ : φu * θt = θFE := by rw [hφu]; field_simp
  have hFEφu : θFE < φu := by
    rw [hφu, lt_div_iff₀ hθt0]; nlinarith
  have hfφu : f φu < A := by
    have := Dm φu ⟨hφu0.le, hφu1.le⟩ ⟨hθt0.le, hθt1.le⟩ ⟨zero_le_one, le_rfl⟩ hθt1
    simp only at this
    rw [hφuθ, hfFE, hθtA, mul_one, one_mul] at this
    linarith
  obtain ⟨φl, hφlm, hφl⟩ := intermediate_value_Icc hFE1.le hfc.continuousOn
    (show A ∈ Set.Icc (f θFE) (f 1) from ⟨by linarith, h1.le⟩)
  have hφl1 : φl < 1 := lt_of_le_of_ne hφlm.2 (by rintro rfl; linarith)
  have hφuφl : φu < φl := by
    by_contra hc; push_neg at hc
    have := hmono.monotoneOn hφlm ⟨hFEφu.le, hφu1.le⟩ hc
    linarith
  -- thresholds in s-space
  obtain ⟨su, hsum, hsu⟩ := intermediate_value_Icc hR.le hφc
    (show φu ∈ Set.Icc (φ 0) (φ R) from ⟨by rw [hφ0]; exact hφu0.le, by rw [hφR]; exact hφu1.le⟩)
  obtain ⟨sl, hslm, hsl'⟩ := intermediate_value_Icc hR.le hφc
    (show φl ∈ Set.Icc (φ 0) (φ R) from
      ⟨by rw [hφ0]; linarith, by rw [hφR]; exact hφl1.le⟩)
  have hsu0 : 0 < su := lt_of_le_of_ne hsum.1 (by rintro rfl; rw [hφ0] at hsu; linarith)
  have hslR : sl < R := lt_of_le_of_ne hslm.2 (by rintro rfl; rw [hφR] at hsl'; linarith)
  have hsusl : su < sl := by
    by_contra hc; push_neg at hc
    have := hφm.monotoneOn hslm hsum hc
    linarith
  -- φ(R-c) relative to φu, φl
  have cmp_lt : ∀ c ∈ Set.Icc (0:ℝ) R, ∀ s ∈ Set.Icc (0:ℝ) R, R - c < s → φ (R - c) < φ s := by
    intro c hc s hs h
    exact hφm ⟨by linarith [hc.2], by linarith [hc.1]⟩ hs h
  have cmp_gt : ∀ c ∈ Set.Icc (0:ℝ) R, ∀ s ∈ Set.Icc (0:ℝ) R, s < R - c → φ s < φ (R - c) := by
    intro c hc s hs h
    exact hφm hs ⟨by linarith [hc.2], by linarith [hc.1]⟩ h
  refine ⟨R - sl, R - su, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
  · -- cheap early market
    intro c hc
    have hcI : c ∈ Set.Icc 0 R := ⟨hc.1, by linarith [hc.2]⟩
    set p := φ (R - c) with hp
    have hpI := hφI c hcI
    have hpl : φl < p := by rw [← hsl']; exact cmp_gt c hcI sl hslm (by linarith [hc.2])
    have hp0 : 0 < p := by linarith
    have hfp : A < f p := by
      have := hmono ⟨hφlm.1, hφl1.le⟩ ⟨by linarith, hpI.2⟩ hpl
      rw [hφl] at this; exact this
    refine ⟨θFE / p, ?_, ?_, ?_⟩
    · rw [div_lt_div_iff₀ (by positivity) hp0]
      rw [div_lt_iff₀ hBd] at hαFE
      nlinarith
    · rw [div_lt_iff₀ hp0]
      have : φu * θt < p * θt := mul_lt_mul_of_pos_right (by linarith) hθt0
      linarith
    · intro θ hθ
      have hD : θ * A < f (p * θ) := by
        rcases hθ.2.lt_or_eq with h | h
        · have := Dm p hpI hθ ⟨zero_le_one, le_rfl⟩ h
          simp only at this; rw [mul_one] at this; linarith
        · rw [h, mul_one]; linarith
      have hearly : (θ * A ≤ E ∧ f (p * θ) ≤ E) ↔ θ ≤ θFE / p := by
        rw [hiff _ (mem01_mul hpI hθ), le_div_iff₀ hp0, mul_comm θ p]
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨?_, h⟩
          rw [hleθt]
          have : θFE / p < θt := by
            rw [div_lt_iff₀ hp0]
            have : φu * θt < p * θt := mul_lt_mul_of_pos_right (by linarith) hθt0
            linarith
          have : θ ≤ θFE / p := by rw [le_div_iff₀ hp0]; linarith
          linarith
      have hnl : ¬ f (p * θ) ≤ θ * A := not_le.2 hD
      unfold chA
      rw [← hp]
      constructor
      · split_ifs <;> simp
      · by_cases he : θ * A ≤ E ∧ f (p * θ) ≤ E
        · rw [if_pos he]
          have := hearly.1 he
          simp only [reduceCtorEq, false_iff, not_lt]; exact this
        · rw [if_neg he, if_neg hnl]
          simp only [true_iff]
          by_contra hc; push_neg at hc
          exact he (hearly.2 hc)
  · -- intermediate cost
    intro c hc
    have hcI : c ∈ Set.Icc 0 R := ⟨by linarith [hc.1], by linarith [hc.2]⟩
    set p := φ (R - c) with hp
    have hpI := hφI c hcI
    have hpl : p < φl := by rw [← hsl']; exact cmp_lt c hcI sl hslm (by linarith [hc.1])
    have hpu : φu < p := by rw [← hsu]; exact cmp_gt c hcI su hsum (by linarith [hc.2])
    have hp0 : 0 < p := by linarith
    have hfp : f p < A := by
      rcases le_or_gt p θFE with h | h
      · have := (hiff p hpI).2 h; linarith
      · have := hmono ⟨h.le, hpI.2⟩ ⟨hφlm.1, hφl1.le⟩ hpl
        rw [hφl] at this; exact this
    have hpθt : θFE < p * θt := by
      have : φu * θt < p * θt := mul_lt_mul_of_pos_right hpu hθt0
      linarith
    have hDθt : 0 < f (p * θt) - θt * A := by
      have hI : p * θt ∈ Set.Icc (0:ℝ) 1 := mem01_mul hpI ⟨hθt0.le, hθt1.le⟩
      have : ¬ f (p * θt) ≤ E := fun h => by have := (hiff _ hI).1 h; linarith
      rw [hθtA]; push_neg at this; linarith
    have hD1 : f (p * 1) - 1 * A < 0 := by rw [mul_one, one_mul]; linarith
    have hDc : ContinuousOn (fun θ => f (p*θ) - θ*A) (Set.Icc θt 1) := by
      apply Continuous.continuousOn; fun_prop
    obtain ⟨θH, hθHm, hθH⟩ := intermediate_value_Icc' hθt1.le hDc
      (show (0:ℝ) ∈ Set.Icc (f (p * 1) - 1 * A) (f (p * θt) - θt * A) from ⟨hD1.le, hDθt.le⟩)
    simp only at hθH
    have hθHt : θt < θH := lt_of_le_of_ne hθHm.1 (by rintro rfl; linarith)
    have hθH1 : θH < 1 := lt_of_le_of_ne hθHm.2 (by rintro rfl; rw [hθH] at hD1; linarith)
    have hθLt : θFE / p < θt := by rw [div_lt_iff₀ hp0]; linarith
    have hθHI : θH ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, hθH1.le⟩
    refine ⟨θFE / p, θH, hθHt, hθH1, by linarith, ?_⟩
    intro θ hθ
    have hDlt : θ < θH → θ * A < f (p * θ) := by
      intro h
      have := Dm p hpI hθ hθHI h
      simp only at this; linarith
    have hDge : θH ≤ θ → f (p * θ) ≤ θ * A := by
      intro h
      have := (Dm p hpI).antitoneOn hθHI hθ h
      linarith
    have hnotlate : θ < θH → chA f E A φ R c θ ≠ Strategy.late := by
      intro h
      have hnl : ¬ f (p * θ) ≤ θ * A := not_le.2 (hDlt h)
      unfold chA; rw [← hp, if_neg hnl]
      split_ifs <;> simp
    refine ⟨?_, hnotlate, ?_, ?_⟩
    · intro h
      have hne : ¬ (θ * A ≤ E ∧ f (p * θ) ≤ E) := by
        rintro ⟨h1', _⟩; rw [hleθt] at h1'; linarith
      unfold chA; rw [← hp, if_neg hne, if_pos (hDge h)]
    · intro hL hH
      have hI := mem01_mul hpI hθ
      have hne : ¬ (θ * A ≤ E ∧ f (p * θ) ≤ E) := by
        rintro ⟨_, h2'⟩
        have := (hiff _ hI).1 h2'
        rw [div_lt_iff₀ hp0] at hL; linarith
      have hnl : ¬ f (p * θ) ≤ θ * A := not_le.2 (hDlt hH)
      unfold chA; rw [← hp, if_neg hne, if_neg hnl]
    · intro hL
      have hI := mem01_mul hpI hθ
      have he : θ * A ≤ E ∧ f (p * θ) ≤ E := by
        refine ⟨by rw [hleθt]; linarith, (hiff _ hI).2 ?_⟩
        rw [le_div_iff₀ hp0] at hL; linarith
      unfold chA; rw [← hp, if_pos he]
  · -- costly early market
    intro c hc θ hθ
    have hcI : c ∈ Set.Icc 0 R := ⟨by linarith [hc.1, hsu0], hc.2⟩
    set p := φ (R - c) with hp
    have hpI := hφI c hcI
    have hpu : p ≤ φu := by
      rw [← hsu]
      exact hφm.monotoneOn ⟨by linarith [hc.2], by linarith [hc.1, hsu0]⟩ hsum (by linarith [hc.1])
    have hlow : f (p * θt) ≤ E := by
      apply (hiff _ (mem01_mul hpI ⟨hθt0.le, hθt1.le⟩)).2
      have := mul_le_mul_of_nonneg_right hpu hθt0.le
      linarith
    constructor
    · intro h
      have hI := mem01_mul hpI hθ
      have he : θ * A ≤ E ∧ f (p * θ) ≤ E := by
        refine ⟨(hleθt θ).2 h, (hiff _ hI).2 ?_⟩
        have := mul_le_mul_of_nonneg_left h hpI.1
        have := mul_le_mul_of_nonneg_right hpu hθt0.le
        linarith
      unfold chA; rw [← hp, if_pos he]
    · intro h
      have hne : ¬ (θ * A ≤ E ∧ f (p * θ) ≤ E) := by
        rintro ⟨h1', _⟩; rw [hleθt] at h1'; linarith
      have hD := Dm p hpI ⟨hθt0.le, hθt1.le⟩ hθ h
      simp only at hD
      have hl : f (p * θ) ≤ θ * A := by rw [hθtA] at hD; linarith
      unfold chA; rw [← hp, if_neg hne, if_pos hl]

end SEP1Aux

namespace SEP1Aux

lemma H_max (a : ℝ) : H (max a (-1)) = max ((a+1)/2) 0 := by
  unfold H
  rcases le_total a (-1) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; norm_num
  · rw [max_eq_left h, max_eq_left (by linarith)]

lemma PiFt_eq (P : Params) (k : ℕ) (hk : P.m = k + 2) :
    PiFt P = ft P.w (P.w + X2 P.n) (piB P.n) k := by
  funext t
  unfold PiFt ft
  rw [hk, integral_eq, Gcdf_eq]
  have : H (vStar P t) = uu P.w (P.w + X2 P.n) (piB P.n) t := by
    unfold vStar uu
    rw [H_max]
    congr 1
    ring
  rw [this]

/-- All the analytic facts in terms of the platform's model. -/
theorem prop1_core (P : Params) (hS : P.Standing) :
    ∃ cl cu : ℝ, 0 < cl ∧ cl < cu ∧ cu < P.R ∧
      (∀ c ∈ Set.Ico 0 cl, ∃ θL : ℝ,
          (P.w - 1) / (P.φ (P.R - c) * (P.w + X1 P.n)) < θL ∧ θL < PiE P / (P.w + X2 P.n) ∧
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            chA (PiFt P) (PiE P) (P.w + X2 P.n) P.φ P.R c θ ≠ Strategy.late ∧
              (chA (PiFt P) (PiE P) (P.w + X2 P.n) P.φ P.R c θ = Strategy.flexible ↔ θL < θ)) ∧
      (∀ c ∈ Set.Ioo cl cu, ∃ θL θH : ℝ,
          PiE P / (P.w + X2 P.n) < θH ∧ θH < 1 ∧ θL < θH ∧
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            (θH ≤ θ → chA (PiFt P) (PiE P) (P.w + X2 P.n) P.φ P.R c θ = Strategy.late) ∧
            (θ < θH → chA (PiFt P) (PiE P) (P.w + X2 P.n) P.φ P.R c θ ≠ Strategy.late) ∧
            (θL < θ → θ < θH →
              chA (PiFt P) (PiE P) (P.w + X2 P.n) P.φ P.R c θ = Strategy.flexible) ∧
            (θ ≤ θL → chA (PiFt P) (PiE P) (P.w + X2 P.n) P.φ P.R c θ = Strategy.early)) ∧
      (∀ c ∈ Set.Icc cu P.R, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
          (θ ≤ PiE P / (P.w + X2 P.n) →
            chA (PiFt P) (PiE P) (P.w + X2 P.n) P.φ P.R c θ = Strategy.early) ∧
          (PiE P / (P.w + X2 P.n) < θ →
            chA (PiFt P) (PiE P) (P.w + X2 P.n) P.φ P.R c θ = Strategy.late)) := by
  obtain ⟨hw, hm2, hmn, hR, hφ0, hφR, hφm, hφc⟩ := hS
  obtain ⟨k, hk⟩ : ∃ k, P.m = k + 2 := ⟨P.m - 2, by omega⟩
  have L3 := StartupExit.ExitChoice.lemma_3
  have hn1 : 1 ≤ P.n := by omega
  have hn2 : 2 ≤ P.n := by omega
  have hX1 := L3.1 P.n hn1
  obtain ⟨hX2, hpb⟩ := L3.2 P.n hn2
  have hX2m := (L3.2 P.m hm2).1
  have hnk : (k:ℝ) + 3 ≤ (P.n:ℝ) := by
    have : k + 3 ≤ P.n := by omega
    exact_mod_cast this
  set nR := (P.n : ℝ) with hnR
  have hn0 : 0 < nR := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hb : piB P.n = 2 / (nR * (nR + 1)) := by
    rw [← hpb, piB]; ring
  set A := P.w + X2 P.n with hA
  set b := piB P.n with hbdef
  have hAv : A = P.w + (nR - 3)/(nR + 1) := by rw [hA, hX2]
  have hbpos : 0 < b := by rw [hb]; positivity
  have hn3 : 0 ≤ (nR - 3)/(nR + 1) := div_nonneg (by linarith) (by linarith)
  have hbA : b * ((k:ℝ)+2) < A := by
    rw [hb, hAv]
    have : 2 / (nR * (nR + 1)) * ((k:ℝ)+2) < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
      nlinarith
    linarith
  have hAw : P.w ≤ A + b := by rw [hAv]; linarith
  have hK1 : A + b - P.w < 1 := by
    rw [hAv, hb]
    have : (nR - 3)/(nR + 1) + 2 / (nR * (nR + 1)) < 1 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_lt_one (by positivity)]
      nlinarith
    linarith
  have hFp : Fp P.w k 1 = PiE P := by
    rw [PiE, piS, hX2m, hk]
    simp only [Fp, Gp_one, one_pow]
    push_cast
    have : ((k:ℝ)+3) ≠ 0 := by positivity
    have : ((k:ℝ)+2+1) ≠ 0 := by positivity
    field_simp
    ring
  have hEA : Fp P.w k 1 < A := by
    rw [hFp, PiE, piS, hX2m, hk, hAv]
    push_cast
    have : ((k:ℝ) + 2 - 3) / ((k:ℝ) + 2 + 1) < (nR - 3)/(nR + 1) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hE : 0 < Fp P.w k 1 := by
    rw [hFp, PiE, piS, hX2m, hk]
    push_cast
    have : -1 ≤ ((k:ℝ) + 2 - 3) / ((k:ℝ) + 2 + 1) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hF := PiFt_eq P k hk
  obtain ⟨θFE, hkFE, hFEt, hfFE, hiff, hmono⟩ :=
    ft_FE P.w A b k hw hbpos hbA hAw hK1 hEA
  have hsl := ft_slope P.w A b k hw hbpos hbA hAw hK1
  have h1 := ft_one P.w A b k hw hbpos hbA hAw hK1
  have hkpos := kink_pos P.w A b k hw hbpos hbA hAw hK1
  have hK := posK P.w A b k hw hbpos hbA hAw hK1
  have hBd : 0 < P.w + X1 P.n := by
    rw [hX1]; have : 0 ≤ (nR - 1)/(nR + 1) := div_nonneg (by linarith) (by linarith)
    linarith
  have hαFE : (P.w - 1) / (P.w + X1 P.n) < θFE := by
    have : (P.w - 1) / (P.w + X1 P.n) ≤ (P.w - 1) / (A + b) := by
      apply div_le_div_of_nonneg_left (by linarith) hK
      rw [hX1, hAv, hb]
      have e1 : 2 / (nR * (nR + 1)) ≤ 2 / (nR + 1) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      have e2 : (nR - 3)/(nR + 1) + 2 / (nR + 1) = (nR - 1)/(nR + 1) := by
        field_simp; ring
      linarith
    linarith
  rw [hF, ← hFp]
  exact main_abstract (ft P.w A b k) (ft_cont P.w A b k) (Fp P.w k 1) A (P.w - 1)
    (P.w + X1 P.n) θFE hE hEA hsl h1 (by linarith) hFEt hfFE hiff hmono hBd hαFE
    P.φ P.R hR hφ0 hφR hφm hφc

end SEP1Aux

theorem solution (P : StartupExit.ExitChoice.Params) (hS : P.Standing) :
    ∃ cl cu : ℝ, 0 < cl ∧ cl < cu ∧ cu < P.R ∧
      (∀ c ∈ Set.Ico 0 cl, ∃ θL : ℝ,
          (P.w - 1) / (P.φ (P.R - c) * (P.w + X1 P.n)) < θL ∧ θL < thetaTilde P ∧
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            choice P c θ ≠ Strategy.late ∧ (choice P c θ = Strategy.flexible ↔ θL < θ)) ∧
      (∀ c ∈ Set.Ioo cl cu, ∃ θL θH : ℝ,
          thetaTilde P < θH ∧ θH < 1 ∧ θL < θH ∧
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            (θH ≤ θ → choice P c θ = Strategy.late) ∧
            (θ < θH → choice P c θ ≠ Strategy.late) ∧
            (θL < θ → θ < θH → choice P c θ = Strategy.flexible) ∧
            (θ ≤ θL → choice P c θ = Strategy.early)) ∧
      (∀ c ∈ Set.Icc cu P.R, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
          (θ ≤ thetaTilde P → choice P c θ = Strategy.early) ∧
          (thetaTilde P < θ → choice P c θ = Strategy.late)) :=
  SEP1Aux.prop1_core P hS
