-- Prove2me | solution 1 for PorteusSS.conv_exp_mem_CK
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:30:23.740376+00:00
-- url     : https://prove2.me/submissions/d15506b8-b0d1-4444-a347-f7051bd6cd6c

import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

theorem aux_ce_det01 : ∀ (k : ℕ) (x t : Fin k → ℝ), StrictMono x → StrictMono t →
    0 ≤ (Matrix.of fun i j : Fin k => if t j ≤ x i then (1:ℝ) else 0).det := by
  intro k
  induction k with
  | zero => intro x t _ _; simp
  | succ k ih =>
    intro x t hx ht
    by_cases h0 : t 0 ≤ x 0
    · by_cases hj : ∃ j : Fin (k+1), j ≠ 0 ∧ t j ≤ x 0
      · obtain ⟨j, hj0, hjx⟩ := hj
        rw [Matrix.det_zero_of_column_eq (Ne.symm hj0)]
        intro r
        have hr : x 0 ≤ x r := hx.monotone (Fin.zero_le r)
        simp only [Matrix.of_apply]
        rw [if_pos (h0.trans hr), if_pos (hjx.trans hr)]
      · push Not at hj
        rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
        have hrest : ∀ i : Fin k, (Matrix.of fun i j : Fin (k+1) =>
            if t j ≤ x i then (1:ℝ) else 0) 0 i.succ = 0 := by
          intro i
          simp only [Matrix.of_apply]
          rw [if_neg (not_le.mpr (hj i.succ (Fin.succ_ne_zero i)))]
        simp only [hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
        simp only [Matrix.of_apply, if_pos h0, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
        have := ih (x ∘ Fin.succ) (t ∘ Fin.succ) (hx.comp (Fin.strictMono_succ))
          (ht.comp (Fin.strictMono_succ))
        convert this using 2
        ext i j
        simp [Matrix.submatrix_apply]
    · rw [Matrix.det_eq_zero_of_row_eq_zero 0]
      intro j
      simp only [Matrix.of_apply]
      rw [if_neg]
      intro hc
      exact h0 ((ht.monotone (Fin.zero_le j)).trans hc)

theorem aux_ce_expD_eq (μ x t : ℝ) : expDensity μ (x - t) =
    (μ * Real.exp (-μ * x)) * (Real.exp (μ * t) * (if t ≤ x then (1:ℝ) else 0)) := by
  unfold expDensity
  by_cases h : t ≤ x
  · rw [if_pos (sub_nonneg.mpr h), if_pos h]
    rw [show -μ * (x - t) = -μ * x + μ * t by ring, Real.exp_add]
    ring
  · rw [if_neg (by intro hc; exact h (sub_nonneg.mp hc)), if_neg h]
    ring

theorem aux_ce_expD_meas (μ : ℝ) : Measurable (expDensity μ) := by
  unfold expDensity
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) (by fun_prop)
    measurable_const

theorem aux_ce_expD_nonneg {μ : ℝ} (hμ : 0 < μ) (t : ℝ) : 0 ≤ expDensity μ t := by
  unfold expDensity
  split_ifs
  · positivity
  · exact le_rfl

theorem aux_ce_expD_integrable {μ : ℝ} (hμ : 0 < μ) : Integrable (expDensity μ) := by
  have h1 : IntegrableOn (fun t => μ * Real.exp (-μ * t)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi ((exp_neg_integrableOn_Ioi 0 hμ).const_mul μ)
  have h2 := h1.integrable_indicator measurableSet_Ici
  refine h2.congr (Eventually.of_forall fun t => ?_)
  simp only [indicator, mem_Ici, expDensity]

theorem aux_ce_expD_integral {μ : ℝ} (hμ : 0 < μ) : ∫ t, expDensity μ t = 1 := by
  have e : expDensity μ = (Ici (0:ℝ)).indicator (fun t => μ * Real.exp (-μ * t)) := by
    funext t
    simp only [indicator, mem_Ici, expDensity]
  rw [e, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
  field_simp
  simp

theorem aux_ce_expPFF {μ : ℝ} (hμ : 0 < μ) : IsPFF (expDensity μ) := by
  intro n _
  refine ⟨⟨aux_ce_expD_integrable hμ, by rw [aux_ce_expD_integral hμ]; norm_num⟩, ?_⟩
  intro k _ _ x t hx ht
  have e : (Matrix.of fun i j : Fin k => expDensity μ (x i - t j)) =
      Matrix.of fun i j => (μ * Real.exp (-μ * x i)) *
        (Matrix.of fun i j => Real.exp (μ * t j) * (if t j ≤ x i then (1:ℝ) else 0)) i j := by
    ext i j
    simp only [Matrix.of_apply]
    exact aux_ce_expD_eq μ (x i) (t j)
  have e2 : (Matrix.of fun i j : Fin k => Real.exp (μ * t j) *
      (if t j ≤ x i then (1:ℝ) else 0)).det = (∏ j, Real.exp (μ * t j)) *
      (Matrix.of fun i j : Fin k => if t j ≤ x i then (1:ℝ) else 0).det :=
    Matrix.det_mul_row _ _
  rw [e, Matrix.det_mul_column, e2]
  refine mul_nonneg (Finset.prod_nonneg fun i _ => by positivity)
    (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (aux_ce_det01 k x t hx ht))

theorem aux_ce_reflPF {n : ℕ} {ψ : ℝ → ℝ} (h : IsPF n ψ) : IsPF n (fun x => ψ (-x)) := by
  refine ⟨⟨h.1.1.comp_neg, by rw [integral_neg_eq_self ψ volume]; exact h.1.2⟩, ?_⟩
  intro k hk1 hkn x t hx ht
  have hx' : StrictMono (fun i => -x (Fin.rev i)) := by
    intro i j hij
    have := hx (Fin.rev_lt_rev.mpr hij)
    simp only
    linarith
  have ht' : StrictMono (fun i => -t (Fin.rev i)) := by
    intro i j hij
    have := ht (Fin.rev_lt_rev.mpr hij)
    simp only
    linarith
  have key := h.2 k hk1 hkn _ _ hx' ht'
  have e : (Matrix.of fun i j : Fin k => ψ (-x (Fin.rev i) - -t (Fin.rev j))) =
      (Matrix.of fun i j : Fin k => ψ (-(x i - t j))).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Fin.revPerm_apply]
    congr 1
    ring
  rw [e, Matrix.det_submatrix_equiv_self] at key
  exact key

theorem aux_ce_reflPFF {ψ : ℝ → ℝ} (h : IsPFF ψ) : IsPFF (fun x => ψ (-x)) :=
  fun n hn => aux_ce_reflPF (h n hn)


theorem aux_ce_pf1_nonneg {ψ : ℝ → ℝ} (h : IsPF 1 ψ) (w : ℝ) : 0 ≤ ψ w := by
  have := h.2 1 le_rfl le_rfl (fun _ => w) (fun _ => 0) (Subsingleton.strictMono _)
    (Subsingleton.strictMono _)
  simpa using this

theorem aux_ce_pf2 {ψ : ℝ → ℝ} (h : IsPF 2 ψ) {a c b : ℝ} (hac : a < c) (hcb : c < b) :
    ψ a * ψ b ≤ ψ c * ψ (a + b - c) := by
  have hx : StrictMono ![c, b] := Fin.strictMono_iff_lt_succ.mpr (by
    intro i; fin_cases i; simp [hcb])
  have ht : StrictMono ![0, c - a] := Fin.strictMono_iff_lt_succ.mpr (by
    intro i; fin_cases i; simp; linarith)
  have := h.2 2 (by norm_num) le_rfl ![c, b] ![0, c - a] hx ht
  rw [Matrix.det_fin_two] at this
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero] at this
  have e1 : c - (c - a) = a := by ring
  have e2 : b - (c - a) = a + b - c := by ring
  rw [e1, e2] at this
  linarith [mul_comm (ψ a) (ψ b)]

theorem aux_ce_meas_bound {ψ : ℝ → ℝ} (hψ0 : ∀ x, 0 ≤ ψ x) (hint : Integrable ψ)
    (h2 : ∀ a c b, a < c → c < b → ψ a * ψ b ≤ ψ c * ψ (a + b - c)) {a b : ℝ} (hab : a < b) :
    ψ a * ψ b * (b - a) ^ 2 ≤ 4 * (∫ x, ψ x) ^ 2 := by
  have hP0 : 0 ≤ ψ a * ψ b := mul_nonneg (hψ0 a) (hψ0 b)
  rcases hP0.eq_or_lt with hP | hP
  · rw [← hP]; simp only [zero_mul]; positivity
  set P := ψ a * ψ b with hPdef
  set s := Real.sqrt P with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hP
  have hss : s * s = P := Real.mul_self_sqrt hP0
  set S := {x | s ≤ ψ x} with hSdef
  have hsub : Ioo a b ⊆ S ∪ (fun c => -c) ⁻¹' ((fun c => c + (a + b)) ⁻¹' S) := by
    intro c hc
    by_contra hn
    simp only [mem_union, mem_preimage, mem_ofPred_eq, not_or, not_le, S] at hn
    have h1 := h2 a c b hc.1 hc.2
    have e : -c + (a + b) = a + b - c := by ring
    rw [e] at hn
    have : ψ c * ψ (a + b - c) < s * s := mul_lt_mul'' hn.1 hn.2 (hψ0 _) (hψ0 _)
    linarith
  have hfin : volume S < ⊤ := by
    have := hint.measure_norm_ge_lt_top hs
    have e : {x | s ≤ ‖ψ x‖} = S := by
      ext x; simp [S, Real.norm_eq_abs, abs_of_nonneg (hψ0 x)]
    rwa [e] at this
  have hvol : ENNReal.ofReal (b - a) ≤ 2 * volume S := by
    rw [← Real.volume_Ioo]
    calc volume (Ioo a b) ≤ volume (S ∪ (fun c => -c) ⁻¹' ((fun c => c + (a + b)) ⁻¹' S)) :=
          measure_mono hsub
      _ ≤ volume S + volume ((fun c => -c) ⁻¹' ((fun c => c + (a + b)) ⁻¹' S)) :=
          measure_union_le _ _
      _ = volume S + volume S := by
          rw [show (fun c : ℝ => -c) = Neg.neg from rfl, Measure.measure_preimage_neg,
            measure_preimage_add_right]
      _ = 2 * volume S := by rw [two_mul]
  have hreal : b - a ≤ 2 * volume.real S := by
    have hne : (2 : ENNReal) * volume S ≠ ⊤ := ENNReal.mul_ne_top (by simp) hfin.ne
    have := ENNReal.toReal_mono hne hvol
    rwa [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_mul] at this
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hψ0) hint s
  have h3 : s * (b - a) ≤ 2 * ∫ x, ψ x := by
    have : s * (b - a) ≤ s * (2 * volume.real S) := mul_le_mul_of_nonneg_left hreal hs.le
    have e : {x | s ≤ ψ x} = S := rfl
    rw [e] at hmk
    try simp only [ENNReal.toReal_ofNat] at this
    linarith
  have hsba : 0 ≤ s * (b - a) := by have : 0 < b - a := by linarith
                                    positivity
  calc P * (b - a) ^ 2 = (s * (b - a)) ^ 2 := by rw [← hss]; ring
    _ ≤ (2 * ∫ x, ψ x) ^ 2 := pow_le_pow_left₀ hsba h3 2
    _ = 4 * (∫ x, ψ x) ^ 2 := by ring

theorem aux_ce_decay {ψ : ℝ → ℝ} (hψ0 : ∀ x, 0 ≤ ψ x) (hint : Integrable ψ)
    (hpos : 0 < ∫ x, ψ x)
    (h2 : ∀ a c b, a < c → c < b → ψ a * ψ b ≤ ψ c * ψ (a + b - c)) :
    ∃ R C c : ℝ, 0 < c ∧ ∀ ξ, R ≤ ξ → ψ ξ ≤ C * Real.exp (-c * ξ) := by
  obtain ⟨p, hp⟩ : ∃ p, 0 < ψ p := by
    by_contra hcon
    push Not at hcon
    have : ∫ x, ψ x = 0 := by
      rw [show ψ = fun _ => 0 from funext fun x => le_antisymm (hcon x) (hψ0 x)]
      simp
    linarith
  set J := ∫ x, ψ x with hJ
  set q := ψ p with hq
  set B := 4 * J ^ 2 / q with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ w, p + 1 ≤ w → ψ w ≤ B := by
    intro w hw
    have := aux_ce_meas_bound hψ0 hint h2 (show p < w by linarith)
    rw [hBdef, le_div_iff₀ hp]
    have h1 : 1 ≤ (w - p) ^ 2 := by nlinarith
    have h4 : 0 ≤ q * ψ w := mul_nonneg hp.le (hψ0 w)
    nlinarith
  set h := 1 + 3 * J / q with hhdef
  have hh1 : 1 ≤ h := by
    have : 0 ≤ 3 * J / q := by positivity
    linarith
  have hph : ψ (p + h) ≤ q / 2 := by
    have := aux_ce_meas_bound hψ0 hint h2 (show p < p + h by linarith)
    simp only [add_sub_cancel_left] at this
    have h3 : 3 * J ≤ h * q := by
      rw [hhdef, add_mul, div_mul_cancel₀ _ hp.ne']
      linarith
    have hq2 : 9 * J ^ 2 ≤ (h * q) ^ 2 := by nlinarith
    by_contra hc
    push Not at hc
    have h5 : q * (q / 2) * h ^ 2 ≤ q * ψ (p + h) * h ^ 2 := by
      have : 0 ≤ q * h ^ 2 := by positivity
      nlinarith
    nlinarith
  have hstep : ∀ w, p < w → ψ (w + h) ≤ ψ w / 2 := by
    intro w hw
    have := h2 p (p + h) (w + h) (by linarith) (by linarith)
    have e : p + (w + h) - (p + h) = w := by ring
    rw [e] at this
    have h6 : q * ψ (w + h) ≤ q * (ψ w / 2) := by nlinarith [hψ0 w]
    exact le_of_mul_le_mul_left h6 hp
  have hiter : ∀ n : ℕ, ∀ w, p + 1 ≤ w → ψ (w + n * h) ≤ B / 2 ^ n := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hB w hw
    | succ n ih =>
      intro w hw
      have e : w + ((n + 1 : ℕ) : ℝ) * h = (w + n * h) + h := by push_cast; ring
      rw [e]
      have hnh : (0:ℝ) ≤ n * h := by positivity
      calc ψ ((w + n * h) + h) ≤ ψ (w + n * h) / 2 := hstep _ (by linarith)
        _ ≤ B / 2 ^ n / 2 := by linarith [ih w hw]
        _ = B / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 : 0 < h := by linarith
  refine ⟨p + 1, 2 * B * Real.exp (Real.log 2 / h * (p + 1)), Real.log 2 / h,
    by positivity, ?_⟩
  intro ξ hξ
  set n := ⌊(ξ - (p + 1)) / h⌋₊ with hndef
  have hn1 : (n : ℝ) ≤ (ξ - (p + 1)) / h := Nat.floor_le (div_nonneg (by linarith) hh0.le)
  have hn2 : (ξ - (p + 1)) / h < n + 1 := Nat.lt_floor_add_one _
  have hw : p + 1 ≤ ξ - n * h := by
    have := (le_div_iff₀ hh0).mp hn1
    linarith
  have key := hiter n (ξ - n * h) hw
  rw [sub_add_cancel] at key
  have e2 : (2:ℝ) ^ n = Real.exp (n * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hlt : -(n * Real.log 2) ≤ Real.log 2 * (1 - (ξ - (p + 1)) / h) := by
    nlinarith
  calc ψ ξ ≤ B / 2 ^ n := key
    _ = B * Real.exp (-(n * Real.log 2)) := by rw [e2, Real.exp_neg, div_eq_mul_inv]
    _ ≤ B * Real.exp (Real.log 2 * (1 - (ξ - (p + 1)) / h)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlt) hB0
    _ = 2 * B * Real.exp (Real.log 2 / h * (p + 1)) * Real.exp (-(Real.log 2 / h) * ξ) := by
        have e3 : Real.log 2 * (1 - (ξ - (p + 1)) / h) =
            Real.log 2 + (Real.log 2 / h * (p + 1) + -(Real.log 2 / h) * ξ) := by
          field_simp
          ring
        rw [e3, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
        ring

theorem aux_ce_integrable_exp_neg_abs {μ : ℝ} (hμ : 0 < μ) :
    Integrable (fun ξ : ℝ => Real.exp (-μ * |ξ|)) := by
  have h1 : IntegrableOn (fun ξ : ℝ => Real.exp (-μ * |ξ|)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hμ).congr_fun (fun x hx => by
      simp only; rw [abs_of_pos (mem_Ioi.mp hx)]) measurableSet_Ioi
  have h2 : IntegrableOn (fun ξ : ℝ => Real.exp (-μ * |ξ|)) (Iic 0) :=
    (integrableOn_exp_mul_Iic hμ 0).congr_fun (fun x hx => by
      simp only; rw [abs_of_nonpos (mem_Iic.mp hx)]; ring_nf) measurableSet_Iic
  have := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at this

theorem aux_ce_pff_expint {ψ : ℝ → ℝ} (hψ : IsPFF ψ) :
    ∃ μ, 0 < μ ∧ Integrable (fun ξ => Real.exp (μ * |ξ|) * ψ ξ) := by
  have h1 := hψ 1 le_rfl
  have h2' := hψ 2 (by norm_num)
  have hψ0 : ∀ x, 0 ≤ ψ x := aux_ce_pf1_nonneg h1
  have hint : Integrable ψ := h1.1.1
  have hpos : 0 < ∫ x, ψ x := h1.1.2
  have h2 : ∀ a c b, a < c → c < b → ψ a * ψ b ≤ ψ c * ψ (a + b - c) :=
    fun a c b hac hcb => aux_ce_pf2 h2' hac hcb
  obtain ⟨R1, C1, c1, hc1, hd1⟩ := aux_ce_decay hψ0 hint hpos h2
  have hψ0' : ∀ x, 0 ≤ ψ (-x) := fun x => hψ0 _
  have hint' : Integrable (fun x => ψ (-x)) := hint.comp_neg
  have hpos' : 0 < ∫ x, ψ (-x) := by rw [integral_neg_eq_self ψ volume]; exact hpos
  have h2r : ∀ a c b, a < c → c < b → ψ (-a) * ψ (-b) ≤ ψ (-c) * ψ (-(a + b - c)) := by
    intro a c b hac hcb
    have := h2 (-b) (-c) (-a) (by linarith) (by linarith)
    have e : -b + -a - -c = -(a + b - c) := by ring
    rw [e] at this
    linarith [mul_comm (ψ (-a)) (ψ (-b))]
  obtain ⟨R2, C2, c2, hc2, hd2⟩ := aux_ce_decay hψ0' hint' hpos' h2r
  set μ := min c1 c2 / 2 with hμdef
  have hμ : 0 < μ := by positivity
  have hμ1 : 2 * μ ≤ c1 := by rw [hμdef]; linarith [min_le_left c1 c2]
  have hμ2 : 2 * μ ≤ c2 := by rw [hμdef]; linarith [min_le_right c1 c2]
  set R := max (max R1 R2) 0 with hRdef
  set C := max (max C1 C2) 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC1 : C1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR1 : R1 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR2 : R2 ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨μ, hμ, ?_⟩
  have hdom : Integrable (fun ξ => Real.exp (μ * R) * ψ ξ + C * Real.exp (-μ * |ξ|)) :=
    (hint.const_mul _).add ((aux_ce_integrable_exp_neg_abs hμ).const_mul C)
  refine hdom.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable.mul
      hint.aestronglyMeasurable
  · have hpos1 : 0 ≤ Real.exp (μ * |ξ|) * ψ ξ := mul_nonneg (Real.exp_pos _).le (hψ0 ξ)
    have hpos2 : 0 ≤ C * Real.exp (-μ * |ξ|) := mul_nonneg hC0 (Real.exp_pos _).le
    have hpos3 : 0 ≤ Real.exp (μ * R) * ψ ξ := mul_nonneg (Real.exp_pos _).le (hψ0 ξ)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos1]
    rcases le_or_gt |ξ| R with hξ | hξ
    · have : Real.exp (μ * |ξ|) ≤ Real.exp (μ * R) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hξ hμ.le)
      have := mul_le_mul_of_nonneg_right this (hψ0 ξ)
      linarith
    · have hψb : ψ ξ ≤ C * Real.exp (-(2 * μ) * |ξ|) := by
        rcases le_or_gt 0 ξ with hs | hs
        · rw [abs_of_nonneg hs] at hξ ⊢
          calc ψ ξ ≤ C1 * Real.exp (-c1 * ξ) := hd1 ξ (by linarith)
            _ ≤ C * Real.exp (-c1 * ξ) := mul_le_mul_of_nonneg_right hC1 (Real.exp_pos _).le
            _ ≤ C * Real.exp (-(2 * μ) * ξ) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC0
        · rw [abs_of_neg hs] at hξ ⊢
          have := hd2 (-ξ) (by linarith)
          rw [neg_neg] at this
          calc ψ ξ ≤ C2 * Real.exp (-c2 * -ξ) := this
            _ ≤ C * Real.exp (-c2 * -ξ) := mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le
            _ ≤ C * Real.exp (-(2 * μ) * -ξ) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC0
      have : Real.exp (μ * |ξ|) * ψ ξ ≤ C * Real.exp (-μ * |ξ|) := by
        calc Real.exp (μ * |ξ|) * ψ ξ ≤ Real.exp (μ * |ξ|) * (C * Real.exp (-(2 * μ) * |ξ|)) :=
              mul_le_mul_of_nonneg_left hψb (Real.exp_pos _).le
          _ = C * (Real.exp (μ * |ξ|) * Real.exp (-(2 * μ) * |ξ|)) := by ring
          _ = C * Real.exp (-μ * |ξ|) := by rw [← Real.exp_add]; ring_nf
      linarith

theorem aux_ce_expD_sum {μ : ℝ} (hμ : 0 < μ) (t : ℝ) :
    μ * Real.exp (-μ * |t|) ≤ expDensity μ t + expDensity μ (-t) := by
  unfold expDensity
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, abs_of_nonneg ht]
    have : 0 ≤ if 0 ≤ -t then μ * Real.exp (-μ * -t) else 0 := by
      split_ifs
      · positivity
      · exact le_rfl
    linarith
  · push Not at ht
    rw [if_neg (not_le.mpr ht), if_pos (by linarith), abs_of_neg ht]
    linarith

theorem aux_ce_f_weighted {f : ℝ → ℝ} (hpf : PFIntegrable f) {μ : ℝ} (hμ : 0 < μ) :
    Integrable (fun u => f u * Real.exp (-μ * |u|)) := by
  have hA := hpf (expDensity μ) (aux_ce_expPFF hμ) 0
  have hB := hpf (fun x => expDensity μ (-x)) (aux_ce_reflPFF (aux_ce_expPFF hμ)) 0
  have hwpos : ∀ ξ, 0 < expDensity μ ξ + expDensity μ (-ξ) := by
    intro ξ
    have := aux_ce_expD_sum hμ ξ
    have : 0 < μ * Real.exp (-μ * |ξ|) := by positivity
    linarith
  have hmeas : AEStronglyMeasurable (fun ξ => f (0 - ξ)) volume := by
    have hw : Measurable (fun ξ => (expDensity μ ξ + expDensity μ (-ξ))⁻¹) :=
      ((aux_ce_expD_meas μ).add ((aux_ce_expD_meas μ).comp measurable_neg)).inv
    have := (hA.aestronglyMeasurable.add hB.aestronglyMeasurable).mul hw.aestronglyMeasurable
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [← mul_add, mul_assoc, mul_inv_cancel₀ (hwpos ξ).ne', mul_one]
  have hξ : Integrable (fun ξ => f (0 - ξ) * Real.exp (-μ * |ξ|)) := by
    refine ((hA.norm.add hB.norm).const_mul μ⁻¹).mono'
      (hmeas.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable)
      (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, Real.abs_exp]
    rw [abs_of_nonneg (aux_ce_expD_nonneg hμ ξ), abs_of_nonneg (aux_ce_expD_nonneg hμ (-ξ))]
    have h1 := aux_ce_expD_sum hμ ξ
    have h2 : Real.exp (-μ * |ξ|) ≤ μ⁻¹ * (expDensity μ ξ + expDensity μ (-ξ)) := by
      rw [le_inv_mul_iff₀ hμ]; exact h1
    calc |f (0 - ξ)| * Real.exp (-μ * |ξ|)
        ≤ |f (0 - ξ)| * (μ⁻¹ * (expDensity μ ξ + expDensity μ (-ξ))) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = μ⁻¹ * (|f (0 - ξ)| * expDensity μ ξ + |f (0 - ξ)| * expDensity μ (-ξ)) := by ring
  have := hξ.comp_neg
  simpa [abs_neg] using this

theorem aux_ce_f_meas {f : ℝ → ℝ} {μ : ℝ} (hw : Integrable (fun u => f u * Real.exp (-μ * |u|))) :
    AEStronglyMeasurable f volume := by
  have hc : AEStronglyMeasurable (fun u => Real.exp (μ * |u|)) volume :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  have := hw.aestronglyMeasurable.mul hc
  refine this.congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← Real.exp_add]
  simp

theorem aux_ce_F_intOn {f : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hw : Integrable (fun u => f u * Real.exp (-lam * |u|))) (z : ℝ) :
    IntegrableOn (fun u => f u * Real.exp (lam * u)) (Iic z) := by
  have hm := aux_ce_f_meas hw
  refine ((hw.norm.mul_const (Real.exp (2 * lam * |z|))).integrableOn).mono'
    ((hm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).restrict)
    (ae_restrict_of_forall_mem measurableSet_Iic fun u hu => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hu' : u ≤ z := hu
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
    have : u ≤ |z| := hu'.trans (le_abs_self z)
    nlinarith
  · rw [abs_of_neg h]
    have := abs_nonneg z
    nlinarith

theorem aux_ce_repr0 (f : ℝ → ℝ) (lam z : ℝ) :
    conv f (expDensity lam) z = ∫ u, f u * expDensity lam (z - u) := by
  unfold conv
  have := integral_sub_left_eq_self (fun u => f u * expDensity lam (z - u)) volume z
  simpa [sub_sub_cancel] using this

theorem aux_ce_repr (f : ℝ → ℝ) (lam z : ℝ) :
    conv f (expDensity lam) z =
      lam * Real.exp (-lam * z) * ∫ u in Iic z, f u * Real.exp (lam * u) := by
  rw [aux_ce_repr0]
  have e2 : (fun u => f u * expDensity lam (z - u)) = (Iic z).indicator
      (fun u => (lam * Real.exp (-lam * z)) * (f u * Real.exp (lam * u))) := by
    funext u
    simp only [indicator, mem_Iic, expDensity]
    by_cases h : u ≤ z
    · rw [if_pos (sub_nonneg.mpr h), if_pos h]
      rw [show -lam * (z - u) = -lam * z + lam * u by ring, Real.exp_add]
      ring
    · rw [if_neg (by intro hc; exact h (sub_nonneg.mp hc)), if_neg h]
      ring
  rw [e2, integral_indicator measurableSet_Iic, integral_const_mul]

theorem aux_ce_int_exp {lam : ℝ} (hlam : 0 < lam) (z w : ℝ) :
    ∫ u in z..w, Real.exp (lam * u) = (Real.exp (lam * w) - Real.exp (lam * z)) / lam := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) hlam.ne', integral_exp,
    smul_eq_mul]
  field_simp

theorem aux_ce_window {f : ℝ → ℝ} {lam : ℝ}
    (hint : ∀ z, IntegrableOn (fun u => f u * Real.exp (lam * u)) (Iic z)) (z w : ℝ) :
    conv f (expDensity lam) w = Real.exp (-lam * (w - z)) * conv f (expDensity lam) z +
      lam * Real.exp (-lam * w) * ∫ u in z..w, f u * Real.exp (lam * u) := by
  rw [aux_ce_repr, aux_ce_repr, ← intervalIntegral.integral_Iic_sub_Iic (hint z) (hint w)]
  have e : Real.exp (-lam * (w - z)) * Real.exp (-lam * z) = Real.exp (-lam * w) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination (-(lam * ∫ u in Iic z, f u * Real.exp (lam * u))) * e

theorem aux_ce_exp_alg {lam : ℝ} (hlam : 0 < lam) (z w s : ℝ) :
    lam * Real.exp (-lam * w) * (s * ((Real.exp (lam * w) - Real.exp (lam * z)) / lam)) =
      (1 - Real.exp (-lam * (w - z))) * s := by
  have e1 : Real.exp (-lam * w) * Real.exp (lam * w) = 1 := by
    rw [← Real.exp_add]; simp
  have e2 : Real.exp (-lam * w) * Real.exp (lam * z) = Real.exp (-lam * (w - z)) := by
    rw [← Real.exp_add]; ring_nf
  have hl : lam ≠ 0 := hlam.ne'
  calc lam * Real.exp (-lam * w) * (s * ((Real.exp (lam * w) - Real.exp (lam * z)) / lam))
      = s * (Real.exp (-lam * w) * Real.exp (lam * w)) -
          s * (Real.exp (-lam * w) * Real.exp (lam * z)) := by field_simp
    _ = (1 - Real.exp (-lam * (w - z))) * s := by rw [e1, e2]; ring

theorem aux_ce_win_lo {f : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hint : ∀ z, IntegrableOn (fun u => f u * Real.exp (lam * u)) (Iic z)) {z w : ℝ} (hzw : z ≤ w)
    (s : ℝ) (hs : ∀ u ∈ Ioo z w, s ≤ f u) :
    Real.exp (-lam * (w - z)) * conv f (expDensity lam) z + (1 - Real.exp (-lam * (w - z))) * s ≤
      conv f (expDensity lam) w := by
  rw [aux_ce_window hint z w]
  have hII : IntervalIntegrable (fun u => f u * Real.exp (lam * u)) volume z w :=
    ((hint w).mono_set (fun x hx => by
      have := hx.2; simp only [mem_Iic]; rwa [max_eq_right hzw] at this)).intervalIntegrable
  have hmono : ∫ u in z..w, s * Real.exp (lam * u) ≤ ∫ u in z..w, f u * Real.exp (lam * u) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hzw
      (by apply Continuous.intervalIntegrable; fun_prop) hII
      (fun u hu => mul_le_mul_of_nonneg_right (hs u hu) (Real.exp_pos _).le)
  rw [intervalIntegral.integral_const_mul, aux_ce_int_exp hlam] at hmono
  have hpos : 0 ≤ lam * Real.exp (-lam * w) := by positivity
  have := mul_le_mul_of_nonneg_left hmono hpos
  rw [aux_ce_exp_alg hlam] at this
  linarith

theorem aux_ce_win_hi {f : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hint : ∀ z, IntegrableOn (fun u => f u * Real.exp (lam * u)) (Iic z)) {z w : ℝ} (hzw : z ≤ w)
    (s : ℝ) (hs : ∀ u ∈ Ioo z w, f u ≤ s) :
    conv f (expDensity lam) w ≤
      Real.exp (-lam * (w - z)) * conv f (expDensity lam) z + (1 - Real.exp (-lam * (w - z))) * s := by
  rw [aux_ce_window hint z w]
  have hII : IntervalIntegrable (fun u => f u * Real.exp (lam * u)) volume z w :=
    ((hint w).mono_set (fun x hx => by
      have := hx.2; simp only [mem_Iic]; rwa [max_eq_right hzw] at this)).intervalIntegrable
  have hmono : ∫ u in z..w, f u * Real.exp (lam * u) ≤ ∫ u in z..w, s * Real.exp (lam * u) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hzw hII
      (by apply Continuous.intervalIntegrable; fun_prop)
      (fun u hu => mul_le_mul_of_nonneg_right (hs u hu) (Real.exp_pos _).le)
  rw [intervalIntegral.integral_const_mul, aux_ce_int_exp hlam] at hmono
  have hpos : 0 ≤ lam * Real.exp (-lam * w) := by positivity
  have := mul_le_mul_of_nonneg_left hmono hpos
  rw [aux_ce_exp_alg hlam] at this
  linarith

theorem aux_ce_tail_lo {f : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hint : ∀ z, IntegrableOn (fun u => f u * Real.exp (lam * u)) (Iic z)) (z s : ℝ)
    (hs : ∀ u ∈ Iic z, s ≤ f u) : s ≤ conv f (expDensity lam) z := by
  rw [aux_ce_repr]
  have hmono : ∫ u in Iic z, s * Real.exp (lam * u) ≤ ∫ u in Iic z, f u * Real.exp (lam * u) :=
    setIntegral_mono_on ((integrableOn_exp_mul_Iic hlam z).const_mul s) (hint z)
      measurableSet_Iic (fun u hu => mul_le_mul_of_nonneg_right (hs u hu) (Real.exp_pos _).le)
  rw [integral_const_mul, integral_exp_mul_Iic hlam] at hmono
  have hpos : 0 ≤ lam * Real.exp (-lam * z) := by positivity
  have := mul_le_mul_of_nonneg_left hmono hpos
  have e : lam * Real.exp (-lam * z) * (s * (Real.exp (lam * z) / lam)) = s := by
    have e1 : Real.exp (-lam * z) * Real.exp (lam * z) = 1 := by
      rw [← Real.exp_add]; simp
    calc lam * Real.exp (-lam * z) * (s * (Real.exp (lam * z) / lam))
        = s * (Real.exp (-lam * z) * Real.exp (lam * z)) := by field_simp
      _ = s := by rw [e1]; ring
  linarith

theorem aux_ce_cont {f : ℝ → ℝ} {lam : ℝ}
    (hint : ∀ z, IntegrableOn (fun u => f u * Real.exp (lam * u)) (Iic z)) :
    Continuous (conv f (expDensity lam)) := by
  have e : conv f (expDensity lam) = fun z => lam * Real.exp (-lam * z) *
      ((∫ u in Iic 0, f u * Real.exp (lam * u)) + ∫ u in (0:ℝ)..z, f u * Real.exp (lam * u)) := by
    funext z
    rw [aux_ce_repr, ← intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint z)]
    ring
  rw [e]
  have hII : ∀ a b, IntervalIntegrable (fun u => f u * Real.exp (lam * u)) volume a b :=
    fun a b => ((hint (max a b)).mono_set (fun x hx => hx.2)).intervalIntegrable
  exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
    (continuous_const.add (intervalIntegral.continuous_primitive hII 0))

theorem aux_ce_expD_le {lam μ : ℝ} (hμ : 0 < μ) (hμl : μ ≤ lam) (z u : ℝ) :
    expDensity lam (z - u) ≤ lam * Real.exp (μ * |z|) * Real.exp (-μ * |u|) := by
  unfold expDensity
  have hl : 0 < lam := lt_of_lt_of_le hμ hμl
  split_ifs with h
  · rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hl.le
    have h1 : |u| ≤ |z| + (z - u) := by
      rcases abs_cases u with ⟨hu, _⟩ | ⟨hu, _⟩ <;> rcases abs_cases z with ⟨hz, _⟩ | ⟨hz, _⟩ <;>
        linarith
    nlinarith
  · positivity

theorem aux_ce_growth {f : ℝ → ℝ} {lam μ : ℝ} (hμ : 0 < μ) (hμl : μ ≤ lam)
    (hw : Integrable (fun u => f u * Real.exp (-μ * |u|))) (z : ℝ) :
    |conv f (expDensity lam) z| ≤
      lam * Real.exp (μ * |z|) * ∫ u, ‖f u * Real.exp (-μ * |u|)‖ := by
  rw [aux_ce_repr0, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hw.norm.const_mul _) (Eventually.of_forall fun u => ?_)
  have hl : 0 < lam := lt_of_lt_of_le hμ hμl
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  rw [abs_of_nonneg (aux_ce_expD_nonneg hl _)]
  have := aux_ce_expD_le hμ hμl z u
  calc |f u| * expDensity lam (z - u) ≤ |f u| * (lam * Real.exp (μ * |z|) * Real.exp (-μ * |u|)) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = lam * Real.exp (μ * |z|) * (|f u| * Real.exp (-μ * |u|)) := by ring

theorem aux_ce_pfint {f : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam) (hpf : PFIntegrable f)
    (hcont : Continuous (conv f (expDensity lam))) :
    PFIntegrable (conv f (expDensity lam)) := by
  intro ψ hψ y
  obtain ⟨μ0, hμ0, hint⟩ := aux_ce_pff_expint hψ
  set μ := min lam μ0 with hμdef
  have hμ : 0 < μ := lt_min hlam hμ0
  have hμl : μ ≤ lam := min_le_left _ _
  have hμ0' : μ ≤ μ0 := min_le_right _ _
  have hw := aux_ce_f_weighted hpf hμ
  set N := lam * ∫ u, ‖f u * Real.exp (-μ * |u|)‖ with hNdef
  have hN0 : 0 ≤ N := mul_nonneg hlam.le (integral_nonneg fun _ => norm_nonneg _)
  have hgrow : ∀ z, |conv f (expDensity lam) z| ≤ N * Real.exp (μ * |z|) := by
    intro z
    have := aux_ce_growth hμ hμl hw z
    rw [hNdef]
    linarith [mul_comm (Real.exp (μ * |z|)) (∫ u, ‖f u * Real.exp (-μ * |u|)‖)]
  have hψ0 : ∀ x, 0 ≤ ψ x := aux_ce_pf1_nonneg (hψ 1 le_rfl)
  refine (hint.const_mul (N * Real.exp (μ * |y|))).mono'
    ((hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      (hψ 1 le_rfl).1.1.aestronglyMeasurable) (Eventually.of_forall fun ξ => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 ξ)]
  have h1 := hgrow (y - ξ)
  have h2 : Real.exp (μ * |y - ξ|) ≤ Real.exp (μ * |y|) * Real.exp (μ0 * |ξ|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := abs_sub y ξ
    have : μ * |ξ| ≤ μ0 * |ξ| := mul_le_mul_of_nonneg_right hμ0' (abs_nonneg _)
    nlinarith [abs_nonneg ξ]
  calc |conv f (expDensity lam) (y - ξ)| * ψ ξ ≤ N * Real.exp (μ * |y - ξ|) * ψ ξ :=
        mul_le_mul_of_nonneg_right h1 (hψ0 ξ)
    _ ≤ N * (Real.exp (μ * |y|) * Real.exp (μ0 * |ξ|)) * ψ ξ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hN0) (hψ0 ξ)
    _ = N * Real.exp (μ * |y|) * (Real.exp (μ0 * |ξ|) * ψ ξ) := by ring

theorem aux_ce_tendsto {f : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hint : ∀ z, IntegrableOn (fun u => f u * Real.exp (lam * u)) (Iic z))
    (htf : Tendsto f (cocompact ℝ) atTop) :
    Tendsto (conv f (expDensity lam)) (cocompact ℝ) atTop := by
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  constructor
  · rw [tendsto_atTop]
    intro M
    obtain ⟨R, hR⟩ := eventually_atBot.mp
      ((htf.mono_left atBot_le_cocompact).eventually_ge_atTop M)
    filter_upwards [eventually_le_atBot R] with z hz
    exact aux_ce_tail_lo hlam hint z M (fun u hu => hR u (le_trans (mem_Iic.mp hu) hz))
  · rw [tendsto_atTop]
    intro M
    obtain ⟨R, hR⟩ := eventually_atTop.mp
      ((htf.mono_left atTop_le_cocompact).eventually_ge_atTop (M + 1))
    set D := M + 1 - conv f (expDensity lam) R with hD
    have h1 : Tendsto (fun z : ℝ => z - R) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b + R, fun z hz => by linarith⟩
    have h2 : Tendsto (fun z : ℝ => -lam * (z - R)) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by linarith) h1
    have hlim : Tendsto (fun z => Real.exp (-lam * (z - R))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h2
    have hev : ∀ᶠ z in atTop, Real.exp (-lam * (z - R)) * |D| ≤ 1 := by
      have : Tendsto (fun z => Real.exp (-lam * (z - R)) * |D|) atTop (𝓝 0) := by
        simpa using hlim.mul_const |D|
      exact this.eventually (eventually_le_nhds zero_lt_one)
    filter_upwards [hev, eventually_ge_atTop R] with z hz1 hz2
    have := aux_ce_win_lo hlam hint hz2 (M + 1) (fun u hu => hR u hu.1.le)
    have hE : 0 ≤ Real.exp (-lam * (z - R)) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left (le_abs_self D) hE
    rw [hD] at this
    nlinarith

theorem aux_ce_anti {f : ℝ → ℝ} {lam a : ℝ} {I : Set ℝ} (hlam : 0 < lam)
    (hint : ∀ z, IntegrableOn (fun u => f u * Real.exp (lam * u)) (Iic z))
    (hI : I = Iio a ∨ I = Iic a) (hanti : AntitoneOn f I) :
    ∀ z1 z2, z1 ≤ z2 → z2 ≤ a → conv f (expDensity lam) z2 ≤ conv f (expDensity lam) z1 := by
  intro z1 z2 h12 h2a
  rcases h12.eq_or_lt with heq | hlt
  · rw [heq]
  have hmemI : ∀ u, u < a → u ∈ I := by
    rcases hI with rfl | rfl
    · exact fun u hu => hu
    · exact fun u hu => le_of_lt hu
  have hz1 : z1 ∈ I := hmemI z1 (by linarith)
  have htail : f z1 ≤ conv f (expDensity lam) z1 :=
    aux_ce_tail_lo hlam hint z1 (f z1) (fun u hu =>
      hanti (hmemI u (by linarith [mem_Iic.mp hu])) hz1 (mem_Iic.mp hu))
  have hwin := aux_ce_win_hi hlam hint h12 (f z1) (fun u hu =>
    hanti hz1 (hmemI u (by linarith [hu.2])) hu.1.le)
  have hE1 : Real.exp (-lam * (z2 - z1)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hE0 : 0 ≤ Real.exp (-lam * (z2 - z1)) := (Real.exp_pos _).le
  nlinarith

theorem aux_ce_qkc {f : ℝ → ℝ} {lam a K : ℝ} {I : Set ℝ} (hlam : 0 < lam) (hK : 0 ≤ K)
    (hint : ∀ z, IntegrableOn (fun u => f u * Real.exp (lam * u)) (Iic z))
    (hI : I = Iio a ∨ I = Iic a) (hanti : AntitoneOn f I) (hnk : NonKDecreasingOn f K Iᶜ)
    (hcont : Continuous (conv f (expDensity lam))) :
    ∀ x z y, x ≤ z → z ≤ y →
      conv f (expDensity lam) z ≤ max (conv f (expDensity lam) x) (conv f (expDensity lam) y + K) := by
  set h := conv f (expDensity lam) with hh
  intro x z y hxz hzy
  by_contra hcon
  push Not at hcon
  have hx' : h x < h z := lt_of_le_of_lt (le_max_left _ _) hcon
  have hy' : h y + K < h z := lt_of_le_of_lt (le_max_right _ _) hcon
  obtain ⟨m, hm, hmax⟩ := (isCompact_Icc (a := x) (b := y)).exists_isMaxOn
    ⟨x, left_mem_Icc.mpr (hxz.trans hzy)⟩ hcont.continuousOn
  rw [isMaxOn_iff] at hmax
  have hzm : h z ≤ h m := hmax z ⟨hxz, hzy⟩
  have hxm : x < m := by
    rcases hm.1.eq_or_lt with he | he
    · rw [← he] at hzm; linarith
    · exact he
  have hmy : m < y := by
    rcases hm.2.eq_or_lt with he | he
    · rw [he] at hzm; linarith
    · exact he
  have ham : a < m := by
    by_contra hc
    push Not at hc
    have := aux_ce_anti hlam hint hI hanti x m hm.1 hc
    linarith
  have hnotI : ∀ u, a < u → u ∉ I := by
    rcases hI with rfl | rfl
    · intro u hu hc; exact absurd (mem_Iio.mp hc) (not_lt.mpr hu.le)
    · intro u hu hc; exact absurd (mem_Iic.mp hc) (not_le.mpr hu)
  set δ := min (m - x) ((m - a) / 2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ m - x := min_le_left _ _
  have hδ2 : δ ≤ (m - a) / 2 := min_le_right _ _
  have hWa : ∀ u ∈ Ioo (m - δ) m, a < u := fun u hu => by linarith [hu.1]
  have hWne : (f '' Ioo (m - δ) m).Nonempty :=
    ⟨_, mem_image_of_mem f (show m - δ / 2 ∈ Ioo (m - δ) m from ⟨by linarith, by linarith⟩)⟩
  have hWbdd : BddAbove (f '' Ioo (m - δ) m) := by
    refine ⟨f m + K, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hnk u (hnotI u (hWa u hu)) m (hnotI m ham) hu.2.le
  set s' := sSup (f '' Ioo (m - δ) m) with hs'
  have hW : ∀ u ∈ Ioo (m - δ) m, f u ≤ s' := fun u hu => le_csSup hWbdd (mem_image_of_mem f hu)
  have hV : ∀ v ∈ Ioo m y, s' - K ≤ f v := by
    intro v hv
    have : s' ≤ f v + K := by
      refine csSup_le hWne ?_
      rintro _ ⟨u, hu, rfl⟩
      exact hnk u (hnotI u (hWa u hu)) v (hnotI v (by linarith [hv.1])) (by linarith [hu.2, hv.1])
    linarith
  have hback := aux_ce_win_hi hlam hint (show m - δ ≤ m by linarith) s' hW
  have hmδ : h (m - δ) ≤ h m := hmax (m - δ) ⟨by linarith, by linarith⟩
  have hE1 : Real.exp (-lam * (m - (m - δ))) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  have hms : h m ≤ s' := by
    by_contra hc
    push Not at hc
    have hE0 : 0 < 1 - Real.exp (-lam * (m - (m - δ))) := by linarith
    have := mul_lt_mul_of_pos_left hc hE0
    have := mul_le_mul_of_nonneg_left hmδ (Real.exp_pos (-lam * (m - (m - δ)))).le
    linarith
  have hfwd := aux_ce_win_lo hlam hint hmy.le (s' - K) hV
  have hE'1 : Real.exp (-lam * (y - m)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hE'0 : 0 ≤ Real.exp (-lam * (y - m)) := (Real.exp_pos _).le
  have : h m - K ≤ h y := by nlinarith
  linarith

theorem aux_ce_backward {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ}
    (hq : ∀ x z y, x ≤ z → z ≤ y → f z ≤ max (f x) (f y + K))
    (hpc : PiecewiseContinuousOn f univ) (hpf : PFIntegrable f)
    (ht : Tendsto f (cocompact ℝ) atTop) : ∃ a : ℝ, CaK a K f := by
  have hev1 : ∀ᶠ x in atBot, f 0 + K < f x :=
    (ht.mono_left atBot_le_cocompact).eventually_gt_atTop _
  have hev2 : ∀ᶠ x in atTop, f 0 < f x :=
    (ht.mono_left atTop_le_cocompact).eventually_gt_atTop _
  obtain ⟨T, hT⟩ := eventually_atBot.mp hev1
  obtain ⟨T', hT'⟩ := eventually_atTop.mp hev2
  set B : Set ℝ := {x | ∃ y, x ≤ y ∧ f y + K < f x} with hBdef
  have hB : ∀ x ∈ B, ∀ w, w ≤ x → f x ≤ f w := by
    rintro x ⟨y, hxy, hlt⟩ w hwx
    have hm := hq w x y hwx hxy
    rcases le_max_iff.mp hm with h | h
    · exact h
    · exact absurd h (not_le.mpr hlt)
  have hne : B.Nonempty := ⟨min T 0, 0, min_le_right _ _, hT _ (min_le_left _ _)⟩
  have hbdd : BddAbove B := by
    refine ⟨max T' 0, ?_⟩
    intro x hx
    by_contra hcon0
    have hcon := not_le.mp hcon0
    have h1 : T' ≤ x := le_trans (le_max_left _ _) hcon.le
    have h2 : (0:ℝ) ≤ x := le_trans (le_max_right _ _) hcon.le
    have h3 := hB x hx 0 h2
    have h4 := hT' x h1
    linarith
  have hanti : AntitoneOn f (Iio (sSup B)) := by
    intro w _ z hz hwz
    obtain ⟨x, hxB, hzx⟩ := exists_lt_of_lt_csSup hne hz
    obtain ⟨y, hxy, hlt⟩ := hxB
    by_cases hc : f y + K < f z
    · exact hB z ⟨y, hzx.le.trans hxy, hc⟩ w hwz
    · have hc := not_lt.mp hc
      have := hB x ⟨y, hxy, hlt⟩ w (hwz.trans hzx.le)
      linarith
  by_cases hbB : sSup B ∈ B
  · refine ⟨sSup B, hK, Iic (sSup B), Or.inr rfl, hpc, hpf, ?_, ?_, ht⟩
    · intro w _ z hz hwz
      rcases eq_or_lt_of_le (show z ≤ sSup B from hz) with hzb | hzb
      · rw [hzb]
        exact hB _ hbB w (hwz.trans hzb.le)
      · exact hanti (show w < sSup B from lt_of_le_of_lt hwz hzb) hzb hwz
    · intro x hx y _ hxy
      by_contra hcon0
      have hcon := not_le.mp hcon0
      exact hx (le_csSup hbdd ⟨y, hxy, hcon⟩)
  · refine ⟨sSup B, hK, Iio (sSup B), Or.inl rfl, hpc, hpf, hanti, ?_, ht⟩
    intro x hx y _ hxy
    by_contra hcon0
    have hcon := not_le.mp hcon0
    have hxB : x ∈ B := ⟨y, hxy, hcon⟩
    have h1 : x ≤ sSup B := le_csSup hbdd hxB
    have h2 : sSup B ≤ x := not_lt.mp hx
    have h3 : x = sSup B := le_antisymm h1 h2
    rw [h3] at hxB
    exact hbB hxB

end PorteusSS

open PorteusSS
open MeasureTheory Filter Topology Set

theorem solution (a K lam : ℝ) (f : ℝ → ℝ) (hf : CaK a K f) (hlam : 0 < lam) :
    CK K (conv f (expDensity lam)) := by
  obtain ⟨hK, I, hI, _, hpf, hanti, hnk, htf⟩ := hf
  have hw := aux_ce_f_weighted hpf hlam
  have hint := aux_ce_F_intOn hlam hw
  have hcont := aux_ce_cont hint
  have hpc : PiecewiseContinuousOn (conv f (expDensity lam)) univ :=
    ⟨∅, by simp, hcont.continuousOn, by simp⟩
  exact ⟨hK, hcont, aux_ce_backward hK (aux_ce_qkc hlam hK hint hI hanti hnk hcont) hpc
    (aux_ce_pfint hlam hpf hcont) (aux_ce_tendsto hlam hint htf)⟩
