-- Prove2me | solution 1 for PostQual.Incumbent.well_defined
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:23:09.104111+00:00
-- url     : https://prove2.me/submissions/9a0bfc9f-3443-4231-bfb2-22878824b3ca

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model


open MeasureTheory Set intervalIntegral

namespace PostQual.Incumbent.Params

variable (P : Params)

section Basic
variable {P}

lemma St_lt (hS : P.Standing) : P.Rlo < P.Rhi := hS.1
lemma St_N (hS : P.Standing) : 2 ≤ P.N := hS.2.1
lemma St_β0 (hS : P.Standing) : 0 < P.β := hS.2.2.1
lemma St_β1 (hS : P.Standing) : P.β < 1 := hS.2.2.2.1
lemma St_K (hS : P.Standing) : 0 < P.K := hS.2.2.2.2.1
lemma St_Δ (hS : P.Standing) : P.Δ < P.Rhi - P.Rlo := hS.2.2.2.2.2.1
lemma St_out (hS : P.Standing) : ∀ t, t ∉ Set.Icc P.Rlo P.Rhi → P.fe t = 0 := hS.2.2.2.2.2.2.1
lemma St_pos (hS : P.Standing) : ∀ t ∈ Set.Icc P.Rlo P.Rhi, 0 < P.fe t := hS.2.2.2.2.2.2.2.1
lemma St_cont (hS : P.Standing) : ContinuousOn P.fe (Set.Icc P.Rlo P.Rhi) :=
  hS.2.2.2.2.2.2.2.2.1
lemma St_int (hS : P.Standing) : ∫ t in P.Rlo..P.Rhi, P.fe t = 1 := hS.2.2.2.2.2.2.2.2.2

lemma Δ_pos (hS : P.Standing) : 0 < P.Δ := div_pos (St_K hS) (St_β0 hS)

lemma fe_nonneg (hS : P.Standing) (t : ℝ) : 0 ≤ P.fe t := by
  by_cases h : t ∈ Set.Icc P.Rlo P.Rhi
  · exact (St_pos hS t h).le
  · rw [St_out hS t h]

lemma fe_integrable (hS : P.Standing) : Integrable P.fe := by
  have h1 : IntegrableOn P.fe (Set.Icc P.Rlo P.Rhi) :=
    (St_cont hS).integrableOn_compact isCompact_Icc
  exact h1.integrable_of_forall_notMem_eq_zero (fun t ht => St_out hS t ht)

lemma fe_ii (hS : P.Standing) (u v : ℝ) : IntervalIntegrable P.fe volume u v :=
  (fe_integrable hS).intervalIntegrable

lemma Fe_Rlo (hS : P.Standing) : P.Fe P.Rlo = 0 := by
  unfold Fe
  rw [integral_Iic_eq_integral_Iio]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  apply St_out hS
  intro h; exact absurd h.1 (not_le.mpr ht)

lemma Fe_eq (hS : P.Standing) (x : ℝ) : P.Fe x = ∫ t in P.Rlo..x, P.fe t := by
  have h := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (f := P.fe) (a := P.Rlo) (b := x)
    (fe_integrable hS).integrableOn (fe_integrable hS).integrableOn
  unfold Fe
  have h0 := Fe_Rlo hS
  unfold Fe at h0
  rw [← h, h0, sub_zero]

lemma Fe_continuous (hS : P.Standing) : Continuous P.Fe := by
  have : P.Fe = fun x => ∫ t in P.Rlo..x, P.fe t := funext (Fe_eq hS)
  rw [this]
  exact intervalIntegral.continuous_primitive (fun u v => fe_ii hS u v) _

lemma Fe_sub (hS : P.Standing) (x y : ℝ) : P.Fe y - P.Fe x = ∫ t in x..y, P.fe t := by
  rw [Fe_eq hS, Fe_eq hS, intervalIntegral.integral_interval_sub_left (fe_ii hS _ _)
    (fe_ii hS _ _)]

lemma Fe_mono (hS : P.Standing) : Monotone P.Fe := by
  intro x y hxy
  have := Fe_sub hS x y
  have h2 : 0 ≤ ∫ t in x..y, P.fe t :=
    intervalIntegral.integral_nonneg hxy (fun t _ => fe_nonneg hS t)
  linarith

lemma Fe_zero (hS : P.Standing) {x : ℝ} (hx : x ≤ P.Rlo) : P.Fe x = 0 := by
  rcases hx.lt_or_eq with hx | hx
  · unfold Fe
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    apply St_out hS
    intro h; exact absurd (lt_of_le_of_lt (mem_Iic.mp ht) hx) (not_lt.mpr h.1)
  · rw [hx]; exact Fe_Rlo hS

lemma Fe_one (hS : P.Standing) {x : ℝ} (hx : P.Rhi ≤ x) : P.Fe x = 1 := by
  rw [Fe_eq hS, ← intervalIntegral.integral_add_adjacent_intervals (fe_ii hS P.Rlo P.Rhi)
    (fe_ii hS P.Rhi x), St_int hS]
  have : ∫ t in P.Rhi..x, P.fe t = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    rw [uIoc_of_le hx] at ht
    apply St_out hS
    intro h; exact absurd ht.1 (not_lt.mpr h.2)
  rw [this, add_zero]

lemma Fe_nonneg (hS : P.Standing) (x : ℝ) : 0 ≤ P.Fe x := by
  have := Fe_mono hS (min_le_left x P.Rlo)
  rwa [Fe_zero hS (min_le_right x P.Rlo)] at this

lemma Fe_le_one (hS : P.Standing) (x : ℝ) : P.Fe x ≤ 1 := by
  have := Fe_mono hS (le_max_left x P.Rhi)
  rwa [Fe_one hS (le_max_right x P.Rhi)] at this

lemma Fe_lt_of_lt (hS : P.Standing) {x y : ℝ} (hxy : x < y) (hx : P.Rlo ≤ x) (hy : y ≤ P.Rhi) :
    P.Fe x < P.Fe y := by
  have h := Fe_sub hS x y
  have : 0 < ∫ t in x..y, P.fe t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (fe_ii hS x y) _ hxy
    intro t ht
    exact St_pos hS t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  linarith

lemma Fe_pos (hS : P.Standing) {x : ℝ} (hx : P.Rlo < x) : 0 < P.Fe x := by
  have h1 : P.Fe P.Rlo < P.Fe (min x P.Rhi) :=
    Fe_lt_of_lt hS (lt_min hx (St_lt hS)) le_rfl (min_le_right _ _)
  rw [Fe_Rlo hS] at h1
  exact lt_of_lt_of_le h1 (Fe_mono hS (min_le_left _ _))

lemma fe_contAt (hS : P.Standing) {x : ℝ} (h1 : x ≠ P.Rlo) (h2 : x ≠ P.Rhi) :
    ContinuousAt P.fe x := by
  rcases lt_or_gt_of_ne h1 with h | h
  · apply (continuousAt_const (y := (0:ℝ))).congr
    filter_upwards [Iio_mem_nhds h] with t ht
    rw [St_out hS t (fun h' => absurd h'.1 (not_le.mpr ht))]
  rcases lt_or_gt_of_ne h2 with h' | h'
  · exact (St_cont hS).continuousAt (Icc_mem_nhds h h')
  · apply (continuousAt_const (y := (0:ℝ))).congr
    filter_upwards [Ioi_mem_nhds h'] with t ht
    rw [St_out hS t (fun h'' => absurd h''.2 (not_le.mpr ht))]

lemma Fe_hasDerivAt (hS : P.Standing) {x : ℝ} (h1 : x ≠ P.Rlo) (h2 : x ≠ P.Rhi) :
    HasDerivAt P.Fe (P.fe x) x := by
  have : P.Fe = fun x => ∫ t in P.Rlo..x, P.fe t := funext (Fe_eq hS)
  rw [this]
  exact intervalIntegral.integral_hasDerivAt_right (fe_ii hS _ _)
    (fe_integrable hS).aestronglyMeasurable.stronglyMeasurableAtFilter (fe_contAt hS h1 h2)

lemma fes_integrable (hS : P.Standing) : Integrable (fun z => P.fe (z - P.Δ)) :=
  (fe_integrable hS).comp_sub_right P.Δ

lemma fes_ii (hS : P.Standing) (u v : ℝ) : IntervalIntegrable (fun z => P.fe (z - P.Δ)) volume u v :=
  (fes_integrable hS).intervalIntegrable

end Basic

/-- `gt m z = m Fe(z-Δ)^{m-1} fe(z-Δ)`, the unnormalised density. -/
noncomputable def gt (m : ℕ) (z : ℝ) : ℝ := m * P.Fe (z - P.Δ) ^ (m - 1) * P.fe (z - P.Δ)

/-- `Aux m x0 b = Fe(b-Δ)^m (1-β)^m (b - x0)`. -/
noncomputable def Aux (m : ℕ) (x0 b : ℝ) : ℝ := P.Fe (b - P.Δ) ^ m * (1 - P.β) ^ m * (b - x0)

/-- derivative of `Aux`. -/
noncomputable def Ad (m : ℕ) (x0 z : ℝ) : ℝ :=
  (m * P.Fe (z - P.Δ) ^ (m - 1) * P.fe (z - P.Δ)) * (1 - P.β) ^ m * (z - x0) +
    P.Fe (z - P.Δ) ^ m * (1 - P.β) ^ m

/-- the kernel: derivative of `Aux - ∫ W gt`. -/
noncomputable def Dk (m : ℕ) (W : ℝ → ℝ) (x0 z : ℝ) : ℝ := P.Ad m x0 z - W z * P.gt m z

/-- unnormalised zeta. -/
noncomputable def zt (m : ℕ) (z x0 : ℝ) : ℝ :=
  P.Fe (z - P.Δ) ^ (m - 1) * (1 - P.β) ^ m *
    (-(m * P.β / (1 - P.β)) * (z - x0) * P.fe (z - P.Δ) + P.Fe (z - P.Δ))

section Calc
variable {P}

lemma PiAux_eq (m : ℕ) (hm : 1 ≤ m) (W : ℝ → ℝ) (b x0 p : ℝ) :
    P.PiAux m W b x0 p = ((∫ z in b..p, W z * P.gt m z) + P.Aux m x0 b) / P.Fe (p - P.Δ) ^ m := by
  unfold PiAux g G gt Aux
  have : (fun z => W z * (↑m * P.Fe (z - P.Δ) ^ (m - 1) * P.fe (z - P.Δ) / P.Fe (p - P.Δ) ^ m)) =
      fun z => (W z * (↑m * P.Fe (z - P.Δ) ^ (m - 1) * P.fe (z - P.Δ))) / P.Fe (p - P.Δ) ^ m := by
    funext z; ring
  rw [this, intervalIntegral.integral_div, div_pow, add_div]
  ring

lemma Pi_eq (m : ℕ) (hm : 1 ≤ m) (b x0 p : ℝ) :
    P.Pi m b x0 p = ((∫ z in b..p, P.V (m - 1) x0 z * P.gt m z) + P.Aux m x0 b) /
      P.Fe (p - P.Δ) ^ m := PiAux_eq m hm _ b x0 p

lemma gt_nonneg (hS : P.Standing) (m : ℕ) (z : ℝ) : 0 ≤ P.gt m z := by
  unfold gt
  have := fe_nonneg hS (z - P.Δ)
  have := Fe_nonneg hS (z - P.Δ)
  positivity

lemma ftc_shift (hS : P.Standing) (Φ Φ' : ℝ → ℝ) {u v : ℝ} (huv : u ≤ v)
    (hc : Continuous Φ)
    (hd : ∀ z, z - P.Δ ≠ P.Rlo → z - P.Δ ≠ P.Rhi → HasDerivAt Φ (Φ' z) z)
    (hi : IntervalIntegrable Φ' volume u v) : ∫ z in u..v, Φ' z = Φ v - Φ u := by
  apply integral_eq_of_hasDerivAt_off_countable_of_le Φ Φ' huv
    (s := {P.Rlo + P.Δ, P.Rhi + P.Δ}) (Set.toFinite _).countable hc.continuousOn
  · intro z hz
    apply hd
    · intro h; apply hz.2; left; linarith
    · intro h; apply hz.2; right; simp; linarith
  · exact hi

lemma Fes_continuous (hS : P.Standing) : Continuous fun z => P.Fe (z - P.Δ) :=
  (Fe_continuous hS).comp (continuous_id.sub continuous_const)

lemma Fes_hasDerivAt (hS : P.Standing) {z : ℝ} (h1 : z - P.Δ ≠ P.Rlo) (h2 : z - P.Δ ≠ P.Rhi) :
    HasDerivAt (fun z => P.Fe (z - P.Δ)) (P.fe (z - P.Δ)) z := by
  have := (Fe_hasDerivAt hS h1 h2).comp z ((hasDerivAt_id z).sub_const P.Δ)
  rw [mul_one] at this
  exact this

lemma gt_ii (hS : P.Standing) (m : ℕ) (u v : ℝ) : IntervalIntegrable (P.gt m) volume u v := by
  have h := (fes_ii hS u v).continuousOn_mul (g := fun z => (m:ℝ) * P.Fe (z - P.Δ) ^ (m - 1))
    (by
      apply Continuous.continuousOn
      exact continuous_const.mul ((Fes_continuous hS).pow _))
  unfold gt
  exact h

lemma int_gt (hS : P.Standing) (m : ℕ) (hm : 1 ≤ m) {u v : ℝ} (huv : u ≤ v) :
    ∫ z in u..v, P.gt m z = P.Fe (v - P.Δ) ^ m - P.Fe (u - P.Δ) ^ m := by
  apply ftc_shift hS (fun z => P.Fe (z - P.Δ) ^ m) (P.gt m) huv
    ((Fes_continuous hS).pow m)
  · intro z h1 h2
    have := (Fes_hasDerivAt hS h1 h2).fun_pow m
    unfold gt
    exact this
  · exact gt_ii hS m u v

lemma Ad_ii (hS : P.Standing) (m : ℕ) (x0 u v : ℝ) :
    IntervalIntegrable (P.Ad m x0) volume u v := by
  unfold Ad
  apply IntervalIntegrable.add
  · have h := (gt_ii hS m u v).mul_continuousOn (g := fun z => (1 - P.β) ^ m * (z - x0))
      (Continuous.continuousOn (by fun_prop))
    refine h.congr ?_
    intro z _
    simp only [gt]; ring
  · apply Continuous.intervalIntegrable
    exact ((Fes_continuous hS).pow m).mul continuous_const

lemma int_Ad (hS : P.Standing) (m : ℕ) (x0 : ℝ) {u v : ℝ} (huv : u ≤ v) :
    ∫ z in u..v, P.Ad m x0 z = P.Aux m x0 v - P.Aux m x0 u := by
  apply ftc_shift hS (P.Aux m x0) (P.Ad m x0) huv
  · unfold Aux
    exact (((Fes_continuous hS).pow m).mul continuous_const).mul (continuous_id.sub continuous_const)
  · intro z h1 h2
    have h3 : HasDerivAt (fun y => y - x0) 1 z := (hasDerivAt_id' z).sub_const x0
    have := (((Fes_hasDerivAt hS h1 h2).fun_pow m).mul_const ((1 - P.β) ^ m)).fun_mul h3
    exact this.congr_deriv (by unfold Ad; ring)
  · exact Ad_ii hS m x0 u v

end Calc

end PostQual.Incumbent.Params


open MeasureTheory Set intervalIntegral

namespace PostQual.Incumbent.Params

variable {P : Params}

lemma Fes_pos (hS : P.Standing) {z : ℝ} (hz : P.Rlo + P.Δ < z) : 0 < P.Fe (z - P.Δ) :=
  Fe_pos hS (by linarith)

lemma Fes_zero (hS : P.Standing) {z : ℝ} (hz : z ≤ P.Rlo + P.Δ) : P.Fe (z - P.Δ) = 0 :=
  Fe_zero hS (by linarith)

lemma Fes_one (hS : P.Standing) {z : ℝ} (hz : P.Rhi + P.Δ ≤ z) : P.Fe (z - P.Δ) = 1 :=
  Fe_one hS (by linarith)

lemma fes_zero (hS : P.Standing) {z : ℝ} (hz : P.Rhi + P.Δ < z) : P.fe (z - P.Δ) = 0 :=
  St_out hS _ (fun h => by linarith [h.2])

lemma fes_pos (hS : P.Standing) {z : ℝ} (h1 : P.Rlo + P.Δ ≤ z) (h2 : z ≤ P.Rhi + P.Δ) :
    0 < P.fe (z - P.Δ) := St_pos hS _ ⟨by linarith, by linarith⟩

lemma gt_zero_of_gt (hS : P.Standing) (m : ℕ) {z : ℝ} (hz : P.Rhi + P.Δ < z) : P.gt m z = 0 := by
  unfold gt; rw [fes_zero hS hz]; ring

lemma lo_ge_a (x0 : ℝ) : P.Rlo + P.Δ ≤ P.lo x0 := le_max_left _ _
lemma lo_ge_x0 (x0 : ℝ) : x0 ≤ P.lo x0 := le_max_right _ _

lemma ii_mul_bdd {W h : ℝ → ℝ} {u v C : ℝ} (hW : IntervalIntegrable W volume u v)
    (hb : ∀ z ∈ uIcc u v, |W z| ≤ C) (hh : IntervalIntegrable h volume u v) :
    IntervalIntegrable (fun z => W z * h z) volume u v := by
  rw [intervalIntegrable_iff] at hW hh ⊢
  refine Integrable.bdd_mul (c := C) hh hW.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall ?_)
  intro z hz
  rw [Real.norm_eq_abs]
  exact hb z (uIoc_subset_uIcc hz)

/-- regularity of the continuation value `V k x0` used throughout. -/
def Good (P : Params) (k : ℕ) (x0 : ℝ) : Prop :=
  MonotoneOn (P.V k x0) (Ici (P.lo x0)) ∧
    ∀ z, P.lo x0 ≤ z → P.Rlo + P.Δ < z → (1 - P.β) ^ k * (z - x0) ≤ P.V k x0 z

lemma Good.ii (hS : P.Standing) {k : ℕ} {x0 : ℝ} (hG : P.Good k x0) (m : ℕ) {u v : ℝ}
    (hu : P.lo x0 ≤ u) (hv : P.lo x0 ≤ v) :
    IntervalIntegrable (fun z => P.V k x0 z * P.gt m z) volume u v := by
  have hsub : uIcc u v ⊆ Ici (P.lo x0) := by
    intro z hz; exact le_trans (le_min hu hv) hz.1
  have hmono : MonotoneOn (P.V k x0) (uIcc u v) := hG.1.mono hsub
  apply ii_mul_bdd hmono.intervalIntegrable (C := |P.V k x0 u| + |P.V k x0 v|) _ (gt_ii hS m u v)
  intro z hz
  have h1 : P.V k x0 (min u v) ≤ P.V k x0 z := hmono (by simp [uIcc]) hz hz.1
  have h2 : P.V k x0 z ≤ P.V k x0 (max u v) := hmono hz (by simp [uIcc]) hz.2
  rcases le_total u v with h | h
  · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
    rw [abs_le]; constructor <;> linarith [abs_nonneg (P.V k x0 u), abs_nonneg (P.V k x0 v),
      neg_abs_le (P.V k x0 u), le_abs_self (P.V k x0 v)]
  · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
    rw [abs_le]; constructor <;> linarith [abs_nonneg (P.V k x0 u), abs_nonneg (P.V k x0 v),
      neg_abs_le (P.V k x0 v), le_abs_self (P.V k x0 u)]

/-- `T m x0 b = Aux m x0 b - ∫_{ℓ}^{b} V^{m-1} gt_m`. -/
noncomputable def T (P : Params) (m : ℕ) (x0 b : ℝ) : ℝ :=
  P.Aux m x0 b - ∫ z in P.lo x0..b, P.V (m - 1) x0 z * P.gt m z

lemma V_succ (m : ℕ) (hm : 1 ≤ m) (x0 p : ℝ) :
    P.V m x0 p = sSup ((fun b => P.Pi m b x0 p) '' Icc (P.lo x0) p) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rfl

lemma Pi_T (hS : P.Standing) {m : ℕ} (hm : 1 ≤ m) {x0 : ℝ} (hG : P.Good (m - 1) x0)
    {b p : ℝ} (hb : P.lo x0 ≤ b) (hp : P.lo x0 ≤ p) :
    P.Pi m b x0 p = ((∫ z in P.lo x0..p, P.V (m - 1) x0 z * P.gt m z) + P.T m x0 b) /
      P.Fe (p - P.Δ) ^ m := by
  rw [Pi_eq m hm, T]
  congr 1
  rw [← intervalIntegral.integral_interval_sub_left (hG.ii hS m le_rfl hp) (hG.ii hS m le_rfl hb)]
  ring

lemma Dk_ii (hS : P.Standing) {m : ℕ} {x0 : ℝ} (hG : P.Good (m - 1) x0) {u v : ℝ}
    (hu : P.lo x0 ≤ u) (hv : P.lo x0 ≤ v) :
    IntervalIntegrable (P.Dk m (P.V (m - 1) x0) x0) volume u v :=
  (Ad_ii hS m x0 u v).sub (hG.ii hS m hu hv)

lemma T_sub (hS : P.Standing) {m : ℕ} {x0 : ℝ} (hG : P.Good (m - 1) x0) {u v : ℝ}
    (hu : P.lo x0 ≤ u) (huv : u ≤ v) :
    P.T m x0 v - P.T m x0 u = ∫ z in u..v, P.Dk m (P.V (m - 1) x0) x0 z := by
  have hv : P.lo x0 ≤ v := le_trans hu huv
  unfold Dk
  rw [intervalIntegral.integral_sub (Ad_ii hS m x0 u v) (hG.ii hS m hu hv), int_Ad hS m x0 huv]
  unfold T
  rw [← intervalIntegral.integral_interval_sub_left (hG.ii hS m le_rfl hv) (hG.ii hS m le_rfl hu)]
  ring

lemma T_cont (hS : P.Standing) {m : ℕ} {x0 : ℝ} (hG : P.Good (m - 1) x0) (R : ℝ) :
    ContinuousOn (P.T m x0) (Icc (P.lo x0) R) := by
  rcases le_or_gt (P.lo x0) R with hR | hR
  · have h1 : ContinuousOn (fun b => ∫ z in P.lo x0..b, P.V (m - 1) x0 z * P.gt m z)
        (uIcc (P.lo x0) R) :=
      intervalIntegral.continuousOn_primitive_interval' (hG.ii hS m le_rfl hR) left_mem_uIcc
    rw [uIcc_of_le hR] at h1
    have h2 : Continuous (P.Aux m x0) := by
      unfold Aux
      exact (((Fes_continuous hS).pow m).mul continuous_const).mul
        (continuous_id.sub continuous_const)
    exact h2.continuousOn.sub h1
  · rw [Icc_eq_empty (not_le.mpr hR)]; exact continuousOn_empty _

lemma T_max (hS : P.Standing) {m : ℕ} {x0 : ℝ} (hG : P.Good (m - 1) x0) {p : ℝ}
    (hp : P.lo x0 ≤ p) : ∃ bs ∈ Icc (P.lo x0) p, ∀ b ∈ Icc (P.lo x0) p, P.T m x0 b ≤ P.T m x0 bs := by
  obtain ⟨bs, hbs, h⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hp) (T_cont hS hG p)
  exact ⟨bs, hbs, fun b hb => h hb⟩

lemma V_of_max (hS : P.Standing) {m : ℕ} (hm : 1 ≤ m) {x0 : ℝ} (hG : P.Good (m - 1) x0) {p bs : ℝ}
    (hbs : bs ∈ Icc (P.lo x0) p) (hmax : ∀ b ∈ Icc (P.lo x0) p, P.T m x0 b ≤ P.T m x0 bs) :
    P.V m x0 p = P.Pi m bs x0 p ∧ ∀ b ∈ Icc (P.lo x0) p, P.Pi m b x0 p ≤ P.Pi m bs x0 p := by
  have hp : P.lo x0 ≤ p := le_trans hbs.1 hbs.2
  have hle : ∀ b ∈ Icc (P.lo x0) p, P.Pi m b x0 p ≤ P.Pi m bs x0 p := by
    intro b hb
    rw [Pi_T hS hm hG hb.1 hp, Pi_T hS hm hG hbs.1 hp]
    apply div_le_div_of_nonneg_right _ (pow_nonneg (Fe_nonneg hS _) _)
    linarith [hmax b hb]
  refine ⟨?_, hle⟩
  rw [V_succ m hm]
  apply IsGreatest.csSup_eq
  exact ⟨⟨bs, hbs, rfl⟩, by rintro _ ⟨b, hb, rfl⟩; exact hle b hb⟩

lemma Pi_le_V (hS : P.Standing) {m : ℕ} (hm : 1 ≤ m) {x0 : ℝ} (hG : P.Good (m - 1) x0) {p b : ℝ}
    (hb : b ∈ Icc (P.lo x0) p) : P.Pi m b x0 p ≤ P.V m x0 p := by
  obtain ⟨bs, hbs, hmax⟩ := T_max hS hG (le_trans hb.1 hb.2)
  obtain ⟨h1, h2⟩ := V_of_max hS hm hG hbs hmax
  rw [h1]; exact h2 b hb

lemma Pi_diag (hS : P.Standing) {m : ℕ} (hm : 1 ≤ m) {x0 z : ℝ} (hz : P.Rlo + P.Δ < z) :
    P.Pi m z x0 z = (1 - P.β) ^ m * (z - x0) := by
  rw [Pi_eq m hm, intervalIntegral.integral_same, zero_add, Aux]
  have : P.Fe (z - P.Δ) ^ m ≠ 0 := pow_ne_zero _ (Fes_pos hS hz).ne'
  field_simp

lemma Pi_zero (hS : P.Standing) {m : ℕ} (hm : 1 ≤ m) {x0 b p : ℝ} (hp : p ≤ P.Rlo + P.Δ) :
    P.Pi m b x0 p = 0 := by
  rw [Pi_eq m hm, Fes_zero hS hp, zero_pow (by omega), div_zero]

lemma Good_zero (x0 : ℝ) : P.Good 0 x0 := by
  refine ⟨?_, ?_⟩
  · intro x _ y _ hxy; show x - x0 ≤ y - x0; linarith
  · intro z _ _; show (1 - P.β) ^ 0 * (z - x0) ≤ z - x0; simp

/-- Monotonicity of `Π^m(b; ·)` in the current price (proof of Lemma EC.1 (a)). -/
lemma Pi_mono_p (hS : P.Standing) {m : ℕ} (hm : 1 ≤ m) {x0 : ℝ} (hG : P.Good (m - 1) x0)
    {b p p' : ℝ} (hb : P.lo x0 ≤ b) (hbp : b ≤ p) (hpp : p ≤ p') (ha : P.Rlo + P.Δ < p) :
    P.Pi m b x0 p ≤ P.Pi m b x0 p' ∧ P.Pi m b x0 p ≤ P.V (m - 1) x0 p := by
  have hβ1 := St_β1 hS
  have hβ0 := St_β0 hS
  set W := P.V (m - 1) x0 with hWdef
  have hp : P.lo x0 ≤ p := le_trans hb hbp
  have hp' : P.lo x0 ≤ p' := le_trans hp hpp
  set C := P.Fe (p - P.Δ) ^ m with hC
  set C' := P.Fe (p' - P.Δ) ^ m with hC'
  have hCpos : 0 < C := pow_pos (Fes_pos hS ha) m
  have hCC : C ≤ C' := pow_le_pow_left₀ (Fe_nonneg hS _) (Fe_mono hS (by linarith)) m
  set X := (∫ z in b..p, W z * P.gt m z) + P.Aux m x0 b with hX
  have hPi : P.Pi m b x0 p = X / C := Pi_eq m hm b x0 p
  have hPi' : P.Pi m b x0 p' = (X + ∫ z in p..p', W z * P.gt m z) / C' := by
    rw [Pi_eq m hm, hX, ← intervalIntegral.integral_add_adjacent_intervals
      (hG.ii hS m hb hp) (hG.ii hS m hp hp')]
    ring
  -- `X ≤ W p * C`
  have hWp : (1 - P.β) ^ m * (b - x0) ≤ W p := by
    have h1 := hG.2 p hp ha
    have h2 : (1 - P.β) ^ m ≤ (1 - P.β) ^ (m - 1) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
    have h3 : 0 ≤ b - x0 := by linarith [lo_ge_x0 (P := P) x0]
    calc (1 - P.β) ^ m * (b - x0) ≤ (1 - P.β) ^ (m - 1) * (b - x0) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ ≤ (1 - P.β) ^ (m - 1) * (p - x0) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) _)
      _ ≤ W p := h1
  have hI1 : ∫ z in b..p, W z * P.gt m z ≤ ∫ z in b..p, W p * P.gt m z := by
    apply intervalIntegral.integral_mono_on hbp (hG.ii hS m hb hp)
      ((gt_ii hS m b p).const_mul (W p))
    intro z hz
    exact mul_le_mul_of_nonneg_right (hG.1 (le_trans hb hz.1) hp hz.2) (gt_nonneg hS m z)
  rw [intervalIntegral.integral_const_mul, int_gt hS m hm hbp] at hI1
  have hXle : X ≤ W p * C := by
    have : P.Aux m x0 b ≤ P.Fe (b - P.Δ) ^ m * W p := by
      unfold Aux
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hWp (pow_nonneg (Fe_nonneg hS _) _)
    rw [hX]; nlinarith
  have hπ : X / C ≤ W p := by rw [div_le_iff₀ hCpos]; linarith
  refine ⟨?_, by rw [hPi]; exact hπ⟩
  have hI2 : ∫ z in p..p', (X / C) * P.gt m z ≤ ∫ z in p..p', W z * P.gt m z := by
    apply intervalIntegral.integral_mono_on hpp ((gt_ii hS m p p').const_mul _)
      (hG.ii hS m hp hp')
    intro z hz
    exact mul_le_mul_of_nonneg_right (le_trans hπ (hG.1 hp (le_trans hp hz.1) hz.1))
      (gt_nonneg hS m z)
  rw [intervalIntegral.integral_const_mul, int_gt hS m hm hpp] at hI2
  have hC'pos : 0 < C' := lt_of_lt_of_le hCpos hCC
  rw [hPi, hPi', le_div_iff₀ hC'pos]
  have : X / C * C = X := by field_simp
  nlinarith

lemma Good_succ (hS : P.Standing) {k : ℕ} {x0 : ℝ} (hG : P.Good k x0) : P.Good (k + 1) x0 := by
  have hk : 1 ≤ k + 1 := by omega
  have hG' : P.Good (k + 1 - 1) x0 := by simpa using hG
  have hlow : ∀ z, P.lo x0 ≤ z → P.Rlo + P.Δ < z →
      (1 - P.β) ^ (k + 1) * (z - x0) ≤ P.V (k + 1) x0 z := by
    intro z hz ha
    rw [← Pi_diag hS hk ha]
    exact Pi_le_V hS hk hG' ⟨hz, le_rfl⟩
  refine ⟨?_, hlow⟩
  intro p hp p' hp' hpp
  rcases le_or_gt p (P.Rlo + P.Δ) with ha | ha
  · -- price at the left end: value `0`
    have hV0 : P.V (k + 1) x0 p = 0 := by
      obtain ⟨bs, hbs, hmax⟩ := T_max hS hG' (show P.lo x0 ≤ p from hp)
      rw [(V_of_max hS hk hG' hbs hmax).1, Pi_zero hS hk ha]
    rw [hV0]
    rcases le_or_gt p' (P.Rlo + P.Δ) with ha' | ha'
    · have : p' = p := le_antisymm (le_trans ha' (le_trans (lo_ge_a x0) hp)) hpp
      rw [this, hV0]
    · have := hlow p' hp' ha'
      have h1 : 0 ≤ (1 - P.β) ^ (k + 1) * (p' - x0) :=
        mul_nonneg (pow_nonneg (by linarith [St_β1 hS]) _)
          (by linarith [lo_ge_x0 (P := P) x0, show P.lo x0 ≤ p' from hp'])
      linarith
  · obtain ⟨bs, hbs, hmax⟩ := T_max hS hG' (show P.lo x0 ≤ p from hp)
    rw [(V_of_max hS hk hG' hbs hmax).1]
    calc P.Pi (k + 1) bs x0 p ≤ P.Pi (k + 1) bs x0 p' :=
          (Pi_mono_p hS hk hG' hbs.1 hbs.2 hpp ha).1
      _ ≤ P.V (k + 1) x0 p' := Pi_le_V hS hk hG' ⟨hbs.1, le_trans hbs.2 hpp⟩

lemma Good_all (hS : P.Standing) (k : ℕ) (x0 : ℝ) : P.Good k x0 := by
  induction k with
  | zero => exact Good_zero x0
  | succ k ih => exact Good_succ hS ih

end PostQual.Incumbent.Params


open MeasureTheory Set intervalIntegral

namespace PostQual.Incumbent.Params

variable {P : Params}

/-- Stochastic-dominance step of Lemma EC.1 (b): the `(j+1)`-th order statistic dominates the
`j`-th one, so a nondecreasing payoff `ψ` has a larger expectation under it. -/
lemma sd_step (hS : P.Standing) {j : ℕ} (hj : 1 ≤ j) {ψ : ℝ → ℝ} {b p ψ0 : ℝ}
    (hbp : b ≤ p) (ha : P.Rlo + P.Δ < p) (hψ : MonotoneOn ψ (Icc b p))
    (hψ0 : 0 < P.Fe (b - P.Δ) → ∀ z ∈ Icc b p, ψ0 ≤ ψ z)
    (hi1 : IntervalIntegrable (fun z => ψ z * P.gt j z) volume b p)
    (hi2 : IntervalIntegrable (fun z => ψ z * P.gt (j + 1) z) volume b p) :
    ((∫ z in b..p, ψ z * P.gt j z) + P.Fe (b - P.Δ) ^ j * ψ0) / P.Fe (p - P.Δ) ^ j ≤
      ((∫ z in b..p, ψ z * P.gt (j + 1) z) + P.Fe (b - P.Δ) ^ (j + 1) * ψ0) /
        P.Fe (p - P.Δ) ^ (j + 1) := by
  set C := P.Fe (p - P.Δ) with hC
  set Fb := P.Fe (b - P.Δ) with hFb
  have hCpos : 0 < C := Fes_pos hS ha
  have hFb0 : 0 ≤ Fb := Fe_nonneg hS _
  have hFbC : Fb ≤ C := Fe_mono hS (by linarith)
  -- the weight difference
  set w : ℝ → ℝ := fun z => P.gt (j + 1) z / C ^ (j + 1) - P.gt j z / C ^ j with hw
  set s : ℝ → ℝ := fun z => (j + 1) * P.Fe (z - P.Δ) - j * C with hs
  have hw_eq : ∀ z, w z = P.Fe (z - P.Δ) ^ (j - 1) * P.fe (z - P.Δ) / C ^ (j + 1) * s z := by
    intro z
    simp only [hw, hs, gt]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hC0 : C ≠ 0 := hCpos.ne'
    simp only [Nat.add_sub_cancel]
    field_simp
    push_cast
    ring
  have hcoef : ∀ z, 0 ≤ P.Fe (z - P.Δ) ^ (j - 1) * P.fe (z - P.Δ) / C ^ (j + 1) := by
    intro z
    have := Fe_nonneg hS (z - P.Δ)
    have := fe_nonneg hS (z - P.Δ)
    positivity
  have hs_mono : Monotone s := by
    intro x y hxy
    simp only [hs]
    have := Fe_mono hS (show x - P.Δ ≤ y - P.Δ by linarith)
    have : (0:ℝ) ≤ (j:ℝ) + 1 := by positivity
    nlinarith
  -- threshold point
  set S := {z | z ∈ Icc b p ∧ 0 ≤ s z} with hSdef
  have hpS : p ∈ S := ⟨⟨hbp, le_rfl⟩, by simp only [hs]; rw [← hC]; linarith⟩
  have hSne : S.Nonempty := ⟨p, hpS⟩
  have hSbdd : BddBelow S := ⟨b, fun z hz => hz.1.1⟩
  set zb := sInf S with hzb
  have hzb1 : b ≤ zb := le_csInf hSne (fun z hz => hz.1.1)
  have hzb2 : zb ≤ p := csInf_le hSbdd hpS
  have hzbI : zb ∈ Icc b p := ⟨hzb1, hzb2⟩
  have hkey : ∀ z ∈ Icc b p, 0 ≤ (ψ z - ψ zb) * s z := by
    intro z hz
    rcases lt_trichotomy z zb with h | h | h
    · have hsz : s z < 0 := by
        by_contra hc
        push Not at hc
        exact absurd (csInf_le hSbdd ⟨hz, hc⟩) (not_le.mpr h)
      have : ψ z ≤ ψ zb := hψ hz hzbI h.le
      nlinarith
    · rw [h]; simp
    · obtain ⟨z', hz'S, hz'⟩ := exists_lt_of_csInf_lt hSne h
      have : 0 ≤ s z := le_trans hz'S.2 (hs_mono hz'.le)
      have : ψ zb ≤ ψ z := hψ hzbI hz h.le
      nlinarith
  -- integrals
  have hgi : ∀ k, IntervalIntegrable (P.gt k) volume b p := fun k => gt_ii hS k b p
  have hwi : IntervalIntegrable w volume b p :=
    ((hgi (j + 1)).div_const _).sub ((hgi j).div_const _)
  have hψwi : IntervalIntegrable (fun z => ψ z * w z) volume b p := by
    have : (fun z => ψ z * w z) =
        fun z => (ψ z * P.gt (j + 1) z) / C ^ (j + 1) - (ψ z * P.gt j z) / C ^ j := by
      funext z; simp only [hw]; ring
    rw [this]; exact (hi2.div_const _).sub (hi1.div_const _)
  have hint_w : ∫ z in b..p, w z = Fb ^ j / C ^ j - Fb ^ (j + 1) / C ^ (j + 1) := by
    simp only [hw]
    rw [intervalIntegral.integral_sub ((hgi _).div_const _) ((hgi _).div_const _),
      intervalIntegral.integral_div, intervalIntegral.integral_div, int_gt hS _ (by omega) hbp,
      int_gt hS _ hj hbp]
    have hC0 : C ≠ 0 := hCpos.ne'
    field_simp
    ring
  have hmono_int : ∫ z in b..p, ψ zb * w z ≤ ∫ z in b..p, ψ z * w z := by
    apply intervalIntegral.integral_mono_on hbp (hwi.const_mul _) hψwi
    intro z hz
    have := hkey z hz
    rw [hw_eq z]
    have := hcoef z
    nlinarith
  rw [intervalIntegral.integral_const_mul, hint_w] at hmono_int
  have hsplit : ((∫ z in b..p, ψ z * P.gt (j + 1) z) + Fb ^ (j + 1) * ψ0) / C ^ (j + 1) -
      ((∫ z in b..p, ψ z * P.gt j z) + Fb ^ j * ψ0) / C ^ j =
      (∫ z in b..p, ψ z * w z) - (Fb ^ j / C ^ j - Fb ^ (j + 1) / C ^ (j + 1)) * ψ0 := by
    have : ∫ z in b..p, ψ z * w z = (∫ z in b..p, ψ z * P.gt (j + 1) z) / C ^ (j + 1) -
        (∫ z in b..p, ψ z * P.gt j z) / C ^ j := by
      rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div,
        ← intervalIntegral.integral_sub (hi2.div_const _) (hi1.div_const _)]
      congr 1; funext z; simp only [hw]; ring
    rw [this]; ring
  have hfac : 0 ≤ Fb ^ j / C ^ j - Fb ^ (j + 1) / C ^ (j + 1) := by
    have hu0 : 0 ≤ Fb / C := div_nonneg hFb0 hCpos.le
    have hu1 : Fb / C ≤ 1 := (div_le_one hCpos).mpr hFbC
    have : Fb ^ j / C ^ j - Fb ^ (j + 1) / C ^ (j + 1) = (Fb / C) ^ j * (1 - Fb / C) := by
      have hC0 := hCpos.ne'
      rw [div_pow, pow_succ Fb j, pow_succ C j]; field_simp
    rw [this]; exact mul_nonneg (pow_nonneg hu0 _) (by linarith)
  have hfinal : 0 ≤ (Fb ^ j / C ^ j - Fb ^ (j + 1) / C ^ (j + 1)) * (ψ zb - ψ0) := by
    rcases hFb0.lt_or_eq with hpos | hzero
    · exact mul_nonneg hfac (by linarith [hψ0 hpos zb hzbI])
    · rw [← hzero, zero_pow (by omega), zero_pow (by omega)]; simp
  have := hsplit
  nlinarith

/-- Lemma EC.1 (b): `V^{k+1}_0(x0,p) ≥ (1−β) V^k_0(x0,p)`. -/
lemma V_succ_ge (hS : P.Standing) (x0 : ℝ) (k : ℕ) :
    ∀ p, P.lo x0 < p → (1 - P.β) * P.V k x0 p ≤ P.V (k + 1) x0 p := by
  have hβ1 := St_β1 hS
  induction k with
  | zero =>
    intro p hp
    have ha : P.Rlo + P.Δ < p := lt_of_le_of_lt (lo_ge_a x0) hp
    have h := Pi_le_V hS (m := 1) le_rfl (Good_all hS _ x0) (show p ∈ Icc (P.lo x0) p from
      ⟨hp.le, le_rfl⟩)
    rw [Pi_diag hS le_rfl ha] at h
    show (1 - P.β) * (p - x0) ≤ _
    simpa using h
  | succ k ih =>
    intro p hp
    have ha : P.Rlo + P.Δ < p := lt_of_le_of_lt (lo_ge_a x0) hp
    set m := k + 1 with hm
    have hm1 : 1 ≤ m := by omega
    have hG : P.Good (m - 1) x0 := Good_all hS _ x0
    have hG' : P.Good (m + 1 - 1) x0 := Good_all hS _ x0
    obtain ⟨bs, hbs, hmax⟩ := T_max hS hG hp.le
    rw [(V_of_max hS hm1 hG hbs hmax).1]
    refine le_trans ?_ (Pi_le_V hS (by omega) hG' hbs)
    -- `Π^{m+1}(b) ≥ (1-β) Π^m(b)`
    have hb := hbs.1
    have hbp := hbs.2
    rw [Pi_eq m hm1, Pi_eq (m + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    have hWk : ∀ z ∈ Ioo bs p, (1 - P.β) * P.V k x0 z ≤ P.V m x0 z :=
      fun z hz => ih z (lt_of_le_of_lt hb hz.1)
    have hGk : P.Good k x0 := Good_all hS _ x0
    have hGm : P.Good m x0 := Good_all hS _ x0
    have hI : ∫ z in bs..p, ((1 - P.β) * P.V k x0 z) * P.gt (m + 1) z ≤
        ∫ z in bs..p, P.V m x0 z * P.gt (m + 1) z := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hbp
      · have := (hGk.ii hS (m + 1) hb hp.le).const_mul (1 - P.β)
        refine this.congr (fun z _ => ?_); ring
      · exact hGm.ii hS (m + 1) hb hp.le
      · intro z hz
        exact mul_le_mul_of_nonneg_right (hWk z hz) (gt_nonneg hS _ z)
    have hsd := sd_step hS hm1 (ψ := P.V k x0) (ψ0 := (1 - P.β) ^ m * (bs - x0)) hbp ha
      (hGk.1.mono (fun z hz => le_trans hb hz.1))
      (by
        intro hF z hz
        have hza : P.Rlo + P.Δ < z := by
          by_contra hc; push Not at hc
          have := Fes_zero hS (le_trans hz.1 hc); rw [this] at hF; exact lt_irrefl _ hF
        have h1 := hGk.2 z (le_trans hb hz.1) hza
        have h2 : (1 - P.β) ^ m ≤ (1 - P.β) ^ k :=
          pow_le_pow_of_le_one (by linarith [St_β0 hS]) (by linarith [St_β0 hS]) (by omega)
        have h3 : 0 ≤ bs - x0 := by linarith [lo_ge_x0 (P := P) x0]
        calc (1 - P.β) ^ m * (bs - x0) ≤ (1 - P.β) ^ k * (bs - x0) :=
              mul_le_mul_of_nonneg_right h2 h3
          _ ≤ (1 - P.β) ^ k * (z - x0) :=
              mul_le_mul_of_nonneg_left (by linarith [hz.1]) (pow_nonneg (by linarith) _)
          _ ≤ _ := h1)
      (hGk.ii hS m hb hp.le) (hGk.ii hS (m + 1) hb hp.le)
    have hCpos : 0 < P.Fe (p - P.Δ) ^ (m + 1) := pow_pos (Fes_pos hS ha) _
    have hI' : ∫ z in bs..p, ((1 - P.β) * P.V k x0 z) * P.gt (m + 1) z =
        (1 - P.β) * ∫ z in bs..p, P.V k x0 z * P.gt (m + 1) z := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext z; ring
    rw [hI'] at hI
    unfold Aux
    have e1 : P.Fe (bs - P.Δ) ^ m * (1 - P.β) ^ m * (bs - x0) =
        P.Fe (bs - P.Δ) ^ m * ((1 - P.β) ^ m * (bs - x0)) := by ring
    have e2 : P.Fe (bs - P.Δ) ^ (m + 1) * (1 - P.β) ^ (m + 1) * (bs - x0) =
        (1 - P.β) * (P.Fe (bs - P.Δ) ^ (m + 1) * ((1 - P.β) ^ m * (bs - x0))) := by ring
    rw [e1, e2]
    calc (1 - P.β) * (((∫ z in bs..p, P.V k x0 z * P.gt m z) +
            P.Fe (bs - P.Δ) ^ m * ((1 - P.β) ^ m * (bs - x0))) / P.Fe (p - P.Δ) ^ m)
        ≤ (1 - P.β) * (((∫ z in bs..p, P.V k x0 z * P.gt (m + 1) z) +
            P.Fe (bs - P.Δ) ^ (m + 1) * ((1 - P.β) ^ m * (bs - x0))) /
              P.Fe (p - P.Δ) ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left hsd (by linarith)
      _ ≤ _ := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hCpos]
          nlinarith

/-- Lemma EC.1 (c), in difference form. -/
lemma V_diff_x (hS : P.Standing) (k : ℕ) :
    ∀ x x' : ℝ, x ≤ x' → ∀ z, P.lo x' ≤ z → P.Rlo + P.Δ < z →
      (1 - P.β) ^ k * (x' - x) ≤ P.V k x z - P.V k x' z := by
  have hβ1 := St_β1 hS
  have hβ0 := St_β0 hS
  induction k with
  | zero => intro x x' _ z _ _; show (1 - P.β) ^ 0 * (x' - x) ≤ (z - x) - (z - x'); simp
  | succ k ih =>
    intro x x' hxx z hz ha
    set m := k + 1
    have hm1 : 1 ≤ m := by omega
    have hlo : P.lo x ≤ P.lo x' := max_le_max le_rfl hxx
    have hG' : P.Good (m - 1) x' := Good_all hS _ x'
    have hG : P.Good (m - 1) x := Good_all hS _ x
    obtain ⟨bs, hbs, hmax⟩ := T_max hS hG' hz
    rw [(V_of_max hS hm1 hG' hbs hmax).1]
    have hle := Pi_le_V hS hm1 hG (show bs ∈ Icc (P.lo x) z from ⟨le_trans hlo hbs.1, hbs.2⟩)
    suffices h : (1 - P.β) ^ m * (x' - x) ≤ P.Pi m bs x z - P.Pi m bs x' z by linarith
    rw [Pi_eq m hm1, Pi_eq m hm1, ← sub_div]
    have hCpos : 0 < P.Fe (z - P.Δ) ^ m := pow_pos (Fes_pos hS ha) _
    rw [le_div_iff₀ hCpos]
    have hb := hbs.1
    have hbz := hbs.2
    have hGk : P.Good k x := Good_all hS _ x
    have hGk' : P.Good k x' := Good_all hS _ x'
    have hI : ∫ y in bs..z, ((1 - P.β) ^ m * (x' - x)) * P.gt m y ≤
        ∫ y in bs..z, (P.V k x y - P.V k x' y) * P.gt m y := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hbz ((gt_ii hS m bs z).const_mul _)
      · have h1 := hGk.ii hS m (le_trans hlo hb) (le_trans hlo (le_trans hb hbz))
        have h2 := hGk'.ii hS m hb (le_trans hb hbz)
        refine (h1.sub h2).congr (fun y _ => ?_); ring
      · intro y hy
        apply mul_le_mul_of_nonneg_right _ (gt_nonneg hS _ y)
        have h1 := ih x x' hxx y (le_trans hb hy.1.le)
          (lt_of_le_of_lt (le_trans (lo_ge_a x') hb) hy.1)
        have h2 : (1 - P.β) ^ m ≤ (1 - P.β) ^ k :=
          pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
        nlinarith
    rw [intervalIntegral.integral_const_mul, int_gt hS m hm1 hbz] at hI
    have hsub : (∫ y in bs..z, (P.V k x y - P.V k x' y) * P.gt m y) =
        (∫ y in bs..z, P.V (m - 1) x y * P.gt m y) - ∫ y in bs..z, P.V (m - 1) x' y * P.gt m y := by
      rw [show m - 1 = k from rfl, ← intervalIntegral.integral_sub]
      · congr 1; funext y; ring
      · exact hGk.ii hS m (le_trans hlo hb) (le_trans hlo (le_trans hb hbz))
      · exact hGk'.ii hS m hb (le_trans hb hbz)
    unfold Aux
    rw [hsub] at hI
    nlinarith

end PostQual.Incumbent.Params


open MeasureTheory Set intervalIntegral

namespace PostQual.Incumbent.Params

variable {P : Params}

lemma cont_neg_nbhd {g : ℝ → ℝ} {s : Set ℝ} {t : ℝ} (hg : ContinuousWithinAt g s t) (h : g t < 0) :
    ∃ δ > 0, ∀ y ∈ s, |y - t| < δ → g y < 0 := by
  have h1 : ∀ᶠ y in nhdsWithin t s, g y < 0 := hg.eventually (gt_mem_nhds h)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨ε, hε, h2⟩ := h1
  exact ⟨ε, hε, fun y hy hd => h2 (by rw [Real.dist_eq]; exact hd) hy⟩

lemma cont_pos_nbhd {g : ℝ → ℝ} {s : Set ℝ} {t : ℝ} (hg : ContinuousWithinAt g s t) (h : 0 < g t) :
    ∃ δ > 0, ∀ y ∈ s, |y - t| < δ → 0 < g y := by
  have h1 : ∀ᶠ y in nhdsWithin t s, 0 < g y := hg.eventually (lt_mem_nhds h)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨ε, hε, h2⟩ := h1
  exact ⟨ε, hε, fun y hy hd => h2 (by rw [Real.dist_eq]; exact hd) hy⟩

/-- the set whose infimum / supremum are `b⋆` / `b⋆⋆`. -/
def Sset (P : Params) (m : ℕ) (x0 : ℝ) : Set ℝ :=
  {b | b ∈ Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ) ∧ P.H b - P.L m b x0 < 0}

lemma lo_eq' (x0 : ℝ) : P.lo x0 = max x0 (P.Rlo + P.Δ) := max_comm _ _

section
variable (hS : P.Standing)
include hS

lemma a_lt_c : P.Rlo + P.Δ < P.Rhi + P.Δ := by linarith [St_lt hS]

lemma lo_lt_c {x0 : ℝ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) : P.lo x0 < P.Rhi + P.Δ :=
  max_lt (a_lt_c hS) (by linarith [hx0.2, Δ_pos hS])

lemma H_cont : ContinuousOn P.H (Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ)) := by
  unfold H
  apply ContinuousOn.div (Fes_continuous hS).continuousOn
  · have : MapsTo (fun b => b - P.Δ) (Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ)) (Icc P.Rlo P.Rhi) := by
      intro b hb; exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    exact (St_cont hS).comp (continuous_id.sub continuous_const).continuousOn this
  · intro b hb; exact (fes_pos hS hb.1 hb.2).ne'

lemma phi_cont (m : ℕ) (x0 : ℝ) :
    ContinuousOn (fun b => P.H b - P.L m b x0) (Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ)) := by
  apply (H_cont hS).sub
  unfold L
  exact Continuous.continuousOn (by fun_prop)

lemma H_a : P.H (P.Rlo + P.Δ) = 0 := by
  unfold H; rw [show P.Rlo + P.Δ - P.Δ = P.Rlo by ring, Fe_Rlo hS, zero_div]

lemma H_pos {b : ℝ} (h1 : P.Rlo + P.Δ < b) (h2 : b ≤ P.Rhi + P.Δ) : 0 < P.H b :=
  div_pos (Fes_pos hS h1) (fes_pos hS h1.le h2)

lemma phi_conv (hA1 : P.Assumption1) (m : ℕ) (x0 : ℝ) {u v : ℝ}
    (hu : u ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ)) (hv : v ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    P.H (θ * u + (1 - θ) * v) - P.L m (θ * u + (1 - θ) * v) x0 ≤
      θ * (P.H u - P.L m u x0) + (1 - θ) * (P.H v - P.L m v x0) := by
  have hc := hA1.2.2 (x := u - P.Δ) (y := v - P.Δ) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    ⟨by linarith [hv.1], by linarith [hv.2]⟩ h0 (by linarith : 0 ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hc
  have e : θ * (u - P.Δ) + (1 - θ) * (v - P.Δ) = θ * u + (1 - θ) * v - P.Δ := by ring
  rw [e] at hc
  unfold H L
  have : ↑m * P.β * (θ * u + (1 - θ) * v - x0) / (1 - P.β) =
      θ * (↑m * P.β * (u - x0) / (1 - P.β)) + (1 - θ) * (↑m * P.β * (v - x0) / (1 - P.β)) := by
    ring
  rw [this]
  linarith

/-- convexity: between two negative points the function is negative. -/
lemma phi_between (hA1 : P.Assumption1) (m : ℕ) (x0 : ℝ) {u y v : ℝ}
    (hu : u ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ)) (hv : v ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ))
    (huy : u < y) (hyv : y < v) (hφu : P.H u - P.L m u x0 ≤ 0) (hφv : P.H v - P.L m v x0 ≤ 0)
    (hstrict : P.H u - P.L m u x0 < 0 ∨ P.H v - P.L m v x0 < 0) :
    P.H y - P.L m y x0 < 0 := by
  set θ := (v - y) / (v - u) with hθ
  have hvu : 0 < v - u := by linarith
  have h0 : 0 < θ := div_pos (by linarith) hvu
  have h1 : θ < 1 := (div_lt_one hvu).mpr (by linarith)
  have hy : y = θ * u + (1 - θ) * v := by
    rw [hθ]; field_simp; ring
  have := phi_conv hS hA1 m x0 hu hv h0.le h1.le
  rw [← hy] at this
  rcases hstrict with h | h
  · nlinarith
  · nlinarith

lemma phi_eq_ratio {x0 b : ℝ} (m : ℕ) (hx : x0 < b) (h1 : P.Rlo + P.Δ < b)
    (h2 : b ≤ P.Rhi + P.Δ) :
    P.H b - P.L m b x0 = P.β * (b - x0) / (1 - P.β) * (P.ratio x0 b - m) := by
  have hf := (fes_pos hS h1.le h2).ne'
  have hb0 : b - x0 ≠ 0 := by linarith
  have hβ0 := (St_β0 hS).ne'
  have hβ1 : 1 - P.β ≠ 0 := by linarith [St_β1 hS]
  unfold H L ratio
  field_simp

lemma mStar_dom_ne {x0 : ℝ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) :
    (Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ)).Nonempty := by
  refine ⟨P.Rhi + P.Δ, ?_, le_rfl⟩
  rw [← lo_eq']; exact lo_lt_c hS hx0

lemma ratio_pos {x0 b : ℝ} (hb : b ∈ Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ)) :
    0 < P.ratio x0 b := by
  have h1 : P.Rlo + P.Δ < b := lt_of_le_of_lt (le_max_right _ _) hb.1
  have h2 : x0 < b := lt_of_le_of_lt (le_max_left _ _) hb.1
  unfold ratio
  have := Fes_pos hS h1
  have := fes_pos hS h1.le hb.2
  have := St_β0 hS
  have := St_β1 hS
  apply div_pos (mul_pos (by linarith) (by assumption))
  apply mul_pos (mul_pos (by assumption) (by linarith)) (by assumption)

lemma sInf_ratio_nonneg (x0 : ℝ) :
    0 ≤ sInf (P.ratio x0 '' Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ)) := by
  apply Real.sInf_nonneg
  rintro _ ⟨b, hb, rfl⟩; exact (ratio_pos hS hb).le

lemma mStar_lt {x0 : ℝ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) {m : ℕ} (hm : P.mStar x0 < m) :
    ∃ b ∈ Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ), P.H b - P.L m b x0 < 0 := by
  unfold mStar at hm
  rw [Nat.floor_lt (sInf_ratio_nonneg hS x0)] at hm
  obtain ⟨_, ⟨b, hb, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((mStar_dom_ne hS hx0).image _) hm
  refine ⟨b, hb, ?_⟩
  have h1 : P.Rlo + P.Δ < b := lt_of_le_of_lt (le_max_right _ _) hb.1
  have h2 : x0 < b := lt_of_le_of_lt (le_max_left _ _) hb.1
  rw [phi_eq_ratio hS m h2 h1 hb.2]
  apply mul_neg_of_pos_of_neg
  · have := St_β0 hS; have := St_β1 hS
    apply div_pos (mul_pos (by assumption) (by linarith)) (by linarith)
  · linarith

lemma mStar_ge {x0 : ℝ} {m : ℕ} (hm : m ≤ P.mStar x0) :
    ∀ b ∈ Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ), 0 ≤ P.H b - P.L m b x0 := by
  intro b hb
  unfold mStar at hm
  rw [Nat.le_floor_iff (sInf_ratio_nonneg hS x0)] at hm
  have hbdd : BddBelow (P.ratio x0 '' Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ)) :=
    ⟨0, by rintro _ ⟨b', hb', rfl⟩; exact (ratio_pos hS hb').le⟩
  have h3 := csInf_le hbdd (mem_image_of_mem _ hb)
  have h1 : P.Rlo + P.Δ < b := lt_of_le_of_lt (le_max_right _ _) hb.1
  have h2 : x0 < b := lt_of_le_of_lt (le_max_left _ _) hb.1
  rw [phi_eq_ratio hS m h2 h1 hb.2]
  apply mul_nonneg
  · have := St_β0 hS; have := St_β1 hS
    apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  · linarith

lemma mStar_mono : MonotoneOn P.mStar (Icc P.Rlo P.Rhi) := by
  intro x hx x' hx' hxx
  unfold mStar
  apply Nat.floor_le_floor
  apply le_csInf ((mStar_dom_ne hS hx').image _)
  rintro _ ⟨b, hb, rfl⟩
  have hb' : b ∈ Ioc (max x (P.Rlo + P.Δ)) (P.Rhi + P.Δ) :=
    ⟨lt_of_le_of_lt (max_le_max hxx le_rfl) hb.1, hb.2⟩
  have hbdd : BddBelow (P.ratio x '' Ioc (max x (P.Rlo + P.Δ)) (P.Rhi + P.Δ)) :=
    ⟨0, by rintro _ ⟨b', hb'', rfl⟩; exact (ratio_pos hS hb'').le⟩
  refine le_trans (csInf_le hbdd (mem_image_of_mem _ hb')) ?_
  have h1 : P.Rlo + P.Δ < b := lt_of_le_of_lt (le_max_right _ _) hb.1
  have h2 : x' < b := lt_of_le_of_lt (le_max_left _ _) hb.1
  unfold ratio
  have := Fes_pos hS h1
  have := fes_pos hS h1.le hb.2
  have := St_β0 hS
  have := St_β1 hS
  apply div_le_div_of_nonneg_left
  · exact (mul_pos (by linarith) (by assumption)).le
  · exact mul_pos (mul_pos (by assumption) (by linarith)) (by assumption)
  · apply mul_le_mul_of_nonneg_right _ (by linarith)
    apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-! ### The sets `S_m(x0)` -/

variable {m : ℕ} {x0 b : ℝ}

omit hS in
lemma Sset_sub (hb : b ∈ P.Sset m x0) : b ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ) :=
  ⟨le_trans (le_max_right _ _) hb.1.1.le, hb.1.2⟩

lemma Sset_ne (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) : (P.Sset m x0).Nonempty := by
  obtain ⟨b, hb, h⟩ := mStar_lt hS hx0 hm
  exact ⟨b, hb, h⟩

omit hS in
lemma Sset_bddB : BddBelow (P.Sset m x0) := ⟨max x0 (P.Rlo + P.Δ), fun b hb => hb.1.1.le⟩
omit hS in
lemma Sset_bddA : BddAbove (P.Sset m x0) := ⟨P.Rhi + P.Δ, fun b hb => hb.1.2⟩

omit hS in
lemma bSS_eq : P.bStarStar m x0 = sSup (P.Sset m x0) := rfl

lemma Sset_mono_m {m m' : ℕ} (hmm : m ≤ m') (hx : b ∈ P.Sset m x0) : b ∈ P.Sset m' x0 := by
  refine ⟨hx.1, ?_⟩
  have h2 : x0 < b := lt_of_le_of_lt (le_max_left _ _) hx.1.1
  have : P.L m b x0 ≤ P.L m' b x0 := by
    unfold L
    have := St_β0 hS; have := St_β1 hS
    apply div_le_div_of_nonneg_right _ (by linarith)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact_mod_cast hmm
  linarith [hx.2]

lemma Sset_mono_x {x x' : ℝ} (hxx : x' ≤ x) (hx : b ∈ P.Sset m x) : b ∈ P.Sset m x' := by
  refine ⟨⟨lt_of_le_of_lt (max_le_max hxx le_rfl) hx.1.1, hx.1.2⟩, ?_⟩
  have : P.L m b x ≤ P.L m b x' := by
    unfold L
    have := St_β0 hS; have := St_β1 hS
    apply div_le_div_of_nonneg_right _ (by linarith)
    apply mul_le_mul_of_nonneg_left (by linarith)
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  linarith [hx.2]

/-- `b⋆ = inf S`. -/
lemma bStar_eq (hA1 : P.Assumption1) (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    P.bStar m x0 = sInf (P.Sset m x0) := by
  unfold bStar
  split_ifs with h
  · -- `x0 ≤ a`: the set accumulates at `a`
    obtain ⟨b1, hb1⟩ := Sset_ne hS hx0 hm
    have hmax : max x0 (P.Rlo + P.Δ) = P.Rlo + P.Δ := max_eq_right h
    have hb1a : P.Rlo + P.Δ < b1 := by have := hb1.1.1; rwa [hmax] at this
    have haI : P.Rlo + P.Δ ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ) := ⟨le_rfl, (a_lt_c hS).le⟩
    have hφa : P.H (P.Rlo + P.Δ) - P.L m (P.Rlo + P.Δ) x0 ≤ 0 := by
      rw [H_a hS]; unfold L
      have := St_β0 hS; have := St_β1 hS
      have : 0 ≤ ↑m * P.β * (P.Rlo + P.Δ - x0) / (1 - P.β) :=
        div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by linarith))
          (by linarith)
      linarith
    have hin : ∀ y ∈ Ioo (P.Rlo + P.Δ) b1, y ∈ P.Sset m x0 := by
      intro y hy
      refine ⟨⟨by rw [hmax]; exact hy.1, le_trans hy.2.le hb1.1.2⟩, ?_⟩
      exact phi_between hS hA1 m x0 haI (Sset_sub hb1) hy.1 hy.2 hφa hb1.2.le (Or.inr hb1.2)
    apply le_antisymm
    · apply le_csInf ⟨b1, hb1⟩
      intro b hb; rw [← hmax]; exact hb.1.1.le
    · by_contra hc
      push Not at hc
      set y := (P.Rlo + P.Δ + min (sInf (P.Sset m x0)) b1) / 2
      have hy1 : P.Rlo + P.Δ < y := by
        have : P.Rlo + P.Δ < min (sInf (P.Sset m x0)) b1 := lt_min hc hb1a
        simp only [y]; linarith
      have hy2 : y < min (sInf (P.Sset m x0)) b1 := by
        have : P.Rlo + P.Δ < min (sInf (P.Sset m x0)) b1 := lt_min hc hb1a
        simp only [y]; linarith
      have hyS := hin y ⟨hy1, lt_of_lt_of_le hy2 (min_le_right _ _)⟩
      have := csInf_le Sset_bddB hyS
      linarith [min_le_left (sInf (P.Sset m x0)) b1]
  · push Not at h
    have hmax : max x0 (P.Rlo + P.Δ) = x0 := max_eq_left h.le
    unfold Sset; rw [hmax]

lemma bStar_ge_lo (hA1 : P.Assumption1) (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    P.lo x0 ≤ P.bStar m x0 := by
  rw [bStar_eq hS hA1 hx0 hm, lo_eq']
  exact le_csInf (Sset_ne hS hx0 hm) (fun b hb => hb.1.1.le)

lemma bSS_le_c (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    P.bStarStar m x0 ≤ P.Rhi + P.Δ :=
  csSup_le (Sset_ne hS hx0 hm) (fun b hb => hb.1.2)

lemma bStar_lt_bSS (hA1 : P.Assumption1) (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    P.bStar m x0 < P.bStarStar m x0 := by
  obtain ⟨s, hs⟩ := Sset_ne hS hx0 hm
  have hsI := Sset_sub hs
  obtain ⟨δ, hδ, hneg⟩ := cont_neg_nbhd ((phi_cont hS m x0) s hsI) hs.2
  set l := max x0 (P.Rlo + P.Δ)
  have hls : l < s := hs.1.1
  set y := (max l (s - δ) + s) / 2
  have hy1 : l < y := by
    have := le_max_left l (s - δ); have : max l (s - δ) < s := max_lt hls (by linarith)
    simp only [y]; linarith
  have hy2 : y < s := by
    have : max l (s - δ) < s := max_lt hls (by linarith)
    simp only [y]; linarith
  have hy3 : s - δ < y := by
    have := le_max_right l (s - δ); have : max l (s - δ) < s := max_lt hls (by linarith)
    simp only [y]; linarith
  have hyI : y ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ) :=
    ⟨le_trans (le_max_right _ _) hy1.le, le_trans hy2.le hsI.2⟩
  have hyS : y ∈ P.Sset m x0 :=
    ⟨⟨hy1, le_trans hy2.le hs.1.2⟩, hneg y hyI (by rw [abs_lt]; constructor <;> linarith)⟩
  rw [bStar_eq hS hA1 hx0 hm]
  calc sInf (P.Sset m x0) ≤ y := csInf_le Sset_bddB hyS
    _ < s := hy2
    _ ≤ sSup (P.Sset m x0) := le_csSup Sset_bddA hs

lemma bStar_gt_x0 (hA1 : P.Assumption1) (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m)
    (hne : x0 ≠ P.Rlo + P.Δ) : x0 < P.bStar m x0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · unfold bStar; rw [if_pos h.le]; exact h
  · have hxI : x0 ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ) := ⟨h.le, by linarith [hx0.2, Δ_pos hS]⟩
    have hφ : 0 < P.H x0 - P.L m x0 x0 := by
      have := H_pos hS h hxI.2
      unfold L; simp; linarith
    obtain ⟨δ, hδ, hpos⟩ := cont_pos_nbhd ((phi_cont hS m x0) x0 hxI) hφ
    rw [bStar_eq hS hA1 hx0 hm]
    have : x0 + δ ≤ sInf (P.Sset m x0) := by
      apply le_csInf (Sset_ne hS hx0 hm)
      intro b hb
      by_contra hc; push Not at hc
      have hb1 : x0 < b := lt_of_le_of_lt (le_max_left _ _) hb.1.1
      have := hpos b (Sset_sub hb) (by rw [abs_lt]; constructor <;> linarith)
      linarith [hb.2]
    linarith

lemma x0_le_bStar (hA1 : P.Assumption1) (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    x0 ≤ P.bStar m x0 := le_trans (lo_ge_x0 x0) (bStar_ge_lo hS hA1 hx0 hm)

/-- (EC.16), middle part. -/
lemma phi_neg_mid (hA1 : P.Assumption1) (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m)
    {b : ℝ} (hb1 : P.bStar m x0 < b) (hb2 : b < P.bStarStar m x0) :
    b ∈ P.Sset m x0 := by
  rw [bStar_eq hS hA1 hx0 hm] at hb1
  obtain ⟨u, hu, hub⟩ := exists_lt_of_csInf_lt (Sset_ne hS hx0 hm) hb1
  obtain ⟨v, hv, hbv⟩ := exists_lt_of_lt_csSup (Sset_ne hS hx0 hm) hb2
  refine ⟨⟨lt_trans hu.1.1 hub, le_trans hbv.le hv.1.2⟩, ?_⟩
  exact phi_between hS hA1 m x0 (Sset_sub hu) (Sset_sub hv) hub hbv hu.2.le hv.2.le
    (Or.inl hu.2)

/-- (EC.16), left part. -/
lemma phi_pos_left (hA1 : P.Assumption1) (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m)
    {b : ℝ} (hb1 : P.lo x0 < b) (hb2 : b < P.bStar m x0) :
    0 < P.H b - P.L m b x0 := by
  have hbS := bStar_eq hS hA1 hx0 hm
  obtain ⟨v, hv⟩ := Sset_ne hS hx0 hm
  have hvb : P.bStar m x0 ≤ v := by rw [hbS]; exact csInf_le Sset_bddB hv
  have hbc : b ≤ P.Rhi + P.Δ := le_trans hb2.le (le_trans hvb hv.1.2)
  have hbI : b ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ) := ⟨le_trans (lo_ge_a x0) hb1.le, hbc⟩
  have hdom : ∀ y, b ≤ y → y ≤ P.Rhi + P.Δ → y ∈ Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ) := by
    intro y hy1 hy2; rw [← lo_eq']; exact ⟨lt_of_lt_of_le hb1 hy1, hy2⟩
  by_contra hc
  push Not at hc
  set y := (b + P.bStar m x0) / 2
  have hy1 : b < y := by simp only [y]; linarith
  have hy2 : y < P.bStar m x0 := by simp only [y]; linarith
  have hφy := phi_between hS hA1 m x0 hbI (Sset_sub hv) hy1 (by linarith) hc hv.2.le
    (Or.inr hv.2)
  have hyS : y ∈ P.Sset m x0 := ⟨hdom y hy1.le (by linarith [hv.1.2]), hφy⟩
  have := csInf_le Sset_bddB hyS
  rw [← hbS] at this
  linarith

/-- (EC.16), right part. -/
lemma phi_pos_right (hA1 : P.Assumption1) (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m)
    {b : ℝ} (hb1 : P.bStarStar m x0 < b) (hb2 : b ≤ P.Rhi + P.Δ) :
    0 < P.H b - P.L m b x0 := by
  obtain ⟨u, hu⟩ := Sset_ne hS hx0 hm
  have hub : u ≤ P.bStarStar m x0 := le_csSup Sset_bddA hu
  have hbdom : b ∈ Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ) :=
    ⟨lt_of_lt_of_le hu.1.1 (le_trans hub hb1.le), hb2⟩
  have hbI : b ∈ Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ) :=
    ⟨le_trans (le_max_right _ _) hbdom.1.le, hb2⟩
  by_contra hc
  push Not at hc
  set y := (P.bStarStar m x0 + b) / 2
  have hy1 : P.bStarStar m x0 < y := by simp only [y]; linarith
  have hy2 : y < b := by simp only [y]; linarith
  have hφy := phi_between hS hA1 m x0 (Sset_sub hu) hbI (by linarith) hy2 hu.2.le hc
    (Or.inl hu.2)
  have hyS : y ∈ P.Sset m x0 :=
    ⟨⟨lt_of_lt_of_le hu.1.1 (by linarith), by linarith⟩, hφy⟩
  have := le_csSup Sset_bddA hyS
  rw [← bSS_eq] at this
  linarith

end

/-! ### `zt` -/

lemma zt_eq_phi (hS : P.Standing) (m : ℕ) (x0 : ℝ) {z : ℝ} (h1 : P.Rlo + P.Δ ≤ z)
    (h2 : z ≤ P.Rhi + P.Δ) :
    P.zt m z x0 = P.Fe (z - P.Δ) ^ (m - 1) * (1 - P.β) ^ m * P.fe (z - P.Δ) *
      (P.H z - P.L m z x0) := by
  have hf := (fes_pos hS h1 h2).ne'
  have hβ1 : 1 - P.β ≠ 0 := by linarith [St_β1 hS]
  unfold zt H L
  field_simp
  ring

lemma zt_gt_c (hS : P.Standing) (m : ℕ) (x0 : ℝ) {z : ℝ} (h : P.Rhi + P.Δ < z) :
    P.zt m z x0 = (1 - P.β) ^ m := by
  unfold zt
  rw [Fes_one hS h.le, fes_zero hS h]; simp

lemma zt_coef_pos (hS : P.Standing) (m : ℕ) {z : ℝ} (h1 : P.Rlo + P.Δ < z)
    (h2 : z ≤ P.Rhi + P.Δ) :
    0 < P.Fe (z - P.Δ) ^ (m - 1) * (1 - P.β) ^ m * P.fe (z - P.Δ) := by
  have := Fes_pos hS h1
  have := fes_pos hS h1.le h2
  have : 0 < 1 - P.β := by linarith [St_β1 hS]
  positivity

/-- `Dk` versus `zt`: `Dk = zt + gt·((1-β)^{m-1}(z-x0) - W z)`. -/
lemma Dk_eq (m : ℕ) (hm : 1 ≤ m) (W : ℝ → ℝ) (x0 z : ℝ) (hβ : P.β < 1) :
    P.Dk m W x0 z = P.zt m z x0 + P.gt m z * ((1 - P.β) ^ (m - 1) * (z - x0) - W z) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hβ1 : 1 - P.β ≠ 0 := by linarith
  unfold Dk Ad zt gt
  simp only [Nat.add_sub_cancel]
  field_simp
  push_cast
  ring

end PostQual.Incumbent.Params


open MeasureTheory Set intervalIntegral

namespace PostQual.Incumbent.Params

variable {P : Params}

section General
variable (hS : P.Standing)
include hS

lemma T_lt_of_pos {m : ℕ} {x0 u v : ℝ} (hu : P.lo x0 ≤ u) (huv : u < v)
    (h : ∀ z ∈ Ioo u v, 0 < P.Dk m (P.V (m - 1) x0) x0 z) : P.T m x0 u < P.T m x0 v := by
  have := T_sub hS (Good_all hS (m - 1) x0) hu huv.le
  have h2 := intervalIntegral.intervalIntegral_pos_of_pos_on
    (Dk_ii hS (Good_all hS (m - 1) x0) hu (le_trans hu huv.le)) h huv
  linarith

lemma T_lt_of_neg {m : ℕ} {x0 u v : ℝ} (hu : P.lo x0 ≤ u) (huv : u < v)
    (h : ∀ z ∈ Ioo u v, P.Dk m (P.V (m - 1) x0) x0 z < 0) : P.T m x0 v < P.T m x0 u := by
  have := T_sub hS (Good_all hS (m - 1) x0) hu huv.le
  have h2 := intervalIntegral.intervalIntegral_pos_of_pos_on
    (Dk_ii hS (Good_all hS (m - 1) x0) hu (le_trans hu huv.le)).neg
    (fun z hz => neg_pos.mpr (h z hz)) huv
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at h2
  linarith

lemma T_le_of_nonneg {m : ℕ} {x0 u v : ℝ} (hu : P.lo x0 ≤ u) (huv : u ≤ v)
    (h : ∀ z ∈ Ioo u v, 0 ≤ P.Dk m (P.V (m - 1) x0) x0 z) : P.T m x0 u ≤ P.T m x0 v := by
  have := T_sub hS (Good_all hS (m - 1) x0) hu huv
  have h2 : ∫ z in u..v, (0:ℝ) ≤ ∫ z in u..v, P.Dk m (P.V (m - 1) x0) x0 z :=
    intervalIntegral.integral_mono_on_of_le_Ioo huv intervalIntegrable_const
      (Dk_ii hS (Good_all hS (m - 1) x0) hu (le_trans hu huv)) h
  simp at h2
  linarith

lemma Dk_le_zt {m : ℕ} (hm : 1 ≤ m) {x0 z : ℝ} (hz : P.lo x0 < z) :
    P.Dk m (P.V (m - 1) x0) x0 z ≤ P.zt m z x0 := by
  rw [Dk_eq m hm _ x0 z (St_β1 hS)]
  have h1 := (Good_all hS (m - 1) x0).2 z hz.le (lt_of_le_of_lt (lo_ge_a x0) hz)
  have := gt_nonneg hS m z
  nlinarith

lemma Dk_eq_zt {m : ℕ} (hm : 1 ≤ m) {x0 z : ℝ}
    (hW : P.V (m - 1) x0 z = (1 - P.β) ^ (m - 1) * (z - x0)) :
    P.Dk m (P.V (m - 1) x0) x0 z = P.zt m z x0 := by
  rw [Dk_eq m hm _ x0 z (St_β1 hS), hW]; ring

lemma Dk_gt_c {m : ℕ} (hm : 1 ≤ m) {x0 z : ℝ} (hz : P.Rhi + P.Δ < z) :
    P.Dk m (P.V (m - 1) x0) x0 z = (1 - P.β) ^ m := by
  rw [Dk_eq m hm _ x0 z (St_β1 hS), zt_gt_c hS m x0 hz, gt_zero_of_gt hS m hz]; ring

lemma T_beyond_c {m : ℕ} (hm : 1 ≤ m) {x0 b : ℝ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi)
    (hb : P.Rhi + P.Δ ≤ b) :
    P.T m x0 b = (1 - P.β) ^ m * (b - x0) -
      ∫ z in P.lo x0..P.Rhi + P.Δ, P.V (m - 1) x0 z * P.gt m z := by
  have hG := Good_all hS (m - 1) x0
  have hlc := (lo_lt_c hS hx0).le
  unfold T Aux
  rw [Fes_one hS hb, one_pow, one_mul,
    ← intervalIntegral.integral_add_adjacent_intervals (hG.ii hS m le_rfl hlc)
      (hG.ii hS m hlc (le_trans hlc hb))]
  have : ∫ z in P.Rhi + P.Δ..b, P.V (m - 1) x0 z * P.gt m z = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with z hz
    rw [uIoc_of_le hb] at hz
    rw [gt_zero_of_gt hS m hz.1, mul_zero]
  rw [this]; ring

end General

section Compete
variable (hS : P.Standing) (hA1 : P.Assumption1)
include hS hA1

variable {x0 : ℝ} {m : ℕ}

lemma m_pos (hm : P.mStar x0 < m) : 1 ≤ m := by omega

lemma zt_neg_mid (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) {z : ℝ}
    (h1 : P.bStar m x0 < z) (h2 : z < P.bStarStar m x0) : P.zt m z x0 < 0 := by
  have ha : P.Rlo + P.Δ < z :=
    lt_of_le_of_lt (le_trans (lo_ge_a x0) (bStar_ge_lo hS hA1 hx0 hm)) h1
  have hc : z ≤ P.Rhi + P.Δ := le_trans h2.le (bSS_le_c hS hx0 hm)
  rw [zt_eq_phi hS m x0 ha.le hc]
  exact mul_neg_of_pos_of_neg (zt_coef_pos hS m ha hc) (phi_neg_mid hS hA1 hx0 hm h1 h2).2

lemma zt_pos_left (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) {z : ℝ}
    (h1 : P.lo x0 < z) (h2 : z < P.bStar m x0) : 0 < P.zt m z x0 := by
  have ha : P.Rlo + P.Δ < z := lt_of_le_of_lt (lo_ge_a x0) h1
  have hc : z ≤ P.Rhi + P.Δ :=
    le_trans h2.le (le_trans (bStar_lt_bSS hS hA1 hx0 hm).le (bSS_le_c hS hx0 hm))
  rw [zt_eq_phi hS m x0 ha.le hc]
  exact mul_pos (zt_coef_pos hS m ha hc) (phi_pos_left hS hA1 hx0 hm h1 h2)

lemma zt_pos_right (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) {z : ℝ}
    (h1 : P.bStarStar m x0 < z) : 0 < P.zt m z x0 := by
  rcases le_or_gt z (P.Rhi + P.Δ) with hc | hc
  · have ha : P.Rlo + P.Δ < z := lt_of_le_of_lt (le_trans (lo_ge_a x0) (le_trans
      (bStar_ge_lo hS hA1 hx0 hm) (bStar_lt_bSS hS hA1 hx0 hm).le)) h1
    rw [zt_eq_phi hS m x0 ha.le hc]
    exact mul_pos (zt_coef_pos hS m ha hc) (phi_pos_right hS hA1 hx0 hm h1 hc)
  · rw [zt_gt_c hS m x0 hc]; exact pow_pos (by linarith [St_β1 hS]) _

lemma T_anti_mid (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    StrictAntiOn (P.T m x0) (Icc (P.bStar m x0) (P.bStarStar m x0)) := by
  intro u hu v hv huv
  apply T_lt_of_neg hS (le_trans (bStar_ge_lo hS hA1 hx0 hm) hu.1) huv
  intro z hz
  have h1 : P.bStar m x0 < z := lt_of_le_of_lt hu.1 hz.1
  have h2 : z < P.bStarStar m x0 := lt_of_lt_of_le hz.2 hv.2
  exact lt_of_le_of_lt (Dk_le_zt hS (m_pos hS hA1 hm)
    (lt_of_le_of_lt (bStar_ge_lo hS hA1 hx0 hm) h1)) (zt_neg_mid hS hA1 hx0 hm h1 h2)

/-- `Π^m_0(b; x0, R̄+∆) − Π^m_0(b⋆; x0, R̄+∆) = T b − T b⋆`. -/
lemma Pic_diff (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) {b : ℝ} (hb : P.lo x0 ≤ b) :
    P.Pi m b x0 (P.Rhi + P.Δ) - P.Pi m (P.bStar m x0) x0 (P.Rhi + P.Δ) =
      P.T m x0 b - P.T m x0 (P.bStar m x0) := by
  have hG := Good_all hS (m - 1) x0
  have hm1 := m_pos hS hA1 hm
  have hlc := (lo_lt_c hS hx0).le
  rw [Pi_T hS hm1 hG hb hlc, Pi_T hS hm1 hG (bStar_ge_lo hS hA1 hx0 hm) hlc,
    Fes_one hS le_rfl, one_pow, div_one, div_one]
  ring

/-- the set defining `p⋆`. -/
lemma pStar_props (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    IsLeast {b | P.bStar m x0 < b ∧
        0 ≤ P.Pi m b x0 (P.Rhi + P.Δ) - P.Pi m (P.bStar m x0) x0 (P.Rhi + P.Δ)}
      (P.pStar m x0) ∧
    P.bStarStar m x0 < P.pStar m x0 ∧
    P.T m x0 (P.pStar m x0) = P.T m x0 (P.bStar m x0) ∧
    ∀ b ∈ Ioo (P.bStar m x0) (P.pStar m x0), P.T m x0 b < P.T m x0 (P.bStar m x0) := by
  have hm1 := m_pos hS hA1 hm
  set bs := P.bStar m x0 with hbs
  set bss := P.bStarStar m x0 with hbss
  have hlo := bStar_ge_lo hS hA1 hx0 hm
  have hlt := bStar_lt_bSS hS hA1 hx0 hm
  have hbssc := bSS_le_c hS hx0 hm
  set Q := {b | bs < b ∧ 0 ≤ P.Pi m b x0 (P.Rhi + P.Δ) - P.Pi m bs x0 (P.Rhi + P.Δ)} with hQ
  have hQT : ∀ b, bs < b → (b ∈ Q ↔ P.T m x0 bs ≤ P.T m x0 b) := by
    intro b hb
    simp only [hQ, Set.mem_ofPred_eq]
    rw [Pic_diff hS hA1 hx0 hm (le_trans hlo hb.le)]
    constructor
    · rintro ⟨_, h⟩; linarith
    · intro h; exact ⟨hb, by linarith⟩
  -- nonempty
  set I := ∫ z in P.lo x0..P.Rhi + P.Δ, P.V (m - 1) x0 z * P.gt m z
  have hβm : 0 < (1 - P.β) ^ m := pow_pos (by linarith [St_β1 hS]) _
  set B := max (P.Rhi + P.Δ + 1) (x0 + (|P.T m x0 bs + I| + 1) / (1 - P.β) ^ m) with hB
  have hBc : P.Rhi + P.Δ ≤ B := le_trans (by linarith) (le_max_left _ _)
  have hBQ : B ∈ Q := by
    have hbsB : bs < B := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    rw [hQT B hbsB, T_beyond_c hS hm1 hx0 hBc]
    have h1 : x0 + (|P.T m x0 bs + I| + 1) / (1 - P.β) ^ m ≤ B := le_max_right _ _
    have h2 : (|P.T m x0 bs + I| + 1) ≤ (1 - P.β) ^ m * (B - x0) := by
      rw [← div_le_iff₀' hβm]; linarith
    have := le_abs_self (P.T m x0 bs + I)
    linarith
  have hQne : Q.Nonempty := ⟨B, hBQ⟩
  have hQbdd : BddBelow Q := ⟨bs, fun b hb => hb.1.le⟩
  have hps : P.pStar m x0 = sInf Q := rfl
  -- no element of `Q` in `(b⋆, b⋆⋆]`
  have hanti := T_anti_mid hS hA1 hx0 hm
  have hmidlt : ∀ b, bs < b → b ≤ bss → P.T m x0 b < P.T m x0 bs := by
    intro b h1 h2
    exact hanti ⟨le_rfl, hlt.le⟩ ⟨h1.le, h2⟩ h1
  have hge : bss ≤ sInf Q := by
    apply le_csInf hQne
    intro b hb
    by_contra hc; push Not at hc
    have := (hQT b hb.1).mp hb
    have := hmidlt b hb.1 hc.le
    linarith
  set ps := sInf Q with hpsdef
  have hcont := T_cont hS (Good_all hS (m - 1) x0) (m := m) (ps + 1)
  have hpsI : ps ∈ Icc (P.lo x0) (ps + 1) := ⟨by linarith, by linarith⟩
  -- `T ps ≥ T bs`
  have hTge : P.T m x0 bs ≤ P.T m x0 ps := by
    by_contra hc; push Not at hc
    obtain ⟨δ, hδ, hneg⟩ := cont_neg_nbhd (g := fun b => P.T m x0 b - P.T m x0 bs)
      ((hcont ps hpsI).sub continuousWithinAt_const) (by linarith)
    obtain ⟨q, hqQ, hq⟩ := exists_lt_of_csInf_lt hQne (show sInf Q < ps + min δ 1 by
      have := lt_min hδ one_pos; linarith)
    have hqps : ps ≤ q := csInf_le hQbdd hqQ
    have := hneg q ⟨by linarith, by linarith [min_le_right δ 1]⟩
      (by rw [abs_lt]; constructor <;> linarith [min_le_left δ 1])
    have := (hQT q hqQ.1).mp hqQ
    linarith
  have hgt : bss < ps := by
    rcases hge.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hmidlt bss hlt le_rfl
      rw [h] at this; linarith
  have hTle : P.T m x0 ps ≤ P.T m x0 bs := by
    by_contra hc; push Not at hc
    obtain ⟨δ, hδ, hpos⟩ := cont_pos_nbhd (g := fun b => P.T m x0 b - P.T m x0 bs)
      ((hcont ps hpsI).sub continuousWithinAt_const) (by linarith)
    set y := (max bss (ps - δ) + ps) / 2
    have hy1 : max bss (ps - δ) < ps := max_lt hgt (by linarith)
    have hya : bss < y := by have := le_max_left bss (ps - δ); simp only [y]; linarith
    have hyb : y < ps := by simp only [y]; linarith
    have hyc : ps - δ < y := by have := le_max_right bss (ps - δ); simp only [y]; linarith
    have hyI : y ∈ Icc (P.lo x0) (ps + 1) := ⟨by linarith, by linarith⟩
    have := hpos y hyI (by rw [abs_lt]; constructor <;> linarith)
    have hyQ : y ∈ Q := (hQT y (by linarith)).mpr (by linarith)
    have := csInf_le hQbdd hyQ
    linarith
  have hTeq : P.T m x0 ps = P.T m x0 bs := le_antisymm hTle hTge
  have hpsQ : ps ∈ Q := (hQT ps (by linarith)).mpr hTeq.ge
  refine ⟨⟨hpsQ, fun b hb => csInf_le hQbdd hb⟩, hgt, hTeq, ?_⟩
  intro b hb
  by_contra hc; push Not at hc
  have := csInf_le hQbdd ((hQT b hb.1).mpr hc)
  linarith [hb.2]

lemma pStar_gt_bStar (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    P.bStar m x0 < P.pStar m x0 :=
  lt_trans (bStar_lt_bSS hS hA1 hx0 hm) (pStar_props hS hA1 hx0 hm).2.1

/-- Lemma EC.1 (d). -/
lemma ec1d (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) {p : ℝ} (hp : P.lo x0 < p) :
    P.Pi m (P.bStar m x0) x0 p = P.Pi m (P.pStar m x0) x0 p ∧
    ∀ b ∈ Ioo (P.bStar m x0) (P.pStar m x0), P.Pi m b x0 p < P.Pi m (P.bStar m x0) x0 p := by
  have hm1 := m_pos hS hA1 hm
  have hG := Good_all hS (m - 1) x0
  obtain ⟨_, _, hTeq, hlt⟩ := pStar_props hS hA1 hx0 hm
  have hlo := bStar_ge_lo hS hA1 hx0 hm
  have hlo' : P.lo x0 ≤ P.pStar m x0 := le_trans hlo (pStar_gt_bStar hS hA1 hx0 hm).le
  have hC : 0 < P.Fe (p - P.Δ) ^ m := pow_pos (Fes_pos hS (lt_of_le_of_lt (lo_ge_a x0) hp)) _
  refine ⟨?_, ?_⟩
  · rw [Pi_T hS hm1 hG hlo hp.le, Pi_T hS hm1 hG hlo' hp.le, hTeq]
  · intro b hb
    rw [Pi_T hS hm1 hG (le_trans hlo hb.1.le) hp.le, Pi_T hS hm1 hG hlo hp.le]
    apply div_lt_div_of_pos_right _ hC
    linarith [hlt b hb]

/-! ### The induction hypothesis `H^m(x0)` -/

/-- the left half of `H^m(x0)`, from the explicit form of `V^{m-1}` below `b⋆`. -/
lemma H_left (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m)
    (hW : ∀ z, P.lo x0 < z → z < P.bStar m x0 →
      P.V (m - 1) x0 z = (1 - P.β) ^ (m - 1) * (z - x0)) :
    StrictMonoOn (P.T m x0) (Icc (P.lo x0) (P.bStar m x0)) := by
  intro u hu v hv huv
  apply T_lt_of_pos hS hu.1 huv
  intro z hz
  have h1 : P.lo x0 < z := lt_of_le_of_lt hu.1 hz.1
  have h2 : z < P.bStar m x0 := lt_of_lt_of_le hz.2 hv.2
  rw [Dk_eq_zt hS (m_pos hS hA1 hm) (hW z h1 h2)]
  exact zt_pos_left hS hA1 hx0 hm h1 h2

lemma H_right (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m)
    (hW : ∀ z, P.pStar m x0 < z → z ≤ P.Rhi + P.Δ →
      P.V (m - 1) x0 z = (1 - P.β) ^ (m - 1) * (z - x0)) :
    StrictMonoOn (P.T m x0) (Ici (P.pStar m x0)) := by
  have hm1 := m_pos hS hA1 hm
  have hlo' : P.lo x0 ≤ P.pStar m x0 :=
    le_trans (bStar_ge_lo hS hA1 hx0 hm) (pStar_gt_bStar hS hA1 hx0 hm).le
  have hss := (pStar_props hS hA1 hx0 hm).2.1
  intro u hu v hv huv
  apply T_lt_of_pos hS (le_trans hlo' hu) huv
  intro z hz
  have h1 : P.pStar m x0 < z := lt_of_le_of_lt hu hz.1
  rcases le_or_gt z (P.Rhi + P.Δ) with hc | hc
  · rw [Dk_eq_zt hS hm1 (hW z h1 hc)]
    exact zt_pos_right hS hA1 hx0 hm (lt_trans hss h1)
  · rw [Dk_gt_c hS hm1 hc]; exact pow_pos (by linarith [St_β1 hS]) _

/-- `V^m` is explicit wherever `T_m` is maximised at the current price. -/
lemma V_explicit_of_max {k : ℕ} (hk : 1 ≤ k) {z : ℝ} (hz : P.lo x0 < z)
    (hmax : ∀ b ∈ Icc (P.lo x0) z, P.T k x0 b ≤ P.T k x0 z) :
    P.V k x0 z = (1 - P.β) ^ k * (z - x0) := by
  rw [(V_of_max hS hk (Good_all hS (k - 1) x0) ⟨hz.le, le_rfl⟩ hmax).1,
    Pi_diag hS hk (lt_of_le_of_lt (lo_ge_a x0) hz)]

/-- consequence of `H^k(x0)`: `V^k` is explicit on `(ℓ, b⋆_k] ∪ [p⋆_k, ∞)`. -/
lemma V_explicit_of_H {k : ℕ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hk : P.mStar x0 < k)
    (hL : StrictMonoOn (P.T k x0) (Icc (P.lo x0) (P.bStar k x0)))
    (hR : StrictMonoOn (P.T k x0) (Ici (P.pStar k x0))) {z : ℝ} (hz : P.lo x0 < z)
    (hz' : z ≤ P.bStar k x0 ∨ P.pStar k x0 ≤ z) :
    P.V k x0 z = (1 - P.β) ^ k * (z - x0) := by
  have hk1 := m_pos hS hA1 hk
  apply V_explicit_of_max hS hA1 hk1 hz
  intro b hb
  rcases hz' with h | h
  · exact hL.monotoneOn ⟨hb.1, le_trans hb.2 h⟩ ⟨hz.le, h⟩ hb.2
  · obtain ⟨_, _, hTeq, hlt⟩ := pStar_props hS hA1 hx0 hk
    have hbs := bStar_ge_lo hS hA1 hx0 hk
    have hps := pStar_gt_bStar hS hA1 hx0 hk
    have hpz : P.T k x0 (P.pStar k x0) ≤ P.T k x0 z := hR.monotoneOn (Set.self_mem_Ici) h h
    rcases le_or_gt b (P.bStar k x0) with h1 | h1
    · have := hL.monotoneOn ⟨hb.1, h1⟩ ⟨hbs, le_rfl⟩ h1
      linarith
    rcases lt_or_ge b (P.pStar k x0) with h2 | h2
    · have := hlt b ⟨h1, h2⟩; linarith
    · exact hR.monotoneOn h2 h hb.2

/-- the fold regime: for `k ≤ m⋆(x0)`, `V^k(x0,z) = (1−β)^k (z − x0)` and `T_k` is monotone. -/
lemma fold_explicit (hx0 : x0 ∈ Icc P.Rlo P.Rhi) :
    ∀ k : ℕ, k ≤ P.mStar x0 → ∀ z, P.lo x0 < z → P.V k x0 z = (1 - P.β) ^ k * (z - x0) := by
  intro k
  induction k with
  | zero => intro _ z _; show z - x0 = _; simp
  | succ k ih =>
    intro hk z hz
    have ih' := ih (by omega)
    apply V_explicit_of_max hS hA1 (by omega) hz
    intro b hb
    apply T_le_of_nonneg hS hb.1 hb.2
    intro y hy
    have hy1 : P.lo x0 < y := lt_of_le_of_lt hb.1 hy.1
    rw [Dk_eq_zt hS (by omega) (by simpa using ih' y hy1)]
    rcases le_or_gt y (P.Rhi + P.Δ) with hc | hc
    · have ha : P.Rlo + P.Δ < y := lt_of_le_of_lt (lo_ge_a x0) hy1
      rw [zt_eq_phi hS _ x0 ha.le hc]
      apply mul_nonneg (zt_coef_pos hS _ ha hc).le
      exact mStar_ge hS hk y ⟨by rw [← lo_eq']; exact hy1, hc⟩
    · rw [zt_gt_c hS _ x0 hc]; exact (pow_pos (by linarith [St_β1 hS]) _).le

lemma fold_mono (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm1 : 1 ≤ m) (hm : m ≤ P.mStar x0) :
    MonotoneOn (P.T m x0) (Ici (P.lo x0)) := by
  intro u hu v hv huv
  apply T_le_of_nonneg hS hu huv
  intro y hy
  have hy1 : P.lo x0 < y := lt_of_le_of_lt hu hy.1
  rw [Dk_eq_zt hS hm1 (fold_explicit hS hA1 hx0 (m - 1) (by omega) y hy1)]
  rcases le_or_gt y (P.Rhi + P.Δ) with hc | hc
  · have ha : P.Rlo + P.Δ < y := lt_of_le_of_lt (lo_ge_a x0) hy1
    rw [zt_eq_phi hS _ x0 ha.le hc]
    apply mul_nonneg (zt_coef_pos hS _ ha hc).le
    exact mStar_ge hS hm y ⟨by rw [← lo_eq']; exact hy1, hc⟩
  · rw [zt_gt_c hS _ x0 hc]; exact (pow_pos (by linarith [St_β1 hS]) _).le

lemma bStar_anti_m (hx0 : x0 ∈ Icc P.Rlo P.Rhi) {m m' : ℕ} (hm : P.mStar x0 < m) (hmm : m ≤ m') :
    P.bStar m' x0 ≤ P.bStar m x0 := by
  have hm' : P.mStar x0 < m' := lt_of_lt_of_le hm hmm
  rw [bStar_eq hS hA1 hx0 hm, bStar_eq hS hA1 hx0 hm']
  exact csInf_le_csInf Sset_bddB (Sset_ne hS hx0 hm) (fun b hb => Sset_mono_m hS hmm hb)

lemma bSS_mono_m (hx0 : x0 ∈ Icc P.Rlo P.Rhi) {m m' : ℕ} (hm : P.mStar x0 < m) (hmm : m ≤ m') :
    P.bStarStar m x0 ≤ P.bStarStar m' x0 :=
  csSup_le_csSup Sset_bddA (Sset_ne hS hx0 hm) (fun b hb => Sset_mono_m hS hmm hb)

/-- `A^k_1(x0)`: `p⋆_k(x0) ≤ p⋆_{k+1}(x0)`, given `H^k(x0)` and the left half of `H^{k+1}(x0)`. -/
lemma A1 {k : ℕ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hk : P.mStar x0 < k)
    (hL : StrictMonoOn (P.T k x0) (Icc (P.lo x0) (P.bStar k x0)))
    (hL' : StrictMonoOn (P.T (k + 1) x0) (Icc (P.lo x0) (P.bStar (k + 1) x0))) :
    P.pStar k x0 ≤ P.pStar (k + 1) x0 := by
  have hk' : P.mStar x0 < k + 1 := by omega
  have hk1 := m_pos hS hA1 hk
  by_contra hc
  push Not at hc
  set q := P.pStar (k + 1) x0 with hq
  obtain ⟨_, hss', hTeq', hlt'⟩ := pStar_props hS hA1 hx0 hk'
  have hbs' := bStar_ge_lo hS hA1 hx0 hk'
  have hqgt : P.bStar (k + 1) x0 < q := pStar_gt_bStar hS hA1 hx0 hk'
  have hqlo : P.lo x0 < q := lt_of_le_of_lt hbs' hqgt
  -- `V^{k+1}(q) = (1-β)^{k+1}(q-x0)`
  have hV1 : P.V (k + 1) x0 q = (1 - P.β) ^ (k + 1) * (q - x0) := by
    apply V_explicit_of_max hS hA1 (by omega) hqlo
    intro b hb
    rcases le_or_gt b (P.bStar (k + 1) x0) with h1 | h1
    · have := hL'.monotoneOn ⟨hb.1, h1⟩ ⟨hbs', le_rfl⟩ h1; linarith
    rcases lt_or_ge b q with h2 | h2
    · have := hlt' b ⟨h1, h2⟩; linarith
    · rw [le_antisymm hb.2 h2]
  -- EC.1 (b)
  have hb := V_succ_ge hS x0 k q hqlo
  rw [hV1] at hb
  have hβ : 0 < 1 - P.β := by linarith [St_β1 hS]
  have hVk : P.V k x0 q ≤ (1 - P.β) ^ k * (q - x0) := by
    rw [pow_succ] at hb; nlinarith
  -- but `q ∈ (b⋆_k, p⋆_k)`
  have hq1 : P.bStar k x0 < q :=
    lt_of_lt_of_le (bStar_lt_bSS hS hA1 hx0 hk)
      (le_trans (bSS_mono_m hS hA1 hx0 hk (Nat.le_succ k)) hss'.le)
  have h1 := (ec1d hS hA1 hx0 hk hqlo).2 q ⟨hq1, hc⟩
  rw [Pi_diag hS hk1 (lt_of_le_of_lt (lo_ge_a x0) hqlo)] at h1
  have h2 := Pi_le_V hS hk1 (Good_all hS (k - 1) x0)
    (show P.bStar k x0 ∈ Icc (P.lo x0) q from ⟨bStar_ge_lo hS hA1 hx0 hk, hq1.le⟩)
  linarith

/-- Lemma EC.2, the induction: `H^m(x0)` for every `m > m⋆(x0)`, and `A^m_1(x0)`. -/
lemma H_all (hx0 : x0 ∈ Icc P.Rlo P.Rhi) :
    ∀ n : ℕ, let m := P.mStar x0 + 1 + n;
      StrictMonoOn (P.T m x0) (Icc (P.lo x0) (P.bStar m x0)) ∧
      StrictMonoOn (P.T m x0) (Ici (P.pStar m x0)) := by
  intro n
  induction n with
  | zero =>
    simp only [add_zero]
    have hm : P.mStar x0 < P.mStar x0 + 1 := by omega
    have hW : ∀ z, P.lo x0 < z →
        P.V (P.mStar x0 + 1 - 1) x0 z = (1 - P.β) ^ (P.mStar x0 + 1 - 1) * (z - x0) := by
      intro z hz; simpa using fold_explicit hS hA1 hx0 (P.mStar x0) le_rfl z hz
    exact ⟨H_left hS hA1 hx0 hm (fun z h1 _ => hW z h1),
      H_right hS hA1 hx0 hm (fun z h1 _ => hW z (lt_of_le_of_lt (le_trans
        (bStar_ge_lo hS hA1 hx0 hm) (pStar_gt_bStar hS hA1 hx0 hm).le) h1))⟩
  | succ n ih =>
    simp only at ih ⊢
    set k := P.mStar x0 + 1 + n with hkdef
    have hk : P.mStar x0 < k := by omega
    have hk' : P.mStar x0 < k + 1 := by omega
    rw [show P.mStar x0 + 1 + (n + 1) = k + 1 by omega]
    obtain ⟨hL, hR⟩ := ih
    have hbb := bStar_anti_m hS hA1 hx0 hk (Nat.le_succ k)
    have hL' : StrictMonoOn (P.T (k + 1) x0) (Icc (P.lo x0) (P.bStar (k + 1) x0)) := by
      apply H_left hS hA1 hx0 hk'
      intro z h1 h2
      simp only [Nat.add_sub_cancel]
      exact V_explicit_of_H hS hA1 hx0 hk hL hR h1 (Or.inl (le_trans h2.le hbb))
    have hA := A1 hS hA1 hx0 hk hL hL'
    refine ⟨hL', ?_⟩
    apply H_right hS hA1 hx0 hk'
    intro z h1 _
    simp only [Nat.add_sub_cancel]
    have hlo : P.lo x0 < z := lt_of_le_of_lt (le_trans (bStar_ge_lo hS hA1 hx0 hk')
      (pStar_gt_bStar hS hA1 hx0 hk').le) h1
    exact V_explicit_of_H hS hA1 hx0 hk hL hR hlo (Or.inr (le_trans hA h1.le))

lemma H_of (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    StrictMonoOn (P.T m x0) (Icc (P.lo x0) (P.bStar m x0)) ∧
      StrictMonoOn (P.T m x0) (Ici (P.pStar m x0)) := by
  have := H_all hS hA1 hx0 (m - P.mStar x0 - 1)
  simp only at this
  rwa [show P.mStar x0 + 1 + (m - P.mStar x0 - 1) = m by omega] at this

lemma pStar_mono_m (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (hm : P.mStar x0 < m) :
    ∀ m', m ≤ m' → P.pStar m x0 ≤ P.pStar m' x0 := by
  intro m' hmm
  induction m', hmm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have hk' : P.mStar x0 < k := lt_of_lt_of_le hm hk
    exact le_trans ih (A1 hS hA1 hx0 hk' (H_of hS hA1 hx0 hk').1
      (H_of hS hA1 hx0 (by omega)).1)

end Compete

end PostQual.Incumbent.Params


open MeasureTheory Set intervalIntegral

namespace PostQual.Incumbent.Params

variable {P : Params}

section Final
variable (hS : P.Standing) (hA1 : P.Assumption1)
include hS hA1

lemma bStar_mono_x {m : ℕ} {x x' : ℝ} (hx : x ∈ Icc P.Rlo P.Rhi) (hx' : x' ∈ Icc P.Rlo P.Rhi)
    (hxx : x ≤ x') (hm : P.mStar x' < m) : P.bStar m x ≤ P.bStar m x' := by
  have hm0 : P.mStar x < m := lt_of_le_of_lt (mStar_mono hS hx hx' hxx) hm
  rw [bStar_eq hS hA1 hx hm0, bStar_eq hS hA1 hx' hm]
  exact csInf_le_csInf Sset_bddB (Sset_ne hS hx' hm) (fun b hb => Sset_mono_x hS hxx hb)

lemma Dk_mono_x {m : ℕ} (hm1 : 1 ≤ m) {x x' z : ℝ} (hxx : x' ≤ x) (hz : P.lo x ≤ z)
    (ha : P.Rlo + P.Δ < z) :
    P.Dk m (P.V (m - 1) x') x' z ≤ P.Dk m (P.V (m - 1) x) x z := by
  have h1 := V_diff_x hS (m - 1) x' x hxx z hz ha
  have hβ1 := St_β1 hS
  have hβ0 := St_β0 hS
  have h2 : (1 - P.β) ^ m ≤ (1 - P.β) ^ (m - 1) :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  have hg := gt_nonneg hS m z
  have e : P.Dk m (P.V (m - 1) x) x z - P.Dk m (P.V (m - 1) x') x' z =
      P.gt m z * ((1 - P.β) ^ m * (x' - x) + (P.V (m - 1) x' z - P.V (m - 1) x z)) := by
    unfold Dk Ad gt; ring
  have : 0 ≤ (1 - P.β) ^ m * (x' - x) + (P.V (m - 1) x' z - P.V (m - 1) x z) := by
    nlinarith
  nlinarith

/-- `A^m_2`: `p⋆_m` is nonincreasing in `x0`. -/
lemma pStar_anti_x {m : ℕ} {x x' : ℝ} (hx : x ∈ Icc P.Rlo P.Rhi) (hx' : x' ∈ Icc P.Rlo P.Rhi)
    (hxx : x' ≤ x) (hm : P.mStar x < m) : P.pStar m x ≤ P.pStar m x' := by
  have hm' : P.mStar x' < m := lt_of_le_of_lt (mStar_mono hS hx' hx hxx) hm
  have hm1 := m_pos hS hA1 hm
  by_contra hc
  push Not at hc
  -- facts at `x'`
  have hR' := (H_of hS hA1 hx' hm').2
  obtain ⟨_, _, hTeq', _⟩ := pStar_props hS hA1 hx' hm'
  obtain ⟨_, _, hTeq, _⟩ := pStar_props hS hA1 hx hm
  have hbx : P.bStar m x' ≤ P.bStar m x := bStar_mono_x hS hA1 hx' hx hxx hm
  have hbss : P.bStar m x ≤ P.bStarStar m x' := by
    rw [bStar_eq hS hA1 hx hm]
    exact le_trans (csInf_le_csSup (Sset_ne hS hx hm) Sset_bddB Sset_bddA)
      (csSup_le_csSup Sset_bddA (Sset_ne hS hx hm) (fun b hb => Sset_mono_x hS hxx hb))
  have hanti := (T_anti_mid hS hA1 hx' hm').antitoneOn
  have hT1 : P.T m x' (P.bStar m x) ≤ P.T m x' (P.bStar m x') :=
    hanti ⟨le_rfl, (bStar_lt_bSS hS hA1 hx' hm').le⟩ ⟨hbx, hbss⟩ hbx
  -- integral comparison
  have hlox : P.lo x ≤ P.bStar m x := bStar_ge_lo hS hA1 hx hm
  have hlox' : P.lo x' ≤ P.lo x := max_le_max le_rfl hxx
  have hbp := (pStar_gt_bStar hS hA1 hx hm).le
  have hI1 := T_sub hS (Good_all hS (m - 1) x') (le_trans hlox' hlox) hbp
  have hI2 := T_sub hS (Good_all hS (m - 1) x) hlox hbp
  have hcmp : ∫ z in P.bStar m x..P.pStar m x, P.Dk m (P.V (m - 1) x') x' z ≤
      ∫ z in P.bStar m x..P.pStar m x, P.Dk m (P.V (m - 1) x) x z := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hbp
      (Dk_ii hS (Good_all hS (m - 1) x') (le_trans hlox' hlox)
        (le_trans hlox' (le_trans hlox hbp)))
      (Dk_ii hS (Good_all hS (m - 1) x) hlox (le_trans hlox hbp))
    intro z hz
    exact Dk_mono_x hS hA1 hm1 hxx (le_trans hlox hz.1.le)
      (lt_of_le_of_lt (le_trans (lo_ge_a x) hlox) hz.1)
  have hlo2 : P.lo x' ≤ P.pStar m x' :=
    le_trans (bStar_ge_lo hS hA1 hx' hm') (pStar_gt_bStar hS hA1 hx' hm').le
  have hstrict := hR' (Set.self_mem_Ici) (show P.pStar m x ∈ Ici (P.pStar m x') from hc.le) hc
  linarith

/-- the maximiser of `T_m` on `[ℓ, p]` is `s⋆_m(x0; p)`. -/
lemma T_max_sStar {x0 : ℝ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) {m : ℕ} (hm1 : 1 ≤ m) {p : ℝ}
    (hp : P.lo x0 ≤ p) :
    P.sStar m x0 p ∈ Icc (P.lo x0) p ∧
      ∀ b ∈ Icc (P.lo x0) p, P.T m x0 b ≤ P.T m x0 (P.sStar m x0 p) := by
  unfold sStar
  split_ifs with hc
  · obtain ⟨hm, hpp⟩ := hc
    have hbs := bStar_ge_lo hS hA1 hx0 hm
    have hL := (H_of hS hA1 hx0 hm).1
    obtain ⟨_, _, hTeq, hlt⟩ := pStar_props hS hA1 hx0 hm
    refine ⟨⟨le_min hbs hp, min_le_right _ _⟩, ?_⟩
    intro b hb
    rcases le_total p (P.bStar m x0) with h | h
    · rw [min_eq_right h]
      exact hL.monotoneOn ⟨hb.1, le_trans hb.2 h⟩ ⟨hp, h⟩ hb.2
    · rw [min_eq_left h]
      rcases le_or_gt b (P.bStar m x0) with h1 | h1
      · exact hL.monotoneOn ⟨hb.1, h1⟩ ⟨hbs, le_rfl⟩ h1
      rcases lt_or_ge b (P.pStar m x0) with h2 | h2
      · exact (hlt b ⟨h1, h2⟩).le
      · rw [le_antisymm (le_trans hb.2 hpp) h2, hTeq]
  · refine ⟨⟨hp, le_rfl⟩, ?_⟩
    intro b hb
    push Not at hc
    by_cases hm : P.mStar x0 < m
    · have hpp := hc hm
      obtain ⟨hL, hR⟩ := H_of hS hA1 hx0 hm
      obtain ⟨_, _, hTeq, hlt⟩ := pStar_props hS hA1 hx0 hm
      have hbs := bStar_ge_lo hS hA1 hx0 hm
      have hpz : P.T m x0 (P.pStar m x0) ≤ P.T m x0 p :=
        hR.monotoneOn (Set.self_mem_Ici) (show p ∈ Ici (P.pStar m x0) from hpp.le) hpp.le
      rcases le_or_gt b (P.bStar m x0) with h1 | h1
      · have := hL.monotoneOn ⟨hb.1, h1⟩ ⟨hbs, le_rfl⟩ h1
        linarith
      rcases lt_or_ge b (P.pStar m x0) with h2 | h2
      · have := hlt b ⟨h1, h2⟩; linarith
      · exact hR.monotoneOn h2 (show p ∈ Ici (P.pStar m x0) from hpp.le) hb.2
    · push Not at hm
      exact fold_mono hS hA1 hx0 hm1 hm hb.1 hp hb.2

omit hS hA1 in
lemma sStar_le_p (m : ℕ) (x0 p : ℝ) : P.sStar m x0 p ≤ p := by
  unfold sStar; split_ifs
  · exact min_le_right _ _
  · exact le_rfl

end Final

end PostQual.Incumbent.Params

open PostQual.Incumbent PostQual.Incumbent.Params in
theorem PQ_theorem_2 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) :
    -- (i) m⋆ is well-defined: the minimized ratio is positive
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ b ∈ Set.Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ),
      0 < P.ratio x0 b) ∧
    -- (i) b⋆, p⋆ are well-defined and ordered
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ m : ℕ, 1 ≤ m → m ≤ P.N → P.mStar x0 < m →
      (P.Rlo + P.Δ < x0 →
        {b | b ∈ Set.Ioc x0 (P.Rhi + P.Δ) ∧ P.H b - P.L m b x0 < 0}.Nonempty) ∧
      IsLeast {b | P.bStar m x0 < b ∧
          0 ≤ P.Pi m b x0 (P.Rhi + P.Δ) - P.Pi m (P.bStar m x0) x0 (P.Rhi + P.Δ)}
        (P.pStar m x0) ∧
      x0 ≤ P.bStar m x0 ∧ P.bStar m x0 < P.pStar m x0 ∧
      (x0 ≠ P.Rlo + P.Δ → x0 < P.bStar m x0)) ∧
    -- (i) monotonicity
    MonotoneOn P.mStar (Set.Icc P.Rlo P.Rhi) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ P.N → ∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ x0' ∈ Set.Icc P.Rlo P.Rhi,
      x0 ≤ x0' → P.mStar x0' < m →
        P.bStar m x0 ≤ P.bStar m x0' ∧ P.pStar m x0' ≤ P.pStar m x0) ∧
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ m m' : ℕ, 1 ≤ m → m ≤ m' → m' ≤ P.N → P.mStar x0 < m →
      P.bStar m' x0 ≤ P.bStar m x0 ∧ P.pStar m x0 ≤ P.pStar m' x0) ∧
    -- (ii) s⋆ is a maximizer in (8)
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ m : ℕ, 1 ≤ m → m ≤ P.N → ∀ p, P.lo x0 ≤ p →
      P.sStar m x0 p ∈ Set.Icc (P.lo x0) p ∧
      (∀ b ∈ Set.Icc (P.lo x0) p, P.Pi m b x0 p ≤ P.Pi m (P.sStar m x0 p) x0 p) ∧
      P.V m x0 p = P.Pi m (P.sStar m x0 p) x0 p) ∧
    -- (ii) monotonicity of s⋆ in x0, p and m
    (∀ m : ℕ, 1 ≤ m → m ≤ P.N → ∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ x0' ∈ Set.Icc P.Rlo P.Rhi,
      x0 ≤ x0' → ∀ p, P.lo x0' ≤ p → P.sStar m x0 p ≤ P.sStar m x0' p) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ P.N → ∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ p p' : ℝ,
      P.lo x0 ≤ p → p ≤ p' → P.sStar m x0 p ≤ P.sStar m x0 p') ∧
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ m m' : ℕ, 1 ≤ m → m ≤ m' → m' ≤ P.N → ∀ p, P.lo x0 ≤ p →
      P.sStar m' x0 p ≤ P.sStar m x0 p) := by
  refine ⟨?_, ?_, mStar_mono hS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x0 _ b hb; exact ratio_pos hS hb
  · intro x0 hx0 m _ _ hm
    refine ⟨?_, (pStar_props hS hA1 hx0 hm).1, x0_le_bStar hS hA1 hx0 hm,
      pStar_gt_bStar hS hA1 hx0 hm, bStar_gt_x0 hS hA1 hx0 hm⟩
    intro hxa
    obtain ⟨b, hb⟩ := Sset_ne hS hx0 hm
    refine ⟨b, ?_, hb.2⟩
    have := hb.1; rwa [max_eq_left hxa.le] at this
  · intro m _ _ x0 hx0 x0' hx0' hxx hm
    exact ⟨bStar_mono_x hS hA1 hx0 hx0' hxx hm, pStar_anti_x hS hA1 hx0' hx0 hxx hm⟩
  · intro x0 hx0 m m' _ hmm _ hm
    exact ⟨bStar_anti_m hS hA1 hx0 hm hmm, pStar_mono_m hS hA1 hx0 hm m' hmm⟩
  · intro x0 hx0 m hm1 _ p hp
    obtain ⟨hs, hmax⟩ := T_max_sStar hS hA1 hx0 hm1 hp
    obtain ⟨hV, hle⟩ := V_of_max hS hm1 (Good_all hS (m - 1) x0) hs hmax
    exact ⟨hs, hle, hV⟩
  · intro m _ _ x0 hx0 x0' hx0' hxx p hp
    by_cases hc : P.mStar x0' < m ∧ p ≤ P.pStar m x0'
    · have hm0 : P.mStar x0 < m := lt_of_le_of_lt (mStar_mono hS hx0 hx0' hxx) hc.1
      have hp0 : p ≤ P.pStar m x0 := le_trans hc.2 (pStar_anti_x hS hA1 hx0' hx0 hxx hc.1)
      unfold sStar
      rw [if_pos hc, if_pos ⟨hm0, hp0⟩]
      exact min_le_min_right _ (bStar_mono_x hS hA1 hx0 hx0' hxx hc.1)
    · have : P.sStar m x0' p = p := by unfold sStar; rw [if_neg hc]
      rw [this]; exact sStar_le_p m x0 p
  · intro m _ _ x0 _ p p' _ hpp
    by_cases hc : P.mStar x0 < m ∧ p' ≤ P.pStar m x0
    · unfold sStar
      rw [if_pos hc, if_pos ⟨hc.1, le_trans hpp hc.2⟩]
      exact min_le_min_left _ hpp
    · have : P.sStar m x0 p' = p' := by unfold sStar; rw [if_neg hc]
      rw [this]; exact le_trans (sStar_le_p m x0 p) hpp
  · intro x0 hx0 m m' _ hmm _ p _
    by_cases hc : P.mStar x0 < m ∧ p ≤ P.pStar m x0
    · have hm' : P.mStar x0 < m' := lt_of_lt_of_le hc.1 hmm
      have hp' : p ≤ P.pStar m' x0 := le_trans hc.2 (pStar_mono_m hS hA1 hx0 hc.1 m' hmm)
      unfold sStar
      rw [if_pos hc, if_pos ⟨hm', hp'⟩]
      exact min_le_min_right _ (bStar_anti_m hS hA1 hx0 hc.1 hmm)
    · have : P.sStar m x0 p = p := by unfold sStar; rw [if_neg hc]
      rw [this]; exact sStar_le_p m' x0 p


open MeasureTheory Set intervalIntegral

namespace PostQual.Incumbent.Params

variable {P : Params}

lemma zeta_eq_zt (m : ℕ) (b x0 p : ℝ) : P.zeta m b x0 p = P.zt m b x0 / P.Fe (p - P.Δ) ^ m := by
  unfold zeta zt; ring

section
variable (hS : P.Standing) (hA1 : P.Assumption1)
include hS hA1

lemma M_ec8_ec9 {x0 : ℝ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) (m : ℕ) {p : ℝ} (hp : P.lo x0 < p) :
    (∀ b ∈ Set.Icc (P.lo x0) (P.Rhi + P.Δ),
      P.zeta m b x0 p = (1 - P.β) ^ m * P.Fe (b - P.Δ) ^ (m - 1) * (P.Fe (p - P.Δ) ^ m)⁻¹ *
        P.fe (b - P.Δ) * (P.H b - P.L m b x0)) ∧
    (∀ b ∈ Set.Ioi (P.Rhi + P.Δ),
      P.zeta m b x0 p = (1 - P.β) ^ m * (P.Fe (p - P.Δ) ^ m)⁻¹ ∧ 0 < P.zeta m b x0 p) := by
  have hFp : 0 < P.Fe (p - P.Δ) ^ m := pow_pos (Fes_pos hS (lt_of_le_of_lt (lo_ge_a x0) hp)) _
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [zeta_eq_zt, zt_eq_phi hS m x0 (le_trans (lo_ge_a x0) hb.1) hb.2]
    ring
  · intro b hb
    rw [zeta_eq_zt, zt_gt_c hS m x0 hb]
    refine ⟨by ring, div_pos (pow_pos (by linarith [St_β1 hS]) _) hFp⟩

lemma M_well_defined {x0 : ℝ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) {m : ℕ} (hm : P.mStar x0 < m) :
    (∃ b' ∈ Set.Ioo (P.lo x0) (P.Rhi + P.Δ), P.H b' < P.L m b' x0) ∧
    (∃ p' ≥ P.Rhi + P.Δ,
      0 < P.Pi m p' x0 (P.Rhi + P.Δ) - P.Pi m (P.bStar m x0) x0 (P.Rhi + P.Δ)) := by
  refine ⟨?_, ?_⟩
  · have hlt := bStar_lt_bSS hS hA1 hx0 hm
    set y := (P.bStar m x0 + P.bStarStar m x0) / 2
    have h1 : P.bStar m x0 < y := by simp only [y]; linarith
    have h2 : y < P.bStarStar m x0 := by simp only [y]; linarith
    have hy := phi_neg_mid hS hA1 hx0 hm h1 h2
    refine ⟨y, ⟨lt_of_le_of_lt (bStar_ge_lo hS hA1 hx0 hm) h1,
      lt_of_lt_of_le h2 (bSS_le_c hS hx0 hm)⟩, by linarith [hy.2]⟩
  · obtain ⟨_, _, hTeq, _⟩ := pStar_props hS hA1 hx0 hm
    have hR := (H_of hS hA1 hx0 hm).2
    set p' := max (P.Rhi + P.Δ) (P.pStar m x0 + 1)
    have hp'1 : P.pStar m x0 < p' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    refine ⟨p', le_max_left _ _, ?_⟩
    have hlo : P.lo x0 ≤ p' := le_trans (le_trans (bStar_ge_lo hS hA1 hx0 hm)
      (pStar_gt_bStar hS hA1 hx0 hm).le) hp'1.le
    rw [Pic_diff hS hA1 hx0 hm hlo]
    have := hR (Set.self_mem_Ici) (show p' ∈ Ici (P.pStar m x0) from hp'1.le) hp'1
    linarith

lemma M_ec12 {x' : ℝ} (hx' : x' ∈ Icc P.Rlo P.Rhi) {m' : ℕ} (hm' : P.mStar x' < m') {p : ℝ}
    (hp : P.lo x' < p) :
    (∀ b ∈ Set.Ico (P.lo x') (P.bStar m' x') ∪ Set.Ioi (P.bStarStar m' x'),
      0 < P.zeta m' b x' p) ∧
    (∀ b ∈ Set.Ioo (P.bStar m' x') (P.bStarStar m' x'), P.zeta m' b x' p < 0) := by
  have hFp : 0 < P.Fe (p - P.Δ) ^ m' := pow_pos (Fes_pos hS (lt_of_le_of_lt (lo_ge_a x') hp)) _
  refine ⟨?_, ?_⟩
  · rintro b (hb | hb)
    · rw [zeta_eq_zt]
      apply div_pos _ hFp
      rcases hb.1.lt_or_eq with h | h
      · exact zt_pos_left hS hA1 hx' hm' h hb.2
      · -- `b = ℓ < b⋆` forces `x' > a`, `ℓ = x'`
        have hxa : P.Rlo + P.Δ < x' := by
          by_contra hc; push Not at hc
          have : P.bStar m' x' = P.Rlo + P.Δ := by unfold bStar; rw [if_pos hc]
          have hl : P.lo x' = P.Rlo + P.Δ := max_eq_left hc
          rw [← h, hl, this] at hb; exact lt_irrefl _ hb.2
        have hl : P.lo x' = x' := max_eq_right hxa.le
        rw [← h, hl]
        have hc : x' ≤ P.Rhi + P.Δ := by linarith [hx'.2, Δ_pos hS]
        rw [zt_eq_phi hS m' x' hxa.le hc]
        apply mul_pos (zt_coef_pos hS m' hxa hc)
        have := H_pos hS hxa hc
        unfold L; simp; linarith
    · rw [zeta_eq_zt]; exact div_pos (zt_pos_right hS hA1 hx' hm' hb) hFp
  · intro b hb
    rw [zeta_eq_zt]; exact div_neg_of_neg_of_pos (zt_neg_mid hS hA1 hx' hm' hb.1 hb.2) hFp

lemma M_ec13_ec14 {x' : ℝ} (hx' : x' ∈ Icc P.Rlo P.Rhi) {m' : ℕ} (hm' : P.mStar x' < m') :
    (∀ m'' : ℕ, m' ≤ m'' → m'' ≤ P.N →
      P.bStarStar m'' x' < P.pStar m'' x' ∧ P.bStar m' x' ≤ P.bStarStar m'' x' ∧
        P.bStar m'' x' ≤ P.bStar m' x') ∧
    (∀ x'' ∈ Set.Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ), x'' ≤ x' →
      P.bStarStar m' x' < P.pStar m' x' ∧ P.bStar m' x'' ≤ P.bStarStar m' x' ∧
        P.bStarStar m' x' ≤ P.bStarStar m' x'') := by
  refine ⟨?_, ?_⟩
  · intro m'' hmm _
    have hm'' : P.mStar x' < m'' := lt_of_lt_of_le hm' hmm
    exact ⟨(pStar_props hS hA1 hx' hm'').2.1,
      le_trans (bStar_lt_bSS hS hA1 hx' hm').le (bSS_mono_m hS hA1 hx' hm' hmm),
      bStar_anti_m hS hA1 hx' hm' hmm⟩
  · intro x'' hx'' hxx
    have hx''I : x'' ∈ Icc P.Rlo P.Rhi :=
      ⟨by linarith [hx''.1, Δ_pos hS], le_trans hxx hx'.2⟩
    have hm'' : P.mStar x'' < m' := lt_of_le_of_lt (mStar_mono hS hx''I hx' hxx) hm'
    refine ⟨(pStar_props hS hA1 hx' hm').2.1,
      le_trans (bStar_mono_x hS hA1 hx''I hx' hxx hm') (bStar_lt_bSS hS hA1 hx' hm').le, ?_⟩
    exact csSup_le_csSup Sset_bddA (Sset_ne hS hx' hm') (fun b hb => Sset_mono_x hS hxx hb)

lemma M_lemma_EC_2 {x0 : ℝ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) {m' : ℕ} (hm' : P.mStar x0 < m') :
    (∀ p, P.lo x0 < p →
      StrictMonoOn (fun b => P.Pi m' b x0 p) (Set.Icc (P.lo x0) (P.bStar m' x0)) ∧
      StrictMonoOn (fun b => P.Pi m' b x0 p) (Set.Icc (P.pStar m' x0) p)) ∧
    (m' + 1 ≤ P.N → P.pStar m' x0 ≤ P.pStar (m' + 1) x0) ∧
    AntitoneOn (P.pStar m') {x | x ∈ Set.Icc P.Rlo P.Rhi ∧ P.mStar x < m'} := by
  have hm1 := m_pos hS hA1 hm'
  have hG := Good_all hS (m' - 1) x0
  obtain ⟨hL, hR⟩ := H_of hS hA1 hx0 hm'
  have hps : P.lo x0 ≤ P.pStar m' x0 :=
    le_trans (bStar_ge_lo hS hA1 hx0 hm') (pStar_gt_bStar hS hA1 hx0 hm').le
  refine ⟨?_, fun _ => pStar_mono_m hS hA1 hx0 hm' (m' + 1) (Nat.le_succ _), ?_⟩
  · intro p hp
    have hC : 0 < P.Fe (p - P.Δ) ^ m' := pow_pos (Fes_pos hS (lt_of_le_of_lt (lo_ge_a x0) hp)) _
    refine ⟨?_, ?_⟩
    · intro u hu v hv huv
      simp only
      rw [Pi_T hS hm1 hG hu.1 hp.le, Pi_T hS hm1 hG hv.1 hp.le]
      apply div_lt_div_of_pos_right _ hC
      linarith [hL hu hv huv]
    · intro u hu v hv huv
      simp only
      rw [Pi_T hS hm1 hG (le_trans hps hu.1) hp.le, Pi_T hS hm1 hG (le_trans hps hv.1) hp.le]
      apply div_lt_div_of_pos_right _ hC
      linarith [hR (show u ∈ Ici (P.pStar m' x0) from hu.1)
        (show v ∈ Ici (P.pStar m' x0) from hv.1) huv]
  · intro x hx y hy hxy
    exact pStar_anti_x hS hA1 hy.1 hx.1 hxy hy.2

lemma M_fold_only {x0 : ℝ} (hx0 : x0 ∈ Icc P.Rlo P.Rhi) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ P.mStar x0) {p : ℝ} (hp : P.lo x0 < p) :
    MonotoneOn (fun b => P.Pi m b x0 p) (Set.Icc (P.lo x0) p) ∧
    P.V m x0 p = (1 - P.β) ^ m * (p - x0) := by
  refine ⟨?_, fold_explicit hS hA1 hx0 m hm p hp⟩
  have hG := Good_all hS (m - 1) x0
  have hmono := fold_mono hS hA1 hx0 hm1 hm
  intro u hu v hv huv
  simp only
  rw [Pi_T hS hm1 hG hu.1 hp.le, Pi_T hS hm1 hG hv.1 hp.le]
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Fe_nonneg hS _) _)
  linarith [hmono hu.1 hv.1 huv]

end

end PostQual.Incumbent.Params

open PostQual.Incumbent PostQual.Incumbent.Params in
theorem solution (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x0 : ℝ) (hx0 : x0 ∈ Set.Icc P.Rlo P.Rhi) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ P.N)
    (hm : P.mStar x0 < m) :
    (∃ b' ∈ Set.Ioo (P.lo x0) (P.Rhi + P.Δ), P.H b' < P.L m b' x0) ∧
    (∃ p' ≥ P.Rhi + P.Δ,
      0 < P.Pi m p' x0 (P.Rhi + P.Δ) - P.Pi m (P.bStar m x0) x0 (P.Rhi + P.Δ)) :=
  M_well_defined hS hA1 hx0 hm
