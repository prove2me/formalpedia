-- Prove2me | solution 1 for PostQual.Incumbent.lemma_EC_1_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:02:10.780769+00:00
-- url     : https://prove2.me/submissions/febb2199-afc9-4194-9ba2-ad1287bdfb80

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

open PostQual.Incumbent PostQual.Incumbent.Params in
theorem solution (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x' : ℝ) (hx' : x' ∈ Set.Icc P.Rlo P.Rhi) (m' : ℕ) (hm'N : m' ≤ P.N) :
    MonotoneOn (fun p => P.V m' x' p) (Set.Ioi (P.lo x')) :=
  (Good_all hS m' x').1.mono Set.Ioi_subset_Ici_self
