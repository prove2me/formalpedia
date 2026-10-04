-- Prove2me | solution 1 for PorteusSS.conv_polya_mem_CK
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:00:39.846854+00:00
-- url     : https://prove2.me/submissions/2ff4d705-3791-44e9-8114-1e59df8b5b00

import Mathlib
import Definitions.Def_PorteusSS_Functions

set_option autoImplicit false

open Filter Topology Set

namespace PorteusSS
namespace Lib

section Core

open MeasureTheory

/-- Pointwise TP2 of `(x, t) ↦ φ (x - t)`: the `k = 2` determinant condition of `IsPF 2`. -/
def TP2 (φ : ℝ → ℝ) : Prop :=
  ∀ x1 x2 t1 t2 : ℝ, x1 < x2 → t1 < t2 → φ (x1 - t2) * φ (x2 - t1) ≤ φ (x1 - t1) * φ (x2 - t2)

variable {φ : ℝ → ℝ}

theorem tp2_weak (hT : TP2 φ) {x1 x2 t1 t2 : ℝ} (hx : x1 ≤ x2) (ht : t1 ≤ t2) :
    φ (x1 - t2) * φ (x2 - t1) ≤ φ (x1 - t1) * φ (x2 - t2) := by
  rcases hx.lt_or_eq with hx | hx
  · rcases ht.lt_or_eq with ht | ht
    · exact hT _ _ _ _ hx ht
    · subst ht; exact le_rfl
  · subst hx; rw [mul_comm]

/-- `conv h ψ w = ∫ t, h t * ψ (w - t)` (substitution `t = w - ξ`). -/
theorem conv_eq_t (h ψ : ℝ → ℝ) (w : ℝ) : conv h ψ w = ∫ t, h t * ψ (w - t) := by
  have := integral_sub_left_eq_self (fun t => h t * ψ (w - t)) (volume : Measure ℝ) w
  simp only [sub_sub_cancel] at this
  exact this

/-- **Ray case of (I)**: the interval masses of a TP2 function are TP2 under translation. -/
theorem ray_I (hφi : Integrable φ) (hT : TP2 φ) {x y z a b : ℝ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hab : a ≤ b) :
    (∫ u in (y - a)..(z - a), φ u) * (∫ u in (x - b)..(y - b), φ u) ≤
      (∫ u in (x - a)..(y - a), φ u) * (∫ u in (y - b)..(z - b), φ u) := by
  have e1 : (∫ u in (y - a)..(z - a), φ u) = ∫ v in y..z, φ (v - a) :=
    (intervalIntegral.integral_comp_sub_right φ a).symm
  have e2 : (∫ u in (x - b)..(y - b), φ u) = ∫ u in x..y, φ (u - b) :=
    (intervalIntegral.integral_comp_sub_right φ b).symm
  have e3 : (∫ u in (x - a)..(y - a), φ u) = ∫ u in x..y, φ (u - a) :=
    (intervalIntegral.integral_comp_sub_right φ a).symm
  have e4 : (∫ u in (y - b)..(z - b), φ u) = ∫ v in y..z, φ (v - b) :=
    (intervalIntegral.integral_comp_sub_right φ b).symm
  rw [e1, e2, e3, e4]
  have hi : ∀ (s p q : ℝ), IntervalIntegrable (fun u => φ (u - s)) volume p q :=
    fun s p q => (hφi.comp_sub_right s).intervalIntegrable
  have l1 : (∫ v in y..z, φ (v - a)) * (∫ u in x..y, φ (u - b)) =
      ∫ u in x..y, (∫ v in y..z, φ (v - a)) * φ (u - b) :=
    (intervalIntegral.integral_const_mul _ _).symm
  have l2 : (∫ u in x..y, φ (u - a)) * (∫ v in y..z, φ (v - b)) =
      ∫ u in x..y, φ (u - a) * (∫ v in y..z, φ (v - b)) :=
    (intervalIntegral.integral_mul_const _ _).symm
  rw [l1, l2]
  apply intervalIntegral.integral_mono_on hxy ((hi b x y).const_mul _) ((hi a x y).mul_const _)
  intro u hu
  have m1 : (∫ v in y..z, φ (v - a)) * φ (u - b) = ∫ v in y..z, φ (v - a) * φ (u - b) :=
    (intervalIntegral.integral_mul_const _ _).symm
  have m2 : φ (u - a) * (∫ v in y..z, φ (v - b)) = ∫ v in y..z, φ (u - a) * φ (v - b) :=
    (intervalIntegral.integral_const_mul _ _).symm
  rw [m1, m2]
  apply intervalIntegral.integral_mono_on hyz ((hi a y z).mul_const _) ((hi b y z).const_mul _)
  intro v hv
  have := tp2_weak hT (x1 := u) (x2 := v) (by linarith [hu.2, hv.1]) hab
  linarith

theorem integrable_ind_mul (hφi : Integrable φ) {S : Set ℝ} (hS : MeasurableSet S) (w : ℝ) :
    Integrable (fun t => S.indicator 1 t * φ (w - t)) := by
  have : (fun t => S.indicator 1 t * φ (w - t)) = S.indicator (fun t => φ (w - t)) := by
    funext t; by_cases ht : t ∈ S <;> simp [ht]
  rw [this]; exact (hφi.comp_sub_left w).indicator hS

/-- **Aggregated TP2**: a lower set `L` against a nonnegative weight living on `Lᶜ`. -/
theorem tp2_agg (hφi : Integrable φ) (hT : TP2 φ) {L : Set ℝ} (hL : IsLowerSet L)
    (hLm : MeasurableSet L) {W : ℝ → ℝ} (hW0 : ∀ t, 0 ≤ W t) (hWL : ∀ t ∈ L, W t = 0)
    (hWi : ∀ w, Integrable (fun t => W t * φ (w - t))) {x y : ℝ} (hxy : x ≤ y) :
    (∫ t, L.indicator 1 t * φ (y - t)) * (∫ t, W t * φ (x - t)) ≤
      (∫ t, L.indicator 1 t * φ (x - t)) * (∫ t, W t * φ (y - t)) := by
  rw [← integral_mul_const, ← integral_mul_const]
  apply integral_mono ((integrable_ind_mul hφi hLm y).mul_const _)
    ((integrable_ind_mul hφi hLm x).mul_const _)
  intro s
  by_cases hs : s ∈ L
  · simp only [Set.indicator_of_mem hs, Pi.one_apply, one_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_mono ((hWi x).const_mul _) ((hWi y).const_mul _)
    intro t
    by_cases ht : t ∈ L
    · simp [hWL t ht]
    · have hst : s ≤ t := by
        by_contra h
        push Not at h
        exact ht (hL h.le hs)
      have := mul_le_mul_of_nonneg_left (tp2_weak hT hxy hst) (hW0 t)
      nlinarith
  · simp [Set.indicator_of_notMem hs]

theorem integrable_ind_conv (hφi : Integrable φ) {S : Set ℝ} (hS : MeasurableSet S) (w : ℝ) :
    Integrable (fun ξ => S.indicator 1 (w - ξ) * φ ξ) := by
  refine hφi.bdd_mul (c := 1) ?_ (ae_of_all _ fun ξ => ?_)
  · exact ((measurable_one.indicator hS).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · by_cases h : w - ξ ∈ S <;> simp [h]

theorem conv_ind_anti (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) {L : Set ℝ} (hL : IsLowerSet L)
    (hLm : MeasurableSet L) {w w' : ℝ} (hww : w ≤ w') :
    conv (L.indicator 1) φ w' ≤ conv (L.indicator 1) φ w := by
  unfold conv
  apply integral_mono (integrable_ind_conv hφi hLm w') (integrable_ind_conv hφi hLm w)
  intro ξ
  by_cases h : w' - ξ ∈ L
  · have h' : w - ξ ∈ L := hL (by linarith) h
    simp [h, h']
  · simp only [Set.indicator_of_notMem h, zero_mul]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hφ0 ξ)

theorem conv_ind_mono (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) {V : Set ℝ} (hV : IsUpperSet V)
    (hVm : MeasurableSet V) {w w' : ℝ} (hww : w ≤ w') :
    conv (V.indicator 1) φ w ≤ conv (V.indicator 1) φ w' := by
  unfold conv
  apply integral_mono (integrable_ind_conv hφi hVm w) (integrable_ind_conv hφi hVm w')
  intro ξ
  by_cases h : w - ξ ∈ V
  · have h' : w' - ξ ∈ V := hV (by linarith) h
    simp [h, h']
  · simp only [Set.indicator_of_notMem h, zero_mul]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hφ0 ξ)

theorem conv_nonneg (hφ0 : ∀ t, 0 ≤ φ t) {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t) (w : ℝ) :
    0 ≤ conv h φ w :=
  integral_nonneg fun ξ => mul_nonneg (h0 _) (hφ0 ξ)

/-- **Ray case of (II)**: a lower set `L` against a `[0,K]`-valued `e` vanishing on `L`. -/
theorem ray_II (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hφ1 : ∫ t, φ t = 1) (hT : TP2 φ)
    {L : Set ℝ} (hL : IsLowerSet L) (hLm : MeasurableSet L) {e : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (he0 : ∀ t, 0 ≤ e t) (heK : ∀ t, e t ≤ K) (heL : ∀ t ∈ L, e t = 0) (hem : Measurable e)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv (L.indicator 1) φ y - conv (L.indicator 1) φ z) * (conv e φ y - conv e φ x) ≤
      (conv (L.indicator 1) φ x - conv (L.indicator 1) φ y) * (K - (conv e φ y - conv e φ z)) := by
  have hshift : ∀ w, ∫ t, φ (w - t) = 1 := fun w => by
    rw [integral_sub_left_eq_self φ volume w]; exact hφ1
  set W : ℝ → ℝ := fun t => K - e t - K * L.indicator 1 t with hWdef
  have hW0 : ∀ t, 0 ≤ W t := by
    intro t
    by_cases ht : t ∈ L
    · simp [hWdef, ht, heL t ht]
    · simp only [hWdef, Set.indicator_of_notMem ht, mul_zero, sub_zero]
      linarith [heK t]
  have hWK : ∀ t, W t ≤ K := by
    intro t
    by_cases ht : t ∈ L
    · simp [hWdef, ht, heL t ht, hK]
    · simp only [hWdef, Set.indicator_of_notMem ht, mul_zero, sub_zero]
      linarith [he0 t]
  have hWL : ∀ t ∈ L, W t = 0 := by intro t ht; simp [hWdef, ht, heL t ht]
  have hWm : Measurable W :=
    (measurable_const.sub hem).sub (measurable_const.mul (measurable_one.indicator hLm))
  have hWi : ∀ w, Integrable (fun t => W t * φ (w - t)) := fun w =>
    (hφi.comp_sub_left w).bdd_mul (c := K) hWm.aestronglyMeasurable (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 t)]; exact hWK t)
  have hEi : ∀ w, Integrable (fun t => e t * φ (w - t)) := fun w =>
    (hφi.comp_sub_left w).bdd_mul (c := K) hem.aestronglyMeasurable (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (he0 t)]; exact heK t)
  have hm : ∀ w, ∫ t, W t * φ (w - t) = K - conv e φ w - K * conv (L.indicator 1) φ w := by
    intro w
    rw [conv_eq_t, conv_eq_t]
    have : (fun t => W t * φ (w - t)) = fun t =>
        K * φ (w - t) - e t * φ (w - t) - K * (L.indicator 1 t * φ (w - t)) := by
      funext t; simp only [hWdef]; ring
    have i1 : Integrable (fun t => K * φ (w - t) - e t * φ (w - t)) :=
      ((hφi.comp_sub_left w).const_mul K).sub (hEi w)
    rw [this, integral_sub i1 ((integrable_ind_mul hφi hLm w).const_mul K),
      integral_sub ((hφi.comp_sub_left w).const_mul K) (hEi w), integral_const_mul,
      integral_const_mul, hshift]
    ring
  have hTT := tp2_agg hφi hT hL hLm hW0 hWL hWi hxy
  rw [hm, hm, ← conv_eq_t, ← conv_eq_t] at hTT
  have hmx0 : 0 ≤ K - conv e φ x - K * conv (L.indicator 1) φ x := by
    rw [← hm]; exact integral_nonneg fun t => mul_nonneg (hW0 t) (hφ0 _)
  have hmy0 : 0 ≤ K - conv e φ y - K * conv (L.indicator 1) φ y := by
    rw [← hm]; exact integral_nonneg fun t => mul_nonneg (hW0 t) (hφ0 _)
  have hpxy := conv_ind_anti hφ0 hφi hL hLm hxy
  have hpyz := conv_ind_anti hφ0 hφi hL hLm hyz
  have hpz := conv_nonneg hφ0 (Set.indicator_nonneg (fun _ _ => zero_le_one) : ∀ t, 0 ≤ L.indicator (1 : ℝ → ℝ) t) z
  have hEz := conv_nonneg hφ0 he0 z
  set px := conv (L.indicator 1) φ x
  set py := conv (L.indicator 1) φ y
  set pz := conv (L.indicator 1) φ z
  set Ex := conv e φ x
  set Ey := conv e φ y
  set Ez := conv e φ z
  set mx := K - Ex - K * px with hmx
  set my := K - Ey - K * py with hmy
  have key : 0 ≤ (px - pz) * my - (py - pz) * mx := by
    rcases le_total my mx with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h hpz]
    · nlinarith [mul_nonneg (sub_nonneg.2 hpxy) hmy0, mul_nonneg (sub_nonneg.2 hpyz) (sub_nonneg.2 h)]
  nlinarith [mul_nonneg (mul_nonneg hK (sub_nonneg.2 hpxy)) hpz, mul_nonneg (sub_nonneg.2 hpxy) hEz]

/-- `conv` of an indicator is the `φ`-mass of the reflected, translated set. -/
theorem conv_indicator {S : Set ℝ} (hS : MeasurableSet S) (w : ℝ) :
    conv (S.indicator 1) φ w = ∫ ξ in {ξ | w - ξ ∈ S}, φ ξ := by
  unfold conv
  have hS' : MeasurableSet {ξ : ℝ | w - ξ ∈ S} :=
    hS.preimage (measurable_const.sub measurable_id)
  rw [← integral_indicator hS']
  congr 1
  funext ξ
  by_cases h : w - ξ ∈ S <;> simp [h]

/-- **Layer cake** against the density `φ`, with integrability of the layer masses. -/
theorem layer_cake (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) {h : ℝ → ℝ} (hh0 : ∀ t, 0 ≤ h t)
    (hhm : Measurable h) (hhi : Integrable (fun ξ => h ξ * φ ξ)) :
    IntegrableOn (fun l => ∫ ξ in {ξ | l < h ξ}, φ ξ) (Ioi 0) ∧
      ∫ ξ, h ξ * φ ξ = ∫ l in Ioi 0, ∫ ξ in {ξ | l < h ξ}, φ ξ := by
  set μ : Measure ℝ := volume.withDensity (fun ξ => ENNReal.ofReal (φ ξ)) with hμ
  have hd : AEMeasurable (fun ξ => ENNReal.ofReal (φ ξ)) volume :=
    hφi.aemeasurable.ennreal_ofReal
  have hfin : ∀ᵐ ξ ∂(volume : Measure ℝ), ENNReal.ofReal (φ ξ) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hsm : ∀ ξ, (ENNReal.ofReal (φ ξ)).toReal • h ξ = h ξ * φ ξ := fun ξ => by
    rw [ENNReal.toReal_ofReal (hφ0 ξ), smul_eq_mul, mul_comm]
  have hint : Integrable h μ := by
    rw [hμ, integrable_withDensity_iff_integrable_smul₀' hd hfin]
    simp only [hsm]
    exact hhi
  have hlhs : ∫ ξ, h ξ ∂μ = ∫ ξ, h ξ * φ ξ := by
    rw [hμ, integral_withDensity_eq_integral_toReal_smul₀ hd hfin]
    simp only [hsm]
  have hmeas : ∀ l : ℝ, μ.real {ξ | l < h ξ} = ∫ ξ in {ξ | l < h ξ}, φ ξ := by
    intro l
    have hS : MeasurableSet {ξ | l < h ξ} := measurableSet_lt measurable_const hhm
    rw [measureReal_def, hμ, withDensity_apply _ hS,
      ← ofReal_integral_eq_lintegral_ofReal hφi.integrableOn (ae_of_all _ hφ0),
      ENNReal.toReal_ofReal (setIntegral_nonneg hS fun ξ _ => hφ0 ξ)]
  have key := hint.integral_eq_integral_meas_lt (ae_of_all _ hh0)
  simp only [hmeas] at key
  refine ⟨?_, by rw [← hlhs, key]⟩
  have hlint := lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hh0) hint.aemeasurable
  have hne : ∫⁻ l in Ioi 0, μ {ξ | l < h ξ} ≠ ⊤ := by
    rw [← hlint]; exact hint.lintegral_lt_top.ne
  have hanti : Antitone (fun l : ℝ => μ {ξ | l < h ξ}) := fun s t hst =>
    measure_mono fun ξ hx => lt_of_le_of_lt hst hx
  have hI := integrable_toReal_of_lintegral_ne_top hanti.measurable.aemeasurable hne
  refine hI.congr (ae_of_all _ fun l => ?_)
  simp only
  rw [← measureReal_def, hmeas]

/-- **Layer-cake reduction** of a three-point linear functional to the level sets. -/
theorem lc3_nonpos (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t)
    (hfm : Measurable f) (hfi : ∀ w, Integrable (fun ξ => f (w - ξ) * φ ξ)) (x y z c1 c2 c3 : ℝ)
    (h : ∀ l : ℝ, 0 < l → c1 * conv ({t | l < f t}.indicator 1) φ x +
      c2 * conv ({t | l < f t}.indicator 1) φ y + c3 * conv ({t | l < f t}.indicator 1) φ z ≤ 0) :
    c1 * conv f φ x + c2 * conv f φ y + c3 * conv f φ z ≤ 0 := by
  have hc : ∀ w, IntegrableOn (fun l => conv ({t | l < f t}.indicator 1) φ w) (Ioi 0) ∧
      conv f φ w = ∫ l in Ioi 0, conv ({t | l < f t}.indicator 1) φ w := by
    intro w
    have hm : Measurable (fun ξ => f (w - ξ)) := hfm.comp (measurable_const.sub measurable_id)
    obtain ⟨h1, h2⟩ := layer_cake hφ0 hφi (fun ξ => hf0 (w - ξ)) hm (hfi w)
    have hset : ∀ l : ℝ, conv ({t | l < f t}.indicator 1) φ w = ∫ ξ in {ξ | l < f (w - ξ)}, φ ξ :=
      fun l => conv_indicator (measurableSet_lt measurable_const hfm) w
    simp only [hset]
    exact ⟨h1, h2⟩
  obtain ⟨ix, ex⟩ := hc x
  obtain ⟨iy, ey⟩ := hc y
  obtain ⟨iz, ez⟩ := hc z
  have hsum : ∫ l in Ioi 0, (c1 * conv ({t | l < f t}.indicator 1) φ x +
      c2 * conv ({t | l < f t}.indicator 1) φ y + c3 * conv ({t | l < f t}.indicator 1) φ z) =
      c1 * conv f φ x + c2 * conv f φ y + c3 * conv f φ z := by
    have i1 : Integrable (fun l => c1 * conv ({t | l < f t}.indicator 1) φ x)
        (volume.restrict (Ioi 0)) := ix.const_mul c1
    have i2 : Integrable (fun l => c2 * conv ({t | l < f t}.indicator 1) φ y)
        (volume.restrict (Ioi 0)) := iy.const_mul c2
    have i3 : Integrable (fun l => c3 * conv ({t | l < f t}.indicator 1) φ z)
        (volume.restrict (Ioi 0)) := iz.const_mul c3
    have i12 : Integrable (fun l => c1 * conv ({t | l < f t}.indicator 1) φ x +
        c2 * conv ({t | l < f t}.indicator 1) φ y) (volume.restrict (Ioi 0)) := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, ← ex, ← ey, ← ez]
  rw [← hsum]
  exact setIntegral_nonpos measurableSet_Ioi fun l hl => h l hl

/-- A set squeezed between `Iio a` and `Iic a`: `conv` of its indicator is a tail mass. -/
theorem conv_ind_lower (hφi : Integrable φ) {L : Set ℝ} {a : ℝ} (h1 : Iio a ⊆ L)
    (h2 : L ⊆ Iic a) (hLm : MeasurableSet L) (w : ℝ) :
    conv (L.indicator 1) φ w = (∫ ξ, φ ξ) - ∫ ξ in Iic (w - a), φ ξ := by
  rw [conv_indicator hLm]
  have hS : {ξ | w - ξ ∈ L} =ᵐ[volume] Ioi (w - a) := by
    have hsub1 : {ξ | w - ξ ∈ L} ⊆ Ici (w - a) := fun ξ hξ => by
      have := h2 hξ
      simp only [mem_Iic] at this
      simp only [mem_Ici]
      linarith
    have hsub2 : Ioi (w - a) ⊆ {ξ | w - ξ ∈ L} := fun ξ hξ => h1 (by
      simp only [mem_Ioi] at hξ
      simp only [mem_Iio]
      linarith)
    apply EventuallyLE.antisymm
    · exact (ae_le_set.2 (by rw [sdiff_eq_empty.2 hsub1, measure_empty])).trans
        Ioi_ae_eq_Ici.symm.le
    · exact ae_le_set.2 (by rw [sdiff_eq_empty.2 hsub2, measure_empty])
  rw [setIntegral_congr_set hS]
  have := integral_add_compl (measurableSet_Iic (a := w - a)) hφi
  rw [compl_Iic] at this
  linarith

/-- A set squeezed between `Ioi b` and `Ici b`: `conv` of its indicator is a CDF value. -/
theorem conv_ind_upper {V : Set ℝ} {b : ℝ} (h1 : Ioi b ⊆ V) (h2 : V ⊆ Ici b)
    (hVm : MeasurableSet V) (w : ℝ) :
    conv (V.indicator 1) φ w = ∫ ξ in Iic (w - b), φ ξ := by
  rw [conv_indicator hVm]
  have hS : {ξ | w - ξ ∈ V} =ᵐ[volume] Iic (w - b) := by
    have hsub1 : {ξ | w - ξ ∈ V} ⊆ Iic (w - b) := fun ξ hξ => by
      have := h2 hξ
      simp only [mem_Ici] at this
      simp only [mem_Iic]
      linarith
    have hsub2 : Iio (w - b) ⊆ {ξ | w - ξ ∈ V} := fun ξ hξ => h1 (by
      simp only [mem_Iio] at hξ
      simp only [mem_Ioi]
      linarith)
    apply EventuallyLE.antisymm
    · exact ae_le_set.2 (by rw [sdiff_eq_empty.2 hsub1, measure_empty])
    · exact Iio_ae_eq_Iic.symm.le.trans
        (ae_le_set.2 (by rw [sdiff_eq_empty.2 hsub2, measure_empty]))
  rw [setIntegral_congr_set hS]

/-- Ray case of (I) for a lower set `L ⊆ (-∞,0)` and an upper set `V ⊆ [0,∞)`. -/
theorem ray_I_sets (hφi : Integrable φ) (hT : TP2 φ) {L V : Set ℝ} (hL : IsLowerSet L)
    (hV : IsUpperSet V) (hLm : MeasurableSet L) (hVm : MeasurableSet V) (hLneg : ∀ t ∈ L, t < 0)
    (hVpos : ∀ t ∈ V, 0 ≤ t) {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv (L.indicator 1) φ y - conv (L.indicator 1) φ z) *
        (conv (V.indicator 1) φ y - conv (V.indicator 1) φ x) ≤
      (conv (L.indicator 1) φ x - conv (L.indicator 1) φ y) *
        (conv (V.indicator 1) φ z - conv (V.indicator 1) φ y) := by
  rcases L.eq_empty_or_nonempty with hL0 | hLne
  · subst hL0; simp [conv]
  rcases V.eq_empty_or_nonempty with hV0 | hVne
  · subst hV0; simp [conv]
  have hLb : BddAbove L := ⟨0, fun t ht => (hLneg t ht).le⟩
  have hVb : BddBelow V := ⟨0, fun t ht => hVpos t ht⟩
  set a := sSup L with ha
  set b := sInf V with hb
  have ha0 : a ≤ 0 := csSup_le hLne fun t ht => (hLneg t ht).le
  have hb0 : 0 ≤ b := le_csInf hVne hVpos
  have hL1 : Iio a ⊆ L := fun t ht => by
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hLne ht
    exact hL hts.le hs
  have hL2 : L ⊆ Iic a := fun t ht => le_csSup hLb ht
  have hV1 : Ioi b ⊆ V := fun t ht => by
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hVne ht
    exact hV hst.le hs
  have hV2 : V ⊆ Ici b := fun t ht => csInf_le hVb ht
  have hIic : ∀ c : ℝ, IntegrableOn φ (Iic c) := fun c => hφi.integrableOn
  have dL : ∀ p q : ℝ, conv (L.indicator 1) φ p - conv (L.indicator 1) φ q =
      ∫ u in (p - a)..(q - a), φ u := fun p q => by
    rw [conv_ind_lower hφi hL1 hL2 hLm, conv_ind_lower hφi hL1 hL2 hLm,
      ← intervalIntegral.integral_Iic_sub_Iic (hIic _) (hIic _)]
    ring
  have dV : ∀ p q : ℝ, conv (V.indicator 1) φ q - conv (V.indicator 1) φ p =
      ∫ u in (p - b)..(q - b), φ u := fun p q => by
    rw [conv_ind_upper hV1 hV2 hVm, conv_ind_upper hV1 hV2 hVm,
      intervalIntegral.integral_Iic_sub_Iic (hIic _) (hIic _)]
  rw [dL, dL, dV, dV]
  exact ray_I hφi hT hxy hyz (by linarith)

/-- (I) for a fixed lower set `L` and a general monotone `B ≥ 0` vanishing on `(-∞,0)`. -/
theorem ineq_I_L (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hT : TP2 φ) {L : Set ℝ}
    (hL : IsLowerSet L) (hLm : MeasurableSet L) (hLneg : ∀ t ∈ L, t < 0) {B : ℝ → ℝ}
    (hB : Monotone B) (hB0 : ∀ t, 0 ≤ B t) (hBz : ∀ t, t < 0 → B t = 0)
    (hBi : ∀ w, Integrable (fun ξ => B (w - ξ) * φ ξ)) {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv (L.indicator 1) φ y - conv (L.indicator 1) φ z) * (conv B φ y - conv B φ x) ≤
      (conv (L.indicator 1) φ x - conv (L.indicator 1) φ y) * (conv B φ z - conv B φ y) := by
  set β := conv (L.indicator 1) φ y - conv (L.indicator 1) φ z
  set α := conv (L.indicator 1) φ x - conv (L.indicator 1) φ y
  have := lc3_nonpos hφ0 hφi hB0 hB.measurable hBi x y z (-β) (β + α) (-α) ?_
  · linarith
  · intro l hl
    have hV : IsUpperSet {t | l < B t} := fun s t hst hs => lt_of_lt_of_le hs (hB hst)
    have hVm : MeasurableSet {t | l < B t} := measurableSet_lt measurable_const hB.measurable
    have hVpos : ∀ t ∈ {t | l < B t}, 0 ≤ t := by
      intro t ht
      by_contra h
      push Not at h
      rw [mem_ofPred_eq, hBz t h] at ht
      linarith
    have := ray_I_sets hφi hT hL hV hLm hVm hLneg hVpos hxy hyz
    linarith

/-- **Inequality (I)**: `β γ ≤ α δ` for the antitone left part `A` and monotone right part `B`. -/
theorem ineq_I (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hT : TP2 φ) {A B : ℝ → ℝ}
    (hA : Antitone A) (hB : Monotone B) (hA0 : ∀ t, 0 ≤ A t) (hB0 : ∀ t, 0 ≤ B t)
    (hAz : ∀ t, 0 ≤ t → A t = 0) (hBz : ∀ t, t < 0 → B t = 0)
    (hAi : ∀ w, Integrable (fun ξ => A (w - ξ) * φ ξ))
    (hBi : ∀ w, Integrable (fun ξ => B (w - ξ) * φ ξ)) {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv A φ y - conv A φ z) * (conv B φ y - conv B φ x) ≤
      (conv A φ x - conv A φ y) * (conv B φ z - conv B φ y) := by
  set γ := conv B φ y - conv B φ x
  set δ := conv B φ z - conv B φ y
  have := lc3_nonpos hφ0 hφi hA0 hA.measurable hAi x y z (-δ) (γ + δ) (-γ) ?_
  · linarith
  · intro l hl
    have hL : IsLowerSet {t | l < A t} := fun s t hts hs => lt_of_lt_of_le hs (hA hts)
    have hLm : MeasurableSet {t | l < A t} := measurableSet_lt measurable_const hA.measurable
    have hLneg : ∀ t ∈ {t | l < A t}, t < 0 := by
      intro t ht
      by_contra h
      push Not at h
      rw [mem_ofPred_eq, hAz t h] at ht
      linarith
    have := ineq_I_L hφ0 hφi hT hL hLm hLneg hB hB0 hBz hBi hxy hyz
    linarith

/-- **Inequality (II)**: `β b₁ ≤ α (K - b₂)` for the antitone left part `A` and the
`[0,K]`-valued remainder `e` vanishing on `(-∞,0)`. -/
theorem ineq_II (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hφ1 : ∫ t, φ t = 1) (hT : TP2 φ)
    {A e : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hA : Antitone A) (hA0 : ∀ t, 0 ≤ A t)
    (hAz : ∀ t, 0 ≤ t → A t = 0) (hAi : ∀ w, Integrable (fun ξ => A (w - ξ) * φ ξ))
    (he0 : ∀ t, 0 ≤ e t) (heK : ∀ t, e t ≤ K) (hez : ∀ t, t < 0 → e t = 0) (hem : Measurable e)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv A φ y - conv A φ z) * (conv e φ y - conv e φ x) ≤
      (conv A φ x - conv A φ y) * (K - (conv e φ y - conv e φ z)) := by
  set b1 := conv e φ y - conv e φ x
  set b2 := conv e φ y - conv e φ z
  have := lc3_nonpos hφ0 hφi hA0 hA.measurable hAi x y z (-(K - b2)) (b1 + (K - b2)) (-b1) ?_
  · linarith
  · intro l hl
    have hL : IsLowerSet {t | l < A t} := fun s t hts hs => lt_of_lt_of_le hs (hA hts)
    have hLm : MeasurableSet {t | l < A t} := measurableSet_lt measurable_const hA.measurable
    have heL : ∀ t ∈ {t | l < A t}, e t = 0 := by
      intro t ht
      apply hez
      by_contra h
      push Not at h
      rw [mem_ofPred_eq, hAz t h] at ht
      linarith
    have := ray_II hφ0 hφi hφ1 hT hL hLm hK he0 heK heL hem hxy hyz
    linarith

/-- The decomposition `g = c + A + B + e` of a function of class `C_0(K)`:
`A ≥ 0` antitone and supported in `(-∞,0)`, `B ≥ 0` monotone and supported in `[0,∞)`,
`e ∈ [0,K]` supported in `[0,∞)`. (`B = M - c` with `M t = inf_{v ≥ t} g v`.) -/
theorem decomp {g : ℝ → ℝ} {K : ℝ} (hgm : Measurable g) (hgA : AntitoneOn g (Iio 0))
    (hgK : NonKDecreasingOn g K (Ici 0)) (hgb : BddBelow (g '' Iio 0)) :
    ∃ (c : ℝ) (A B e : ℝ → ℝ), (∀ t, g t = c + A t + B t + e t) ∧ Antitone A ∧ Monotone B ∧
      (∀ t, 0 ≤ A t) ∧ (∀ t, 0 ≤ B t) ∧ (∀ t, 0 ≤ e t) ∧ (∀ t, e t ≤ K) ∧
      (∀ t, 0 ≤ t → A t = 0) ∧ (∀ t, t < 0 → B t = 0) ∧ (∀ t, t < 0 → e t = 0) ∧
      Measurable e ∧ (∀ t, A t ≤ g t - c) ∧ (∀ t, B t ≤ g t - c) := by
  have hK0 : 0 ≤ K := by
    have := hgK 0 (mem_Ici.2 le_rfl) 0 (mem_Ici.2 le_rfl) le_rfl
    linarith
  obtain ⟨c1, hc1⟩ := hgb
  set c := min c1 (g 0 - K) with hc
  have hgc : ∀ t, c ≤ g t := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · exact (min_le_left _ _).trans (hc1 ⟨t, ht, rfl⟩)
    · have := hgK 0 (mem_Ici.2 le_rfl) t (mem_Ici.2 ht) ht
      exact (min_le_right _ _).trans (by linarith)
  have hbdd : ∀ t : ℝ, BddBelow (range fun v : Ici t => g v) := fun t =>
    ⟨c, by rintro _ ⟨v, rfl⟩; exact hgc v⟩
  set M : ℝ → ℝ := fun t => ⨅ v : Ici t, g v with hM
  have hMle : ∀ t, M t ≤ g t := fun t => ciInf_le (hbdd t) ⟨t, mem_Ici.2 le_rfl⟩
  have hMge : ∀ t, c ≤ M t := fun t => le_ciInf fun v => hgc v
  have hMK : ∀ t, 0 ≤ t → g t - K ≤ M t := fun t ht => le_ciInf fun v => by
    have := hgK t (mem_Ici.2 ht) v (mem_Ici.2 (le_trans ht v.2)) v.2
    linarith
  have hMmono : Monotone M := fun s t hst =>
    le_ciInf fun v => ciInf_le (hbdd s) ⟨v, mem_Ici.2 (le_trans hst v.2)⟩
  refine ⟨c, fun t => if t < 0 then g t - c else 0, fun t => if t < 0 then 0 else M t - c,
    fun t => if t < 0 then 0 else g t - M t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; ring
    · simp only [if_neg ht]; ring
  · intro s t hst
    by_cases ht : t < 0
    · have hs : s < 0 := lt_of_le_of_lt hst ht
      simp only [if_pos ht, if_pos hs]
      linarith [hgA (mem_Iio.2 hs) (mem_Iio.2 ht) hst]
    · simp only [if_neg ht]
      by_cases hs : s < 0
      · simp only [if_pos hs]; linarith [hgc s]
      · simp only [if_neg hs]; exact le_rfl
  · intro s t hst
    by_cases hs : s < 0
    · simp only [if_pos hs]
      by_cases ht : t < 0
      · simp only [if_pos ht]; exact le_rfl
      · simp only [if_neg ht]; linarith [hMge t]
    · have ht : ¬ t < 0 := fun ht => hs (lt_of_le_of_lt hst ht)
      simp only [if_neg hs, if_neg ht]
      linarith [hMmono hst]
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; linarith [hgc t]
    · simp only [if_neg ht]; exact le_rfl
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; exact le_rfl
    · simp only [if_neg ht]; linarith [hMge t]
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; exact le_rfl
    · simp only [if_neg ht]; linarith [hMle t]
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; exact hK0
    · simp only [if_neg ht]; linarith [hMK t (not_lt.1 ht)]
  · intro t ht
    simp only [if_neg (not_lt.2 ht)]
  · intro t ht
    simp only [if_pos ht]
  · intro t ht
    simp only [if_pos ht]
  · exact Measurable.ite measurableSet_Iio measurable_const (hgm.sub hMmono.measurable)
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; exact le_rfl
    · simp only [if_neg ht]; linarith [hgc t]
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; linarith [hgc t]
    · simp only [if_neg ht]; linarith [hMle t]

/-- **CORE LEMMA (S2).** Convolution with a TP2 probability density `φ` maps the class `C_0(K)`
(antitone on `(-∞,0)`, non-`K`-decreasing on `[0,∞)`) into quasi-`K`-convex functions:
for `x < y < z`, `F y ≤ max (F x) (F z + K)` where `F = conv g φ`. -/
theorem conv_quasiK {φ g : ℝ → ℝ} {K : ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) (hT : TP2 φ) (hgm : Measurable g) (hgA : AntitoneOn g (Iio 0))
    (hgK : NonKDecreasingOn g K (Ici 0)) (hgb : BddBelow (g '' Iio 0))
    (hgi : ∀ w, Integrable (fun ξ => g (w - ξ) * φ ξ)) {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    conv g φ y ≤ max (conv g φ x) (conv g φ z + K) := by
  have hK : 0 ≤ K := by
    have := hgK 0 (mem_Ici.2 le_rfl) 0 (mem_Ici.2 le_rfl) le_rfl
    linarith
  obtain ⟨c, A, B, e, hdec, hA, hB, hA0, hB0, he0, heK, hAz, hBz, hez, hem, hAg, hBg⟩ :=
    decomp hgm hgA hgK hgb
  have hgc : ∀ w, Integrable (fun ξ => (g (w - ξ) - c) * φ ξ) := fun w => by
    have := (hgi w).sub (hφi.const_mul c)
    refine this.congr (ae_of_all _ fun ξ => ?_)
    simp only [Pi.sub_apply]
    ring
  have dom : ∀ h : ℝ → ℝ, Measurable h → (∀ t, 0 ≤ h t) → (∀ t, h t ≤ g t - c) →
      ∀ w, Integrable (fun ξ => h (w - ξ) * φ ξ) := by
    intro h hm h0 hle w
    refine (hgc w).mono ((hm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hφi.aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
    have hle' := hle (w - ξ)
    have h0' := h0 (w - ξ)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg h0',
      Real.norm_of_nonneg (show 0 ≤ g (w - ξ) - c by linarith)]
    exact mul_le_mul_of_nonneg_right hle' (norm_nonneg _)
  have hAi := dom A hA.measurable hA0 hAg
  have hBi := dom B hB.measurable hB0 hBg
  have hei : ∀ w, Integrable (fun ξ => e (w - ξ) * φ ξ) := fun w =>
    hφi.bdd_mul (c := K) (hem.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun ξ => by rw [Real.norm_eq_abs, abs_of_nonneg (he0 _)]; exact heK _)
  have hF : ∀ w, conv g φ w = c + conv A φ w + conv B φ w + conv e φ w := by
    intro w
    unfold conv
    have : (fun ξ => g (w - ξ) * φ ξ) = fun ξ =>
        c * φ ξ + A (w - ξ) * φ ξ + B (w - ξ) * φ ξ + e (w - ξ) * φ ξ := by
      funext ξ; rw [hdec (w - ξ)]; ring
    have i1 : Integrable (fun ξ => c * φ ξ + A (w - ξ) * φ ξ) := (hφi.const_mul c).add (hAi w)
    have i2 : Integrable (fun ξ => c * φ ξ + A (w - ξ) * φ ξ + B (w - ξ) * φ ξ) :=
      i1.add (hBi w)
    rw [this, integral_add i2 (hei w), integral_add i1 (hBi w),
      integral_add (hφi.const_mul c) (hAi w), integral_const_mul, hφ1, mul_one]
  have hI := ineq_I hφ0 hφi hT hA hB hA0 hB0 hAz hBz hAi hBi hxy.le hyz.le
  have hII := ineq_II hφ0 hφi hφ1 hT hK hA hA0 hAz hAi he0 heK hez hem hxy.le hyz.le
  have hα : conv A φ y ≤ conv A φ x :=
    integral_mono (hAi y) (hAi x) fun ξ =>
      mul_le_mul_of_nonneg_right (hA (by linarith : x - ξ ≤ y - ξ)) (hφ0 ξ)
  have hδ : conv B φ y ≤ conv B φ z :=
    integral_mono (hBi y) (hBi z) fun ξ =>
      mul_le_mul_of_nonneg_right (hB (by linarith : y - ξ ≤ z - ξ)) (hφ0 ξ)
  have hEy : conv e φ y ≤ K := by
    have := integral_mono (hei y) (hφi.const_mul K) fun ξ =>
      mul_le_mul_of_nonneg_right (heK (y - ξ)) (hφ0 ξ)
    rw [integral_const_mul, hφ1, mul_one] at this
    exact this
  have hEz := conv_nonneg hφ0 he0 z
  have hFx := hF x
  have hFy := hF y
  have hFz := hF z
  by_contra hcon
  push Not at hcon
  rw [max_lt_iff] at hcon
  obtain ⟨h1, h2⟩ := hcon
  set α := conv A φ x - conv A φ y with hαd
  set β := conv A φ y - conv A φ z with hβd
  set γ := conv B φ y - conv B φ x with hγd
  set δ := conv B φ z - conv B φ y with hδd
  set b1 := conv e φ y - conv e φ x with hb1d
  set b2 := conv e φ y - conv e φ z with hb2d
  have k1 : 0 < γ + b1 - α := by linarith
  have k2 : δ + K - b2 < β := by linarith
  have hβpos : 0 < β := by linarith
  nlinarith [mul_pos hβpos k1, mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 k2.le)]

/-- The same, in the Definitions' `QuasiKConvexOn` form. -/
theorem conv_quasiKConvexOn {φ g : ℝ → ℝ} {K : ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) (hT : TP2 φ) (hgm : Measurable g) (hgA : AntitoneOn g (Iio 0))
    (hgK : NonKDecreasingOn g K (Ici 0)) (hgb : BddBelow (g '' Iio 0))
    (hgi : ∀ w, Integrable (fun ξ => g (w - ξ) * φ ξ)) :
    QuasiKConvexOn (conv g φ) K univ := by
  have hK : 0 ≤ K := by
    have := hgK 0 (mem_Ici.2 le_rfl) 0 (mem_Ici.2 le_rfl) le_rfl
    linarith
  refine ⟨convex_univ, fun x _ y _ hxy l hl0 hl1 => ?_⟩
  have h1 : x ≤ l * x + (1 - l) * y := by nlinarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hxy)]
  have h2 : l * x + (1 - l) * y ≤ y := by nlinarith [mul_nonneg hl0 (sub_nonneg.2 hxy)]
  rcases h1.lt_or_eq with h1 | h1
  · rcases h2.lt_or_eq with h2 | h2
    · exact conv_quasiK hφ0 hφi hφ1 hT hgm hgA hgK hgb hgi h1 h2
    · rw [h2]; exact le_max_of_le_right (by linarith)
  · rw [← h1]; exact le_max_left _ _

/-- `IsPF n` with `1 ≤ n` forces `φ ≥ 0` (the `k = 1` determinant). -/
theorem nonneg_of_isPF {n : ℕ} (hn : 1 ≤ n) (h : IsPF n φ) (t : ℝ) : 0 ≤ φ t := by
  have := h.2 1 le_rfl hn ![t] ![0] (Subsingleton.strictMono _) (Subsingleton.strictMono _)
  simpa [Matrix.det_fin_one] using this

/-- `IsPF n` with `2 ≤ n` gives the pointwise `TP2` inequality (the `k = 2` determinant). -/
theorem tp2_of_isPF {n : ℕ} (hn : 2 ≤ n) (h : IsPF n φ) : TP2 φ := by
  intro x1 x2 t1 t2 hx ht
  have hxm : StrictMono ![x1, x2] := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simpa using hx
  have htm : StrictMono ![t1, t2] := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simpa using ht
  have := h.2 2 (by norm_num) hn ![x1, x2] ![t1, t2] hxm htm
  rw [Matrix.det_fin_two] at this
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  linarith

/-- The four facts about a Pólya density that the core lemma uses. -/
theorem polya_facts (h : IsPolyaDensity φ) :
    (∀ t, 0 ≤ φ t) ∧ Integrable φ ∧ ∫ t, φ t = 1 ∧ TP2 φ := by
  have h2 := h.1 2 (by norm_num)
  exact ⟨nonneg_of_isPF (by norm_num) h2, h2.1.1, h.2, tp2_of_isPF le_rfl h2⟩

end Core

section S3x
open MeasureTheory
theorem measurable_of_piecewiseContinuous {f : ℝ → ℝ} (h : PiecewiseContinuousOn f univ) :
    Measurable f := by
  obtain ⟨A, -, hcont, -⟩ := h
  have hAm : MeasurableSet (↑A : Set ℝ) := A.measurableSet
  refine measurable_of_restrict_of_restrict_compl hAm ?_ ?_
  · exact measurable_of_countable _
  · have h2 : ContinuousOn f (↑A : Set ℝ)ᶜ := by
      rw [compl_eq_univ_sdiff]; exact hcont
    exact (continuousOn_iff_continuous_domRestrict.1 h2).measurable

theorem int_shift_one {φ : ℝ → ℝ} (hφ1 : ∫ t, φ t = 1) (z : ℝ) : ∫ t, φ (z - t) = 1 := by
  have := integral_sub_left_eq_self φ (volume : Measure ℝ) z
  rw [this, hφ1]

theorem conv_atTop {φ u : ℝ → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) {Q : ℝ} (hQ : 0 ≤ Q) (hu : ∀ t, -Q ≤ u t)
    (hint : ∀ y, Integrable (fun ξ => u (y - ξ) * φ ξ)) (hlim : Tendsto u atTop atTop) :
    Tendsto (fun y => conv u φ y) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hBB' : B ≤ B' := le_max_left _ _
  have hmass : ∀ᶠ n : ℕ in atTop, (1:ℝ)/2 < ∫ ξ in Iic (n:ℝ), φ ξ := by
    have := tendsto_setIntegral_of_monotone (μ := volume) (f := φ) (s := fun n : ℕ => Iic (n:ℝ))
      (fun n => measurableSet_Iic) (fun a b hab => Iic_subset_Iic.2 (by exact_mod_cast hab))
      hφi.integrableOn
    have hU : (⋃ n : ℕ, Iic (n:ℝ)) = univ := by
      ext x
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      exact exists_nat_ge x
    rw [hU, setIntegral_univ, hφ1] at this
    exact this.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := hmass.exists
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually_ge_atTop (2 * (B' + Q)))
  refine eventually_atTop.2 ⟨T + N, fun y hy => ?_⟩
  set M1 := 2 * (B' + Q) with hM1
  have hpt : ∀ ξ, -Q * φ ξ + (M1 + Q) * (Iic (N:ℝ)).indicator φ ξ ≤ u (y - ξ) * φ ξ := by
    intro ξ
    by_cases hξ : ξ ≤ N
    · have := hT (y - ξ) (by linarith)
      have h2 : (Iic (N:ℝ)).indicator φ ξ = φ ξ := indicator_of_mem (mem_Iic.2 hξ) _
      rw [h2]
      nlinarith [hφ0 ξ]
    · have h2 : (Iic (N:ℝ)).indicator φ ξ = 0 := indicator_of_notMem (by simpa using hξ) _
      rw [h2]
      nlinarith [hφ0 ξ, hu (y - ξ)]
  have hI : Integrable (fun ξ => -Q * φ ξ + (M1 + Q) * (Iic (N:ℝ)).indicator φ ξ) :=
    (hφi.const_mul _).add ((hφi.indicator measurableSet_Iic).const_mul _)
  have h1 := integral_mono hI (hint y) hpt
  rw [integral_add (hφi.const_mul _) ((hφi.indicator measurableSet_Iic).const_mul _),
    integral_const_mul, integral_const_mul, hφ1, integral_indicator measurableSet_Iic] at h1
  have h2 : conv u φ y = ∫ ξ, u (y - ξ) * φ ξ := rfl
  rw [h2]
  nlinarith

theorem conv_atBot {φ u : ℝ → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) (hneg : ∀ x, x < 0 → φ x = 0)
    (hint : ∀ y, Integrable (fun ξ => u (y - ξ) * φ ξ)) (hlim : Tendsto u atBot atTop) :
    Tendsto (fun y => conv u φ y) atBot atTop := by
  rw [tendsto_atTop]
  intro B
  obtain ⟨T, hT⟩ := eventually_atBot.1 (hlim.eventually_ge_atTop B)
  refine eventually_atBot.2 ⟨T, fun y hy => ?_⟩
  have hpt : ∀ ξ, B * φ ξ ≤ u (y - ξ) * φ ξ := by
    intro ξ
    by_cases hξ : ξ < 0
    · simp [hneg ξ hξ]
    · push Not at hξ
      exact mul_le_mul_of_nonneg_right (hT (y - ξ) (by linarith)) (hφ0 ξ)
  have h1 := integral_mono (hφi.const_mul B) (hint y) hpt
  rw [integral_const_mul, hφ1] at h1
  have h2 : conv u φ y = ∫ ξ, u (y - ξ) * φ ξ := rfl
  rw [h2]
  linarith


/-! The model layer -/
end S3x

end Lib
end PorteusSS

open MeasureTheory

namespace PorteusSS
namespace NewA

/-! ## Staircase determinants and the exponential Pólya densities -/

theorem stair_det : ∀ (k : ℕ) (a b : Fin k → ℝ), Monotone a → Monotone b →
    0 ≤ (Matrix.of fun i j : Fin k => if b j ≤ a i then (1:ℝ) else 0).det := by
  intro k
  induction k with
  | zero => intro a b _ _; simp
  | succ k ih =>
    intro a b ha hb
    set S := (Matrix.of fun i j : Fin (k+1) => if b j ≤ a i then (1:ℝ) else 0) with hS
    by_cases h0 : b 0 ≤ a 0
    · by_cases hall : ∀ j : Fin (k+1), j ≠ 0 → ¬ b j ≤ a 0
      · rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
        have hrest : ∀ j : Fin k, (-1 : ℝ) ^ ((j.succ : Fin (k+1)) : ℕ) * S 0 j.succ *
            (S.submatrix Fin.succ (j.succ).succAbove).det = 0 := by
          intro j
          have : S 0 j.succ = 0 := by
            simp only [hS, Matrix.of_apply]
            rw [if_neg (hall j.succ (Fin.succ_ne_zero j))]
          rw [this]; ring
        simp only [hrest, Finset.sum_const_zero, add_zero]
        have e00 : S 0 0 = 1 := by simp [hS, h0]
        rw [e00, Fin.succAbove_zero]
        have hsub : S.submatrix Fin.succ Fin.succ =
            Matrix.of fun i j : Fin k => if (b ∘ Fin.succ) j ≤ (a ∘ Fin.succ) i then (1:ℝ) else 0 := by
          ext i j; simp [hS]
        rw [hsub]
        have := ih (a ∘ Fin.succ) (b ∘ Fin.succ) (ha.comp (Fin.strictMono_succ.monotone))
          (hb.comp (Fin.strictMono_succ.monotone))
        simpa using this
      · push Not at hall
        obtain ⟨j, hj0, hj⟩ := hall
        have : S.det = 0 := by
          refine Matrix.det_zero_of_column_eq hj0.symm (fun i => ?_)
          have hi : a 0 ≤ a i := ha (Fin.zero_le i)
          simp only [hS, Matrix.of_apply]
          rw [if_pos (le_trans h0 hi), if_pos (le_trans hj hi)]
        rw [this]
    · have : S.det = 0 := by
        refine Matrix.det_eq_zero_of_row_eq_zero 0 (fun j => ?_)
        have hj : b 0 ≤ b j := hb (Fin.zero_le j)
        simp only [hS, Matrix.of_apply]
        rw [if_neg (fun h => h0 (le_trans hj h))]
      rw [this]

theorem expDensity_nonneg {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 ≤ expDensity c t := by
  unfold expDensity
  split_ifs
  · positivity
  · exact le_rfl

theorem expDensity_eq_indicator (c : ℝ) :
    expDensity c = (Ici (0:ℝ)).indicator (fun t => c * Real.exp (-c * t)) := by
  ext t
  simp [expDensity, indicator]

theorem expDensity_integrable {c : ℝ} (hc : 0 < c) : Integrable (expDensity c) := by
  rw [expDensity_eq_indicator, integrable_indicator_iff measurableSet_Ici]
  have := (exp_neg_integrableOn_Ioi 0 hc).const_mul c
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact this

theorem expDensity_integral_pos {c : ℝ} (hc : 0 < c) : 0 < ∫ t, expDensity c t := by
  have hnn : 0 ≤ expDensity c := fun t => expDensity_nonneg hc t
  rw [integral_pos_iff_support_of_nonneg hnn (expDensity_integrable hc)]
  have hsupp : Ici (0:ℝ) ⊆ Function.support (expDensity c) := by
    intro t ht
    simp only [Function.mem_support, expDensity, if_pos (mem_Ici.1 ht)]
    positivity
  have : volume (Ici (0:ℝ)) = ⊤ := Real.volume_Ici
  calc (0 : ENNReal) < volume (Ici (0:ℝ)) := by rw [this]; exact ENNReal.zero_lt_top
    _ ≤ _ := measure_mono hsupp

theorem expDensity_isPFF {c : ℝ} (hc : 0 < c) : IsPFF (expDensity c) := by
  intro n _
  refine ⟨⟨expDensity_integrable hc, expDensity_integral_pos hc⟩, ?_⟩
  intro k _ _ x t hx ht
  have hM : (Matrix.of fun i j : Fin k => expDensity c (x i - t j)) =
      Matrix.of fun i j => (c * Real.exp (-c * x i)) *
        (Matrix.of fun i j => Real.exp (c * t j) *
          (Matrix.of fun i j : Fin k => if t j ≤ x i then (1:ℝ) else 0) i j) i j := by
    ext i j
    simp only [Matrix.of_apply, expDensity, sub_nonneg]
    split_ifs
    · rw [show -c * (x i - t j) = -c * x i + c * t j by ring, Real.exp_add]; ring
    · ring
  rw [hM, Matrix.det_mul_column, Matrix.det_mul_row]
  have h1 := stair_det k x t hx.monotone ht.monotone
  have h2 : 0 ≤ ∏ i, (c * Real.exp (-c * x i)) := Finset.prod_nonneg fun i _ => by positivity
  have h3 : 0 ≤ ∏ i, Real.exp (c * t i) := Finset.prod_nonneg fun i _ => by positivity
  exact mul_nonneg h2 (mul_nonneg h3 h1)

theorem expDensity_neg_isPFF {c : ℝ} (hc : 0 < c) : IsPFF (fun t => expDensity c (-t)) := by
  intro n _
  refine ⟨⟨(expDensity_integrable hc).comp_neg, ?_⟩, ?_⟩
  · rw [integral_neg_eq_self (fun t => expDensity c t)]
    exact expDensity_integral_pos hc
  intro k _ _ x t hx ht
  have hM : (Matrix.of fun i j : Fin k => expDensity c (-(x i - t j))) =
      Matrix.of fun i j => (c * Real.exp (c * x i)) *
        (Matrix.of fun i j => Real.exp (-c * t j) *
          (Matrix.of fun j i : Fin k => if x i ≤ t j then (1:ℝ) else 0).transpose i j) i j := by
    ext i j
    simp only [Matrix.of_apply, Matrix.transpose_apply, expDensity, neg_sub, sub_nonneg]
    split_ifs
    · rw [show -c * (t j - x i) = c * x i + -c * t j by ring, Real.exp_add]; ring
    · ring
  rw [hM, Matrix.det_mul_column, Matrix.det_mul_row, Matrix.det_transpose]
  have h1 := stair_det k t x ht.monotone hx.monotone
  have h2 : 0 ≤ ∏ i, (c * Real.exp (c * x i)) := Finset.prod_nonneg fun i _ => by positivity
  have h3 : 0 ≤ ∏ i, Real.exp (-c * t i) := Finset.prod_nonneg fun i _ => by positivity
  exact mul_nonneg h2 (mul_nonneg h3 h1)

theorem exp_abs_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    Real.exp (-c * |u|) ≤ c⁻¹ * (expDensity c u + expDensity c (-u)) := by
  have hn1 := expDensity_nonneg hc u
  have hn2 := expDensity_nonneg hc (-u)
  rcases le_total 0 u with hu | hu
  · have : expDensity c u = c * Real.exp (-c * |u|) := by
      simp [expDensity, hu, abs_of_nonneg hu]
    rw [this, mul_add, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    nlinarith [inv_pos.2 hc]
  · have : expDensity c (-u) = c * Real.exp (-c * |u|) := by
      simp [expDensity, hu, abs_of_nonpos hu]
    rw [this, mul_add, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    nlinarith [inv_pos.2 hc]

theorem integrable_exp_abs {c : ℝ} (hc : 0 < c) : Integrable (fun u => Real.exp (-c * |u|)) := by
  refine Integrable.mono' (((expDensity_integrable hc).add
    (expDensity_integrable hc).comp_neg).const_mul c⁻¹)
    (by fun_prop) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_abs_le hc u

theorem integrable_f_exp {f : ℝ → ℝ} (hfm : Measurable f) (hpf : PFIntegrable f) {c : ℝ}
    (hc : 0 < c) (w : ℝ) : Integrable (fun u => f (w - u) * Real.exp (-c * |u|)) := by
  have h1 := hpf _ (expDensity_isPFF hc) w
  have h2 := hpf _ (expDensity_neg_isPFF hc) w
  refine Integrable.mono' ((h1.norm.add h2.norm).const_mul c⁻¹)
    ((hfm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul (by fun_prop))
    (Eventually.of_forall fun u => ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
  rw [abs_of_nonneg (expDensity_nonneg hc u), abs_of_nonneg (expDensity_nonneg hc (-u))]
  have := exp_abs_le hc u
  have hfa := abs_nonneg (f (w - u))
  calc |f (w - u)| * Real.exp (-c * |u|) ≤ |f (w - u)| * (c⁻¹ * (expDensity c u + expDensity c (-u))) :=
        mul_le_mul_of_nonneg_left this hfa
    _ = c⁻¹ * (|f (w - u)| * expDensity c u + |f (w - u)| * expDensity c (-u)) := by ring

/-! ## Exponential tails of PF2 functions -/

def LCond (ψ : ℝ → ℝ) : Prop :=
  ∀ a c b : ℝ, a < c → c < b → ψ a * ψ b ≤ ψ c * ψ (a + b - c)

theorem lcond_neg {ψ : ℝ → ℝ} (h : LCond ψ) : LCond (fun t => ψ (-t)) := by
  intro a c b hac hcb
  have := h (-b) (-c) (-a) (by linarith) (by linarith)
  simp only
  rw [show -(a + b - c) = -b + -a - -c by ring]
  linarith [mul_comm (ψ (-a)) (ψ (-b))]

theorem half_bound {ψ : ℝ → ℝ} (h0 : ∀ t, 0 ≤ ψ t) (hi : Integrable ψ) (hL : LCond ψ)
    {a b : ℝ} (hab : a < b) : (b - a) * √(ψ a * ψ b) ≤ 2 * ∫ t, ψ t := by
  have key : ∀ c ∈ Icc a b, √(ψ a * ψ b) ≤ ψ c + ψ (a + b - c) := by
    intro c hc
    rw [Real.sqrt_le_iff]
    refine ⟨add_nonneg (h0 _) (h0 _), ?_⟩
    rcases hc.1.lt_or_eq with h1 | h1
    · rcases hc.2.lt_or_eq with h2 | h2
      · have := hL a c b h1 h2
        nlinarith [h0 c, h0 (a + b - c), mul_nonneg (h0 c) (h0 (a + b - c))]
      · subst h2
        rw [show a + c - c = a by ring]
        nlinarith [h0 a, h0 c, mul_nonneg (h0 a) (h0 c)]
    · subst h1
      rw [show a + b - a = b by ring]
      nlinarith [h0 b, h0 a, mul_nonneg (h0 b) (h0 a)]
  have hI1 : IntervalIntegrable ψ volume a b := hi.intervalIntegrable
  have hI2 : IntervalIntegrable (fun c => ψ (a + b - c)) volume a b :=
    (hi.comp_sub_left (a + b)).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
    (hI1.add hI2) key
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_comp_sub_left
      (fun t => ψ t) (a + b)] at hmono
  rw [show a + b - b = a by ring, show a + b - a = b by ring] at hmono
  have hle : ∫ t in a..b, ψ t ≤ ∫ t, ψ t := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact setIntegral_le_integral hi (Eventually.of_forall h0)
  linarith

/-- from `d * √(α y) ≤ 2M` with `δ ≤ d` -/
theorem bound_of_half {α y d δ M : ℝ} (hα : 0 < α) (hy : 0 ≤ y) (hδ : 0 < δ) (hd : δ ≤ d)
    (h : d * √(α * y) ≤ 2 * M) : y ≤ (2 * M / δ) ^ 2 / α := by
  have hs0 : 0 ≤ √(α * y) := Real.sqrt_nonneg _
  have h1 : √(α * y) ≤ 2 * M / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have h2 : α * y ≤ (2 * M / δ) ^ 2 := by
    have := Real.sq_sqrt (mul_nonneg hα.le hy)
    nlinarith
  rw [le_div_iff₀ hα]; linarith

theorem exists_pos_point {ψ : ℝ → ℝ} (hpos : 0 < ∫ t, ψ t) : ∃ p, 0 < ψ p := by
  by_contra h
  push Not at h
  have : ∫ t, ψ t ≤ 0 := integral_nonpos h
  linarith

theorem exists_two_points {ψ : ℝ → ℝ} (h0 : ∀ t, 0 ≤ ψ t) (hpos : 0 < ∫ t, ψ t) :
    ∃ p q, p < q ∧ 0 < ψ p ∧ 0 < ψ q := by
  obtain ⟨p, hp⟩ := exists_pos_point hpos
  by_cases h : ∃ q, q ≠ p ∧ 0 < ψ q
  · obtain ⟨q, hqp, hq⟩ := h
    rcases lt_or_gt_of_ne hqp with h1 | h1
    · exact ⟨q, p, h1, hq, hp⟩
    · exact ⟨p, q, h1, hp, hq⟩
  · push Not at h
    have hae : ψ =ᵐ[volume] 0 := by
      rw [EventuallyEq, ae_iff]
      refine measure_mono_null (fun t ht => ?_) (measure_singleton p)
      simp only [mem_ofPred_eq, Pi.zero_apply] at ht
      by_contra hne
      exact ht (le_antisymm (h t hne) (h0 t))
    rw [integral_eq_zero_of_ae hae] at hpos
    exact absurd hpos (lt_irrefl _)

theorem lc_bdd {ψ : ℝ → ℝ} (h0 : ∀ t, 0 ≤ ψ t) (hi : Integrable ψ) (hL : LCond ψ)
    (hpos : 0 < ∫ t, ψ t) : ∃ B, ∀ x, ψ x ≤ B := by
  obtain ⟨p, q, hpq, hp, hq⟩ := exists_two_points h0 hpos
  set M := ∫ t, ψ t
  set δ := (q - p) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ⟨(2 * M / δ) ^ 2 / ψ p + (2 * M / δ) ^ 2 / ψ q, fun x => ?_⟩
  have hA : 0 ≤ (2 * M / δ) ^ 2 / ψ p := div_nonneg (sq_nonneg _) hp.le
  have hB : 0 ≤ (2 * M / δ) ^ 2 / ψ q := div_nonneg (sq_nonneg _) hq.le
  rcases le_or_gt ((p + q) / 2) x with hx | hx
  · have hpx : p < x := by linarith
    have := half_bound h0 hi hL hpx
    have := bound_of_half hp (h0 x) hδ0 (by rw [hδ]; linarith) this
    linarith
  · have hxq : x < q := by linarith
    have h1 := half_bound h0 hi hL hxq
    rw [mul_comm (ψ x)] at h1
    have := bound_of_half hq (h0 x) hδ0 (by rw [hδ]; linarith) h1
    linarith

theorem lc_right_tail {ψ : ℝ → ℝ} (h0 : ∀ t, 0 ≤ ψ t) (hi : Integrable ψ) (hL : LCond ψ)
    {B : ℝ} (hB : ∀ x, ψ x ≤ B) {p : ℝ} (hp : 0 < ψ p) :
    ∃ C c, 0 ≤ C ∧ 0 < c ∧ ∀ x, p ≤ x → ψ x ≤ C * Real.exp (-c * (x - p)) := by
  set M := ∫ t, ψ t with hM
  have hM0 : 0 ≤ M := integral_nonneg h0
  set α := ψ p
  set h := 4 * M / α + 1 with hh
  have hh0 : 0 < h := by rw [hh]; have := div_nonneg (by linarith : (0:ℝ) ≤ 4 * M) hp.le; linarith
  have hph : ψ (p + h) ≤ α / 2 := by
    have := half_bound h0 hi hL (show p < p + h by linarith)
    rw [show p + h - p = h by ring] at this
    have hs0 : 0 ≤ √(α * ψ (p + h)) := Real.sqrt_nonneg _
    have h4 : 4 * M < h * α := by
      rw [hh, add_mul, div_mul_cancel₀ _ hp.ne']; linarith
    have h1 : √(α * ψ (p + h)) * 2 ≤ α := by nlinarith
    have h2 := Real.sq_sqrt (mul_nonneg hp.le (h0 (p + h)))
    nlinarith [h0 (p + h)]
  have hrec : ∀ x, p ≤ x → ψ (x + h) ≤ ψ x / 2 := by
    intro x hx
    rcases hx.lt_or_eq with hx | hx
    · have := hL p x (x + h) hx (by linarith)
      rw [show p + (x + h) - x = p + h by ring] at this
      have : α * ψ (x + h) ≤ ψ x * (α / 2) :=
        le_trans this (mul_le_mul_of_nonneg_left hph (h0 x))
      nlinarith [h0 (x + h)]
    · subst hx; exact hph
  have hB0 : 0 ≤ B := le_trans (h0 p) (hB p)
  have hind : ∀ n : ℕ, ∀ x, p + n * h ≤ x → ψ x ≤ B / 2 ^ n := by
    intro n
    induction n with
    | zero => intro x _; simpa using hB x
    | succ n ihn =>
      intro x hx
      have hx' : p + n * h ≤ x - h := by push_cast at hx; linarith
      have hpx : p ≤ x - h := le_trans (by nlinarith [n.cast_nonneg (α := ℝ)]) hx'
      have := hrec (x - h) hpx
      rw [sub_add_cancel] at this
      have := ihn (x - h) hx'
      rw [pow_succ]
      calc ψ x ≤ ψ (x - h) / 2 := by assumption
        _ ≤ B / 2 ^ n / 2 := by linarith
        _ = B / (2 ^ n * 2) := by rw [div_div]
  refine ⟨2 * B, Real.log 2 / h, by linarith, div_pos (Real.log_pos (by norm_num)) hh0,
    fun x hx => ?_⟩
  set r := (x - p) / h with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hh0.le
  set n := ⌊r⌋₊ with hn
  have hn1 : (n : ℝ) ≤ r := Nat.floor_le hr0
  have hn2 : r < n + 1 := Nat.lt_floor_add_one r
  have hpx : p + n * h ≤ x := by
    have : (n : ℝ) * h ≤ r * h := mul_le_mul_of_nonneg_right hn1 hh0.le
    rw [hr, div_mul_cancel₀ _ hh0.ne'] at this; linarith
  have h1 := hind n x hpx
  have h2 : (2:ℝ) ^ n = Real.exp (n * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm]
  have h3 : -(Real.log 2 / h) * (x - p) = -(r * Real.log 2) := by rw [hr]; ring
  rw [h3]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.exp (-(r * Real.log 2)) * 2 ≥ Real.exp (-(n * Real.log 2)) := by
    have : -((n:ℝ) * Real.log 2) ≤ -(r * Real.log 2) + Real.log 2 := by nlinarith
    calc Real.exp (-(n * Real.log 2)) ≤ Real.exp (-(r * Real.log 2) + Real.log 2) :=
          Real.exp_le_exp.2 this
      _ = Real.exp (-(r * Real.log 2)) * 2 := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
  have h5 : B / 2 ^ n = B * Real.exp (-(n * Real.log 2)) := by
    rw [h2, Real.exp_neg, div_eq_mul_inv]
  calc ψ x ≤ B * Real.exp (-(n * Real.log 2)) := by rw [← h5]; exact h1
    _ ≤ B * (Real.exp (-(r * Real.log 2)) * 2) := mul_le_mul_of_nonneg_left h4 hB0
    _ = 2 * B * Real.exp (-(r * Real.log 2)) := by ring

theorem lc_tail {ψ : ℝ → ℝ} (h0 : ∀ t, 0 ≤ ψ t) (hi : Integrable ψ) (hL : LCond ψ)
    (hpos : 0 < ∫ t, ψ t) : ∃ C c, 0 < c ∧ ∀ x, ψ x ≤ C * Real.exp (-c * |x|) := by
  obtain ⟨B, hB⟩ := lc_bdd h0 hi hL hpos
  obtain ⟨p, hp⟩ := exists_pos_point hpos
  obtain ⟨C1, c1, hC1, hc1, h1⟩ := lc_right_tail h0 hi hL hB hp
  have h0' : ∀ t, 0 ≤ (fun t => ψ (-t)) t := fun t => h0 _
  have hp' : 0 < (fun t => ψ (-t)) (-p) := by simpa using hp
  obtain ⟨C2, c2, hC2, hc2, h2⟩ := lc_right_tail h0' hi.comp_neg (lcond_neg hL)
    (B := B) (fun x => hB _) hp'
  set c := min c1 c2
  have hc : 0 < c := lt_min hc1 hc2
  refine ⟨(C1 + C2) * Real.exp (c * |p|), c, hc, fun x => ?_⟩
  have hE : 0 < Real.exp (-c * |x|) := Real.exp_pos _
  rcases le_total p x with hx | hx
  · have := h1 x hx
    have e1 : Real.exp (-c1 * (x - p)) ≤ Real.exp (c * |p|) * Real.exp (-c * |x|) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : |x| ≤ (x - p) + |p| := by
        have := abs_sub_abs_le_abs_sub x p
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - p)] at this; linarith
      have : c ≤ c1 := min_le_left _ _
      nlinarith [abs_nonneg x, abs_nonneg p]
    have hpos' : 0 ≤ Real.exp (c * |p|) * Real.exp (-c * |x|) := by positivity
    calc ψ x ≤ C1 * Real.exp (-c1 * (x - p)) := this
      _ ≤ C1 * (Real.exp (c * |p|) * Real.exp (-c * |x|)) := mul_le_mul_of_nonneg_left e1 hC1
      _ ≤ (C1 + C2) * Real.exp (c * |p|) * Real.exp (-c * |x|) := by nlinarith
  · have := h2 (-x) (by linarith)
    simp only [neg_neg] at this
    have e1 : Real.exp (-c2 * (-x - -p)) ≤ Real.exp (c * |p|) * Real.exp (-c * |x|) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : |x| ≤ (p - x) + |p| := by
        have := abs_sub_abs_le_abs_sub x p
        rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ p - x)] at this; linarith
      have : c ≤ c2 := min_le_right _ _
      nlinarith [abs_nonneg x, abs_nonneg p]
    have hpos' : 0 ≤ Real.exp (c * |p|) * Real.exp (-c * |x|) := by positivity
    calc ψ x ≤ C2 * Real.exp (-c2 * (-x - -p)) := this
      _ ≤ C2 * (Real.exp (c * |p|) * Real.exp (-c * |x|)) := mul_le_mul_of_nonneg_left e1 hC2
      _ ≤ (C1 + C2) * Real.exp (c * |p|) * Real.exp (-c * |x|) := by nlinarith

end NewA
end PorteusSS

namespace PorteusSS
namespace NewA

/-! ## PF2 facts read off `IsPF 2` directly -/

theorem nonneg_of_isPF' {ψ : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n) (h : IsPF n ψ) (t : ℝ) : 0 ≤ ψ t := by
  have := h.2 1 le_rfl hn ![t] ![0] (Subsingleton.strictMono _) (Subsingleton.strictMono _)
  simpa [Matrix.det_fin_one] using this

theorem lcond_of_isPF {ψ : ℝ → ℝ} {n : ℕ} (hn : 2 ≤ n) (h : IsPF n ψ) : LCond ψ := by
  intro a c b hac hcb
  have hxm : StrictMono ![c, b] := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simpa using hcb
  have htm : StrictMono ![0, c - a] := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simp; linarith
  have := h.2 2 (by norm_num) hn ![c, b] ![0, c - a] hxm htm
  rw [Matrix.det_fin_two] at this
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  rw [show c - (c - a) = a by ring, show b - 0 = b by ring, show c - 0 = c by ring,
    show b - (c - a) = a + b - c by ring] at this
  linarith

theorem pff_tail {ψ : ℝ → ℝ} (hψ : IsPFF ψ) :
    (∀ t, 0 ≤ ψ t) ∧ Integrable ψ ∧ ∃ C c, 0 < c ∧ ∀ x, ψ x ≤ C * Real.exp (-c * |x|) := by
  have h2 := hψ 2 (by norm_num)
  have h0 := nonneg_of_isPF' (by norm_num) h2
  exact ⟨h0, h2.1.1, lc_tail h0 h2.1.1 (lcond_of_isPF le_rfl h2) h2.1.2⟩

/-! ## PF-integrability of the convolution -/

theorem pfint_conv {f φ : ℝ → ℝ} (hfm : Measurable f) (hpf : PFIntegrable f)
    (hφ : IsPFF φ) (hG : Continuous (conv f φ)) : PFIntegrable (conv f φ) := by
  intro ψ hψ y
  obtain ⟨hψ0, hψi, Cψ, cψ, hcψ, hψb⟩ := pff_tail hψ
  obtain ⟨hφ0, hφi, Cφ, cφ, hcφ, hφb⟩ := pff_tail hφ
  set c := min cψ cφ
  have hc : 0 < c := lt_min hcψ hcφ
  have hc2 : 0 < c / 2 := by linarith
  have hψb' : ∀ x, ψ x ≤ Cψ * Real.exp (-c * |x|) := by
    intro x
    refine le_trans (hψb x) (mul_le_mul_of_nonneg_left ?_ ?_)
    · rw [Real.exp_le_exp]
      have : c ≤ cψ := min_le_left _ _
      nlinarith [abs_nonneg x]
    · have := le_trans (hψ0 x) (hψb x)
      by_contra hneg; push Not at hneg
      have := hψ0 0
      have h00 := hψb 0
      nlinarith [Real.exp_pos (-cψ * |(0:ℝ)|)]
  have hCφ : 0 ≤ Cφ := by
    have := le_trans (hφ0 0) (hφb 0)
    by_contra hneg; push Not at hneg
    nlinarith [Real.exp_pos (-cφ * |(0:ℝ)|)]
  have hCψ : 0 ≤ Cψ := by
    have := le_trans (hψ0 0) (hψb 0)
    by_contra hneg; push Not at hneg
    nlinarith [Real.exp_pos (-cψ * |(0:ℝ)|)]
  have hφb' : ∀ x, φ x ≤ Cφ * Real.exp (-c * |x|) := by
    intro x
    refine le_trans (hφb x) (mul_le_mul_of_nonneg_left ?_ hCφ)
    rw [Real.exp_le_exp]
    have : c ≤ cφ := min_le_right _ _
    nlinarith [abs_nonneg x]
  set F : ℝ → ℝ := fun u => |f (y - u)| * Real.exp (-(c / 2) * |u|) with hF
  have hFi : Integrable F := by
    have := (integrable_f_exp hfm hpf hc2 y).norm
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp [hF, norm_mul, abs_of_pos (Real.exp_pos _)]
  set J := ∫ u, F u with hJ
  have hbound : ∀ ξ, ‖conv f φ (y - ξ) * ψ ξ‖ ≤ Cψ * (Cφ * J) * Real.exp (-(c / 2) * |ξ|) := by
    intro ξ
    have hin : ∀ x, ‖f (y - ξ - x) * φ x‖ ≤
        Cφ * Real.exp ((c / 2) * |ξ|) * F (ξ + x) := by
      intro x
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ0 x), hF]
      rw [show y - (ξ + x) = y - ξ - x by ring]
      have e1 : Real.exp (-c * |x|) ≤ Real.exp ((c / 2) * |ξ|) * Real.exp (-(c / 2) * |ξ + x|) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        have := abs_add_le ξ x
        nlinarith [abs_nonneg x, abs_nonneg ξ]
      have hfa := abs_nonneg (f (y - ξ - x))
      calc |f (y - ξ - x)| * φ x ≤ |f (y - ξ - x)| * (Cφ * Real.exp (-c * |x|)) :=
            mul_le_mul_of_nonneg_left (hφb' x) hfa
        _ ≤ |f (y - ξ - x)| * (Cφ * (Real.exp ((c / 2) * |ξ|) *
              Real.exp (-(c / 2) * |ξ + x|))) := by
            gcongr
        _ = Cφ * Real.exp ((c / 2) * |ξ|) * (|f (y - ξ - x)| * Real.exp (-(c / 2) * |ξ + x|)) := by
            ring
    have hGi : |conv f φ (y - ξ)| ≤ Cφ * Real.exp ((c / 2) * |ξ|) * J := by
      have h1 : |conv f φ (y - ξ)| ≤ ∫ x, ‖f (y - ξ - x) * φ x‖ := by
        unfold conv
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm (fun x => f (y - ξ - x) * φ x)
      have h2 : ∫ x, ‖f (y - ξ - x) * φ x‖ ≤ ∫ x, Cφ * Real.exp ((c / 2) * |ξ|) * F (ξ + x) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
          ((hFi.comp_add_left ξ).const_mul _) (Eventually.of_forall hin)
      rw [integral_const_mul, integral_add_left_eq_self F ξ] at h2
      linarith
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hψ0 ξ)]
    have hJ0 : 0 ≤ J := integral_nonneg fun u => by
      simp only [hF]; exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    calc |conv f φ (y - ξ)| * ψ ξ ≤ (Cφ * Real.exp ((c / 2) * |ξ|) * J) *
          (Cψ * Real.exp (-c * |ξ|)) :=
          mul_le_mul hGi (hψb' ξ) (hψ0 ξ) (by positivity)
      _ = Cψ * (Cφ * J) * (Real.exp ((c / 2) * |ξ|) * Real.exp (-c * |ξ|)) := by ring
      _ = Cψ * (Cφ * J) * Real.exp (-(c / 2) * |ξ|) := by
          rw [← Real.exp_add]; congr 2; ring
  refine Integrable.mono' ((integrable_exp_abs hc2).const_mul (Cψ * (Cφ * J)))
    ((hG.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hψi.1)
    (Eventually.of_forall hbound)

/-! ## Lower bound, shape bound and continuity of the convolution -/

theorem punct_lower {f : ℝ → ℝ} (hpc : PiecewiseContinuousOn f univ) (p : ℝ) :
    ∃ δ > 0, ∃ L, (∀ z ∈ Ioo (p - δ) p, L ≤ f z) ∧ (∀ z ∈ Ioo p (p + δ), L ≤ f z) := by
  obtain ⟨A, -, hc, hlim⟩ := hpc
  have hev : ∃ L, (∀ᶠ z in 𝓝[<] p, L ≤ f z) ∧ (∀ᶠ z in 𝓝[>] p, L ≤ f z) := by
    by_cases hp : p ∈ A
    · obtain ⟨hl, hr⟩ := hlim p hp
      rw [univ_inter] at hl hr
      obtain ⟨l1, hl1⟩ := hl inferInstance
      obtain ⟨l2, hl2⟩ := hr inferInstance
      refine ⟨min (l1 - 1) (l2 - 1), ?_, ?_⟩
      · filter_upwards [hl1.eventually (lt_mem_nhds (by linarith : l1 - 1 < l1))] with z hz
        exact le_trans (min_le_left _ _) hz.le
      · filter_upwards [hl2.eventually (lt_mem_nhds (by linarith : l2 - 1 < l2))] with z hz
        exact le_trans (min_le_right _ _) hz.le
    · have hopen : IsOpen (univ \ (↑A : Set ℝ)) := by
        rw [← compl_eq_univ_sdiff]; exact A.finite_toSet.isClosed.isOpen_compl
      have hca : ContinuousAt f p := hc.continuousAt (hopen.mem_nhds ⟨mem_univ _, hp⟩)
      have hev := hca.eventually (lt_mem_nhds (by linarith : f p - 1 < f p))
      refine ⟨f p - 1, ?_, ?_⟩
      · filter_upwards [nhdsWithin_le_nhds hev] with z hz; exact hz.le
      · filter_upwards [nhdsWithin_le_nhds hev] with z hz; exact hz.le
  obtain ⟨L, h1, h2⟩ := hev
  obtain ⟨l, hl, hls⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h1
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h2
  refine ⟨min (p - l) (u - p), lt_min (by simp at hl; linarith) (by simp at hu; linarith), L,
    fun z hz => hls ⟨by linarith [hz.1, min_le_left (p - l) (u - p)], hz.2⟩,
    fun z hz => hus ⟨hz.1, by linarith [hz.2, min_le_right (p - l) (u - p)]⟩⟩

theorem I_cases {I : Set ℝ} {a : ℝ} (hI : I = Iio a ∨ I = Iic a) {t : ℝ} :
    (t < a → t ∈ I) ∧ (a < t → t ∈ Iᶜ) := by
  rcases hI with rfl | rfl
  · exact ⟨fun h => h, fun h => by simp only [mem_compl_iff, mem_Iio, not_lt]; exact h.le⟩
  · exact ⟨fun h => le_of_lt h, fun h => by simpa using h⟩

theorem lower_bound {f : ℝ → ℝ} {I : Set ℝ} {a K : ℝ} (_hK : 0 ≤ K)
    (hI : I = Iio a ∨ I = Iic a) (hpc : PiecewiseContinuousOn f univ)
    (hanti : AntitoneOn f I) (hnkd : NonKDecreasingOn f K Iᶜ) :
    ∃ Q, 0 ≤ Q ∧ ∀ t, -Q ≤ f t := by
  obtain ⟨δ, hδ, L, hL1, hL2⟩ := punct_lower hpc a
  set L0 := min (min L (L - K)) (f a)
  refine ⟨|L0|, abs_nonneg _, fun t => ?_⟩
  have hL0 : -|L0| ≤ L0 := neg_abs_le L0
  suffices L0 ≤ f t by linarith
  rcases lt_trichotomy t a with ht | ht | ht
  · by_cases ht2 : a - δ < t
    · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (hL1 t ⟨ht2, ht⟩)
    · push Not at ht2
      have hs : a - δ / 2 ∈ Ioo (a - δ) a := ⟨by linarith, by linarith⟩
      have := hanti ((I_cases hI).1 ht) ((I_cases hI).1 hs.2) (by linarith)
      exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (le_trans (hL1 _ hs) this)
  · subst ht; exact min_le_right _ _
  · set s := min t (a + δ / 2)
    have hs : s ∈ Ioo a (a + δ) := ⟨lt_min ht (by linarith), by
      have := min_le_right t (a + δ / 2); linarith⟩
    have := hnkd s ((I_cases hI).2 hs.1) t ((I_cases hI).2 ht) (min_le_left _ _)
    have := hL2 s hs
    have : L - K ≤ f t := by linarith
    exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) this

theorem shape_upper {f : ℝ → ℝ} {I : Set ℝ} {a K : ℝ} (hK : 0 ≤ K)
    (hI : I = Iio a ∨ I = Iic a) (hanti : AntitoneOn f I) (hnkd : NonKDecreasingOn f K Iᶜ)
    {m w M : ℝ} (hmw : m ≤ w) (hwM : w ≤ M) : f w ≤ |f m| + |f (max M (a + 1))| + K := by
  by_cases hw : w ∈ I
  · have hm : m ∈ I := by
      rcases hI with rfl | rfl
      · exact lt_of_le_of_lt hmw hw
      · exact le_trans hmw hw
    have := hanti hm hw hmw
    linarith [le_abs_self (f m), abs_nonneg (f (max M (a + 1)))]
  · have hM' : max M (a + 1) ∈ Iᶜ := (I_cases hI).2 (by
      have := le_max_right M (a + 1); linarith)
    have := hnkd w hw _ hM' (le_trans hwM (le_max_left _ _))
    linarith [le_abs_self (f (max M (a + 1))), abs_nonneg (f m)]

theorem conv_continuous {f φ : ℝ → ℝ} {I : Set ℝ} {a K Q : ℝ} (hK : 0 ≤ K)
    (hI : I = Iio a ∨ I = Iic a) (hpc : PiecewiseContinuousOn f univ) (hfm : Measurable f)
    (hanti : AntitoneOn f I) (hnkd : NonKDecreasingOn f K Iᶜ) (hQ : 0 ≤ Q)
    (hlow : ∀ t, -Q ≤ f t) (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hint : ∀ w, Integrable (fun ξ => f (w - ξ) * φ ξ)) : Continuous (conv f φ) := by
  obtain ⟨A, -, hc, -⟩ := hpc
  have hopen : IsOpen (univ \ (↑A : Set ℝ)) := by
    rw [← compl_eq_univ_sdiff]; exact A.finite_toSet.isClosed.isOpen_compl
  rw [continuous_iff_continuousAt]
  intro y
  set bound : ℝ → ℝ := fun x =>
    (Q + |f (y - 1 - x)| + |f (y + 1 - x)| + |f (a + 1)| + K) * φ x with hb
  have hbi : Integrable bound := by
    have h1 := (hint (y - 1)).norm
    have h2 := (hint (y + 1)).norm
    have h3 := hφi.const_mul (Q + |f (a + 1)| + K)
    refine ((h1.add h2).add h3).congr (Eventually.of_forall fun x => ?_)
    simp only [hb, Pi.add_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ0 x)]
    ring
  refine continuousAt_of_dominated (F := fun y' x => f (y' - x) * φ x) (bound := bound) ?_ ?_ hbi ?_
  · exact Eventually.of_forall fun y' =>
      ((hfm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hφi.1)
  · filter_upwards [Ioo_mem_nhds (show y - 1 < y by linarith) (show y < y + 1 by linarith)]
      with y' hy'
    refine Eventually.of_forall fun x => ?_
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ0 x), hb]
    refine mul_le_mul_of_nonneg_right ?_ (hφ0 x)
    have hup := shape_upper hK hI hanti hnkd (m := y - 1 - x) (w := y' - x) (M := y + 1 - x)
      (by linarith [hy'.1]) (by linarith [hy'.2])
    have hmax : |f (max (y + 1 - x) (a + 1))| ≤ |f (y + 1 - x)| + |f (a + 1)| := by
      rcases max_choice (y + 1 - x) (a + 1) with h | h <;> rw [h] <;>
        linarith [abs_nonneg (f (y + 1 - x)), abs_nonneg (f (a + 1))]
    rw [abs_le]
    constructor
    · linarith [hlow (y' - x), abs_nonneg (f (y - 1 - x)), abs_nonneg (f (y + 1 - x)),
        abs_nonneg (f (a + 1))]
    · linarith
  · have hnull : volume ((fun z => y - z) '' (↑A : Set ℝ)) = 0 :=
      (A.finite_toSet.image _).measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    have hyx : y - x ∈ univ \ (↑A : Set ℝ) := by
      refine ⟨mem_univ _, fun hmem => hx ⟨y - x, hmem, by ring⟩⟩
    have hca : ContinuousAt f (y - x) := hc.continuousAt (hopen.mem_nhds hyx)
    have hg : ContinuousAt (fun y' : ℝ => y' - x) y :=
      (continuous_id.sub continuous_const).continuousAt
    exact (ContinuousAt.comp (g := f) (f := fun y' : ℝ => y' - x) hca hg).mul continuousAt_const

/-! ## Shape of a continuous coercive three-point quasi-K-convex function -/

theorem shape_of_qk {G : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hG : Continuous G)
    (hco : Tendsto G (cocompact ℝ) atTop)
    (hqk : ∀ x y z, x < y → y < z → G y ≤ max (G x) (G z + K)) :
    ∃ a', AntitoneOn G (Iic a') ∧ NonKDecreasingOn G K (Iic a')ᶜ := by
  set T := {x | ∀ z, x ≤ z → G x ≤ G z + K} with hT
  obtain ⟨x0, hx0⟩ := hG.exists_forall_le hco
  have hx0T : x0 ∈ T := fun z _ => by linarith [hx0 z]
  have hbot : Tendsto G atBot atTop := hco.mono_left atBot_le_cocompact
  obtain ⟨b, hb⟩ := eventually_atBot.1 (hbot.eventually_gt_atTop (G x0 + K))
  have hTbdd : BddBelow T := by
    refine ⟨min b x0, fun x hx => ?_⟩
    by_contra hlt
    push Not at hlt
    have h1 := hx x0 (le_trans hlt.le (min_le_right _ _))
    have h2 := hb x (le_trans hlt.le (min_le_left _ _))
    linarith
  have hTne : T.Nonempty := ⟨x0, hx0T⟩
  have hup : ∀ x x', x ∈ T → x ≤ x' → x' ∈ T := by
    intro x x' hx hxx' z hz
    rcases hxx'.lt_or_eq with h1 | h1
    · rcases hz.lt_or_eq with h2 | h2
      · have := hqk x x' z h1 h2
        have := hx z (by linarith)
        rcases le_max_iff.1 (le_of_le_of_eq ‹G x' ≤ max (G x) (G z + K)› rfl) with h | h
        · linarith
        · linarith
      · subst h2; linarith
    · subst h1; exact hx z hz
  set a' := sInf T
  have hgt : ∀ x, a' < x → x ∈ T := by
    intro x hx
    obtain ⟨t, ht, htx⟩ := exists_lt_of_csInf_lt hTne hx
    exact hup t x ht htx.le
  have hlt : ∀ x, x < a' → x ∉ T := fun x hx hxT => by
    have := csInf_le hTbdd hxT; linarith
  have hanti_lt : ∀ s t, s ≤ t → t < a' → G t ≤ G s := by
    intro s t hst ht
    have := hlt t ht
    simp only [hT, mem_ofPred_eq, not_forall, not_le] at this
    obtain ⟨z, htz, hz⟩ := this
    have htz' : t < z := by
      rcases htz.lt_or_eq with h | h
      · exact h
      · subst h; linarith
    rcases hst.lt_or_eq with h | h
    · have := hqk s t z h htz'
      rcases le_max_iff.1 this with h' | h'
      · exact h'
      · linarith
    · rw [h]
  refine ⟨a', fun s hs t ht hst => ?_, fun x hx z hz hxz => ?_⟩
  · rcases (mem_Iic.1 ht).lt_or_eq with h | h
    · exact hanti_lt s t hst h
    · rcases hst.lt_or_eq with h1 | h1
      · have hlim : Tendsto G (𝓝[<] a') (𝓝 (G a')) :=
          (hG.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        have hev : ∀ᶠ u in 𝓝[<] a', G u ≤ G s := by
          filter_upwards [Ioo_mem_nhdsLT (show s < a' by rw [← h]; exact h1)] with u hu
          exact hanti_lt s u hu.1.le hu.2
        rw [h]
        exact le_of_tendsto hlim hev
      · rw [h1]
  · have hx' : a' < x := by simpa using hx
    exact hgt x hx' z hxz

end NewA
end PorteusSS

namespace PorteusSS
namespace NewA

theorem ae_ne_pt (w : ℝ) : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ≠ w := by
  have : volume ({w} : Set ℝ) = 0 := measure_singleton w
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with ξ hξ
  simpa using hξ

theorem conv_qk {f φ : ℝ → ℝ} {I : Set ℝ} {a K Q : ℝ} (hK : 0 ≤ K)
    (hI : I = Iio a ∨ I = Iic a) (hfm : Measurable f)
    (hanti : AntitoneOn f I) (hnkd : NonKDecreasingOn f K Iᶜ)
    (hlow : ∀ t, -Q ≤ f t) (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hφ1 : ∫ t, φ t = 1)
    (hT : Lib.TP2 φ) (hint : ∀ w, Integrable (fun ξ => f (w - ξ) * φ ξ)) :
    ∀ x y z, x < y → y < z → conv f φ y ≤ max (conv f φ x) (conv f φ z + K) := by
  intro x y z hxy hyz
  set g : ℝ → ℝ := fun t => if t + a = a then -Q else f (t + a) with hg
  have hglow : ∀ t, -Q ≤ g t := by
    intro t; simp only [hg]; split_ifs
    · exact le_rfl
    · exact hlow _
  have hgm : Measurable g := by
    refine Measurable.ite ?_ measurable_const (hfm.comp (measurable_id.add_const a))
    exact measurableSet_eq_fun (measurable_id.add_const a) measurable_const
  have hgA : AntitoneOn g (Iio 0) := by
    intro s hs t ht hst
    have hs' : s + a ≠ a := by simp only [mem_Iio] at hs; intro h; linarith
    have ht' : t + a ≠ a := by simp only [mem_Iio] at ht; intro h; linarith
    simp only [hg, if_neg hs', if_neg ht']
    exact hanti ((I_cases hI).1 (by simp only [mem_Iio] at hs; linarith))
      ((I_cases hI).1 (by simp only [mem_Iio] at ht; linarith)) (by linarith)
  have hgK : NonKDecreasingOn g K (Ici 0) := by
    intro s hs t ht hst
    simp only [mem_Ici] at hs ht
    rcases hs.lt_or_eq with hs | hs
    · have hs' : s + a ≠ a := by intro h; linarith
      have ht' : t + a ≠ a := by intro h; linarith
      simp only [hg, if_neg hs', if_neg ht']
      exact hnkd _ ((I_cases hI).2 (by linarith)) _ ((I_cases hI).2 (by linarith)) (by linarith)
    · have : g s = -Q := by simp only [hg]; rw [if_pos (by rw [← hs]; ring)]
      rw [this]; linarith [hglow t]
  have hgb : BddBelow (g '' Iio 0) := ⟨-Q, by rintro _ ⟨t, -, rfl⟩; exact hglow t⟩
  have hae : ∀ w, (fun ξ => g (w - ξ) * φ ξ) =ᵐ[volume] (fun ξ => f (w + a - ξ) * φ ξ) := by
    intro w
    filter_upwards [ae_ne_pt w] with ξ hξ
    have : w - ξ + a ≠ a := by intro h; apply hξ; linarith
    simp only [hg, if_neg this]
    rw [show w - ξ + a = w + a - ξ by ring]
  have hgi : ∀ w, Integrable (fun ξ => g (w - ξ) * φ ξ) := fun w =>
    (hint (w + a)).congr (hae w).symm
  have hconv : ∀ w, conv g φ w = conv f φ (w + a) := by
    intro w; unfold conv; exact integral_congr_ae (hae w)
  have := Lib.conv_quasiK hφ0 hφi hφ1 hT hgm hgA hgK hgb hgi
    (show x - a < y - a by linarith) (show y - a < z - a by linarith)
  simp only [hconv, sub_add_cancel] at this
  exact this

end NewA
end PorteusSS

open MeasureTheory Filter Topology Set PorteusSS in
theorem solution (a K : ℝ) (f φ : ℝ → ℝ) (hf : CaK a K f)
    (hφ : IsOneSidedPolyaDensity φ) :
    CK K (conv f φ) := by
  obtain ⟨hK, I, hI, hpc, hpf, hanti, hnkd, hco⟩ := hf
  obtain ⟨hφ0, hφi, hφ1, hT⟩ := PorteusSS.Lib.polya_facts hφ.1
  have hfm : Measurable f := PorteusSS.Lib.measurable_of_piecewiseContinuous hpc
  have hint : ∀ w, Integrable (fun ξ => f (w - ξ) * φ ξ) := hpf φ hφ.1.1
  obtain ⟨Q, hQ, hlow⟩ := PorteusSS.NewA.lower_bound hK hI hpc hanti hnkd
  have hcont : Continuous (PorteusSS.conv f φ) :=
    PorteusSS.NewA.conv_continuous hK hI hpc hfm hanti hnkd hQ hlow hφ0 hφi hint
  have hqk := PorteusSS.NewA.conv_qk hK hI hfm hanti hnkd hlow hφ0 hφi hφ1 hT hint
  have hcoG : Tendsto (PorteusSS.conv f φ) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    refine tendsto_sup.2 ⟨?_, ?_⟩
    · exact PorteusSS.Lib.conv_atBot hφ0 hφi hφ1 hφ.2 hint (hco.mono_left atBot_le_cocompact)
    · exact PorteusSS.Lib.conv_atTop hφ0 hφi hφ1 hQ hlow hint (hco.mono_left atTop_le_cocompact)
  obtain ⟨a', hA', hN'⟩ := PorteusSS.NewA.shape_of_qk hK hcont hcoG hqk
  have hPF : PorteusSS.PFIntegrable (PorteusSS.conv f φ) :=
    PorteusSS.NewA.pfint_conv hfm hpf hφ.1.1 hcont
  refine ⟨hK, hcont, a', hK, Iic a', Or.inr rfl, ⟨∅, by simp, ?_, by simp⟩, hPF, hA', hN', hcoG⟩
  simpa using hcont
