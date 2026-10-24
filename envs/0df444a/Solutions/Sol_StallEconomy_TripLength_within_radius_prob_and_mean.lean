-- Prove2me | solution 1 for StallEconomy.TripLength.within_radius_prob_and_mean
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:37:35.632729+00:00
-- url     : https://prove2.me/submissions/35e8c0ae-52f8-4cc1-a54d-dda2750910a1

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

open MeasureTheory Set

namespace TripRotTest
open StallEconomy.TripLength

noncomputable def rotL : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ :=
  (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)

lemma rotL_apply (p : ℝ × ℝ) : rotL p = (p.1 + p.2, p.1 - p.2) := rfl

lemma det_rotL : LinearMap.det rotL = -2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, rotL]
  norm_num

lemma map_rotL : Measure.map rotL (volume : Measure (ℝ × ℝ)) = ENNReal.ofReal (1/2) • volume := by
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (ℝ × ℝ))) (by rw [det_rotL]; norm_num)]
  rw [det_rotL]; norm_num

noncomputable def rinv (q : ℝ × ℝ) : ℝ × ℝ := ((q.1 + q.2) / 2, (q.1 - q.2) / 2)

lemma rinv_rot (p : ℝ × ℝ) : rinv (rotL p) = p := by
  ext <;> simp [rinv, rotL_apply]

lemma rot_rinv (q : ℝ × ℝ) : rotL (rinv q) = q := by
  ext <;> simp [rinv, rotL_apply] <;> ring

noncomputable def rotE : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toEquiv := ⟨rotL, rinv, rinv_rot, rot_rinv⟩
  measurable_toFun := by
    show Measurable (fun p : ℝ × ℝ => rotL p)
    simp only [rotL_apply]; fun_prop
  measurable_invFun := by
    show Measurable rinv
    unfold rinv; fun_prop

lemma integral_comp_rot (g : ℝ × ℝ → ℝ) : ∫ p, g (rotL p) = (1/2) * ∫ q, g q := by
  have h := rotE.measurableEmbedding.integral_map (μ := (volume : Measure (ℝ × ℝ))) g
  have hm : Measure.map rotE (volume : Measure (ℝ × ℝ)) = ENNReal.ofReal (1/2) • volume := map_rotL
  rw [hm, integral_smul_measure] at h
  rw [← show (fun p => g (rotE p)) = fun p => g (rotL p) from rfl, ← h]
  simp

def sq (c : ℝ) : Set (ℝ × ℝ) := Icc (-c) c ×ˢ Icc (-c) c

lemma abs_add_abs_le_iff (x y c : ℝ) : |x| + |y| ≤ c ↔ |x + y| ≤ c ∧ |x - y| ≤ c := by
  rw [abs_le, abs_le]
  rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;>
    rw [hx, hy] <;> constructor <;> intro h <;> (try obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h) <;>
    first | (refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith) | linarith

lemma mem_zone_iff (R : ℝ) (p : ℝ × ℝ) : p ∈ zone R ↔ rotL p ∈ sq (R / Real.sqrt 2) := by
  simp only [zone, sq, mem_setOf_eq, rotL_apply, mem_prod, mem_Icc, ← abs_le]
  exact abs_add_abs_le_iff _ _ _

lemma measurableSet_sq (c : ℝ) : MeasurableSet (sq c) := measurableSet_Icc.prod measurableSet_Icc

lemma measurableSet_zone (R : ℝ) : MeasurableSet (zone R) := by
  unfold zone
  exact measurableSet_le (by fun_prop) measurable_const

lemma setIntegral_zone (R : ℝ) (g : ℝ × ℝ → ℝ) :
    ∫ p in zone R, g p = (1/2) * ∫ q in sq (R / Real.sqrt 2), g (rinv q) := by
  rw [← integral_indicator (measurableSet_zone R), ← integral_indicator (measurableSet_sq _)]
  rw [← integral_comp_rot]
  congr 1; ext p
  by_cases hp : p ∈ zone R
  · have hp' := (mem_zone_iff R p).1 hp
    simp [indicator_of_mem hp, indicator_of_mem hp', rinv_rot]
  · have hp' : rotL p ∉ sq (R / Real.sqrt 2) := fun h => hp ((mem_zone_iff R p).2 h)
    simp [indicator_of_notMem hp, indicator_of_notMem hp']

lemma half_abs (u v : ℝ) : |(u + v) / 2| + |(u - v) / 2| = max |u| |v| := by
  rw [abs_div, abs_div, abs_two]
  rcases abs_cases (u+v) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (u-v) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases u with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rcases abs_cases v with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
    rw [h1, h2, h3, h4] <;>
    first
    | (rw [max_eq_left (by linarith)]; linarith)
    | (rw [max_eq_right (by linarith)]; linarith)
    | linarith

lemma l1_rot (s : ℝ) (x y : ℝ × ℝ) :
    l1 (s • rinv x) (rinv y) = max |s * x.1 - y.1| |s * x.2 - y.2| := by
  rw [← half_abs]
  simp only [l1, rinv, Prod.smul_mk, smul_eq_mul]
  congr 2 <;> ring_nf

lemma integral_sq_mul (c : ℝ) (f g : ℝ → ℝ) :
    ∫ y in sq c, f y.1 * g y.2 = (∫ y in Icc (-c) c, f y) * (∫ y in Icc (-c) c, g y) := by
  rw [sq, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_mul f g


lemma ite_max_le (a b t : ℝ) :
    (if max a b ≤ t then (1:ℝ) else 0) = (if a ≤ t then (1:ℝ) else 0) * (if b ≤ t then (1:ℝ) else 0) := by
  by_cases h1 : a ≤ t <;> by_cases h2 : b ≤ t <;> simp [h1, h2, max_le_iff]

lemma Q_eq (R s t : ℝ) :
    ∫ u in zone R, ∫ b in zone R, (if l1 (s • u) b ≤ t then (1:ℝ) else 0)
      = (1/4) * (∫ x in Icc (-(R / Real.sqrt 2)) (R / Real.sqrt 2),
          ∫ y in Icc (-(R / Real.sqrt 2)) (R / Real.sqrt 2), if |s * x - y| ≤ t then (1:ℝ) else 0) ^ 2 := by
  set c := R / Real.sqrt 2 with hc
  set κ : ℝ → ℝ := fun x => ∫ y in Icc (-c) c, if |s * x - y| ≤ t then (1:ℝ) else 0 with hκ
  have inner : ∀ x : ℝ × ℝ, ∫ b in zone R, (if l1 (s • rinv x) b ≤ t then (1:ℝ) else 0)
      = (1/2) * (κ x.1 * κ x.2) := by
    intro x
    rw [setIntegral_zone]
    congr 1
    simp only [l1_rot, ite_max_le]
    exact integral_sq_mul c (fun y => if |s * x.1 - y| ≤ t then (1:ℝ) else 0)
      (fun y => if |s * x.2 - y| ≤ t then (1:ℝ) else 0)
  rw [setIntegral_zone]
  simp only [inner]
  rw [integral_const_mul, integral_sq_mul c κ κ]
  ring

lemma kappa_eq (s x t c : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx : |x| ≤ c) (ht : 0 ≤ t) :
    ∫ y in Icc (-c) c, (if |s * x - y| ≤ t then (1:ℝ) else 0)
      = 2 * t - max (s * x + t - c) 0 - max (t - c - s * x) 0 := by
  have h1 : (fun y => if |s * x - y| ≤ t then (1:ℝ) else 0)
      = (Icc (s * x - t) (s * x + t)).indicator 1 := by
    ext y
    by_cases h : |s * x - y| ≤ t
    · rw [if_pos h, indicator_of_mem]; · rfl
      rw [abs_le] at h; constructor <;> linarith
    · rw [if_neg h, indicator_of_notMem]
      intro hy; apply h; rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  rw [h1, integral_indicator_one measurableSet_Icc, measureReal_restrict_apply measurableSet_Icc,
    Icc_inter_Icc, Real.volume_real_Icc]
  have hsx : |s * x| ≤ c := by
    rw [abs_mul, abs_of_nonneg hs0]
    nlinarith [abs_nonneg x]
  rw [abs_le] at hsx
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma hasDerivAt_pp_sq (u : ℝ) : HasDerivAt (fun y : ℝ => (max y 0) ^ 2 / 2) (max u 0) u := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have : (fun y : ℝ => (max y 0) ^ 2 / 2) =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hu] with y hy
      rw [max_eq_right (le_of_lt hy)]; ring
    rw [max_eq_right hu.le]
    exact (hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq this
  · subst hu
    rw [max_self, hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, max_self, smul_zero, sub_zero]
    refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) one_lt_two)
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun h => ?_)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero,
      Real.norm_eq_abs, one_mul]
    rw [abs_div, abs_pow, abs_pow, abs_two]
    have : |max h 0| ≤ |h| := by
      rcases le_total h 0 with hh | hh
      · rw [max_eq_right hh]; simp
      · rw [max_eq_left hh]
    have h2 : |max h 0| ^ 2 ≤ |h| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    have h3 : (0:ℝ) ≤ |h| ^ 2 := by positivity
    linarith
  · have : (fun y : ℝ => (max y 0) ^ 2 / 2) =ᶠ[nhds u] fun y => y ^ 2 / 2 := by
      filter_upwards [Ioi_mem_nhds hu] with y hy
      rw [max_eq_left (le_of_lt hy)]
    rw [max_eq_left hu.le]
    have hd : HasDerivAt (fun y : ℝ => y ^ 2 / 2) u u := by
      have h := ((hasDerivAt_id u).mul (hasDerivAt_id u)).div_const 2
      have e : (fun y : ℝ => y ^ 2 / 2) = (fun y => id y * id y / 2) := by ext y; simp only [id]; ring
      rw [e]
      exact h.congr_deriv (by simp)
    exact hd.congr_of_eventuallyEq this

lemma integral_pp (α β : ℝ) :
    ∫ u in α..β, max u 0 = (max β 0) ^ 2 / 2 - (max α 0) ^ 2 / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_pp_sq u)]
  exact (continuous_id.max continuous_const).intervalIntegrable _ _

lemma A_eq (c s t : ℝ) (hc : 0 ≤ c) (hs0 : 0 < s) (hs1 : s ≤ 1) (ht : 0 ≤ t) :
    ∫ x in Icc (-c) c, ∫ y in Icc (-c) c, (if |s * x - y| ≤ t then (1:ℝ) else 0)
      = 4 * c * t - ((max (s * c + t - c) 0) ^ 2 - (max (t - c - s * c) 0) ^ 2) / s := by
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun x => 2 * t - max (s * x + t - c) 0 - max (t - c - s * x) 0)
    (fun x hx => kappa_eq s x t c hs0.le hs1 (abs_le.2 hx) ht)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have i1 : IntervalIntegrable (fun x : ℝ => max (s * x + t - c) 0) volume (-c) c := by
    apply Continuous.intervalIntegrable; fun_prop
  have i2 : IntervalIntegrable (fun x : ℝ => max (t - c - s * x) 0) volume (-c) c := by
    apply Continuous.intervalIntegrable; fun_prop
  have i0 : IntervalIntegrable (fun x : ℝ => 2 * t - max (s * x + t - c) 0) volume (-c) c := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub i0 i2, intervalIntegral.integral_sub intervalIntegrable_const i1,
    intervalIntegral.integral_const]
  have e1 : ∫ x in (-c)..c, max (s * x + t - c) 0 = s⁻¹ * ((max (s * c + t - c) 0) ^ 2 / 2 - (max (t - c - s * c) 0) ^ 2 / 2) := by
    have := intervalIntegral.integral_comp_mul_add (a := -c) (b := c) (fun u => max u 0) hs0.ne' (t - c)
    simp only [smul_eq_mul] at this
    rw [show (fun x => max (s * x + t - c) 0) = fun x => max (s * x + (t - c)) 0 by ext x; ring_nf, this,
      integral_pp]
    have a1 : s * -c + (t - c) = t - c - s * c := by ring
    have a2 : s * c + (t - c) = s * c + t - c := by ring
    rw [a1, a2]
  have e2 : ∫ x in (-c)..c, max (t - c - s * x) 0 = s⁻¹ * ((max (s * c + t - c) 0) ^ 2 / 2 - (max (t - c - s * c) 0) ^ 2 / 2) := by
    have := intervalIntegral.integral_comp_mul_add (a := -c) (b := c) (fun u => max u 0) (neg_ne_zero.2 hs0.ne') (t - c)
    simp only [smul_eq_mul] at this
    rw [show (fun x => max (t - c - s * x) 0) = fun x => max (-s * x + (t - c)) 0 by ext x; ring_nf, this,
      integral_pp]
    rw [inv_neg]
    have a1 : -s * c + (t - c) = t - c - s * c := by ring
    have a2 : -s * -c + (t - c) = s * c + t - c := by ring
    rw [a1, a2]; ring
  rw [e1, e2, smul_eq_mul]
  field_simp
  ring

lemma layer (ρ K m : ℝ) (hm : m ≤ K) (ψ : ℝ → ℝ) :
    ∫ t in Ioc ρ K, ψ t * (if t < m then (1:ℝ) else 0) = if m ≤ ρ then 0 else ∫ t in ρ..m, ψ t := by
  have h1 : (fun t => ψ t * (if t < m then (1:ℝ) else 0)) = (Iio m).indicator ψ := by
    ext t; by_cases h : t < m
    · simp [h]
    · simp [h]
  rw [h1, setIntegral_indicator measurableSet_Iio]
  split_ifs with h
  · have : Ioc ρ K ∩ Iio m = ∅ := by
      ext t; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_empty_iff_false, iff_false]
      intro ⟨⟨h1, _⟩, h3⟩; linarith
    rw [this]; simp
  · push_neg at h
    have : Ioc ρ K ∩ Iio m = Ioo ρ m := by
      ext t; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · intro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · intro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [this, intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo]


lemma integrable_ind {γ : Type*} [MeasurableSpace γ] (P : Measure γ) [IsFiniteMeasure P]
    (g : γ → ℝ) (hg : Measurable g) (t : ℝ) :
    Integrable (fun w => if g w ≤ t then (1:ℝ) else 0) P := by
  refine (integrable_const (1:ℝ)).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
  · exact (Measurable.ite (measurableSet_le hg measurable_const) measurable_const
      measurable_const).aestronglyMeasurable
  · split_ifs <;> simp

lemma fubini_core {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : α × β → ℝ) (hf : Measurable f)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (ρ K : ℝ) :
    ∫ u, ∫ b, (∫ t in Ioc ρ K, ψ t * (if t < f (u, b) then (1:ℝ) else 0)) ∂ν ∂μ
      = ∫ t in Ioc ρ K, ψ t * (μ.real univ * ν.real univ
          - ∫ u, ∫ b, (if f (u, b) ≤ t then (1:ℝ) else 0) ∂ν ∂μ) := by
  set P := μ.prod ν
  set F : (α × β) × ℝ → ℝ := fun p => ψ p.2 * (if p.2 < f p.1 then (1:ℝ) else 0) with hFdef
  have hψi : Integrable ψ (volume.restrict (Ioc ρ K)) := hψ.integrableOn_Ioc
  have hF : Integrable F (P.prod (volume.restrict (Ioc ρ K))) := by
    refine (hψi.comp_snd P).mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (Measurable.ite (measurableSet_lt measurable_snd (hf.comp measurable_fst))
        measurable_const measurable_const).aestronglyMeasurable
    · split_ifs <;> simp
  have step1 : ∫ u, ∫ b, (∫ t in Ioc ρ K, ψ t * (if t < f (u, b) then (1:ℝ) else 0)) ∂ν ∂μ
      = ∫ w, (∫ t in Ioc ρ K, F (w, t)) ∂P := by
    rw [integral_prod _ hF.integral_prod_left]
  have step2 : ∫ w, (∫ t in Ioc ρ K, F (w, t)) ∂P = ∫ t in Ioc ρ K, ∫ w, F (w, t) ∂P :=
    integral_integral_swap (f := fun w t => F (w, t)) hF
  rw [step1, step2]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
  simp only [hFdef]
  rw [integral_const_mul]
  congr 1
  have hi := integrable_ind P f hf t
  have e : (fun w => if t < f w then (1:ℝ) else 0) = fun w => 1 - (if f w ≤ t then (1:ℝ) else 0) := by
    ext w; by_cases h : f w ≤ t
    · simp [h, not_lt.2 h]
    · simp [h, lt_of_not_ge h]
  rw [e, integral_sub (integrable_const _) hi, integral_const, ← integral_prod _ hi]
  simp [P, measureReal_def, Measure.prod_prod, ← univ_prod_univ]


lemma integral_poly5 (a0 a1 a2 a3 a4 a5 x : ℝ) :
    ∫ τ in (0:ℝ)..x, (a0 + a1 * τ + a2 * τ ^ 2 + a3 * τ ^ 3 + a4 * τ ^ 4 + a5 * τ ^ 5)
      = a0 * x + a1 * x ^ 2 / 2 + a2 * x ^ 3 / 3 + a3 * x ^ 4 / 4 + a4 * x ^ 5 / 5 + a5 * x ^ 6 / 6 := by
  have hd : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => a0 * τ + a1 * τ ^ 2 / 2 + a2 * τ ^ 3 / 3 + a3 * τ ^ 4 / 4
      + a4 * τ ^ 5 / 5 + a5 * τ ^ 6 / 6)
      (a0 + a1 * τ + a2 * τ ^ 2 + a3 * τ ^ 3 + a4 * τ ^ 4 + a5 * τ ^ 5) τ := by
    intro τ
    have h := ((((((hasDerivAt_id τ).const_mul a0).add
      ((((hasDerivAt_id τ).pow 2).const_mul a1).div_const 2)).add
      ((((hasDerivAt_id τ).pow 3).const_mul a2).div_const 3)).add
      ((((hasDerivAt_id τ).pow 4).const_mul a3).div_const 4)).add
      ((((hasDerivAt_id τ).pow 5).const_mul a4).div_const 5)).add
      ((((hasDerivAt_id τ).pow 6).const_mul a5).div_const 6)
    refine h.congr_deriv ?_
    simp only [id]
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hd τ)]
  · ring
  · apply Continuous.intervalIntegrable; fun_prop

lemma zone_sub_sq (R : ℝ) : zone R ⊆ sq (R / Real.sqrt 2) := by
  intro p hp
  simp only [zone, mem_setOf_eq] at hp
  simp only [sq, mem_prod, mem_Icc]
  have := abs_nonneg p.1
  have := abs_nonneg p.2
  exact ⟨abs_le.1 (by linarith), abs_le.1 (by linarith)⟩

lemma finite_zone (R : ℝ) : IsFiniteMeasure (volume.restrict (zone R)) := by
  have : volume (zone R) < ⊤ := (measure_mono (zone_sub_sq R)).trans_lt
    ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)
  exact isFiniteMeasure_restrict.2 this.ne

lemma vol_zone (R : ℝ) (hR : 0 < R) : (volume.restrict (zone R)).real univ = R ^ 2 := by
  have h1 : (volume.restrict (zone R)).real univ = ∫ p in zone R, (1:ℝ) := by
    haveI := finite_zone R
    rw [integral_const]; simp
  rw [h1, setIntegral_zone]
  have := integral_sq_mul (R / Real.sqrt 2) (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
  simp only [mul_one] at this
  rw [this, integral_const]
  have hc : 0 ≤ R / Real.sqrt 2 := by positivity
  simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul, mul_one,
    measureReal_restrict_apply MeasurableSet.univ, Real.volume_real_Icc_of_le (by linarith : -(R / Real.sqrt 2) ≤ R / Real.sqrt 2)]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [h2]; ring

noncomputable def Aint (R s t : ℝ) : ℝ :=
  ∫ x in Icc (-(R / Real.sqrt 2)) (R / Real.sqrt 2),
    ∫ y in Icc (-(R / Real.sqrt 2)) (R / Real.sqrt 2), if |s * x - y| ≤ t then (1:ℝ) else 0

lemma measurable_l1s (s : ℝ) : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => l1 (s • w.1) w.2) := by
  unfold l1; fun_prop

lemma E_layer (R r ρ K : ℝ) (hR : 0 < R) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (F : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hF : ∀ u ∈ zone R, ∀ b ∈ zone R, F (shrink R r • u) b
      = ∫ t in Ioc ρ K, ψ t * (if t < l1 (shrink R r • u) b then (1:ℝ) else 0)) :
    E R r F = (1 / R ^ 4) * ∫ t in Ioc ρ K, ψ t * (R ^ 2 * R ^ 2 - (1/4) * Aint R (shrink R r) t ^ 2) := by
  haveI := finite_zone R
  unfold E
  congr 1
  rw [setIntegral_congr_fun (measurableSet_zone R) (fun u hu =>
    setIntegral_congr_fun (measurableSet_zone R) (fun b hb => hF u hu b hb))]
  have := fubini_core (volume.restrict (zone R)) (volume.restrict (zone R))
    (fun w => l1 (shrink R r • w.1) w.2) (measurable_l1s _) ψ hψ ρ K
  simp only at this
  rw [this]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
  rw [vol_zone R hR, Q_eq]
  rfl


lemma shrink_facts (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    0 < R / Real.sqrt 2 ∧ R ^ 2 = 2 * (R / Real.sqrt 2) ^ 2 ∧
      shrink R r * (R / Real.sqrt 2) = R / Real.sqrt 2 - r ∧ 0 ≤ shrink R r ∧ shrink R r ≤ 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : 0 < Real.sqrt 2 := by positivity
  have hc : 0 < R / Real.sqrt 2 := by positivity
  have hsc : shrink R r * (R / Real.sqrt 2) = R / Real.sqrt 2 - r := by
    unfold shrink; field_simp
  refine ⟨hc, ?_, hsc, ?_, ?_⟩
  · field_simp; rw [h2]
  · have : 0 ≤ shrink R r * (R / Real.sqrt 2) := by rw [hsc]; linarith
    exact nonneg_of_mul_nonneg_left this hc
  · unfold shrink
    have : 0 ≤ Real.sqrt 2 * r / R := by positivity
    linarith

lemma l1_le_K (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) (u b : ℝ × ℝ)
    (hu : u ∈ zone R) (hb : b ∈ zone R) :
    0 ≤ l1 (shrink R r • u) b ∧ l1 (shrink R r • u) b ≤ 2 * (R / Real.sqrt 2) - r := by
  obtain ⟨hc, -, hsc, hs0, -⟩ := shrink_facts R r hR hr0 hr
  simp only [zone, mem_setOf_eq] at hu hb
  unfold l1
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · positivity
  have e1 : |shrink R r * u.1 - b.1| ≤ shrink R r * |u.1| + |b.1| := by
    calc _ ≤ |shrink R r * u.1| + |b.1| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg hs0]
  have e2 : |shrink R r * u.2 - b.2| ≤ shrink R r * |u.2| + |b.2| := by
    calc _ ≤ |shrink R r * u.2| + |b.2| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg hs0]
  have e3 : shrink R r * (|u.1| + |u.2|) ≤ shrink R r * (R / Real.sqrt 2) :=
    mul_le_mul_of_nonneg_left hu hs0
  nlinarith

lemma Aint_eq (R r t : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r < R / Real.sqrt 2)
    (ht : t ∈ Ioc r (2 * (R / Real.sqrt 2) - r)) :
    Aint R (shrink R r) t = 4 * (R / Real.sqrt 2) * t - (t - r) ^ 2 / shrink R r := by
  obtain ⟨hc, -, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr.le
  have hspos : 0 < shrink R r := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hsc; linarith
  unfold Aint
  rw [A_eq _ _ _ hc.le hspos hs1 (by linarith [ht.1]), hsc]
  rw [max_eq_left (by linarith [ht.1]), max_eq_right (by linarith [ht.2])]
  ring_nf


lemma meanL_lt (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r < R / Real.sqrt 2) :
    meanL R r = 2 * (R / Real.sqrt 2 - r) ^ 2 * (7 * (R / Real.sqrt 2) + 3 * r)
      / (15 * (R / Real.sqrt 2) ^ 2) := by
  obtain ⟨hc, hR2, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr.le
  have hF : ∀ u ∈ zone R, ∀ b ∈ zone R, Lr r (shrink R r • u) b
      = ∫ t in Ioc r (2 * (R / Real.sqrt 2) - r), (fun _ => (1:ℝ)) t *
          (if t < l1 (shrink R r • u) b then (1:ℝ) else 0) := by
    intro u hu b hb
    obtain ⟨-, hK⟩ := l1_le_K R r hR hr0 hr.le u b hu hb
    rw [layer r _ _ hK]
    unfold Lr
    split_ifs with h
    · exact max_eq_right (by linarith)
    · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
      exact max_eq_left (by linarith)
  unfold meanL
  rw [E_layer R r r _ hR (fun _ => 1) continuous_const (Lr r) hF]
  set c := R / Real.sqrt 2 with hcdef
  set s := shrink R r with hsdef
  have ha : 0 < c - r := by linarith
  have hseq : s = (c - r) / c := by field_simp; linarith
  have h1 : ∫ t in Ioc r (2 * c - r), (fun _ => (1:ℝ)) t * (R ^ 2 * R ^ 2 - 1 / 4 * Aint R s t ^ 2)
      = ∫ t in r..(2 * c - r), (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    simp only [one_mul]
    rw [Aint_eq R r t hR hr0 hr ht]
  have h2 : ∫ t in r..(2 * c - r), (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2)
      = ∫ τ in (0:ℝ)..(2 * (c - r)), (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * (τ + r) - (τ + r - r) ^ 2 / s) ^ 2) := by
    rw [intervalIntegral.integral_comp_add_right
      (fun t => R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2) r]
    congr 1 <;> ring
  have h3 : ∫ τ in (0:ℝ)..(2 * (c - r)), (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * (τ + r) - (τ + r - r) ^ 2 / s) ^ 2)
      = ∫ τ in (0:ℝ)..(2 * (c - r)), ((4 * c ^ 4 - 4 * c ^ 2 * r ^ 2) + (-8 * c ^ 2 * r) * τ
          + ((-4 * (c - r) * c ^ 2 + 2 * c ^ 2 * r) / (c - r)) * τ ^ 2 + (2 * c ^ 2 / (c - r)) * τ ^ 3
          + (-c ^ 2 / (4 * (c - r) ^ 2)) * τ ^ 4 + 0 * τ ^ 5) := by
    refine intervalIntegral.integral_congr (fun τ _ => ?_)
    rw [hR2, hseq]
    field_simp
    ring
  rw [h1, h2, h3, integral_poly5]
  rw [show R ^ 4 = (R ^ 2) ^ 2 by ring, hR2]
  field_simp
  ring

lemma secondL_lt (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r < R / Real.sqrt 2) :
    E R r (fun a b => Lr r a b ^ 2) = 4 * (R / Real.sqrt 2 - r) ^ 3 * (4 * (R / Real.sqrt 2) + r)
      / (15 * (R / Real.sqrt 2) ^ 2) := by
  obtain ⟨hc, hR2, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr.le
  have hF : ∀ u ∈ zone R, ∀ b ∈ zone R, (fun a b => Lr r a b ^ 2) (shrink R r • u) b
      = ∫ t in Ioc r (2 * (R / Real.sqrt 2) - r), (fun t => 2 * (t - r)) t *
          (if t < l1 (shrink R r • u) b then (1:ℝ) else 0) := by
    intro u hu b hb
    obtain ⟨-, hK⟩ := l1_le_K R r hR hr0 hr.le u b hu hb
    rw [layer r _ _ hK]
    unfold Lr
    beta_reduce
    split_ifs with h
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_left (by linarith)]
      rw [intervalIntegral.integral_comp_sub_right (fun x => 2 * x) r, sub_self,
        intervalIntegral.integral_const_mul, integral_id]
      ring
  rw [E_layer R r r _ hR (fun t => 2 * (t - r)) (by fun_prop) _ hF]
  set c := R / Real.sqrt 2 with hcdef
  set s := shrink R r with hsdef
  have ha : 0 < c - r := by linarith
  have hseq : s = (c - r) / c := by field_simp; linarith
  have h1 : ∫ t in Ioc r (2 * c - r), (fun t => 2 * (t - r)) t * (R ^ 2 * R ^ 2 - 1 / 4 * Aint R s t ^ 2)
      = ∫ t in r..(2 * c - r), 2 * (t - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    simp only
    rw [Aint_eq R r t hR hr0 hr ht]
  have h2 : ∫ t in r..(2 * c - r), 2 * (t - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2)
      = ∫ τ in (0:ℝ)..(2 * (c - r)), 2 * (τ + r - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * (τ + r) - (τ + r - r) ^ 2 / s) ^ 2) := by
    rw [intervalIntegral.integral_comp_add_right
      (fun t => 2 * (t - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2)) r]
    congr 1 <;> ring
  have h3 : ∫ τ in (0:ℝ)..(2 * (c - r)), 2 * (τ + r - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * (τ + r) - (τ + r - r) ^ 2 / s) ^ 2)
      = ∫ τ in (0:ℝ)..(2 * (c - r)), (0 + (8 * c ^ 4 - 8 * c ^ 2 * r ^ 2) * τ + (-16 * c ^ 2 * r) * τ ^ 2
          + ((-8 * (c - r) * c ^ 2 + 4 * c ^ 2 * r) / (c - r)) * τ ^ 3 + (4 * c ^ 2 / (c - r)) * τ ^ 4
          + (-c ^ 2 / (2 * (c - r) ^ 2)) * τ ^ 5) := by
    refine intervalIntegral.integral_congr (fun τ _ => ?_)
    rw [hR2, hseq]
    field_simp
    ring
  rw [h1, h2, h3, integral_poly5]
  rw [show R ^ 4 = (R ^ 2) ^ 2 by ring, hR2]
  field_simp
  ring


lemma E_zero (R r : ℝ) (hR : 0 < R) (hr : r = R / Real.sqrt 2) (F : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hF : ∀ b ∈ zone R, F 0 b = 0) : E R r F = 0 := by
  have hs : shrink R r = 0 := by
    unfold shrink; rw [hr]
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp; ring
  unfold E
  rw [hs]
  simp only [zero_smul]
  rw [setIntegral_congr_fun (measurableSet_zone R) (g := fun _ => (0:ℝ)) (fun u _ => by
    simp only
    rw [setIntegral_congr_fun (measurableSet_zone R) (g := fun _ => (0:ℝ)) (fun b hb => hF b hb)]
    simp)]
  simp

lemma Lr_zero (R r : ℝ) (hr : r = R / Real.sqrt 2) (b : ℝ × ℝ) (hb : b ∈ zone R) : Lr r 0 b = 0 := by
  simp only [zone, mem_setOf_eq] at hb
  unfold Lr l1
  simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, abs_neg]
  exact max_eq_right (by linarith)

noncomputable def fm (c r : ℝ) : ℝ := (c - r) ^ 2 * (7 * c + 3 * r)
noncomputable def fv (c r : ℝ) : ℝ := (c - r) ^ 3 * (11 * c ^ 3 + 22 * c ^ 2 * r + 33 * c * r ^ 2 + 9 * r ^ 3)

lemma meanL_c (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    meanL R r = 2 * fm (R / Real.sqrt 2) r / (15 * (R / Real.sqrt 2) ^ 2) := by
  rcases hr.lt_or_eq with h | h
  · rw [meanL_lt R r hR hr0 h, fm]; ring
  · unfold meanL
    rw [E_zero R r hR h _ (fun b hb => Lr_zero R r h b hb), fm, ← h]; simp

lemma secondL_c (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => Lr r a b ^ 2) = 4 * (R / Real.sqrt 2 - r) ^ 3 * (4 * (R / Real.sqrt 2) + r)
      / (15 * (R / Real.sqrt 2) ^ 2) := by
  rcases hr.lt_or_eq with h | h
  · exact secondL_lt R r hR hr0 h
  · rw [E_zero R r hR h _ (fun b hb => by beta_reduce; rw [Lr_zero R r h b hb]; ring), ← h]; simp

lemma varL_c (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    varL R r = 4 * fv (R / Real.sqrt 2) r / (225 * (R / Real.sqrt 2) ^ 4) := by
  unfold varL
  rw [secondL_c R r hR hr0 hr, meanL_c R r hR hr0 hr, fm, fv]
  have hc : 0 < R / Real.sqrt 2 := by positivity
  field_simp
  ring

lemma alg_mean (q c r : ℝ) (hq : q ^ 2 = 2) (hc : 0 < c) (hq0 : 0 < q) :
    2 * fm c r / (15 * c ^ 2) = (7 * q * (q * c) ^ 3 - 22 * (q * c) ^ 2 * r + 2 * q * (q * c) * r ^ 2
      + 12 * r ^ 3) / (15 * (q * c) ^ 2) := by
  rw [div_eq_div_iff (by positivity) (by positivity), fm]
  linear_combination (-105*c^5*q^2 + 90*c^2*r^3) * hq

lemma alg_var (q c r : ℝ) (hq : q ^ 2 = 2) (hc : 0 < c) (hq0 : 0 < q) :
    4 * fv c r / (225 * c ^ 4) = (22 * (q * c) ^ 6 - 22 * q * (q * c) ^ 5 * r - 140 * q * (q * c) ^ 3 * r ^ 3
      + 400 * (q * c) ^ 2 * r ^ 4 - 48 * q * (q * c) * r ^ 5 - 144 * r ^ 6) / (225 * (q * c) ^ 4) := by
  rw [div_eq_div_iff (by positivity) (by positivity), fv]
  linear_combination (450*c^4*(-11*c^6*q^4 + 11*c^5*q^4*r + 100*c^2*q^2*r^4 - 12*c*q^2*r^5
    - 18*q^2*r^6 - 36*r^6)) * hq

lemma fm_anti (c r1 r2 : ℝ) (h0 : 0 ≤ r1) (h12 : r1 ≤ r2) (h2 : r2 ≤ c) : fm c r2 ≤ fm c r1 := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ r2 = r1 + d := ⟨r2 - r1, by linarith, by ring⟩
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ c = r1 + d + x := ⟨c - r1 - d, by linarith, by ring⟩
  unfold fm
  rw [← sub_nonneg]
  ring_nf
  repeat' (first | assumption | positivity | apply add_nonneg | apply mul_nonneg | apply pow_nonneg)

lemma fv_anti (c r1 r2 : ℝ) (h0 : 0 ≤ r1) (h12 : r1 ≤ r2) (h2 : r2 ≤ c) : fv c r2 ≤ fv c r1 := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ r2 = r1 + d := ⟨r2 - r1, by linarith, by ring⟩
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ c = r1 + d + x := ⟨c - r1 - d, by linarith, by ring⟩
  unfold fv
  rw [← sub_nonneg]
  ring_nf
  repeat' (first | assumption | positivity | apply add_nonneg | apply mul_nonneg | apply pow_nonneg)

lemma fm_mono (c1 c2 r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ c1) (h12 : c1 ≤ c2) :
    fm c1 r * c2 ^ 2 ≤ fm c2 r * c1 ^ 2 := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ c1 = r + x := ⟨c1 - r, by linarith, by ring⟩
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ c2 = r + x + d := ⟨c2 - r - x, by linarith, by ring⟩
  unfold fm
  rw [← sub_nonneg]
  ring_nf
  repeat' (first | assumption | positivity | apply add_nonneg | apply mul_nonneg | apply pow_nonneg)

lemma fv_mono (c1 c2 r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ c1) (h12 : c1 ≤ c2) :
    fv c1 r * c2 ^ 4 ≤ fv c2 r * c1 ^ 4 := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ c1 = r + x := ⟨c1 - r, by linarith, by ring⟩
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ c2 = r + x + d := ⟨c2 - r - x, by linarith, by ring⟩
  unfold fv
  rw [← sub_nonneg]
  ring_nf
  repeat' (first | assumption | positivity | apply add_nonneg | apply mul_nonneg | apply pow_nonneg)


lemma Aint_low (R r t : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2)
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    Aint R (shrink R r) t = 4 * (R / Real.sqrt 2) * t := by
  obtain ⟨hc, -, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr
  unfold Aint
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => 2 * t) (fun x hx => by
    rw [kappa_eq _ x t _ hs0 hs1 (abs_le.2 hx) ht0]
    have h1 : shrink R r * x ≤ shrink R r * (R / Real.sqrt 2) := mul_le_mul_of_nonneg_left hx.2 hs0
    have h2 : shrink R r * (-(R / Real.sqrt 2)) ≤ shrink R r * x := mul_le_mul_of_nonneg_left hx.1 hs0
    rw [max_eq_right (by nlinarith), max_eq_right (by nlinarith)]
    ring)]
  rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
  ring

lemma Jm (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    ∫ t in r..(2 * (R / Real.sqrt 2) - r), (R ^ 2 * R ^ 2 - 1 / 4 *
      (4 * (R / Real.sqrt 2) * t - (t - r) ^ 2 / shrink R r) ^ 2)
      = R ^ 4 * (2 * (R / Real.sqrt 2 - r) ^ 2 * (7 * (R / Real.sqrt 2) + 3 * r)
        / (15 * (R / Real.sqrt 2) ^ 2)) := by
  obtain ⟨hc, hR2, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr
  set c := R / Real.sqrt 2 with hcdef
  set s := shrink R r with hsdef
  rcases hr.lt_or_eq with hr' | hr'
  · have ha : 0 < c - r := by linarith
    have hseq : s = (c - r) / c := by field_simp; linarith
    have h2 : ∫ t in r..(2 * c - r), (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2)
        = ∫ τ in (0:ℝ)..(2 * (c - r)), (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * (τ + r) - (τ + r - r) ^ 2 / s) ^ 2) := by
      rw [intervalIntegral.integral_comp_add_right
        (fun t => R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2) r]
      congr 1 <;> ring
    have h3 : ∫ τ in (0:ℝ)..(2 * (c - r)), (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * (τ + r) - (τ + r - r) ^ 2 / s) ^ 2)
        = ∫ τ in (0:ℝ)..(2 * (c - r)), ((4 * c ^ 4 - 4 * c ^ 2 * r ^ 2) + (-8 * c ^ 2 * r) * τ
            + ((-4 * (c - r) * c ^ 2 + 2 * c ^ 2 * r) / (c - r)) * τ ^ 2 + (2 * c ^ 2 / (c - r)) * τ ^ 3
            + (-c ^ 2 / (4 * (c - r) ^ 2)) * τ ^ 4 + 0 * τ ^ 5) := by
      refine intervalIntegral.integral_congr (fun τ _ => ?_)
      rw [hR2, hseq]
      field_simp
      ring
    rw [h2, h3, integral_poly5]
    rw [show R ^ 4 = (R ^ 2) ^ 2 by ring, hR2]
    field_simp
    ring
  · rw [← hr', show 2 * r - r = r by ring, intervalIntegral.integral_same]
    simp

lemma Js (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    ∫ t in r..(2 * (R / Real.sqrt 2) - r), 2 * (t - r) * (R ^ 2 * R ^ 2 - 1 / 4 *
      (4 * (R / Real.sqrt 2) * t - (t - r) ^ 2 / shrink R r) ^ 2)
      = R ^ 4 * (4 * (R / Real.sqrt 2 - r) ^ 3 * (4 * (R / Real.sqrt 2) + r)
        / (15 * (R / Real.sqrt 2) ^ 2)) := by
  obtain ⟨hc, hR2, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr
  set c := R / Real.sqrt 2 with hcdef
  set s := shrink R r with hsdef
  rcases hr.lt_or_eq with hr' | hr'
  · have ha : 0 < c - r := by linarith
    have hseq : s = (c - r) / c := by field_simp; linarith
    have h2 : ∫ t in r..(2 * c - r), 2 * (t - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2)
        = ∫ τ in (0:ℝ)..(2 * (c - r)), 2 * (τ + r - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * (τ + r) - (τ + r - r) ^ 2 / s) ^ 2) := by
      rw [intervalIntegral.integral_comp_add_right
        (fun t => 2 * (t - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2)) r]
      congr 1 <;> ring
    have h3 : ∫ τ in (0:ℝ)..(2 * (c - r)), 2 * (τ + r - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * (τ + r) - (τ + r - r) ^ 2 / s) ^ 2)
        = ∫ τ in (0:ℝ)..(2 * (c - r)), (0 + (8 * c ^ 4 - 8 * c ^ 2 * r ^ 2) * τ + (-16 * c ^ 2 * r) * τ ^ 2
            + ((-8 * (c - r) * c ^ 2 + 4 * c ^ 2 * r) / (c - r)) * τ ^ 3 + (4 * c ^ 2 / (c - r)) * τ ^ 4
            + (-c ^ 2 / (2 * (c - r) ^ 2)) * τ ^ 5) := by
      refine intervalIntegral.integral_congr (fun τ _ => ?_)
      rw [hR2, hseq]
      field_simp
      ring
    rw [h2, h3, integral_poly5]
    rw [show R ^ 4 = (R ^ 2) ^ 2 by ring, hR2]
    field_simp
    ring
  · rw [← hr', show 2 * r - r = r by ring, intervalIntegral.integral_same]
    simp

lemma E_split (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (F : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hF : ∀ u ∈ zone R, ∀ b ∈ zone R, F (shrink R r • u) b
      = ∫ t in Ioc 0 (2 * (R / Real.sqrt 2) - r), ψ t * (if t < l1 (shrink R r • u) b then (1:ℝ) else 0)) :
    E R r F = (1 / R ^ 4) * ((∫ t in (0:ℝ)..r, ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * (R / Real.sqrt 2) * t) ^ 2))
      + ∫ t in r..(2 * (R / Real.sqrt 2) - r), ψ t * (R ^ 2 * R ^ 2 - 1 / 4 *
          (4 * (R / Real.sqrt 2) * t - (t - r) ^ 2 / shrink R r) ^ 2)) := by
  rw [E_layer R r 0 _ hR ψ hψ F hF]
  congr 1
  have hK : r ≤ 2 * (R / Real.sqrt 2) - r := by linarith
  set c := R / Real.sqrt 2 with hcdef
  set s := shrink R r with hsdef
  have e1 : EqOn (fun t => ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t) ^ 2))
      (fun t => ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * Aint R s t ^ 2)) (Ioc 0 r) := by
    intro t ht
    simp only
    rw [Aint_low R r t hR hr0 hr ht.1.le ht.2]
  have e2 : EqOn (fun t => ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2))
      (fun t => ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * Aint R s t ^ 2)) (Ioc r (2 * c - r)) := by
    intro t ht
    simp only
    have hr' : r < c := by linarith [ht.1, ht.2]
    rw [Aint_eq R r t hR hr0 hr' ht]
  have i1 : IntegrableOn (fun t => ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t) ^ 2)) (Ioc 0 r) :=
    (by fun_prop : Continuous (fun t => ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t) ^ 2))).integrableOn_Ioc
  have i2 : IntegrableOn (fun t => ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2))
      (Ioc r (2 * c - r)) :=
    (by fun_prop : Continuous (fun t => ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2))).integrableOn_Ioc
  rw [← Ioc_union_Ioc_eq_Ioc hr0 hK, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (i1.congr_fun e1 measurableSet_Ioc) (i2.congr_fun e2 measurableSet_Ioc),
    ← setIntegral_congr_fun measurableSet_Ioc e1, ← setIntegral_congr_fun measurableSet_Ioc e2,
    intervalIntegral.integral_of_le hr0, intervalIntegral.integral_of_le hK]


lemma layer_min (r m : ℝ) (hr0 : 0 ≤ r) (hm : 0 ≤ m) (ψ : ℝ → ℝ) :
    ∫ t in Ioc 0 r, ψ t * (if t < m then (1:ℝ) else 0) = ∫ t in (0:ℝ)..min m r, ψ t := by
  rcases le_or_gt m r with h | h
  · rw [layer 0 r m h, min_eq_left h]
    split_ifs with h0
    · have : m = 0 := le_antisymm h0 hm
      subst this; simp
    · rfl
  · rw [min_eq_right h.le]
    have h1 : (fun t => ψ t * (if t < m then (1:ℝ) else 0)) = (Iio m).indicator ψ := by
      ext t; by_cases ht : t < m
      · simp [ht]
      · simp [ht]
    have h2 : Ioc 0 r ∩ Iio m = Ioc 0 r :=
      inter_eq_left.2 (fun t (ht : t ∈ Ioc 0 r) => (lt_of_le_of_lt ht.2 h : t ∈ Iio m))
    rw [h1, setIntegral_indicator measurableSet_Iio, h2, intervalIntegral.integral_of_le hr0]

lemma E_add (R r : ℝ) (F G : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hF : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => F (shrink R r • w.1) w.2)
      ((volume.restrict (zone R)).prod (volume.restrict (zone R))))
    (hG : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => G (shrink R r • w.1) w.2)
      ((volume.restrict (zone R)).prod (volume.restrict (zone R)))) :
    E R r (fun a b => F a b + G a b) = E R r F + E R r G := by
  unfold E
  rw [← mul_add]
  congr 1
  rw [← integral_prod _ hF, ← integral_prod _ hG, ← integral_add hF hG]
  exact (integral_prod _ (hF.add hG)).symm

lemma E_const (R r κ : ℝ) (hR : 0 < R) : E R r (fun _ _ => κ) = κ := by
  unfold E
  simp only [integral_const, smul_eq_mul]
  rw [vol_zone R hR]
  field_simp

lemma E_mul (R r κ : ℝ) (F : ℝ × ℝ → ℝ × ℝ → ℝ) : E R r (fun a b => κ * F a b) = κ * E R r F := by
  unfold E
  simp only [integral_const_mul]
  ring

lemma integrable_bdd (R : ℝ) (H : (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hH : Measurable H) (C : ℝ)
    (hC : ∀ w, |H w| ≤ C) :
    Integrable H ((volume.restrict (zone R)).prod (volume.restrict (zone R))) := by
  haveI := finite_zone R
  exact (integrable_const C).mono' hH.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w => by simpa [Real.norm_eq_abs] using hC w))

lemma E_min (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (F : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hF : ∀ u ∈ zone R, ∀ b ∈ zone R, F (shrink R r • u) b
      = ∫ t in (0:ℝ)..min (l1 (shrink R r • u) b) r, ψ t) :
    E R r F = (1 / R ^ 4) * ∫ t in (0:ℝ)..r, ψ t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * (R / Real.sqrt 2) * t) ^ 2) := by
  have hF' : ∀ u ∈ zone R, ∀ b ∈ zone R, F (shrink R r • u) b
      = ∫ t in Ioc 0 r, ψ t * (if t < l1 (shrink R r • u) b then (1:ℝ) else 0) := by
    intro u hu b hb
    rw [hF u hu b hb, layer_min r _ hr0 (l1_le_K R r hR hr0 hr u b hu hb).1]
  rw [E_layer R r 0 r hR ψ hψ F hF', intervalIntegral.integral_of_le hr0]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  rw [Aint_low R r t hR hr0 hr ht.1.le ht.2]

lemma l1_nonneg (a b : ℝ × ℝ) : 0 ≤ l1 a b := by unfold l1; positivity

lemma expected_l1_c (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r l1 = (4 * (R / Real.sqrt 2) ^ 4 * r - 4 / 3 * (R / Real.sqrt 2) ^ 2 * r ^ 3)
        / (4 * (R / Real.sqrt 2) ^ 4)
      + 2 * (R / Real.sqrt 2 - r) ^ 2 * (7 * (R / Real.sqrt 2) + 3 * r) / (15 * (R / Real.sqrt 2) ^ 2) := by
  obtain ⟨hc, hR2, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr
  have hF : ∀ u ∈ zone R, ∀ b ∈ zone R, l1 (shrink R r • u) b
      = ∫ t in Ioc 0 (2 * (R / Real.sqrt 2) - r), (fun _ => (1:ℝ)) t *
          (if t < l1 (shrink R r • u) b then (1:ℝ) else 0) := by
    intro u hu b hb
    obtain ⟨h0, hK⟩ := l1_le_K R r hR hr0 hr u b hu hb
    rw [layer 0 _ _ hK]
    split_ifs with h
    · linarith
    · simp
  rw [E_split R r hR hr0 hr (fun _ => 1) continuous_const l1 hF]
  simp only [one_mul]
  rw [Jm R r hR hr0 hr]
  set c := R / Real.sqrt 2 with hcdef
  clear_value c
  have h1 : ∫ t in (0:ℝ)..r, (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t) ^ 2)
      = ∫ t in (0:ℝ)..r, (R ^ 2 * R ^ 2 + 0 * t + (-4 * c ^ 2) * t ^ 2 + 0 * t ^ 3 + 0 * t ^ 4 + 0 * t ^ 5) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    (try simp only); ring
  rw [h1, integral_poly5, show R ^ 4 = (R ^ 2) ^ 2 by ring, hR2]
  field_simp
  ring

lemma expected_l1_sq_c (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => l1 a b ^ 2) = (4 * (R / Real.sqrt 2) ^ 4 * r ^ 2 - 2 * (R / Real.sqrt 2) ^ 2 * r ^ 4)
        / (4 * (R / Real.sqrt 2) ^ 4)
      + 4 * (R / Real.sqrt 2 - r) ^ 3 * (4 * (R / Real.sqrt 2) + r) / (15 * (R / Real.sqrt 2) ^ 2)
      + 2 * r * (2 * (R / Real.sqrt 2 - r) ^ 2 * (7 * (R / Real.sqrt 2) + 3 * r) / (15 * (R / Real.sqrt 2) ^ 2)) := by
  obtain ⟨hc, hR2, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr
  have hF : ∀ u ∈ zone R, ∀ b ∈ zone R, (fun a b => l1 a b ^ 2) (shrink R r • u) b
      = ∫ t in Ioc 0 (2 * (R / Real.sqrt 2) - r), (fun t => 2 * t) t *
          (if t < l1 (shrink R r • u) b then (1:ℝ) else 0) := by
    intro u hu b hb
    obtain ⟨h0, hK⟩ := l1_le_K R r hR hr0 hr u b hu hb
    rw [layer 0 _ _ hK]
    beta_reduce
    split_ifs with h
    · have : l1 (shrink R r • u) b = 0 := le_antisymm h h0
      rw [this]; ring
    · rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [E_split R r hR hr0 hr (fun t => 2 * t) (by fun_prop) _ hF]
  have hJs := Js R r hR hr0 hr
  have hJm := Jm R r hR hr0 hr
  set c := R / Real.sqrt 2 with hcdef
  set s := shrink R r with hsdef
  clear_value c s
  have h2 : ∫ t in r..(2 * c - r), (fun t => 2 * t) t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2)
      = (∫ t in r..(2 * c - r), 2 * (t - r) * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2))
        + 2 * r * ∫ t in r..(2 * c - r), (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t - (t - r) ^ 2 / s) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr (fun t _ => ?_)
      (try simp only); ring
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
  rw [h2, hJs, hJm]
  have h1 : ∫ t in (0:ℝ)..r, (fun t => 2 * t) t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t) ^ 2)
      = ∫ t in (0:ℝ)..r, (0 + (2 * R ^ 2 * R ^ 2) * t + 0 * t ^ 2 + (-8 * c ^ 2) * t ^ 3 + 0 * t ^ 4 + 0 * t ^ 5) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    (try simp only); ring
  rw [h1, integral_poly5, show R ^ 4 = (R ^ 2) ^ 2 by ring, hR2]
  field_simp
  ring

lemma wr_prob_c (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => if l1 a b ≤ r then 1 else 0) = 2 * r ^ 2 / R ^ 2 := by
  obtain ⟨hc, hR2, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr
  unfold E
  rw [Q_eq]
  have := Aint_low R r r hR hr0 hr hr0 le_rfl
  unfold Aint at this
  rw [this, show R ^ 4 = (R ^ 2) ^ 2 by ring, hR2]
  field_simp
  ring

lemma E_minl1 (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => min (l1 a b) r) = r - r ^ 3 / (3 * (R / Real.sqrt 2) ^ 2) := by
  obtain ⟨hc, hR2, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr
  rw [E_min R r hR hr0 hr (fun _ => 1) continuous_const _ (fun u hu b hb => by simp)]
  simp only [one_mul]
  set c := R / Real.sqrt 2 with hcdef
  clear_value c
  have h1 : ∫ t in (0:ℝ)..r, (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t) ^ 2)
      = ∫ t in (0:ℝ)..r, (R ^ 2 * R ^ 2 + 0 * t + (-4 * c ^ 2) * t ^ 2 + 0 * t ^ 3 + 0 * t ^ 4 + 0 * t ^ 5) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    (try simp only); ring
  rw [h1, integral_poly5, show R ^ 4 = (R ^ 2) ^ 2 by ring, hR2]
  field_simp
  ring

lemma E_minl1_sq (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => min (l1 a b) r ^ 2) = r ^ 2 - r ^ 4 / (2 * (R / Real.sqrt 2) ^ 2) := by
  obtain ⟨hc, hR2, hsc, hs0, hs1⟩ := shrink_facts R r hR hr0 hr
  rw [E_min R r hR hr0 hr (fun t => 2 * t) (by fun_prop) _ (fun u hu b hb => by
    beta_reduce
    rw [intervalIntegral.integral_const_mul, integral_id]; ring)]
  set c := R / Real.sqrt 2 with hcdef
  clear_value c
  have h1 : ∫ t in (0:ℝ)..r, 2 * t * (R ^ 2 * R ^ 2 - 1 / 4 * (4 * c * t) ^ 2)
      = ∫ t in (0:ℝ)..r, (0 + (2 * R ^ 2 * R ^ 2) * t + 0 * t ^ 2 + (-8 * c ^ 2) * t ^ 3 + 0 * t ^ 4 + 0 * t ^ 5) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    (try simp only); ring
  rw [h1, integral_poly5, show R ^ 4 = (R ^ 2) ^ 2 by ring, hR2]
  field_simp
  ring

lemma meas_ind (R r : ℝ) : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
    if l1 (shrink R r • w.1) w.2 ≤ r then (1:ℝ) else 0) :=
  Measurable.ite (measurableSet_le (measurable_l1s _) measurable_const) measurable_const measurable_const

lemma wr_mean_c (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => if l1 a b ≤ r then l1 a b else 0)
      = r - r ^ 3 / (3 * (R / Real.sqrt 2) ^ 2) + r * (2 * r ^ 2 / R ^ 2) - r := by
  have e : (fun a b => if l1 a b ≤ r then l1 a b else 0)
      = fun a b => (min (l1 a b) r + r * (if l1 a b ≤ r then 1 else 0)) + (fun _ _ => -r) a b := by
    ext a b
    split_ifs with h
    · rw [min_eq_left h]; ring
    · rw [min_eq_right (le_of_not_ge h)]; ring
  have imin : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => min (l1 (shrink R r • w.1) w.2) r)
      ((volume.restrict (zone R)).prod (volume.restrict (zone R))) := by
    refine integrable_bdd R _ ((measurable_l1s _).min measurable_const) r (fun w => ?_)
    rw [abs_le]; constructor
    · have := l1_nonneg (shrink R r • w.1) w.2
      exact le_min (by linarith) (by linarith)
    · exact min_le_right _ _
  have iind : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => r * (if l1 (shrink R r • w.1) w.2 ≤ r then (1:ℝ) else 0))
      ((volume.restrict (zone R)).prod (volume.restrict (zone R))) :=
    (integrable_bdd R _ (meas_ind R r) 1 (fun w => by split_ifs <;> simp)).const_mul r
  have iconst : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => (fun _ _ => -r) (shrink R r • w.1) w.2)
      ((volume.restrict (zone R)).prod (volume.restrict (zone R))) := by
    haveI := finite_zone R
    exact integrable_const _
  rw [e, E_add R r _ _ (imin.add iind) iconst, E_add R r _ _ imin iind,
    E_mul R r r (fun a b => if l1 a b ≤ r then 1 else 0), E_minl1 R r hR hr0 hr,
    wr_prob_c R r hR hr0 hr, E_const R r _ hR]
  ring

lemma wr_second_c (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => if l1 a b ≤ r then l1 a b ^ 2 else 0)
      = r ^ 2 - r ^ 4 / (2 * (R / Real.sqrt 2) ^ 2) + r ^ 2 * (2 * r ^ 2 / R ^ 2) - r ^ 2 := by
  have e : (fun a b => if l1 a b ≤ r then l1 a b ^ 2 else 0)
      = fun a b => (min (l1 a b) r ^ 2 + r ^ 2 * (if l1 a b ≤ r then 1 else 0)) + (fun _ _ => -r ^ 2) a b := by
    ext a b
    split_ifs with h
    · rw [min_eq_left h]; ring
    · rw [min_eq_right (le_of_not_ge h)]; ring
  have imin : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => min (l1 (shrink R r • w.1) w.2) r ^ 2)
      ((volume.restrict (zone R)).prod (volume.restrict (zone R))) := by
    refine integrable_bdd R _ (((measurable_l1s _).min measurable_const).pow_const 2) (r ^ 2) (fun w => ?_)
    have h0 := l1_nonneg (shrink R r • w.1) w.2
    have h1 : 0 ≤ min (l1 (shrink R r • w.1) w.2) r := le_min h0 hr0
    have h2 : min (l1 (shrink R r • w.1) w.2) r ≤ r := min_le_right _ _
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ h1 h2 2
  have iind : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => r ^ 2 * (if l1 (shrink R r • w.1) w.2 ≤ r then (1:ℝ) else 0))
      ((volume.restrict (zone R)).prod (volume.restrict (zone R))) :=
    (integrable_bdd R _ (meas_ind R r) 1 (fun w => by split_ifs <;> simp)).const_mul (r ^ 2)
  have iconst : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => (fun _ _ => -r ^ 2) (shrink R r • w.1) w.2)
      ((volume.restrict (zone R)).prod (volume.restrict (zone R))) := by
    haveI := finite_zone R
    exact integrable_const _
  rw [e, E_add R r _ _ (imin.add iind) iconst, E_add R r _ _ imin iind,
    E_mul R r (r ^ 2) (fun a b => if l1 a b ≤ r then 1 else 0), E_minl1_sq R r hR hr0 hr,
    wr_prob_c R r hR hr0 hr, E_const R r _ hR]
  ring


lemma q_pows (q : ℝ) (hq : q ^ 2 = 2) : q ^ 3 = 2 * q ∧ q ^ 4 = 4 ∧ q ^ 5 = 4 * q ∧ q ^ 6 = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_succ, hq]
  · rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq]; norm_num
  · rw [show q ^ 5 = (q ^ 2) ^ 2 * q by ring, hq]; ring
  · rw [show q ^ 6 = (q ^ 2) ^ 3 by ring, hq]; norm_num

lemma alg_l1 (q c r : ℝ) (hq : q ^ 2 = 2) (hc : 0 < c) (hq0 : 0 < q) :
    (4 * c ^ 4 * r - 4 / 3 * c ^ 2 * r ^ 3) / (4 * c ^ 4)
      + 2 * (c - r) ^ 2 * (7 * c + 3 * r) / (15 * c ^ 2)
      = 7 * q * (q * c) / 15 - 7 * r / 15 + 2 * q * r ^ 2 / (15 * (q * c)) + 2 * r ^ 3 / (15 * (q * c) ^ 2) := by
  obtain ⟨h3, h4, h5, h6⟩ := q_pows q hq
  field_simp
  ring_nf
  simp only [hq, h3, h4, h5, h6]
  ring_nf

lemma alg_l1sq (q c r : ℝ) (hq : q ^ 2 = 2) (hc : 0 < c) (hq0 : 0 < q) :
    (4 * c ^ 4 * r ^ 2 - 2 * c ^ 2 * r ^ 4) / (4 * c ^ 4)
      + 4 * (c - r) ^ 3 * (4 * c + r) / (15 * c ^ 2)
      + 2 * r * (2 * (c - r) ^ 2 * (7 * c + 3 * r) / (15 * c ^ 2))
      = (8 * (q * c) ^ 4 - 8 * q * (q * c) ^ 3 * r + 7 * (q * c) ^ 2 * r ^ 2 + r ^ 4) / (15 * (q * c) ^ 2) := by
  obtain ⟨h3, h4, h5, h6⟩ := q_pows q hq
  field_simp
  ring_nf
  simp only [hq, h3, h4, h5, h6]
  ring_nf


lemma expected_l1_R (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r l1 = 7 * Real.sqrt 2 * R / 15 - 7 * r / 15 + 2 * Real.sqrt 2 * r ^ 2 / (15 * R)
      + 2 * r ^ 3 / (15 * R ^ 2) := by
  have hq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq0 : 0 < Real.sqrt 2 := by positivity
  have hRc : Real.sqrt 2 * (R / Real.sqrt 2) = R := by field_simp
  rw [expected_l1_c R r hR hr0 hr, alg_l1 (Real.sqrt 2) (R / Real.sqrt 2) r hq (by positivity) hq0, hRc]

lemma expected_l1_sq_R (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => l1 a b ^ 2)
      = (8 * R ^ 4 - 8 * Real.sqrt 2 * R ^ 3 * r + 7 * R ^ 2 * r ^ 2 + r ^ 4) / (15 * R ^ 2) := by
  have hq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq0 : 0 < Real.sqrt 2 := by positivity
  have hRc : Real.sqrt 2 * (R / Real.sqrt 2) = R := by field_simp
  rw [expected_l1_sq_c R r hR hr0 hr, alg_l1sq (Real.sqrt 2) (R / Real.sqrt 2) r hq (by positivity) hq0, hRc]

lemma csq (R : ℝ) : (R / Real.sqrt 2) ^ 2 = R ^ 2 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]

end TripRotTest

open StallEconomy.TripLength TripRotTest in
theorem solution (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => if l1 a b ≤ r then 1 else 0) = 2 * r ^ 2 / R ^ 2 ∧
      E R r (fun a b => if l1 a b ≤ r then l1 a b else 0) = (2 / 3) * r * (2 * r ^ 2 / R ^ 2) := by
  refine ⟨wr_prob_c R r hR hr0 hr, ?_⟩
  rw [wr_mean_c R r hR hr0 hr, csq]
  field_simp
  ring
