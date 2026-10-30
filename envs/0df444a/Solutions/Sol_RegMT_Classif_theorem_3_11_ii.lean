-- Prove2me | solution 1 for RegMT.Classif.theorem_3_11_ii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T13:20:34.402328+00:00
-- url     : https://prove2.me/submissions/88a9b56a-160c-44e8-ba68-a46d271f2aea

import Mathlib
import Definitions.Def_RegMT_Classif_Model

set_option autoImplicit false

open DRLogReg.Reformulation in
theorem rc11_sgn_sq (y : Bool) : sgn y * sgn y = 1 := by cases y <;> simp [sgn]

open DRLogReg.Reformulation in
theorem rc11_abs_sgn (y : Bool) : |sgn y| = 1 := by cases y <;> simp [sgn]
open DRLogReg.Reformulation in
theorem rc11_dist_same {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (κ : ℝ)
    (x x' : V) (y : Bool) : featureLabelDist κ (x, y) (x', y) = ‖x - x'‖ := by
  simp [featureLabelDist]

open DRLogReg.Reformulation in
theorem rc11_dist_flip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (κ : ℝ)
    (x x' : V) (y : Bool) : featureLabelDist κ (x, !y) (x', y) = ‖x - x'‖ + κ := by
  cases y <;> norm_num [featureLabelDist, sgn]

open DRLogReg.Reformulation in
theorem rc11_dist_nonneg {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : ℝ}
    (hκ : 0 ≤ κ) (ξ ξ' : V × Bool) : 0 ≤ featureLabelDist κ ξ ξ' := by
  unfold featureLabelDist
  positivity

theorem rc11_norming {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →L[ℝ] ℝ) : ∃ u : V, ‖u‖ ≤ 1 ∧ β u = ‖β‖ := by
  have hK : IsCompact (Metric.closedBall (0 : V) 1) := isCompact_closedBall 0 1
  obtain ⟨u, hu, hmax⟩ := hK.exists_isMaxOn (Metric.nonempty_closedBall.mpr zero_le_one)
    β.continuous.continuousOn
  have hu1 : ‖u‖ ≤ 1 := by simpa using hu
  refine ⟨u, hu1, le_antisymm ?_ ?_⟩
  · have := β.le_opNorm u
    rw [Real.norm_eq_abs] at this
    calc β u ≤ |β u| := le_abs_self _
      _ ≤ ‖β‖ * ‖u‖ := this
      _ ≤ ‖β‖ * 1 := mul_le_mul_of_nonneg_left hu1 (norm_nonneg _)
      _ = ‖β‖ := mul_one _
  · have h0 : 0 ≤ β u := by
      have := isMaxOn_iff.mp hmax 0 (Metric.mem_closedBall_self zero_le_one)
      simpa using this
    apply ContinuousLinearMap.opNorm_le_bound _ h0
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hx' : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : V) 1 := by
        simp [norm_smul, hxn.ne']
      have hx'' : -(‖x‖⁻¹ • x) ∈ Metric.closedBall (0 : V) 1 := by
        simp [norm_smul, hxn.ne']
      have h1 : β (‖x‖⁻¹ • x) ≤ β u := isMaxOn_iff.mp hmax _ hx'
      have h2 : β (-(‖x‖⁻¹ • x)) ≤ β u := isMaxOn_iff.mp hmax _ hx''
      rw [map_neg, map_smul, smul_eq_mul] at h2
      rw [map_smul, smul_eq_mul] at h1
      have e1 : β x ≤ ‖x‖ * β u := (inv_mul_le_iff₀ hxn).mp h1
      have e2 : -β x ≤ ‖x‖ * β u := by
        have : ‖x‖⁻¹ * (-β x) ≤ β u := by linarith
        exact (inv_mul_le_iff₀ hxn).mp this
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith

open Finset in
theorem rc11_knap {N : ℕ} (g : Fin N → ℝ) {m : ℝ} (hm : 0 ≤ m) :
    ∃ ν : ℝ, 0 ≤ ν ∧ ∃ p : Fin N → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∑ i, p i ≤ m ∧
      ν * m + ∑ i, max 0 (g i - ν) ≤ ∑ i, p i * g i := by
  classical
  by_cases hA : (∑ i, if 0 < g i then (1:ℝ) else 0) ≤ m
  · refine ⟨0, le_rfl, fun i => if 0 < g i then 1 else 0, fun i => ?_, hA, ?_⟩
    · dsimp only
      split_ifs <;> norm_num
    · simp only [zero_mul, zero_add, sub_zero]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h
      · rw [max_eq_right h.le, one_mul]
      · rw [max_eq_left (not_lt.mp h), zero_mul]
  push Not at hA
  set cnt : Fin N → ℝ := fun j => ∑ i, if g j ≤ g i then (1:ℝ) else 0 with hcnt
  set S := univ.filter (fun j => 0 < g j ∧ m < cnt j) with hS
  have hpos_ne : (univ.filter (fun i => 0 < g i)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
    have : (∑ i, if 0 < g i then (1:ℝ) else 0) = 0 :=
      sum_eq_zero fun i _ => if_neg (h (mem_univ i))
    linarith
  obtain ⟨j1, hj1, hj1min⟩ := exists_min_image _ g hpos_ne
  have hSne : S.Nonempty := by
    refine ⟨j1, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj1).2, ?_⟩⟩
    refine lt_of_lt_of_le hA (sum_le_sum fun i _ => ?_)
    by_cases h1 : 0 < g i
    · rw [if_pos h1, if_pos (hj1min i (mem_filter.mpr ⟨mem_univ _, h1⟩))]
    · rw [if_neg h1]
      split_ifs <;> norm_num
  obtain ⟨j0, hj0S, hj0max⟩ := exists_max_image S g hSne
  have hj0 := (mem_filter.mp hj0S).2
  set τ := g j0 with hτ
  have hτpos : 0 < τ := hj0.1
  have hgt : (∑ i, if τ < g i then (1:ℝ) else 0) ≤ m := by
    by_contra hc
    push Not at hc
    have hne : (univ.filter (fun i => τ < g i)).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
      have : (∑ i, if τ < g i then (1:ℝ) else 0) = 0 :=
        sum_eq_zero fun i _ => if_neg (h (mem_univ i))
      linarith
    obtain ⟨k, hk, hkmin⟩ := exists_min_image _ g hne
    have hkτ : τ < g k := (mem_filter.mp hk).2
    have hck : cnt k = ∑ i, if τ < g i then (1:ℝ) else 0 := by
      simp only [hcnt]
      apply sum_congr rfl
      intro i _
      by_cases hi : τ < g i
      · rw [if_pos hi, if_pos (hkmin i (mem_filter.mpr ⟨mem_univ _, hi⟩))]
      · rw [if_neg hi, if_neg]
        intro h
        exact hi (lt_of_lt_of_le hkτ h)
    have hkS : k ∈ S := mem_filter.mpr ⟨mem_univ _, by linarith, by rw [hck]; exact hc⟩
    have := hj0max k hkS
    linarith
  set ngt : ℝ := ∑ i, if τ < g i then (1:ℝ) else 0 with hngt
  set neq : ℝ := ∑ i, if g i = τ then (1:ℝ) else 0 with hneq
  have hsplit : cnt j0 = ngt + neq := by
    simp only [hcnt, hngt, hneq]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rcases lt_trichotomy (g i) τ with h | h | h
    · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le), if_neg h.ne]
      norm_num
    · rw [if_pos h.ge, if_neg (not_lt.mpr h.le), if_pos h]
      norm_num
    · rw [if_pos h.le, if_pos h, if_neg h.ne']
      norm_num
  have hm_lt : m < ngt + neq := by rw [← hsplit]; exact hj0.2
  have hneq_pos : 0 < neq := by linarith
  set θ := (m - ngt) / neq with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hneq_pos.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hneq_pos]; linarith
  have hθn : θ * neq = m - ngt := by rw [hθ]; field_simp
  set p : Fin N → ℝ := fun i => if τ < g i then 1 else if g i = τ then θ else 0 with hp
  have hpsum : ∑ i, p i = m := by
    have e : ∀ i, p i = (if τ < g i then (1:ℝ) else 0) + θ * (if g i = τ then (1:ℝ) else 0) := by
      intro i
      simp only [hp]
      rcases lt_trichotomy (g i) τ with h | h | h
      · rw [if_neg (not_lt.mpr h.le), if_neg h.ne, if_neg (not_lt.mpr h.le), if_neg h.ne]
        ring
      · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg (not_lt.mpr h.le), if_pos h]
        ring
      · rw [if_pos h, if_pos h, if_neg h.ne']
        ring
    rw [sum_congr rfl (fun i _ => e i), sum_add_distrib, ← mul_sum]
    linarith
  refine ⟨τ, hτpos.le, p, ?_, hpsum.le, ?_⟩
  · intro i
    simp only [hp]
    split_ifs <;> constructor <;> linarith
  · have hterm : ∀ i, p i * g i - max 0 (g i - τ) = τ * p i := by
      intro i
      simp only [hp]
      rcases lt_trichotomy (g i) τ with h | h | h
      · rw [if_neg (not_lt.mpr h.le), if_neg h.ne, max_eq_left (by linarith)]
        ring
      · rw [if_neg (not_lt.mpr h.le), if_pos h, h, sub_self, max_self]
        ring
      · rw [if_pos h, max_eq_right (by linarith)]
        ring
    have e2 : ∑ i, p i * g i - ∑ i, max 0 (g i - τ) = τ * m := by
      rw [← sum_sub_distrib, sum_congr rfl (fun i _ => hterm i), ← mul_sum, hpsum]
    linarith

open MeasureTheory DRLogReg.Reformulation in
theorem rc11_couple {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] {K : Type*} [Fintype K] {κ ε : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (w : Fin N → K → ℝ) (hw0 : ∀ i k, 0 ≤ w i k)
    (hw1 : ∀ i, ∑ k, w i k = 1) (ζ : Fin N → K → V × Bool)
    (hcost : ∑ i, ∑ k, w i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i) ≤ ε)
    (f : V × Bool → ℝ) (hf : Measurable f) (hf0 : ∀ ξ, 0 ≤ f ξ) :
    ∃ Q ∈ wassersteinBall κ ε (empirical xhat yhat),
      ENNReal.ofReal (∑ i, ∑ k, w i k / N * f (ζ i k)) ≤ ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂Q := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hwN : ∀ i k, 0 ≤ w i k / N := fun i k => div_nonneg (hw0 i k) hNpos.le
  set π : Measure ((V × Bool) × (V × Bool)) := ∑ i, ∑ k,
    ENNReal.ofReal (w i k / N) • Measure.dirac (ζ i k, (xhat i, yhat i)) with hπ
  have hcoef : ∀ i, ∑ k, ENNReal.ofReal (w i k / N) = (N : ENNReal)⁻¹ := by
    intro i
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hwN i k), ← Finset.sum_div, hw1 i,
      one_div, ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  have hπapp : ∀ S, π S = ∑ i, ∑ k, ENNReal.ofReal (w i k / N) *
      S.indicator 1 (ζ i k, (xhat i, yhat i)) := by
    intro S
    simp only [hπ, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  have hsnd : π.map Prod.snd = empirical xhat yhat := by
    ext S hS
    rw [Measure.map_apply measurable_snd hS, hπapp]
    simp only [empirical, Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply,
      smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have e : ∀ k, (Prod.snd ⁻¹' S).indicator (1 : (V × Bool) × (V × Bool) → ENNReal)
        (ζ i k, (xhat i, yhat i)) = S.indicator 1 (xhat i, yhat i) := fun k => rfl
    simp only [e]
    rw [← Finset.sum_mul, hcoef]
  have hprob : IsProbabilityMeasure π := by
    constructor
    rw [hπapp]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one, hcoef]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)
  refine ⟨π.map Prod.fst, ⟨Measure.isProbabilityMeasure_map measurable_fst.aemeasurable, ?_⟩, ?_⟩
  · calc wasserstein κ (π.map Prod.fst) (empirical xhat yhat)
        ≤ ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π :=
          iInf_le_of_le π (iInf_le_of_le hprob (iInf_le_of_le rfl (iInf_le_of_le hsnd le_rfl)))
      _ = ∑ i, ∑ k, ENNReal.ofReal (w i k / N) *
            ENNReal.ofReal (featureLabelDist κ (ζ i k) (xhat i, yhat i)) := by
          simp only [hπ, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
            smul_eq_mul]
      _ = ENNReal.ofReal (∑ i, ∑ k, w i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun k _ =>
            mul_nonneg (hwN i k) (rc11_dist_nonneg hκ _ _))]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ =>
            mul_nonneg (hwN i k) (rc11_dist_nonneg hκ _ _))]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_mul (hwN i k)]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hcost
  · rw [lintegral_map hf.ennreal_ofReal measurable_fst]
    apply le_of_eq
    simp only [hπ, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (hwN i k) (hf0 _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hwN i k) (hf0 _))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_mul (hwN i k)]

open DRLogReg.Reformulation in
theorem rc11_sgn_not (y : Bool) : sgn (!y) = -sgn y := by cases y <;> simp [sgn]

theorem rc11_lip_bound (L : ℝ → ℝ) (hLip : ∃ K : NNReal, LipschitzWith K L) (x y : ℝ) :
    |L x - L y| ≤ (WassersteinDRO.Duality.lipschitzModulus L).toReal * |x - y| := by
  obtain ⟨K, hK⟩ := hLip
  have hfin : WassersteinDRO.Duality.lipschitzModulus L ≤ (K : ENNReal) := by
    unfold WassersteinDRO.Duality.lipschitzModulus
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    have hpos : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
    have h := hK.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at h
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hpos, Real.norm_eq_abs]
    exact h
  have hne : WassersteinDRO.Duality.lipschitzModulus L ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hfin
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have h1 : ENNReal.ofReal (|L x - L y| / ‖x - y‖) ≤ WassersteinDRO.Duality.lipschitzModulus L := by
    unfold WassersteinDRO.Duality.lipschitzModulus
    exact le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hxy le_rfl))
  rw [ENNReal.ofReal_le_iff_le_toReal hne, Real.norm_eq_abs, div_le_iff₀ hpos] at h1
  exact h1

theorem rc11_lip_ne_top (L : ℝ → ℝ) (hLip : ∃ K : NNReal, LipschitzWith K L) :
    WassersteinDRO.Duality.lipschitzModulus L ≠ ⊤ := by
  obtain ⟨K, hK⟩ := hLip
  have hfin : WassersteinDRO.Duality.lipschitzModulus L ≤ (K : ENNReal) := by
    unfold WassersteinDRO.Duality.lipschitzModulus
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    have hpos : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
    have h := hK.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at h
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hpos, Real.norm_eq_abs]
    exact h
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top hfin

/-- A convex Lipschitz function lies above an affine function whose slope is the chord slope
of any pair `x < y`. -/
theorem rc11_chord_affine (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L) {x y : ℝ} (hxy : x < y) :
    ∃ K : ℝ, ∀ z, (L y - L x) / (y - x) * z + K ≤ L z := by
  set ℓ := (WassersteinDRO.Duality.lipschitzModulus L).toReal with hℓ
  have hℓ0 : 0 ≤ ℓ := ENNReal.toReal_nonneg
  set c := (L y - L x) / (y - x) with hc
  have hyx : 0 < y - x := by linarith
  have hcy : L y = L x + c * (y - x) := by
    rw [hc]
    field_simp
    ring
  refine ⟨L x - c * x - (ℓ + |c|) * (y - x), fun z => ?_⟩
  have hM : 0 ≤ (ℓ + |c|) * (y - x) := mul_nonneg (by positivity) hyx.le
  rcases lt_or_ge z x with hzx | hxz
  · have h := hconv.slope_mono_adjacent (Set.mem_univ z) (Set.mem_univ y) hzx hxy
    rw [← hc, div_le_iff₀ (by linarith : (0 : ℝ) < x - z)] at h
    nlinarith
  rcases le_or_gt z y with hzy | hyz
  · have hl := rc11_lip_bound L hLip z x
    have h1 : L x - L z ≤ ℓ * (y - x) := by
      have e : |z - x| = z - x := abs_of_nonneg (by linarith)
      rw [e] at hl
      have h2 : ℓ * (z - x) ≤ ℓ * (y - x) := mul_le_mul_of_nonneg_left (by linarith) hℓ0
      linarith [neg_abs_le (L z - L x)]
    have h3 : c * (z - x) ≤ |c| * (y - x) := by
      calc c * (z - x) ≤ |c| * (z - x) :=
            mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
        _ ≤ |c| * (y - x) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
    nlinarith
  · have h := hconv.slope_mono_adjacent (Set.mem_univ x) (Set.mem_univ z) hxy hyz
    rw [← hc, le_div_iff₀ (by linarith : (0 : ℝ) < z - y)] at h
    nlinarith

/-- Asymptotic slope: for every `η > 0` there is an affine minorant of `L` whose slope has
absolute value at least `lip(L) - η`. -/
theorem rc11_chord (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L) (hL0 : ∀ z, 0 ≤ L z) {η : ℝ} (hη : 0 < η) :
    ∃ g K : ℝ, (WassersteinDRO.Duality.lipschitzModulus L).toReal - η ≤ |g| ∧
      ∀ z, g * z + K ≤ L z := by
  set ℓ := (WassersteinDRO.Duality.lipschitzModulus L).toReal with hℓ
  by_cases hsmall : ℓ - η ≤ 0
  · exact ⟨0, 0, by simpa using hsmall, fun z => by simpa using hL0 z⟩
  push Not at hsmall
  have hne := rc11_lip_ne_top L hLip
  have hlt : ENNReal.ofReal (ℓ - η) < WassersteinDRO.Duality.lipschitzModulus L := by
    rw [← ENNReal.ofReal_toReal hne, ← hℓ]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  simp only [WassersteinDRO.Duality.lipschitzModulus, lt_iSup_iff] at hlt
  obtain ⟨x, y, hxy, hlt⟩ := hlt
  have hlt' : ℓ - η < |L x - L y| / ‖x - y‖ :=
    (ENNReal.ofReal_lt_ofReal_iff'.mp hlt).1
  rw [Real.norm_eq_abs] at hlt'
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨K, hK⟩ := rc11_chord_affine L hconv hLip h
    refine ⟨(L y - L x) / (y - x), K, ?_, hK⟩
    rw [abs_div, abs_sub_comm (L y), abs_sub_comm y]
    exact hlt'.le
  · obtain ⟨K, hK⟩ := rc11_chord_affine L hconv hLip h
    refine ⟨(L x - L y) / (x - y), K, ?_, hK⟩
    rw [abs_div]
    exact hlt'.le

open DRLogReg.Reformulation in
theorem rc11_lipw {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : ℝ → ℝ) (hLip : ∃ K : NNReal, LipschitzWith K L) (w : V →L[ℝ] ℝ)
    {σ : ℝ} (hσ : |σ| = 1) (x x' : V) :
    L (σ * w x) ≤ L (σ * w x') +
      (WassersteinDRO.Duality.lipschitzModulus L).toReal * ‖w‖ * ‖x - x'‖ := by
  have hl := rc11_lip_bound L hLip (σ * w x) (σ * w x')
  have hℓ0 : 0 ≤ (WassersteinDRO.Duality.lipschitzModulus L).toReal := ENNReal.toReal_nonneg
  have h1 : |σ * w x - σ * w x'| ≤ ‖w‖ * ‖x - x'‖ := by
    have h := w.le_opNorm (x - x')
    rw [Real.norm_eq_abs, map_sub] at h
    rw [← mul_sub, abs_mul, hσ, one_mul]
    exact h
  have h2 := mul_le_mul_of_nonneg_left h1 hℓ0
  have h3 := le_abs_self (L (σ * w x) - L (σ * w x'))
  nlinarith

open DRLogReg.Reformulation RegMT.Classif in
theorem rc11_pt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : ℝ} {N : ℕ}
    {xhat : Fin N → V} {yhat : Fin N → Bool} (L : ℝ → ℝ)
    (hLip : ∃ K : NNReal, LipschitzWith K L) (w : V →L[ℝ] ℝ)
    {q : ℝ × (Fin N → ℝ)} (hq : q ∈ feasible18 κ xhat yhat L w)
    (i : Fin N) (ξ : V × Bool) :
    L (sgn ξ.2 * w ξ.1) ≤ q.2 i + q.1 * featureLabelDist κ ξ (xhat i, yhat i) := by
  obtain ⟨h1, h2, h3⟩ := hq
  obtain ⟨x, y⟩ := ξ
  dsimp only
  have hn : 0 ≤ ‖x - xhat i‖ := norm_nonneg _
  have hk := mul_le_mul_of_nonneg_right h3 hn
  by_cases hy : y = yhat i
  · subst hy
    rw [rc11_dist_same]
    have e1 := rc11_lipw L hLip w (rc11_abs_sgn (yhat i)) x (xhat i)
    have e2 := h1 i
    linarith
  · have hy' : y = !yhat i := by
      cases y <;> cases h : yhat i <;> simp_all
    subst hy'
    rw [rc11_dist_flip]
    have e1 := rc11_lipw L hLip w (rc11_abs_sgn (!yhat i)) x (xhat i)
    have e2 := h2 i
    simp only [rc11_sgn_not, neg_mul] at e1 ⊢
    linarith

open DRLogReg.Reformulation in
theorem rc11_meas {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (L : ℝ → ℝ) (hLip : ∃ K : NNReal, LipschitzWith K L) (w : V →L[ℝ] ℝ) :
    Measurable (fun ξ : V × Bool => L (sgn ξ.2 * w ξ.1)) := by
  obtain ⟨K, hK⟩ := hLip
  have h1 : Measurable fun ξ : V × Bool => sgn ξ.2 :=
    (measurable_of_countable sgn).comp measurable_snd
  have h2 : Measurable fun ξ : V × Bool => w ξ.1 := w.continuous.measurable.comp measurable_fst
  exact hK.continuous.measurable.comp (h1.mul h2)

open MeasureTheory DRLogReg.Reformulation RegMT.Classif in
theorem rc11_weak {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] {κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ) {N : ℕ} (hN : 0 < N) {xhat : Fin N → V}
    {yhat : Fin N → Bool} (L : ℝ → ℝ) (hLip : ∃ K : NNReal, LipschitzWith K L)
    (hL0 : ∀ z, 0 ≤ L z) (w : V →L[ℝ] ℝ) {p : ℝ × (Fin N → ℝ)}
    (hp : p ∈ feasible18 κ xhat yhat L w)
    {Q : Measure (V × Bool)} (hQ : Q ∈ wassersteinBall κ ρ (empirical xhat yhat)) :
    ∫⁻ ξ, ENNReal.ofReal (L (sgn ξ.2 * w ξ.1)) ∂Q ≤
      ENNReal.ofReal (p.1 * ρ + (N : ℝ)⁻¹ * ∑ i, p.2 i) := by
  classical
  have hs : ∀ i, 0 ≤ p.2 i := fun i => (hL0 _).trans (hp.1 i)
  have hlam : 0 ≤ p.1 :=
    (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg w)).trans hp.2.2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := (N : ℝ)⁻¹ * ∑ i, p.2 i with hCdef
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr hNpos.le) (Finset.sum_nonneg fun i _ => hs i)
  have hfm : Measurable (fun ξ : V × Bool => ENNReal.ofReal (L (sgn ξ.2 * w ξ.1))) :=
    (rc11_meas L hLip w).ennreal_ofReal
  let g : V × Bool → ENNReal := fun ξ' =>
    ⨅ i, if ξ' = (xhat i, yhat i) then ENNReal.ofReal (p.2 i) else ⊤
  have hg : Measurable g :=
    Measurable.iInf fun i => Measurable.ite measurableSet_eq measurable_const measurable_const
  have hgle : ∀ i, g (xhat i, yhat i) ≤ ENNReal.ofReal (p.2 i) := fun i =>
    (iInf_le _ i).trans (by simp)
  have hpt : ∀ q : (V × Bool) × (V × Bool), ENNReal.ofReal (L (sgn q.1.2 * w q.1.1)) ≤
      g q.2 + ENNReal.ofReal p.1 * ENNReal.ofReal (featureLabelDist κ q.1 q.2) := by
    intro q
    simp only [g]
    rw [ENNReal.iInf_add]
    refine le_iInf fun i => ?_
    split_ifs with h
    · rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add (hs i)
        (mul_nonneg hlam (rc11_dist_nonneg hκ _ _))]
      apply ENNReal.ofReal_le_ofReal
      rw [h]
      exact rc11_pt L hLip w hp i q.1
    · simp
  have hcoup : ∀ π : Measure ((V × Bool) × (V × Bool)), π.map Prod.fst = Q →
      π.map Prod.snd = empirical xhat yhat →
      ∫⁻ ξ, ENNReal.ofReal (L (sgn ξ.2 * w ξ.1)) ∂Q ≤ ENNReal.ofReal C + ENNReal.ofReal p.1 *
        ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
    intro π h1 h2
    calc ∫⁻ ξ, ENNReal.ofReal (L (sgn ξ.2 * w ξ.1)) ∂Q
        = ∫⁻ q, ENNReal.ofReal (L (sgn q.1.2 * w q.1.1)) ∂π := by
          rw [← h1, lintegral_map hfm measurable_fst]
      _ ≤ ∫⁻ q, (g q.2 + ENNReal.ofReal p.1 *
            ENNReal.ofReal (featureLabelDist κ q.1 q.2)) ∂π :=
          lintegral_mono hpt
      _ = ∫⁻ q, g q.2 ∂π + ENNReal.ofReal p.1 *
            ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
          rw [lintegral_add_left (f := fun q : (V × Bool) × (V × Bool) => g q.2)
            (hg.comp measurable_snd), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal p.1 *
            ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
          gcongr
          rw [← lintegral_map hg measurable_snd, h2]
          simp only [empirical, lintegral_smul_measure, lintegral_finsetSum_measure,
            lintegral_dirac, smul_eq_mul]
          calc (N : ENNReal)⁻¹ * ∑ i, g (xhat i, yhat i)
              ≤ (N : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (p.2 i) := by
                gcongr with i
                exact hgle i
            _ = ENNReal.ofReal C := by
                rw [hCdef, ENNReal.ofReal_mul (inv_nonneg.mpr hNpos.le),
                  ENNReal.ofReal_sum_of_nonneg (fun i _ => hs i),
                  ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  have hW := hQ.2
  rw [show p.1 * ρ + (N : ℝ)⁻¹ * ∑ i, p.2 i = p.1 * ρ + C from rfl]
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  set η : ℝ := (δ : ℝ) / (p.1 + 1) with hηdef
  have hη : 0 < η := div_pos hδr (by linarith)
  have hlt : wasserstein κ Q (empirical xhat yhat) < ENNReal.ofReal (ρ + η) := by
    calc _ ≤ ENNReal.ofReal ρ := hW
      _ < ENNReal.ofReal (ρ + η) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  simp only [wasserstein, iInf_lt_iff] at hlt
  obtain ⟨π, _, h1, h2, hcost⟩ := hlt
  have hle : p.1 * η ≤ δ := by
    rw [hηdef, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc ∫⁻ ξ, ENNReal.ofReal (L (sgn ξ.2 * w ξ.1)) ∂Q ≤ ENNReal.ofReal C + ENNReal.ofReal p.1 *
        ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := hcoup π h1 h2
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal p.1 * ENNReal.ofReal (ρ + η) := by gcongr
    _ = ENNReal.ofReal (p.1 * ρ + C + p.1 * η) := by
        rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add hC (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (p.1 * ρ + C) + δ := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add
          (add_nonneg (mul_nonneg hlam hρ) hC) δ.coe_nonneg]
        apply ENNReal.ofReal_le_ofReal
        linarith

set_option maxHeartbeats 1000000 in
open MeasureTheory DRLogReg.Reformulation RegMT.Classif in
theorem rc11_strong {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 ≤ ρ) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L) (hL0 : ∀ z, 0 ≤ L z) (w : V →L[ℝ] ℝ) :
    ∃ q ∈ feasible18 κ xhat yhat L w, ∀ δ : ℝ, 0 < δ →
      ∃ Q ∈ wassersteinBall κ ρ (empirical xhat yhat),
        ENNReal.ofReal (q.1 * ρ + (N : ℝ)⁻¹ * ∑ i, q.2 i - δ) ≤
          ∫⁻ ξ, ENNReal.ofReal (L (sgn ξ.2 * w ξ.1)) ∂Q := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hκne : κ ≠ 0 := hκ.ne'
  have hNi : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
  obtain ⟨u, hu1, hu⟩ := rc11_norming w
  set ℓ := (WassersteinDRO.Duality.lipschitzModulus L).toReal with hℓ
  have hℓ0 : 0 ≤ ℓ := ENNReal.toReal_nonneg
  set Lw := ℓ * ‖w‖ with hLw
  have hLw0 : 0 ≤ Lw := mul_nonneg hℓ0 (norm_nonneg _)
  set mg : Fin N → ℝ := fun i => sgn (yhat i) * w (xhat i) with hmg
  set a : Fin N → ℝ := fun i => L (mg i) with ha
  set b : Fin N → ℝ := fun i => L (-(mg i)) with hb
  set mb : ℝ := N * ρ / κ with hmb
  have hmb0 : 0 ≤ mb := div_nonneg (mul_nonneg hNpos.le hρ) hκ.le
  obtain ⟨ν, hν, p, hp, hpm, hval⟩ := rc11_knap (fun i => b i - a i - Lw * κ) hmb0
  set lam := Lw + ν / κ with hlam
  have hlamκ : κ * lam = Lw * κ + ν := by
    rw [hlam]
    field_simp
  set s : Fin N → ℝ := fun i => max (a i) (b i - κ * lam) with hs
  have hfeas : (lam, s) ∈ feasible18 κ xhat yhat L w := by
    refine ⟨fun i => le_max_left _ _, fun i => le_max_right _ _, ?_⟩
    show Lw ≤ Lw + ν / κ
    have := div_nonneg hν hκ.le
    linarith
  refine ⟨(lam, s), hfeas, ?_⟩
  intro δ hδ
  set SP : ℝ := ∑ i, p i with hSP
  set V1 : ℝ := (N : ℝ)⁻¹ * ∑ i, (a i + p i * (b i - a i)) with hV1
  set ρ' : ℝ := ρ - κ * SP / N with hρ'
  have hSP0 : 0 ≤ SP := Finset.sum_nonneg fun i _ => (hp i).1
  have hρ'0 : 0 ≤ ρ' := by
    have h1 : κ * SP ≤ κ * mb := mul_le_mul_of_nonneg_left hpm hκ.le
    have h2 : κ * mb = N * ρ := by
      rw [hmb]
      field_simp
    have h3 : κ * SP / N ≤ ρ := by
      rw [div_le_iff₀ hNpos]
      linarith
    linarith
  -- the objective is bounded by V1 + Lw ρ'
  have hobj : lam * ρ + (N : ℝ)⁻¹ * ∑ i, s i ≤ V1 + Lw * ρ' := by
    have hsi : ∀ i, s i = a i + max 0 ((b i - a i - Lw * κ) - ν) := by
      intro i
      simp only [hs]
      rw [hlamκ]
      rcases le_total (a i) (b i - (Lw * κ + ν)) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]
        ring
      · rw [max_eq_left h, max_eq_left (by linarith)]
        ring
    have hνm : ν / κ * ρ = ν * mb / N := by
      rw [hmb]
      field_simp
    have e1 : ∑ i, s i = ∑ i, a i + ∑ i, max 0 ((b i - a i - Lw * κ) - ν) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hsi i
    have e2 : ∑ i, p i * (b i - a i - Lw * κ) =
        ∑ i, (a i + p i * (b i - a i)) - ∑ i, a i - Lw * κ * SP := by
      have : ∀ i, p i * (b i - a i - Lw * κ) = (a i + p i * (b i - a i)) - a i - Lw * κ * p i :=
        fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    have hval' : ν * mb + ∑ i, max 0 ((b i - a i - Lw * κ) - ν) ≤
        ∑ i, (a i + p i * (b i - a i)) - ∑ i, a i - Lw * κ * SP := by
      rw [← e2]
      exact hval
    rw [e1, hlam, add_mul, hνm, hV1, hρ']
    have key : (N : ℝ)⁻¹ * (ν * mb + ∑ i, max 0 ((b i - a i - Lw * κ) - ν)) ≤
        (N : ℝ)⁻¹ * (∑ i, (a i + p i * (b i - a i)) - ∑ i, a i - Lw * κ * SP) :=
      mul_le_mul_of_nonneg_left hval' hNi
    have e3 : ν * mb / N = (N : ℝ)⁻¹ * (ν * mb) := by ring
    have e4 : Lw * (ρ - κ * SP / N) = Lw * ρ - (N : ℝ)⁻¹ * (Lw * κ * SP) := by ring
    rw [e3, e4]
    linarith [key]
  -- an affine minorant of L with slope close to lip(L)
  have hwρ : 0 ≤ ‖w‖ * ρ' := mul_nonneg (norm_nonneg _) hρ'0
  set η : ℝ := δ / (2 * (‖w‖ * ρ' + 1)) with hη
  have hηpos : 0 < η := div_pos hδ (by linarith)
  have hηb : η * (‖w‖ * ρ') ≤ δ / 2 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  obtain ⟨g, K, hg, hgK⟩ := rc11_chord L hconv hLip hL0 hηpos
  set σ : ℝ := if 0 ≤ g then 1 else -1 with hσdef
  have hσ : σ * g = |g| := by
    rw [hσdef]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]
      ring
  have hσabs : |σ| = 1 := by
    rw [hσdef]
    split_ifs <;> simp
  -- choice of the push fraction
  set Z : ℝ := (N : ℝ)⁻¹ * ∑ i, (g * mg i + K) with hZ
  set D : ℝ := |V1 - Z| with hD
  have hD0 : 0 ≤ D := abs_nonneg _
  set q : ℝ := min 1 ((δ / 2) / (D + 1)) with hq
  have hq0 : 0 < q := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hqne : q ≠ 0 := hq0.ne'
  have hq1 : q ≤ 1 := min_le_left _ _
  have hqD : q * D ≤ δ / 2 := by
    have h1 : q ≤ (δ / 2) / (D + 1) := min_le_right _ _
    have h2 : q * (D + 1) ≤ δ / 2 := by rwa [le_div_iff₀ (by linarith)] at h1
    linarith
  set t : ℝ := ρ' / q with ht
  have ht0 : 0 ≤ t := div_nonneg hρ'0 hq0.le
  have hqt : q * t = ρ' := by
    rw [ht]
    field_simp
  -- the three destinations of each sample
  set wt : Fin N → Fin 3 → ℝ := fun i => ![(1 - q) * (1 - p i), (1 - q) * p i, q] with hwt
  set ζ : Fin N → Fin 3 → V × Bool := fun i =>
    ![(xhat i, yhat i), (xhat i, !yhat i), (xhat i + (t * σ * sgn (yhat i)) • u, yhat i)] with hζ
  have hw0 : ∀ i k, 0 ≤ wt i k := by
    intro i k
    obtain ⟨h1, h2⟩ := hp i
    fin_cases k
    · show 0 ≤ (1 - q) * (1 - p i)
      exact mul_nonneg (by linarith) (by linarith)
    · show 0 ≤ (1 - q) * p i
      exact mul_nonneg (by linarith) h1
    · show 0 ≤ q
      exact hq0.le
  have hw1 : ∀ i, ∑ k, wt i k = 1 := by
    intro i
    simp [hwt, Fin.sum_univ_three]
    ring
  have hpushd : ∀ i, featureLabelDist κ (xhat i + (t * σ * sgn (yhat i)) • u, yhat i)
      (xhat i, yhat i) ≤ t := by
    intro i
    rw [rc11_dist_same, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
      hσabs, rc11_abs_sgn, mul_one, mul_one, abs_of_nonneg ht0]
    calc t * ‖u‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hu1 ht0
      _ = t := mul_one t
  have hpushl : ∀ i, g * mg i + K + t * |g| * ‖w‖ ≤
      L (sgn (yhat i) * w (xhat i + (t * σ * sgn (yhat i)) • u)) := by
    intro i
    refine le_trans (le_of_eq ?_) (hgK _)
    rw [map_add, map_smul, smul_eq_mul, hu]
    have e1 := rc11_sgn_sq (yhat i)
    simp only [hmg]
    linear_combination (t * ‖w‖) * hσ.symm + (g * t * σ * ‖w‖) * e1.symm
  have hcost : ∑ i, ∑ k, wt i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i) ≤ ρ := by
    have hterm : ∀ i, ∑ k, wt i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i) ≤
        (N : ℝ)⁻¹ * (κ * p i) + (N : ℝ)⁻¹ * (q * t) := by
      intro i
      obtain ⟨h1, h1'⟩ := hp i
      have h2 := hpushd i
      simp only [hwt, hζ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_inv_mul]
      rw [rc11_dist_same κ (xhat i) (xhat i) (yhat i), rc11_dist_flip κ (xhat i) (xhat i) (yhat i),
        sub_self, norm_zero]
      have k1 : (N : ℝ)⁻¹ * ((1 - q) * p i * κ) ≤ (N : ℝ)⁻¹ * (κ * p i) := by
        have : (1 - q) * p i * κ ≤ κ * p i := by
          nlinarith [mul_nonneg (mul_nonneg hq0.le h1) hκ.le]
        exact mul_le_mul_of_nonneg_left this hNi
      have k2 : (N : ℝ)⁻¹ * (q * featureLabelDist κ (xhat i + (t * σ * sgn (yhat i)) • u, yhat i)
          (xhat i, yhat i)) ≤ (N : ℝ)⁻¹ * (q * t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hq0.le) hNi
      linarith [k1, k2]
    calc ∑ i, ∑ k, wt i k / N * featureLabelDist κ (ζ i k) (xhat i, yhat i)
        ≤ ∑ i, ((N : ℝ)⁻¹ * (κ * p i) + (N : ℝ)⁻¹ * (q * t)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (N : ℝ)⁻¹ * (κ * SP) + q * t := by
          rw [hSP]
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ = ρ := by
          rw [hqt, hρ']
          ring
  have hfm := rc11_meas L hLip w
  obtain ⟨Q, hQ, hQle⟩ := rc11_couple hκ.le hN xhat yhat wt hw0 hw1 ζ hcost
    (fun ξ => L (sgn ξ.2 * w ξ.1)) hfm (fun ξ => hL0 _)
  refine ⟨Q, hQ, le_trans (ENNReal.ofReal_le_ofReal ?_) hQle⟩
  -- value lower bound
  have hbi : ∀ i, L (sgn (!yhat i) * w (xhat i)) = b i := by
    intro i
    simp only [hb, hmg, rc11_sgn_not, neg_mul]
  have hvterm : ∀ i, (N : ℝ)⁻¹ * ((1 - q) * (a i + p i * (b i - a i))) +
      (N : ℝ)⁻¹ * (q * (g * mg i + K)) + (N : ℝ)⁻¹ * (q * t * |g| * ‖w‖) ≤
      ∑ k, wt i k / N * L (sgn (ζ i k).2 * w (ζ i k).1) := by
    intro i
    have h1 := hpushl i
    have k2 : (N : ℝ)⁻¹ * (q * (g * mg i + K + t * |g| * ‖w‖)) ≤
        (N : ℝ)⁻¹ * (q * L (sgn (yhat i) * w (xhat i + (t * σ * sgn (yhat i)) • u))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hq0.le) hNi
    simp only [hwt, hζ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_inv_mul]
    rw [hbi i]
    simp only [ha]
    linarith [k2]
  have hsum : ∑ i, ((N : ℝ)⁻¹ * ((1 - q) * (a i + p i * (b i - a i))) +
      (N : ℝ)⁻¹ * (q * (g * mg i + K)) + (N : ℝ)⁻¹ * (q * t * |g| * ‖w‖)) =
      (1 - q) * V1 + q * Z + q * t * |g| * ‖w‖ := by
    rw [hV1, hZ]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    try ring
  have hge := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hvterm i
  rw [hsum] at hge
  have hVZ : V1 - Z ≤ D := le_abs_self _
  have hqVZ : q * (V1 - Z) ≤ q * D := mul_le_mul_of_nonneg_left hVZ hq0.le
  have hqt' : q * t * |g| * ‖w‖ = |g| * (‖w‖ * ρ') := by rw [hqt]; ring
  have hgρ : (ℓ - η) * (‖w‖ * ρ') ≤ |g| * (‖w‖ * ρ') := mul_le_mul_of_nonneg_right hg hwρ
  have e5 : Lw * ρ' = ℓ * (‖w‖ * ρ') := by rw [hLw]; ring
  show lam * ρ + (N : ℝ)⁻¹ * ∑ i, s i - δ ≤
    ∑ i, ∑ k, wt i k / N * L (sgn (ζ i k).2 * w (ζ i k).1)
  linarith

open MeasureTheory DRLogReg.Reformulation RegMT.Classif in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {N : ℕ} (hN : 0 < N) (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (L : ℝ → ℝ)
    (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L)
    (hL0 : ∀ z, 0 ≤ L z) :
    (∀ w : V →L[ℝ] ℝ,
      worstCaseLoss κ ρ xhat yhat L w = value18 κ ρ xhat yhat L w) ∧
    (⨅ w : V →L[ℝ] ℝ, worstCaseLoss κ ρ xhat yhat L w) =
      (⨅ w : V →L[ℝ] ℝ, value18 κ ρ xhat yhat L w) := by
  have key : ∀ w : V →L[ℝ] ℝ,
      worstCaseLoss κ ρ xhat yhat L w = value18 κ ρ xhat yhat L w := by
    intro w
    apply le_antisymm
    · unfold value18
      refine le_iInf₂ fun q hq => ?_
      exact iSup₂_le fun Q hQ => rc11_weak hκ.le hρ hN L hLip hL0 w hq hQ
    · unfold value18
      obtain ⟨q, hq, hδ⟩ := rc11_strong hκ hρ hN xhat yhat L hconv hLip hL0 w
      refine (iInf₂_le q hq).trans ?_
      apply ENNReal.le_of_forall_pos_le_add
      intro δ hδpos _
      obtain ⟨Q, hQ, hQle⟩ := hδ δ (by exact_mod_cast hδpos)
      have h1 : ∫⁻ ξ, ENNReal.ofReal (L (sgn ξ.2 * w ξ.1)) ∂Q ≤
          worstCaseLoss κ ρ xhat yhat L w :=
        le_iSup₂ (f := fun Q (_ : Q ∈ wassersteinBall κ ρ (empirical xhat yhat)) =>
          ∫⁻ ξ, ENNReal.ofReal (L (sgn ξ.2 * w ξ.1)) ∂Q) Q hQ
      calc ENNReal.ofReal (q.1 * ρ + (N : ℝ)⁻¹ * ∑ i, q.2 i)
          = ENNReal.ofReal ((q.1 * ρ + (N : ℝ)⁻¹ * ∑ i, q.2 i - δ) + δ) := by
            congr 1
            ring
        _ ≤ ENNReal.ofReal (q.1 * ρ + (N : ℝ)⁻¹ * ∑ i, q.2 i - δ) + ENNReal.ofReal δ :=
            ENNReal.ofReal_add_le
        _ ≤ worstCaseLoss κ ρ xhat yhat L w + δ := by
            rw [ENNReal.ofReal_coe_nnreal]
            gcongr
            exact hQle.trans h1
  exact ⟨key, iInf_congr key⟩
