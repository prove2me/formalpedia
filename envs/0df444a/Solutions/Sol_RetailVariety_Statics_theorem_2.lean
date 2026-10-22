-- Prove2me | solution 1 for RetailVariety.Statics.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:13:27.773829+00:00
-- url     : https://prove2.me/submissions/79d77de9-f222-416a-b64b-b237a68b79f2

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology


namespace RetailVariety.Statics
open MeasureTheory ProbabilityTheory

noncomputable def phiN (x : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)

noncomputable def PhiN (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

lemma phiN_eq (x : ℝ) : gaussianPDFReal 0 1 x = phiN x := by
  simp [gaussianPDFReal_def, phiN]

lemma phiN_pos (x : ℝ) : 0 < phiN x := by
  unfold phiN; positivity

lemma continuous_phiN : Continuous phiN := by
  unfold phiN; fun_prop

lemma PhiN_sub (a b : ℝ) (hab : a ≤ b) : PhiN b - PhiN a = ∫ x in a..b, phiN x := by
  unfold PhiN
  have h1 : ENNReal.ofReal (cdf (gaussianReal 0 1) b)
      = ENNReal.ofReal (cdf (gaussianReal 0 1) a) + ENNReal.ofReal (∫ x in Set.Ioc a b, phiN x) := by
    have hI : gaussianReal 0 1 (Set.Ioc a b) = ENNReal.ofReal (∫ x in Set.Ioc a b, phiN x) := by
      rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
      simp only [phiN_eq]
    rw [ofReal_cdf, ofReal_cdf, ← Set.Iic_union_Ioc_eq_Iic hab,
      measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, hI]
  have h2 : 0 ≤ ∫ x in Set.Ioc a b, phiN x :=
    setIntegral_nonneg measurableSet_Ioc (fun x _ => (phiN_pos x).le)
  rw [← ENNReal.ofReal_add (cdf_nonneg _ _) h2] at h1
  have := (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ _) (by have := cdf_nonneg (gaussianReal 0 1) a; linarith)).mp h1
  rw [intervalIntegral.integral_of_le hab]
  linarith

lemma PhiN_eq (x : ℝ) : PhiN x = PhiN 0 + ∫ t in (0:ℝ)..x, phiN t := by
  rcases le_total 0 x with h | h
  · have := PhiN_sub 0 x h; linarith
  · have := PhiN_sub x 0 h
    rw [intervalIntegral.integral_symm]; linarith

lemma PhiN_hasDerivAt (x : ℝ) : HasDerivAt PhiN (phiN x) x := by
  have h := (continuous_phiN.integral_hasStrictDerivAt 0 x).hasDerivAt
  have : PhiN = fun y => PhiN 0 + ∫ t in (0:ℝ)..y, phiN t := funext PhiN_eq
  rw [this]
  exact h.const_add _

lemma PhiN_continuous : Continuous PhiN := continuous_iff_continuousAt.2 fun x => (PhiN_hasDerivAt x).continuousAt

lemma PhiN_strictMono : StrictMono PhiN :=
  strictMono_of_deriv_pos (fun x => by rw [(PhiN_hasDerivAt x).deriv]; exact phiN_pos x)

lemma PhiN_mono : Monotone PhiN := PhiN_strictMono.monotone

lemma PhiN_le_one (x : ℝ) : PhiN x ≤ 1 := cdf_le_one _ _
lemma PhiN_nonneg (x : ℝ) : 0 ≤ PhiN x := cdf_nonneg _ _
lemma PhiN_atTop : Tendsto PhiN atTop (𝓝 1) := tendsto_cdf_atTop _
lemma PhiN_atBot : Tendsto PhiN atBot (𝓝 0) := tendsto_cdf_atBot _


lemma cf_spec {p c : ℝ} (hc : 0 < c) (hcp : c < p) :
    PhiN (criticalFractile p c) = 1 - c / p := by
  have hp : 0 < p := hc.trans hcp
  have hu0 : 0 < 1 - c / p := by have : c / p < 1 := (div_lt_one hp).2 hcp; linarith
  have hu1 : 1 - c / p < 1 := by have : 0 < c / p := div_pos hc hp; linarith
  obtain ⟨a, ha⟩ := (PhiN_atBot.eventually (gt_mem_nhds hu0)).exists
  obtain ⟨b, hb⟩ := (PhiN_atTop.eventually (lt_mem_nhds hu1)).exists
  have hab : a ≤ b := by
    by_contra h
    push_neg at h
    have := PhiN_mono h.le
    linarith
  obtain ⟨x0, -, hx0⟩ := intermediate_value_Icc hab PhiN_continuous.continuousOn
    ⟨ha.le, hb.le⟩
  have hT : {x : ℝ | 1 - c / p ≤ cdf (gaussianReal 0 1) x} = Set.Ici x0 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    change 1 - c / p ≤ PhiN x ↔ x0 ≤ x
    rw [← hx0]
    rw [PhiN_strictMono.le_iff_le]
  have hT' : criticalFractile p c = x0 := by
    show sInf {x : ℝ | 1 - c / p ≤ cdf (gaussianReal 0 1) x} = x0
    rw [hT, csInf_Ici]
  rw [hT']
  exact hx0

lemma cf_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun p : ℝ => criticalFractile p c) (Set.Ioi c) := by
  intro p1 h1 p2 h2 h12
  simp only [Set.mem_Ioi] at h1 h2
  have e1 := cf_spec hc h1
  have e2 := cf_spec hc h2
  have hp1 : 0 < p1 := hc.trans h1
  have : 1 - c / p1 < 1 - c / p2 := by
    have : c / p2 < c / p1 := div_lt_div_of_pos_left hc hp1 h12
    linarith
  rw [← e1, ← e2] at this
  exact PhiN_strictMono.lt_iff_lt.1 this

lemma cf_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun p : ℝ => criticalFractile p c) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  have hM : PhiN M < 1 := lt_of_lt_of_le (PhiN_strictMono (lt_add_one M)) (PhiN_le_one _)
  have h1 : ∀ᶠ p : ℝ in atTop, c / p < 1 - PhiN M :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, eventually_gt_atTop c] with p hp hcp
  have := cf_spec hc hcp
  have h3 : PhiN M < PhiN (criticalFractile p c) := by rw [this]; linarith
  exact (PhiN_strictMono.lt_iff_lt.1 h3).le

lemma phiN_hasDerivAt (x : ℝ) : HasDerivAt phiN (-x * phiN x) x := by
  unfold phiN
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    refine this.congr_deriv ?_
    ring
  have := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine this.congr_deriv ?_
  ring

lemma phiN_tendsto_atBot : Tendsto phiN atBot (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => Real.exp (y / 2)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.atBot_div_const (by norm_num : (0:ℝ) < 2))
  have h2 : Tendsto (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (y / 2)) atBot (𝓝 0) := by
    simpa using h.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine squeeze_zero' (Eventually.of_forall (fun y => (phiN_pos y).le)) ?_ h2
  filter_upwards [eventually_le_atBot (-1)] with y hy
  unfold phiN
  gcongr
  nlinarith


noncomputable def Mfun (z : ℝ) : ℝ := phiN z / (-z) - PhiN z

lemma Mfun_hasDerivAt {z : ℝ} (hz : z < 0) : HasDerivAt Mfun (phiN z / z ^ 2) z := by
  have hz0 : z ≠ 0 := hz.ne
  have h1 := (phiN_hasDerivAt z).div (hasDerivAt_id z).neg (by simpa using hz0)
  have h2 := h1.sub (PhiN_hasDerivAt z)
  refine h2.congr_deriv ?_
  simp only [Pi.neg_apply, id]
  field_simp
  ring

lemma Mfun_strictMonoOn : StrictMonoOn Mfun (Set.Iio 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Iio 0)
    (fun x hx => (Mfun_hasDerivAt hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Iio] at hx
  have hx' : x < 0 := hx
  rw [(Mfun_hasDerivAt hx').deriv]
  exact div_pos (phiN_pos x) (by have : x ≠ 0 := hx'.ne; positivity)

lemma Mfun_tendsto : Tendsto Mfun atBot (𝓝 0) := by
  have h1 : Tendsto (fun z => phiN z / (-z)) atBot (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ phiN_tendsto_atBot
    · filter_upwards [eventually_lt_atBot 0] with z hz
      exact div_nonneg (phiN_pos z).le (by linarith)
    · filter_upwards [eventually_le_atBot (-1)] with z hz
      rw [div_le_iff₀ (by linarith)]
      have := phiN_pos z
      nlinarith
  have := h1.sub PhiN_atBot
  have e : Mfun = fun z => phiN z / (-z) - PhiN z := rfl
  rw [e]
  simpa using this

lemma Mfun_pos {z : ℝ} (hz : z < 0) : 0 < Mfun z := by
  have h1 : 0 ≤ Mfun (z - 1) := by
    refine le_of_tendsto Mfun_tendsto ?_
    filter_upwards [eventually_le_atBot (z - 1)] with y hy
    rcases hy.lt_or_eq with h | h
    · exact (Mfun_strictMonoOn (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith) h).le
    · rw [h]
  have h2 : Mfun (z - 1) < Mfun z :=
    Mfun_strictMonoOn (by simp only [Set.mem_Iio]; linarith) hz (by linarith)
  linarith

lemma H_pos (z : ℝ) : 0 < phiN z + z * PhiN z := by
  rcases le_or_gt 0 z with h | h
  · have := phiN_pos z
    have := mul_nonneg h (PhiN_nonneg z)
    linarith
  · have h1 := Mfun_pos h
    have hz0 : z ≠ 0 := h.ne
    have : phiN z + z * PhiN z = (-z) * Mfun z := by
      unfold Mfun
      field_simp
      ring
    rw [this]
    exact mul_pos (by linarith) h1

noncomputable def Gfun (z : ℝ) : ℝ := PhiN z * Real.exp (z ^ 2 / 2)

lemma Gfun_strictMono : StrictMono Gfun := by
  have hd : ∀ z, HasDerivAt Gfun (Real.exp (z ^ 2 / 2) * (phiN z + z * PhiN z)) z := by
    intro z
    have h1 := ((hasDerivAt_pow 2 z).div_const 2).exp
    have h2 := (PhiN_hasDerivAt z).mul h1
    refine h2.congr_deriv ?_
    push_cast
    ring
  refine strictMono_of_deriv_pos (fun z => ?_)
  rw [(hd z).deriv]
  exact mul_pos (Real.exp_pos _) (H_pos z)


open RetailVariety.Structure (share profitI profitT popularSet)

lemma A_succ (n i : ℕ) (hin : i < n) : A n (i+1) = insert ⟨i, hin⟩ (A n i) := by
  ext j
  simp only [A, popularSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

lemma A_not_mem (n i : ℕ) (hin : i < n) : (⟨i, hin⟩ : Fin n) ∉ A n i := by
  simp [A, popularSet]

lemma mem_A {n i : ℕ} {j : Fin n} : j ∈ A n i ↔ j.val < i := by simp [A, popularSet]

lemma sum_share {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n)) :
    ∑ j ∈ S, share v v0 S j = (∑ j ∈ S, v j) / (∑ j ∈ S, v j + v0) := by
  unfold share; rw [Finset.sum_div]

lemma Q_lt {n : ℕ} (v : Fin n → ℝ) (hv : ∀ j, 0 < v j) (v0 : ℝ) (hv0 : 0 < v0)
    (S : Finset (Fin n)) (a : Fin n) (ha : a ∉ S) :
    ∑ j ∈ S, share v v0 S j < ∑ j ∈ insert a S, share v v0 (insert a S) j := by
  rw [sum_share, sum_share, Finset.sum_insert ha]
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => (hv j).le)
  have := hv a
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (hv a) hv0]

lemma e_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun p : ℝ => Real.exp (-(criticalFractile p c) ^ 2 / 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun p : ℝ => criticalFractile p c ^ 2 / 2) atTop atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (cf_tendsto hc)).atTop_div_const two_pos
  have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  refine h2.congr (fun p => ?_)
  simp [neg_div]

lemma alg_I (p c lam σ β z Q Q' R R' : ℝ) (hp : p ≠ 0) :
    ((p - c) * lam * Q' - (p * σ * lam ^ β * Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * Real.pi)) * R')
      - ((p - c) * lam * Q - (p * σ * lam ^ β * Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * Real.pi)) * R)
    = p * ((1 - c / p) * (lam * (Q' - Q))
      - (σ * lam ^ β * Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * Real.pi)) * (R' - R)) := by
  field_simp
  ring

lemma profitI_a_core {n : ℕ} (v : Fin n → ℝ) (v0 c lam σ β : ℝ) (hc : 0 < c) (hlam : 0 < lam)
    (hσ : 0 < σ) (S S' : Finset (Fin n))
    (hQ : ∑ j ∈ S, share v v0 S j < ∑ j ∈ S', share v v0 S' j) :
    ∀ᶠ p in atTop, profitI p c lam σ β v v0 S < profitI p c lam σ β v v0 S' := by
  set Q := ∑ j ∈ S, share v v0 S j
  set Q' := ∑ j ∈ S', share v v0 S' j
  set R := ∑ j ∈ S, share v v0 S j ^ β
  set R' := ∑ j ∈ S', share v v0 S' j ^ β
  let B : ℝ → ℝ := fun p => (1 - c / p) * (lam * (Q' - Q))
    - (σ * lam ^ β * Real.exp (-(criticalFractile p c) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) * (R' - R)
  have hc0 : Tendsto (fun p : ℝ => c / p) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have ht : Tendsto B atTop (𝓝 ((1 - 0) * (lam * (Q' - Q))
      - (σ * lam ^ β * 0 / Real.sqrt (2 * Real.pi)) * (R' - R))) := by
    refine Tendsto.sub (Tendsto.mul (tendsto_const_nhds.sub hc0) tendsto_const_nhds) ?_
    refine Tendsto.mul ?_ tendsto_const_nhds
    exact ((tendsto_const_nhds.mul (e_tendsto hc)).div_const _)
  have hlim : (1 - 0) * (lam * (Q' - Q)) - (σ * lam ^ β * 0 / Real.sqrt (2 * Real.pi)) * (R' - R)
      = lam * (Q' - Q) := by ring
  rw [hlim] at ht
  have hpos : 0 < lam * (Q' - Q) := mul_pos hlam (by linarith)
  filter_upwards [ht.eventually (lt_mem_nhds hpos), eventually_gt_atTop c] with p hB hp
  have hp0 : p ≠ 0 := (hc.trans hp).ne'
  have key : profitI p c lam σ β v v0 S' - profitI p c lam σ β v v0 S = p * B p := by
    exact alg_I p c lam σ β (criticalFractile p c) Q Q' R R' hp0
  have : 0 < p * B p := mul_pos (hc.trans hp) (by simpa using hB)
  linarith


lemma profitT_lin {n : ℕ} (v : Fin n → ℝ) (v0 p c lam : ℝ) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, c < p * share v v0 T j) :
    profitT p c lam v v0 T = lam * (p * ∑ j ∈ T, share v v0 T j - T.card * c) := by
  unfold profitT
  rw [Finset.sum_congr rfl (fun j hj => by rw [max_eq_left (by linarith [hT j hj])])]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  ring

lemma profitT_a_core {n : ℕ} (v : Fin n → ℝ) (hv : ∀ j, 0 < v j) (v0 c lam : ℝ) (hlam : 0 < lam)
    (S S' : Finset (Fin n)) (hS : 0 < ∑ j ∈ S, v j + v0) (hS' : 0 < ∑ j ∈ S', v j + v0)
    (hQ : ∑ j ∈ S, share v v0 S j < ∑ j ∈ S', share v v0 S' j) :
    ∀ᶠ p in atTop, profitT p c lam v v0 S < profitT p c lam v v0 S' := by
  have h1 : ∀ᶠ p : ℝ in atTop, ∀ j, c < p * share v v0 S j ∧ c < p * share v v0 S' j := by
    rw [eventually_all]
    intro j
    have a1 : 0 < share v v0 S j := div_pos (hv j) hS
    have a2 : 0 < share v v0 S' j := div_pos (hv j) hS'
    filter_upwards [eventually_gt_atTop (c / share v v0 S j),
      eventually_gt_atTop (c / share v v0 S' j)] with p h1 h2
    exact ⟨(div_lt_iff₀ a1).1 h1, (div_lt_iff₀ a2).1 h2⟩
  have h2 : ∀ᶠ p : ℝ in atTop,
      c * ((S'.card : ℝ) - S.card) / (∑ j ∈ S', share v v0 S' j - ∑ j ∈ S, share v v0 S j) < p :=
    eventually_gt_atTop _
  filter_upwards [h1, h2] with p hp1 hp2
  rw [profitT_lin v v0 p c lam S (fun j _ => (hp1 j).1),
    profitT_lin v v0 p c lam S' (fun j _ => (hp1 j).2)]
  have hd : 0 < ∑ j ∈ S', share v v0 S' j - ∑ j ∈ S, share v v0 S j := by linarith
  have := (div_lt_iff₀ hd).1 hp2
  apply mul_lt_mul_of_pos_left _ hlam
  nlinarith

lemma alg_c (p c lam σ Ex Sq Q Q' R R' L M : ℝ) (hL : L = lam * M) :
    ((p - c) * lam * Q' - (p * σ * L * Ex / Sq) * R') - ((p - c) * lam * Q - (p * σ * L * Ex / Sq) * R)
    = lam * ((p - c) * (Q' - Q) - (p * σ * Ex / Sq * M) * (R' - R)) := by
  subst hL; ring

lemma profitI_c_core {n : ℕ} (v : Fin n → ℝ) (v0 p c σ β : ℝ) (hc : 0 < c) (hcp : c < p)
    (hσ : 0 < σ) (hβ1 : β < 1) (S S' : Finset (Fin n))
    (hQ : ∑ j ∈ S, share v v0 S j < ∑ j ∈ S', share v v0 S' j) :
    ∀ᶠ lam in atTop, profitI p c lam σ β v v0 S < profitI p c lam σ β v v0 S' := by
  set Q := ∑ j ∈ S, share v v0 S j
  set Q' := ∑ j ∈ S', share v v0 S' j
  set R := ∑ j ∈ S, share v v0 S j ^ β
  set R' := ∑ j ∈ S', share v v0 S' j ^ β
  have hp : 0 < p := hc.trans hcp
  let B : ℝ → ℝ := fun lam => (p - c) * (Q' - Q) - (p * σ * Real.exp (-(criticalFractile p c) ^ 2 / 2)
    / Real.sqrt (2 * Real.pi) * lam ^ (β - 1)) * (R' - R)
  have hM : Tendsto (fun lam : ℝ => lam ^ (β - 1)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (by linarith : 0 < 1 - β)
    have e : β - 1 = -(1 - β) := by ring
    rw [e]; exact this
  have ht : Tendsto B atTop (𝓝 ((p - c) * (Q' - Q) - (p * σ * Real.exp (-(criticalFractile p c) ^ 2 / 2)
    / Real.sqrt (2 * Real.pi) * 0) * (R' - R))) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds.mul hM).mul tendsto_const_nhds)
  have hlim : (p - c) * (Q' - Q) - (p * σ * Real.exp (-(criticalFractile p c) ^ 2 / 2)
    / Real.sqrt (2 * Real.pi) * 0) * (R' - R) = (p - c) * (Q' - Q) := by ring
  rw [hlim] at ht
  have hpos : 0 < (p - c) * (Q' - Q) := mul_pos (by linarith) (by linarith)
  filter_upwards [ht.eventually (lt_mem_nhds hpos), eventually_gt_atTop 0] with lam hB hl
  have hL : lam ^ β = lam * lam ^ (β - 1) := by
    have : lam ^ β = lam ^ ((1:ℝ) + (β - 1)) := by ring_nf
    rw [this, Real.rpow_add hl, Real.rpow_one]
  have key : profitI p c lam σ β v v0 S' - profitI p c lam σ β v v0 S = lam * B lam :=
    alg_c p c lam σ (Real.exp (-(criticalFractile p c) ^ 2 / 2)) (Real.sqrt (2 * Real.pi))
      Q Q' R R' (lam ^ β) (lam ^ (β - 1)) hL
  have : 0 < lam * B lam := mul_pos hl (by simpa using hB)
  linarith


lemma contAt_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ) (x : ℝ)
    (h : ∀ j ∈ S, ContinuousAt (f j) x) : ContinuousAt (fun y => ∑ j ∈ S, f j y) x :=
  tendsto_finsetSum S h

lemma contAt_share {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n)) (hV : 0 < ∑ j ∈ S, v j)
    (j : Fin n) : ContinuousAt (fun v0 : ℝ => share v v0 S j) 0 := by
  unfold share
  refine ContinuousAt.div continuousAt_const (continuousAt_const.add continuousAt_id) ?_
  simpa using hV.ne'

lemma contAt_profitI {n : ℕ} (v : Fin n → ℝ) (p c lam σ β : ℝ) (hβ0 : 0 ≤ β)
    (S : Finset (Fin n)) (hV : 0 < ∑ j ∈ S, v j) :
    ContinuousAt (fun v0 : ℝ => profitI p c lam σ β v v0 S) 0 := by
  unfold profitI
  refine ContinuousAt.sub (continuousAt_const.mul (contAt_sum S _ 0 (fun j _ => contAt_share v S hV j)))
    (continuousAt_const.mul (contAt_sum S _ 0 (fun j _ => (contAt_share v S hV j).rpow_const (Or.inr hβ0))))

lemma contAt_profitT {n : ℕ} (v : Fin n → ℝ) (p c lam : ℝ)
    (S : Finset (Fin n)) (hV : 0 < ∑ j ∈ S, v j) :
    ContinuousAt (fun v0 : ℝ => profitT p c lam v v0 S) 0 := by
  unfold profitT
  refine contAt_sum S _ 0 (fun j _ => ?_)
  exact (((continuousAt_const.mul (contAt_share v S hV j)).sub continuousAt_const).max
    continuousAt_const).mul continuousAt_const

lemma profitI_zero {n : ℕ} (v : Fin n → ℝ) (p c lam σ β : ℝ) (S : Finset (Fin n))
    (hV : 0 < ∑ j ∈ S, v j) :
    profitI p c lam σ β v 0 S = (p - c) * lam
      - (p * σ * lam ^ β * Real.exp (-(criticalFractile p c) ^ 2 / 2) / Real.sqrt (2 * Real.pi))
        * ∑ j ∈ S, (v j / ∑ i ∈ S, v i) ^ β := by
  unfold profitI share
  simp only [add_zero]
  have h1 : ∑ j ∈ S, v j / ∑ i ∈ S, v i = 1 := by
    rw [← Finset.sum_div]; exact div_self hV.ne'
  rw [h1, mul_one]
  rfl

lemma T_lt {ι : Type*} [DecidableEq ι] (S : Finset ι) (v : ι → ℝ) (hv : ∀ j, 0 < v j)
    (hS : S.Nonempty) (a : ι) (ha : a ∉ S) (hle : ∀ j ∈ S, v a ≤ v j) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    ∑ j ∈ S, (v j / ∑ i ∈ S, v i) ^ β < ∑ j ∈ insert a S, (v j / ∑ i ∈ insert a S, v i) ^ β := by
  have hVpos : 0 < ∑ i ∈ S, v i := Finset.sum_pos (fun j _ => hv j) hS
  have hSgpos : 0 < ∑ j ∈ S, v j ^ β :=
    Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hv j) β) hS
  have hW : ∑ i ∈ insert a S, v i = v a + ∑ i ∈ S, v i := Finset.sum_insert ha
  generalize hVd : ∑ i ∈ S, v i = V at hVpos hW ⊢
  generalize hSgd : ∑ j ∈ S, v j ^ β = Sg at hSgpos
  have hδpos : 0 < v a := hv a
  have hWpos : 0 < v a + V := by linarith
  have hL : ∑ j ∈ S, (v j / V) ^ β = Sg / V ^ β := by
    rw [← hSgd, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => Real.div_rpow (hv j).le hVpos.le β)
  have hR : ∑ j ∈ S, (v j / (v a + V)) ^ β = Sg / (v a + V) ^ β := by
    rw [← hSgd, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => Real.div_rpow (hv j).le hWpos.le β)
  rw [Finset.sum_insert ha, hW, hL, hR, Real.div_rpow hδpos.le hWpos.le, ← add_div]
  have hVb : 0 < V ^ β := Real.rpow_pos_of_pos hVpos β
  have hWb : 0 < (v a + V) ^ β := Real.rpow_pos_of_pos hWpos β
  rw [div_lt_div_iff₀ hVb hWb]
  -- Bernoulli
  have hx : (v a + V) ^ β = V ^ β * (1 + v a / V) ^ β := by
    rw [← Real.mul_rpow hVpos.le (by positivity)]
    congr 1
    field_simp
    ring
  have hva : 0 ≤ v a / V := by positivity
  have hB : (1 + v a / V) ^ β ≤ 1 + β * (v a / V) :=
    rpow_one_add_le_one_add_mul_self (by linarith) hβ0 hβ1.le
  -- bound: δ^(1-β) * Sg ≤ V
  have hbound : v a ^ (1 - β) * Sg ≤ V := by
    rw [← hSgd, ← hVd, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have h1 : v a ^ (1 - β) ≤ v j ^ (1 - β) :=
      Real.rpow_le_rpow hδpos.le (hle j hj) (by linarith)
    have h2 : v j = v j ^ (1 - β) * v j ^ β := by
      rw [← Real.rpow_add (hv j)]; simp
    calc v a ^ (1 - β) * v j ^ β ≤ v j ^ (1 - β) * v j ^ β :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hv j).le β)
      _ = v j := h2.symm
  have hδ : v a = v a ^ β * v a ^ (1 - β) := by
    rw [← Real.rpow_add hδpos]; simp
  have hδb : 0 < v a ^ β := Real.rpow_pos_of_pos hδpos β
  have hδb' : 0 < v a ^ (1 - β) := Real.rpow_pos_of_pos hδpos _
  -- key: β * Sg * v a < v a ^ β * V
  have hkey : β * Sg * v a < v a ^ β * V := by
    have h3 : v a ^ β * (v a ^ (1 - β) * Sg) ≤ v a ^ β * V :=
      mul_le_mul_of_nonneg_left hbound hδb.le
    have h4 : v a ^ β * (v a ^ (1 - β) * Sg) = v a * Sg := by
      rw [← mul_assoc, ← hδ]
    have h5 : β * Sg * v a < v a * Sg := by nlinarith [mul_pos hδpos hSgpos]
    linarith
  rw [hx]
  have hxa : Sg * (V ^ β * (1 + v a / V) ^ β) ≤ Sg * (V ^ β * (1 + β * (v a / V))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hVb.le) hSgpos.le
  have : Sg * (V ^ β * (1 + β * (v a / V))) < (v a ^ β + Sg) * V ^ β := by
    have e : Sg * (V ^ β * (1 + β * (v a / V))) = Sg * V ^ β + V ^ β * (β * Sg * v a / V) := by
      field_simp
    rw [e]
    have : β * Sg * v a / V < v a ^ β := by
      rw [div_lt_iff₀ hVpos]; linarith
    nlinarith
  linarith


lemma profitT_zero {n : ℕ} (v : Fin n → ℝ) (p c lam : ℝ) (S : Finset (Fin n)) :
    profitT p c lam v 0 S = lam * ∑ j ∈ S, max (p * (v j / ∑ i ∈ S, v i) - c) 0 := by
  unfold profitT share
  simp only [add_zero]
  rw [← Finset.sum_mul, mul_comm]

lemma sum_lin {ι : Type*} (S : Finset ι) (v : ι → ℝ) (p c X : ℝ) :
    ∑ j ∈ S, (p * (v j / X) - c) = p * (∑ j ∈ S, v j) / X - S.card * c := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  simp
  ring

lemma F_lt {ι : Type*} [DecidableEq ι] (S : Finset ι) (v : ι → ℝ) (hv : ∀ j, 0 < v j)
    (p c : ℝ) (hp : 0 < p) (hc : 0 < c) (a : ι) (ha : a ∉ S) (hle : ∀ j ∈ S, v a ≤ v j)
    (b : ι) (hb : b ∈ S) (hcb : c * ∑ i ∈ S, v i < p * v b) :
    ∑ j ∈ insert a S, max (p * (v j / ∑ i ∈ insert a S, v i) - c) 0
      < ∑ j ∈ S, max (p * (v j / ∑ i ∈ S, v i) - c) 0 := by
  have hVpos : 0 < ∑ i ∈ S, v i := Finset.sum_pos (fun j _ => hv j) ⟨b, hb⟩
  have hW : ∑ i ∈ insert a S, v i = v a + ∑ i ∈ S, v i := Finset.sum_insert ha
  have hδpos : 0 < v a := hv a
  generalize hVd : ∑ i ∈ S, v i = V at hVpos hW hcb ⊢
  have hWpos : 0 < v a + V := by linarith
  rw [Finset.sum_insert ha, hW]
  by_cases hcase : p * (v a / (v a + V)) - c ≤ 0
  · rw [max_eq_right hcase, zero_add]
    apply Finset.sum_lt_sum
    · intro j hj
      have : v j / (v a + V) ≤ v j / V :=
        div_le_div_of_nonneg_left (hv j).le hVpos (by linarith)
      exact max_le_max (by nlinarith) le_rfl
    · refine ⟨b, hb, ?_⟩
      have h1 : v b / (v a + V) < v b / V := div_lt_div_of_pos_left (hv b) hVpos (by linarith)
      have h2 : 0 < p * (v b / V) - c := by
        have : c < p * v b / V := by rw [lt_div_iff₀ hVpos]; linarith
        have e : p * (v b / V) = p * v b / V := by ring
        linarith
      have h3 := mul_lt_mul_of_pos_left h1 hp
      rw [max_eq_left h2.le]
      exact max_lt (by linarith) h2
  · push_neg at hcase
    have hL : ∀ j ∈ S, max (p * (v j / (v a + V)) - c) 0 = p * (v j / (v a + V)) - c := by
      intro j hj
      apply max_eq_left
      have : v a / (v a + V) ≤ v j / (v a + V) :=
        div_le_div_of_nonneg_right (hle j hj) hWpos.le
      nlinarith
    have hR : ∀ j ∈ S, max (p * (v j / V) - c) 0 = p * (v j / V) - c := by
      intro j hj
      apply max_eq_left
      have h1 : v a / (v a + V) ≤ v j / (v a + V) :=
        div_le_div_of_nonneg_right (hle j hj) hWpos.le
      have h2 : v j / (v a + V) ≤ v j / V :=
        div_le_div_of_nonneg_left (hv j).le hVpos (by linarith)
      nlinarith
    rw [max_eq_left hcase.le, Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
    rw [sum_lin, sum_lin]
    rw [hVd]
    have hV0 : V ≠ 0 := hVpos.ne'
    have hW0 : v a + V ≠ 0 := hWpos.ne'
    have e1 : p * (v a / (v a + V)) + p * V / (v a + V) = p := by field_simp
    have e2 : p * V / V = p := by field_simp
    linarith


theorem theorem_2_core (n i : ℕ) (hi : 1 ≤ i) (hin : i < n) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j)
    (hanti : Antitone v) (c σ β : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ lam v0 : ℝ, 0 < lam → 0 < v0 →
      (∀ᶠ p in atTop,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1))) ∧
      (∀ᶠ p in atTop,
          RetailVariety.Structure.profitT p c lam v v0 (A n i) < RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)))) ∧
    (∀ p lam : ℝ, c < p → 0 < lam →
      (∀ᶠ v0 in 𝓝[>] 0,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1)) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n i)) ∧
      (c * ∑ j ∈ A n i, v j < p * v ⟨0, by omega⟩ →
        ∀ᶠ v0 in 𝓝[>] 0,
          RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)) < RetailVariety.Structure.profitT p c lam v v0 (A n i))) ∧
    (∀ p v0 : ℝ, c < p → 0 < v0 →
      ∀ᶠ lam in atTop,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1))) := by
  have hsucc : A n (i+1) = insert ⟨i, hin⟩ (A n i) := A_succ n i hin
  have hna : (⟨i, hin⟩ : Fin n) ∉ A n i := A_not_mem n i hin
  generalize ha : (⟨i, hin⟩ : Fin n) = a at hsucc hna
  have hle : ∀ j ∈ A n i, v a ≤ v j := by
    intro j hj
    apply hanti
    have h1 := mem_A.1 hj
    rw [Fin.le_def, ← ha]
    show j.val ≤ i
    omega
  have hb : (⟨0, by omega⟩ : Fin n) ∈ A n i := mem_A.2 (by simp; omega)
  have hne : (A n i).Nonempty := ⟨_, hb⟩
  have hVpos : 0 < ∑ j ∈ A n i, v j := Finset.sum_pos (fun j _ => hv j) hne
  have hVpos' : 0 < ∑ j ∈ insert a (A n i), v j := by
    rw [Finset.sum_insert hna]; have := hv a; linarith
  rw [hsucc]
  refine ⟨?_, ?_, ?_⟩
  · intro lam v0 hlam hv0
    refine ⟨profitI_a_core v v0 c lam σ β hc hlam hσ _ _ (Q_lt v hv v0 hv0 _ a hna),
      profitT_a_core v hv v0 c lam hlam _ _ (by linarith) (by linarith)
        (Q_lt v hv v0 hv0 _ a hna)⟩
  · intro p lam hcp hlam
    have hp : 0 < p := hc.trans hcp
    constructor
    · have hTlt := T_lt (A n i) v hv hne a hna hle β hβ0 hβ1
      have hκ : 0 < p * σ * lam ^ β * Real.exp (-(criticalFractile p c) ^ 2 / 2)
          / Real.sqrt (2 * Real.pi) := by positivity
      have hcont : ContinuousAt (fun v0 : ℝ => profitI p c lam σ β v v0 (A n i)
          - profitI p c lam σ β v v0 (insert a (A n i))) 0 :=
        (contAt_profitI v p c lam σ β hβ0 _ hVpos).sub (contAt_profitI v p c lam σ β hβ0 _ hVpos')
      have hf0 : 0 < profitI p c lam σ β v 0 (A n i)
          - profitI p c lam σ β v 0 (insert a (A n i)) := by
        rw [profitI_zero v p c lam σ β _ hVpos, profitI_zero v p c lam σ β _ hVpos']
        have := mul_pos hκ (sub_pos.2 hTlt)
        nlinarith
      have hev := hcont.eventually (lt_mem_nhds hf0)
      exact (hev.filter_mono nhdsWithin_le_nhds).mono (fun x hx => by simpa using hx)
    · intro hcond
      have hF := F_lt (A n i) v hv p c hp hc a hna hle _ hb hcond
      have hcont : ContinuousAt (fun v0 : ℝ => profitT p c lam v v0 (A n i)
          - profitT p c lam v v0 (insert a (A n i))) 0 :=
        (contAt_profitT v p c lam _ hVpos).sub (contAt_profitT v p c lam _ hVpos')
      have hf0 : 0 < profitT p c lam v 0 (A n i) - profitT p c lam v 0 (insert a (A n i)) := by
        rw [profitT_zero, profitT_zero]
        have := mul_pos hlam (sub_pos.2 hF)
        nlinarith
      have hev := hcont.eventually (lt_mem_nhds hf0)
      exact (hev.filter_mono nhdsWithin_le_nhds).mono (fun x hx => by simpa using hx)
  · intro p v0 hcp hv0
    exact profitI_c_core v v0 p c σ β hc hcp hσ hβ1 _ _ (Q_lt v hv v0 hv0 _ a hna)

end RetailVariety.Statics

open RetailVariety.Statics


theorem solution (n i : ℕ) (hi : 1 ≤ i) (hin : i < n) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j)
    (hanti : Antitone v) (c σ β : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    -- (a) sufficiently high selling price p, both demand models
    (∀ lam v0 : ℝ, 0 < lam → 0 < v0 →
      (∀ᶠ p in atTop,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1))) ∧
      (∀ᶠ p in atTop,
          RetailVariety.Structure.profitT p c lam v v0 (A n i) < RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)))) ∧
    -- (b) sufficiently low no-purchase preference v0, both demand models
    (∀ p lam : ℝ, c < p → 0 < lam →
      (∀ᶠ v0 in 𝓝[>] 0,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1)) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n i)) ∧
      (c * ∑ j ∈ A n i, v j < p * v ⟨0, by omega⟩ →
        ∀ᶠ v0 in 𝓝[>] 0,
          RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)) < RetailVariety.Structure.profitT p c lam v v0 (A n i))) ∧
    -- (c) sufficiently high store volume lam, independent population model only
    (∀ p v0 : ℝ, c < p → 0 < v0 →
      ∀ᶠ lam in atTop,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1))) := by
  exact theorem_2_core n i hi hin v hv hanti c σ β hc hσ hβ0 hβ1
