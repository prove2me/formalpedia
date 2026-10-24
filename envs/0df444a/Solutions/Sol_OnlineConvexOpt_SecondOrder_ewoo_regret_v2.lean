-- Prove2me | solution 1 for OnlineConvexOpt.SecondOrder.ewoo_regret_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:31:38.934732+00:00
-- url     : https://prove2.me/submissions/dc83059f-afbc-4ca8-9361-0c92bbd7c792

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_EWOO
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2
open MeasureTheory Metric

namespace EW88

theorem jensen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ν : Measure E} [IsFiniteMeasure ν] {K : Set E} (hK : Convex ℝ K)
    (hKae : ∀ᵐ y ∂ν, y ∈ K) {c : E} {r : ℝ} (hball : closedBall c r ⊆ interior K)
    (hν : ν (closedBall c r) ≠ 0) {w h : E → ℝ} (hwpos : ∀ y, 0 < w y)
    (hwi : Integrable w ν) (hwy : Integrable (fun y => w y • y) ν)
    (hwh : Integrable (fun y => w y * h y) ν) (hconc : ConcaveOn ℝ K h)
    (hcont : ContinuousOn h (interior K)) :
    ∫ y, w y * h y ∂ν ≤ h ((∫ y, w y ∂ν)⁻¹ • ∫ y, w y • y ∂ν) * ∫ y, w y ∂ν := by
  set μ := ν.withDensity (fun y => ENNReal.ofReal (w y)) with hμ
  have hwm : AEMeasurable (fun y => ENNReal.ofReal (w y)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable hwi.aemeasurable
  have hlt : ∀ᵐ y ∂ν, ENNReal.ofReal (w y) < ⊤ := Filter.Eventually.of_forall (fun _ => by simp)
  have : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have hint : ∀ g : E → ℝ, ∫ y, g y ∂μ = ∫ y, w y * g y ∂ν := by
    intro g
    rw [hμ, integral_withDensity_eq_integral_toReal_smul₀ hwm hlt]
    congr 1; ext y; simp [ENNReal.toReal_ofReal (hwpos y).le]
  have hintE : ∫ y, y ∂μ = ∫ y, w y • y ∂ν := by
    rw [hμ, integral_withDensity_eq_integral_toReal_smul₀ hwm hlt]
    congr 1; ext y; simp [ENNReal.toReal_ofReal (hwpos y).le]
  have hid : Integrable (fun y : E => y) μ := by
    rw [hμ, integrable_withDensity_iff_integrable_smul₀' hwm hlt]
    refine (integrable_congr (Filter.Eventually.of_forall fun y => ?_)).1 hwy
    simp [ENNReal.toReal_ofReal (hwpos y).le]
  have hhi : Integrable h μ := by
    rw [hμ, integrable_withDensity_iff_integrable_smul₀' hwm hlt]
    refine (integrable_congr (Filter.Eventually.of_forall fun y => ?_)).1 hwh
    simp [ENNReal.toReal_ofReal (hwpos y).le]
  have hmass : μ.real Set.univ = ∫ y, w y ∂ν := by
    have := hint (fun _ => 1)
    simpa using this
  have hμt : μ (closedBall c r) ≠ 0 := by
    rw [hμ, Ne, withDensity_apply_eq_zero' hwm]
    have : {x | ENNReal.ofReal (w x) ≠ 0} = Set.univ := by
      ext y; simp [hwpos y]
    rw [this, Set.univ_inter]; exact hν
  have : NeZero μ := ⟨fun h0 => hμt (by simp [h0])⟩
  have hμae : ∀ᵐ y ∂μ, y ∈ K := (withDensity_absolutelyContinuous ν _).ae_le hKae
  -- barycenter in interior
  have hbar : (⨍ y, y ∂μ) ∈ interior K := by
    refine hK.average_mem_interior_of_set (t := closedBall c r) hμt hμae hid ?_
    exact hball ((convex_closedBall c r).set_average_mem isClosed_closedBall hμt
      (measure_ne_top _ _) (ae_restrict_mem measurableSet_closedBall) hid.integrableOn)
  -- hypograph
  have hpair : (⨍ y, ((y, h y) : E × ℝ) ∂μ) ∈ closure {p : E × ℝ | p.1 ∈ K ∧ p.2 ≤ h p.1} := by
    have := hconc.convex_hypograph.set_average_mem_closure (μ := μ) (t := Set.univ)
      (f := fun y => ((y, h y) : E × ℝ)) (by simpa using NeZero.ne μ) (measure_ne_top _ _)
      (by rw [Measure.restrict_univ]; exact hμae.mono fun y hy => ⟨hy, le_rfl⟩)
      (by rw [integrableOn_univ]; exact hid.prodMk hhi)
    simpa using this
  rw [average_pair hid hhi] at hpair
  have hle : (⨍ y, h y ∂μ) ≤ h (⨍ y, y ∂μ) := by
    obtain ⟨p, hpH, hplim⟩ := mem_closure_iff_seq_limit.1 hpair
    have h1 : Filter.Tendsto (fun k => (p k).1) Filter.atTop (nhds (⨍ y, y ∂μ)) :=
      (continuous_fst.tendsto _).comp hplim
    have h2 : Filter.Tendsto (fun k => (p k).2) Filter.atTop (nhds (⨍ y, h y ∂μ)) :=
      (continuous_snd.tendsto _).comp hplim
    have hca : ContinuousAt h (⨍ y, y ∂μ) :=
      hcont.continuousAt (isOpen_interior.mem_nhds hbar)
    have h3 := hca.tendsto.comp h1
    exact le_of_tendsto_of_tendsto' h2 h3 (fun k => (hpH k).2)
  rw [average_eq, average_eq, hmass, hint, hintE, smul_eq_mul] at hle
  have hpos : 0 < ∫ y, w y ∂ν := by
    rw [← hmass]
    exact ENNReal.toReal_pos (NeZero.ne μ ∘ Measure.measure_univ_eq_zero.1) (measure_ne_top _ _)
  rw [inv_mul_le_iff₀ hpos] at hle
  linarith [hle, mul_comm (h ((∫ y, w y ∂ν)⁻¹ • ∫ y, w y • y ∂ν)) (∫ y, w y ∂ν)]


variable {n : ℕ}

theorem restrict_eq_interior {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K) :
    (volume.restrict K) = volume.restrict (interior K) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null _ (hK.addHaar_frontier volume)
    intro y hy
    exact ⟨subset_closure hy.1, hy.2⟩
  · simp [Set.sdiff_eq_empty.2 interior_subset]

theorem aesm_of_contOn {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : ContinuousOn g (interior K)) :
    AEStronglyMeasurable g (volume.restrict K) := by
  rw [restrict_eq_interior hK]
  exact hg.aestronglyMeasurable isOpen_interior.measurableSet

theorem interior_nonempty {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hvol : 0 < volume K) : (interior K).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have : volume K ≤ volume (frontier K) := by
    apply measure_mono
    intro y hy
    refine ⟨subset_closure hy, by simp [h]⟩
  rw [hK.addHaar_frontier volume] at this
  exact (lt_irrefl _ (lt_of_lt_of_le hvol this))

theorem concave_bdd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {g : E → ℝ} (hg : ConcaveOn ℝ K g)
    (hg0 : ∀ y ∈ K, 0 ≤ g y) (hKb : Bornology.IsBounded K) {c : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ball c ρ ⊆ K) : ∃ M, ∀ y ∈ K, g y ≤ M := by
  obtain ⟨C, hC⟩ := hKb.exists_norm_le
  set D := C + ‖c‖ with hD
  have hcK : c ∈ K := hball (mem_ball_self hρ)
  have hD0 : 0 ≤ D := by have := hC c hcK; linarith [norm_nonneg c]
  set δ := ρ / (2 * (D + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨(1 + δ) / δ * g c, fun y hy => ?_⟩
  have hyc : ‖y - c‖ ≤ D := by
    calc ‖y - c‖ ≤ ‖y‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ D := by linarith [hC y hy]
  set z := c + δ • (c - y) with hz
  have hzK : z ∈ K := by
    apply hball
    rw [mem_ball, dist_eq_norm, hz, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hδ0, norm_sub_rev]
    calc δ * ‖y - c‖ ≤ δ * D := mul_le_mul_of_nonneg_left hyc hδ0.le
      _ < ρ := by
        rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  have key := hg.2 hzK hy (by positivity : (0:ℝ) ≤ 1 / (1 + δ))
    (by positivity : (0:ℝ) ≤ δ / (1 + δ)) (by field_simp)
  have hc : (1 / (1 + δ)) • z + (δ / (1 + δ)) • y = c := by
    rw [hz]
    have h1 : (1 + δ) ≠ 0 := by positivity
    rw [smul_add, smul_smul, smul_sub, ← sub_eq_zero]
    have : (1 / (1 + δ)) • c + ((1 / (1 + δ) * δ) • c - (1 / (1 + δ) * δ) • y) +
        (δ / (1 + δ)) • y - c = ((1 / (1 + δ)) + (1 / (1 + δ) * δ) - 1) • c +
        ((δ / (1 + δ)) - (1 / (1 + δ) * δ)) • y := by
      simp only [sub_smul, add_smul, one_smul]; abel
    rw [this]
    have e1 : (1 / (1 + δ)) + (1 / (1 + δ) * δ) - 1 = 0 := by field_simp; ring
    have e2 : (δ / (1 + δ)) - (1 / (1 + δ) * δ) = 0 := by field_simp; ring
    rw [e1, e2]; simp
  rw [hc, smul_eq_mul, smul_eq_mul] at key
  have := hg0 z hzK
  have h3 : δ / (1 + δ) * g y ≤ g c := by nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 1 / (1 + δ)) this]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h3
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
  linarith

noncomputable def hh {n : ℕ} (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (t : ℕ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ := Real.exp (-α * f t y)

open OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder in
theorem main (n : ℕ) (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (hKmeas : MeasurableSet K) (hKvol : 0 < volume K)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hEWOO : IsEWOO K α f x)
    (T : ℕ) (hT : 2 ≤ T) :
    RegretT K f x T ≤ (n / α) * Real.log T + 2 / α := by
  have hw_succ : ∀ t y, ewooWeight α f (t+1) y = ewooWeight α f t y * hh α f t y := by
    intro t y; simp only [ewooWeight, hh, Finset.sum_range_succ, mul_add, Real.exp_add]
  have hw0 : ∀ y, ewooWeight α f 0 y = 1 := by simp [ewooWeight]
  have hwpos : ∀ t y, 0 < ewooWeight α f t y := fun _ _ => Real.exp_pos _
  have hhpos : ∀ t y, 0 < hh α f t y := fun _ _ => Real.exp_pos _
  have hwprod : ∀ t y, ewooWeight α f t y = ∏ s ∈ Finset.range t, hh α f s y := by
    intro t y; simp only [ewooWeight, hh, Finset.mul_sum, Real.exp_sum]
  have hhconc : ∀ t, ConcaveOn ℝ K (hh α f t) := fun t => (hf t).2
  obtain ⟨c, hc⟩ := interior_nonempty hKconv hKvol
  obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 isOpen_interior c hc
  have hballK : ball c ε ⊆ K := hεb.trans interior_subset
  have hcb : closedBall c (ε/2) ⊆ interior K :=
    (closedBall_subset_ball (by linarith)).trans hεb
  have hhbdd : ∀ t, ∃ M, ∀ y ∈ K, hh α f t y ≤ M := fun t =>
    concave_bdd (hhconc t) (fun y _ => (hhpos t y).le) hKbdd hε hballK
  choose M hM using hhbdd
  have hwbdd : ∀ t, ∃ B, ∀ y ∈ K, ewooWeight α f t y ≤ B := by
    intro t; induction t with
    | zero => exact ⟨1, fun y _ => (hw0 y).le⟩
    | succ t ih =>
      obtain ⟨B, hB⟩ := ih
      exact ⟨B * M t, fun y hy => by
        rw [hw_succ]
        exact mul_le_mul (hB y hy) (hM t y hy) (hhpos t y).le ((hwpos t y).le.trans (hB y hy))⟩
  choose B hB using hwbdd
  have hfc : ∀ t, ContinuousOn (f t) (interior K) := fun t => (hf t).1.continuousOn_interior
  have hhc : ∀ t, ContinuousOn (hh α f t) (interior K) := fun t =>
    (continuousOn_const.mul (hfc t)).rexp
  have hwc : ∀ t, ContinuousOn (ewooWeight α f t) (interior K) := fun t => by
    unfold ewooWeight
    exact (continuousOn_const.mul (continuousOn_finsetSum _ fun s _ => hfc s)).rexp
  have hKfin : volume K < ⊤ := hKbdd.measure_lt_top
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKfin.ne
  obtain ⟨R, hR⟩ := hKbdd.exists_norm_le
  have hwi : ∀ t, Integrable (ewooWeight α f t) (volume.restrict K) := fun t =>
    Integrable.of_bound (aesm_of_contOn hKconv (hwc t)) (B t)
      ((ae_restrict_mem hKmeas).mono fun y hy => by
        rw [Real.norm_eq_abs, abs_of_pos (hwpos t y)]; exact hB t y hy)
  have hwyi : ∀ t, Integrable (fun y => ewooWeight α f t y • y) (volume.restrict K) := fun t =>
    Integrable.of_bound (aesm_of_contOn hKconv ((hwc t).smul continuousOn_id)) (B t * R)
      ((ae_restrict_mem hKmeas).mono fun y hy => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hwpos t y)]
        exact mul_le_mul (hB t y hy) (hR y hy) (norm_nonneg _)
          ((hwpos t y).le.trans (hB t y hy)))
  set I : ℕ → ℝ := fun t => ∫ y in K, ewooWeight α f t y with hI
  have hI0 : I 0 = volume.real K := by simp [hI, hw0]
  have hIpos : ∀ t, 0 < I t := by
    intro t
    simp only [hI]
    rw [integral_pos_iff_support_of_nonneg (fun y => (hwpos t y).le) (hwi t)]
    have : Function.support (ewooWeight α f t) = Set.univ := by
      ext y; simp [(hwpos t y).ne']
    rw [this, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hKvol
  have hν : volume.restrict K (closedBall c (ε/2)) ≠ 0 := by
    rw [Measure.restrict_apply measurableSet_closedBall,
      Set.inter_eq_left.2 (hcb.trans interior_subset)]
    exact (measure_closedBall_pos volume c (by linarith)).ne'
  have hstep : ∀ t, I (t+1) ≤ hh α f t (x t) * I t := by
    intro t
    have e : (fun y => ewooWeight α f t y * hh α f t y) = ewooWeight α f (t+1) :=
      funext fun y => (hw_succ t y).symm
    have hJ := jensen hKconv (ae_restrict_mem hKmeas) hcb hν (hwpos t) (hwi t) (hwyi t)
      (e ▸ hwi (t+1)) (hhconc t) (hhc t)
    rw [← hEWOO t, e] at hJ
    exact hJ
  have htel : ∀ k, I k ≤ (∏ t ∈ Finset.range k, hh α f t (x t)) * I 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ]
      calc I (k+1) ≤ hh α f k (x k) * I k := hstep k
        _ ≤ hh α f k (x k) * ((∏ t ∈ Finset.range k, hh α f t (x t)) * I 0) :=
          mul_le_mul_of_nonneg_left ih (hhpos _ _).le
        _ = _ := by ring
  have hP : (∏ t ∈ Finset.range T, hh α f t (x t)) =
      Real.exp (-α * ∑ t ∈ Finset.range T, f t (x t)) := by
    simp only [hh, Finset.mul_sum, Real.exp_sum]
  have hV : 0 < volume.real K := hI0 ▸ hIpos 0
  have hTr : (2:ℝ) ≤ T := by exact_mod_cast hT
  set cc : ℝ := 1 / (T:ℝ) with hcc
  have hcc0 : 0 < cc := by positivity
  have hcc1 : cc ≤ 1 / 2 := by
    rw [hcc]; exact one_div_le_one_div_of_le (by norm_num) hTr
  have hbound : ∀ ys ∈ K, (∑ t ∈ Finset.range T, f t (x t)) - ∑ t ∈ Finset.range T, f t ys ≤
      (n / α) * Real.log T + 2 / α := by
    intro ys hys
    set S := AffineMap.homothety ys cc '' K with hS
    have hhom : ∀ y, AffineMap.homothety ys cc y = (1 - cc) • ys + cc • y := by
      intro y; rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]; module
    have hSK : S ⊆ K := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hhom]
      exact hKconv hys hy (by linarith) hcc0.le (by ring)
    have hSm : MeasurableSet S := by
      refine hKmeas.image_of_continuousOn_injOn
        (AffineMap.homothety_continuous _ _).continuousOn ?_
      intro a _ b _ hab
      simp only [hhom] at hab
      have h1 := add_left_cancel hab
      exact smul_right_injective _ hcc0.ne' h1
    have hSvol : volume S = ENNReal.ofReal (cc ^ n) * volume K := by
      rw [hS, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
        abs_of_pos (by positivity)]
    have hpt : ∀ z ∈ S, (1 - cc) ^ T * ewooWeight α f T ys ≤ ewooWeight α f T z := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hwprod, hwprod, ← Finset.card_range T, ← Finset.prod_const, Finset.card_range,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod
      · intro t _; exact mul_nonneg (by linarith) (hhpos _ _).le
      · intro t _
        rw [hhom]
        have := (hhconc t).2 hys hy (by linarith : (0:ℝ) ≤ 1 - cc) hcc0.le (by ring)
        rw [smul_eq_mul, smul_eq_mul] at this
        nlinarith [hhpos t y]
    have hSfin : volume S ≠ ⊤ := ((measure_mono hSK).trans_lt hKfin).ne
    have hlow1 : ∫ y in S, ewooWeight α f T y ≤ I T :=
      setIntegral_mono_set (hwi T) (Filter.Eventually.of_forall fun y => (hwpos T y).le)
        hSK.eventuallyLE
    have hlow2 := setIntegral_ge_of_const_le hSm hSfin hpt (IntegrableOn.mono_set (hwi T) hSK)
    have hSreal : volume.real S = cc ^ n * volume.real K := by
      rw [measureReal_def, measureReal_def, hSvol, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
    rw [hSreal, smul_eq_mul] at hlow2
    have hfin := (hlow2.trans hlow1).trans (htel T)
    rw [hP, hI0] at hfin
    have hW : ewooWeight α f T ys = Real.exp (-α * ∑ t ∈ Finset.range T, f t ys) := rfl
    rw [hW] at hfin
    have hineq : cc ^ n * ((1 - cc) ^ T * Real.exp (-α * ∑ t ∈ Finset.range T, f t ys)) ≤
        Real.exp (-α * ∑ t ∈ Finset.range T, f t (x t)) := by
      have := hfin
      rw [show cc ^ n * volume.real K * ((1 - cc) ^ T *
          Real.exp (-α * ∑ t ∈ Finset.range T, f t ys)) =
          (cc ^ n * ((1 - cc) ^ T * Real.exp (-α * ∑ t ∈ Finset.range T, f t ys))) *
          volume.real K by ring] at this
      exact le_of_mul_le_mul_right this hV
    have hu : 0 < 1 - cc := by linarith
    have hlog := Real.log_le_log (by positivity) hineq
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_exp, Real.log_exp] at hlog
    have hlc : Real.log cc = - Real.log T := by rw [hcc, one_div, Real.log_inv]
    have hl1 : 1 - (1 - cc)⁻¹ ≤ Real.log (1 - cc) := Real.one_sub_inv_le_log_of_pos hu
    have hinv : (1 - cc)⁻¹ = (T:ℝ) / (T - 1) := by
      rw [hcc]; field_simp
    have hT2 : -2 ≤ (T:ℝ) * Real.log (1 - cc) := by
      have h1 : (T:ℝ) * (1 - (T:ℝ) / (T - 1)) ≤ (T:ℝ) * Real.log (1 - cc) :=
        mul_le_mul_of_nonneg_left (hinv ▸ hl1) (by linarith)
      have hT1 : (T:ℝ) - 1 ≠ 0 := by linarith
      have h2 : (T:ℝ) * (1 - (T:ℝ) / (T - 1)) = -((T:ℝ) / (T - 1)) := by
        field_simp; ring
      have h3 : (T:ℝ) / (T - 1) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    rw [hlc] at hlog
    have hmain : α * ((∑ t ∈ Finset.range T, f t (x t)) - ∑ t ∈ Finset.range T, f t ys) ≤
        n * Real.log T + 2 := by
      nlinarith
    have hre : (n:ℝ) / α * Real.log T + 2 / α = (n * Real.log T + 2) / α := by field_simp
    rw [hre, le_div_iff₀ hα]
    linarith
  unfold RegretT
  have : (∑ t ∈ Finset.range T, f t (x t)) - ((n / α) * Real.log T + 2 / α) ≤
      sInf ((fun y => ∑ t ∈ Finset.range T, f t y) '' K) := by
    apply le_csInf (hKne.image _)
    rintro _ ⟨ys, hys, rfl⟩
    linarith [hbound ys hys]
  linarith

end EW88

open MeasureTheory OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder

theorem solution (n : ℕ) (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (hKmeas : MeasurableSet K) (hKvol : 0 < volume K)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hEWOO : IsEWOO K α f x)
    (T : ℕ) (hT : 2 ≤ T) :
    RegretT K f x T ≤ (n / α) * Real.log T + 2 / α :=
  EW88.main n hn K hKconv hKne hKbdd hKmeas hKvol α hα f hf x hEWOO T hT
