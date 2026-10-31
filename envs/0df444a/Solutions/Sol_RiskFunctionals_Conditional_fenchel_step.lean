-- Prove2me | solution 1 for RiskFunctionals.Conditional.fenchel_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:58:16.196711+00:00
-- url     : https://prove2.me/submissions/5d7069e6-001b-4db2-bd1a-93e8356f5287

import Mathlib
import Definitions.Def_RiskFunctionals_Conditional_Mappings

open MeasureTheory Filter Topology ENNReal

set_option linter.unusedSectionVars false



namespace CondRepAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)]

/-- The indicator of a measurable set as an element of `Lp`. -/
noncomputable def indL (p : ℝ≥0∞) (P : Measure Ω) [IsProbabilityMeasure P] {E : Set Ω}
    (hE : MeasurableSet E) : Lp ℝ p P :=
  indicatorConstLp p hE (measure_ne_top P E) (1 : ℝ)

lemma indL_congr {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) (h : s = t) :
    indL p P hs = indL p P ht := by subst h; rfl

lemma indL_empty : indL p P (MeasurableSet.empty : MeasurableSet (∅ : Set Ω)) = 0 := by
  simp [indL]

lemma indL_union {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    indL p P (hs.union ht) = indL p P hs + indL p P ht := by
  unfold indL
  exact indicatorConstLp_disjoint_union hs ht _ _ hst 1

lemma indL_range_sum {f : ℕ → Set Ω} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Function.onFun Disjoint f)) (n : ℕ) :
    ∑ i ∈ Finset.range n, indL p P (hf i) =
      indL p P (Finset.measurableSet_biUnion (Finset.range n) (fun i _ => hf i)) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [indL_congr _ MeasurableSet.empty (by simp), indL_empty]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hdisj : Disjoint (⋃ i ∈ Finset.range n, f i) (f n) := by
      rw [Set.disjoint_iUnion_left]
      intro i
      rw [Set.disjoint_iUnion_left]
      intro hi
      exact hd (by simp at hi; omega)
    rw [← indL_union _ (hf n) hdisj]
    apply indL_congr
    ext x
    simp [Finset.range_add_one, or_comm]

lemma tendsto_indL_iUnion (hp : p ≠ ∞) {f : ℕ → Set Ω} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Function.onFun Disjoint f)) :
    Tendsto (fun n => indL p P (Finset.measurableSet_biUnion (Finset.range n) (fun i _ => hf i)))
      atTop (𝓝 (indL p P (MeasurableSet.iUnion hf))) := by
  unfold indL
  apply tendsto_indicatorConstLp_set hp
  have h0 := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint (μ := P)
    (fun i => (hf i).nullMeasurableSet) hd
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => zero_le) ?_
  intro n
  apply measure_mono
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_iUnion, Finset.mem_range] at hx
  simp only [Set.mem_iUnion]
  rcases hx with ⟨⟨i, hi, hx⟩, hn⟩ | ⟨⟨i, hx⟩, hn⟩
  · exact absurd ⟨i, hx⟩ hn
  · refine ⟨i, ?_, hx⟩
    by_contra h
    exact hn ⟨i, by omega, hx⟩


/-- Positive-on-indicators continuous functional gives a measure. -/
noncomputable def nuOf (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) : Measure Ω :=
  Measure.ofMeasurable (fun E hE => ENNReal.ofReal (φ (indL p P hE))) (by simp [indL_empty])
    (by
      intro f hf hd
      have hT := (φ.continuous.tendsto _).comp (tendsto_indL_iUnion hp hf hd)
      have hS : HasSum (fun i => φ (indL p P (hf i))) (φ (indL p P (MeasurableSet.iUnion hf))) := by
        rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => hpos (hf i))]
        refine hT.congr (fun n => ?_)
        simp only [Function.comp_apply]
        rw [← indL_range_sum hf hd n, map_sum]
      rw [hS.tsum_eq.symm, ENNReal.ofReal_tsum_of_nonneg (fun i => hpos (hf i)) hS.summable])

lemma nuOf_apply (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) {E : Set Ω}
    (hE : MeasurableSet E) : nuOf hp φ hpos E = ENNReal.ofReal (φ (indL p P hE)) := by
  unfold nuOf
  rw [Measure.ofMeasurable_apply _ hE]

lemma indL_null (hp : p ≠ ∞) {E : Set Ω} (hE : MeasurableSet E) (h0 : P E = 0) :
    indL p P hE = 0 := by
  rw [← norm_eq_zero]
  unfold indL
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1.out).ne'
  rw [norm_indicatorConstLp hp0 hp, measureReal_def, h0]
  have : 0 < p.toReal⁻¹ := by
    have : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    positivity
  simp [Real.zero_rpow this.ne']

lemma nuOf_ac (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) :
    nuOf hp φ hpos ≪ P := by
  refine Measure.AbsolutelyContinuous.mk (fun E hE h0 => ?_)
  rw [nuOf_apply hp φ hpos hE, indL_null hp hE h0, map_zero, ENNReal.ofReal_zero]

instance nuOf_finite (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) :
    IsFiniteMeasure (nuOf hp φ hpos) :=
  ⟨by rw [nuOf_apply hp φ hpos MeasurableSet.univ]; exact ENNReal.ofReal_lt_top⟩

/-- The density. -/
noncomputable def dens (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) : Ω → ℝ :=
  fun ω => ((nuOf hp φ hpos).rnDeriv P ω).toReal

lemma dens_measurable (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) :
    Measurable (dens hp φ hpos) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma dens_nonneg (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) (ω : Ω) :
    0 ≤ dens hp φ hpos ω := ENNReal.toReal_nonneg

lemma dens_integrable (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) :
    Integrable (dens hp φ hpos) P :=
  Measure.integrable_toReal_rnDeriv

lemma setIntegral_dens (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) {E : Set Ω}
    (hE : MeasurableSet E) : ∫ ω in E, dens hp φ hpos ω ∂P = φ (indL p P hE) := by
  unfold dens
  rw [Measure.setIntegral_toReal_rnDeriv (nuOf_ac hp φ hpos) E, measureReal_def,
    nuOf_apply hp φ hpos hE, ENNReal.toReal_ofReal (hpos hE)]


/-- Multiplication by the indicator of `F`, as a continuous linear operator on `Lp`. -/
noncomputable def mulInd {F : Set Ω} (hF : MeasurableSet F) : Lp ℝ p P →L[ℝ] Lp ℝ p P :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL P ⊤ p p (indL ⊤ P hF)

lemma mulInd_ae {F : Set Ω} (hF : MeasurableSet F) (Y : Lp ℝ p P) :
    (mulInd hF Y : Ω → ℝ) =ᵐ[P] F.indicator (fun x => Y x) := by
  have h1 := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := p) (indL ⊤ P hF) Y
  have h2 : (indL ⊤ P hF : Ω → ℝ) =ᵐ[P] F.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have h3 : (mulInd hF Y : Ω → ℝ) = (ContinuousLinearMap.mul ℝ ℝ).holder p (indL ⊤ P hF) Y := rfl
  rw [h3]
  filter_upwards [h1, h2] with x h1 h2
  rw [h1]
  simp only [ContinuousLinearMap.mul_apply', h2]
  by_cases hx : x ∈ F <;> simp [hx]

lemma indicatorConstLp_eq_smul {s : Set Ω} (hs : MeasurableSet s) (hμs : P s ≠ ∞) (c : ℝ) :
    indicatorConstLp p hs hμs c = c • indL p P hs := by
  apply Lp.ext
  have h1 : (indicatorConstLp p hs hμs c : Ω → ℝ) =ᵐ[P] s.indicator (fun _ => c) :=
    indicatorConstLp_coeFn
  have h2 : (indL p P hs : Ω → ℝ) =ᵐ[P] s.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  filter_upwards [h1, h2, Lp.coeFn_smul c (indL p P hs)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2]
  by_cases hx : x ∈ s <;> simp [hx]

lemma integral_indicatorConstLp_mul {s : Set Ω} (hs : MeasurableSet s) (hμs : P s ≠ ∞) (c : ℝ)
    (g : Ω → ℝ) :
    ∫ x, (indicatorConstLp p hs hμs c : Ω → ℝ) x * g x ∂P = c * ∫ x in s, g x ∂P := by
  have h1 : (indicatorConstLp p hs hμs c : Ω → ℝ) =ᵐ[P] s.indicator (fun _ => c) :=
    indicatorConstLp_coeFn
  rw [← integral_const_mul, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [h1] with x h1
  rw [h1]
  by_cases hx : x ∈ s <;> simp [hx]

lemma rep_trunc (q : ℝ≥0∞) [p.HolderConjugate q] (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) {F : Set Ω}
    (hF : MeasurableSet F) (n : ℝ) (hn0 : 0 ≤ n) (hn : ∀ x ∈ F, dens hp φ hpos x ≤ n) (Y : Lp ℝ p P) :
    φ (mulInd hF Y) = ∫ x, Y x * F.indicator (dens hp φ hpos) x ∂P := by
  set Z := dens hp φ hpos with hZdef
  have hZm : MemLp (F.indicator Z) q P := by
    refine MemLp.of_bound ((dens_measurable hp φ hpos).indicator hF).aestronglyMeasurable n
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ F
    · simp only [Set.indicator_of_mem hx]
      rw [Real.norm_of_nonneg (dens_nonneg hp φ hpos x)]
      exact hn x hx
    · simp only [Set.indicator_of_notMem hx, norm_zero]
      exact hn0
  haveI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let ψ : Lp ℝ p P →L[ℝ] ℝ := ((ContinuousLinearMap.mul ℝ ℝ).lpPairing P p q).flip (hZm.toLp _)
  have hψ : ∀ Y : Lp ℝ p P, ψ Y = ∫ x, Y x * F.indicator Z x ∂P := by
    intro Y
    simp only [ψ, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral,
      ContinuousLinearMap.mul_apply']
    apply integral_congr_ae
    filter_upwards [hZm.coeFn_toLp] with x hx
    simp only [hx]
  rw [← hψ]
  induction Y using Lp.induction hp with
  | @indicatorConst c s hs hμs =>
    rw [Lp.simpleFunc.coe_indicatorConst, hψ, integral_indicatorConstLp_mul,
      indicatorConstLp_eq_smul, map_smul, map_smul, smul_eq_mul]
    congr 1
    have hmi : mulInd hF (indL p P hs) = indL p P (hs.inter hF) := by
      apply Lp.ext
      have h2 : (indL p P (hs.inter hF) : Ω → ℝ) =ᵐ[P] (s ∩ F).indicator (fun _ => (1:ℝ)) :=
        indicatorConstLp_coeFn
      have h3 : (indL p P hs : Ω → ℝ) =ᵐ[P] s.indicator (fun _ => (1:ℝ)) :=
        indicatorConstLp_coeFn
      filter_upwards [mulInd_ae hF (indL p P hs), h2, h3] with x h1 h2 h3
      rw [h1, h2]
      by_cases hxF : x ∈ F <;> by_cases hxs : x ∈ s <;> simp [hxF, hxs, h3]
    rw [hmi, ← setIntegral_dens hp φ hpos (hs.inter hF), setIntegral_indicator hF]
  | add hf hg _ h1 h2 => rw [map_add, map_add, map_add, h1, h2]
  | isClosed => exact isClosed_eq (φ.continuous.comp (mulInd hF).continuous) ψ.continuous


lemma functional_le (φ : Lp ℝ p P →L[ℝ] ℝ) (Y : Lp ℝ p P) : φ Y ≤ ‖φ‖ * ‖Y‖ :=
  (Real.le_norm_self _).trans (φ.le_opNorm Y)

lemma dens_memLp (q : ℝ≥0∞) [hpq : p.HolderConjugate q] (hp : p ≠ ∞) (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) :
    MemLp (dens hp φ hpos) q P := by
  set Z := dens hp φ hpos with hZdef
  have hZmeas : Measurable Z := dens_measurable hp φ hpos
  have hZnn : ∀ x, 0 ≤ Z x := dens_nonneg hp φ hpos
  by_cases hq : q = ∞
  · subst hq
    have hp1' : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).mp rfl
    subst hp1'
    have hle : Z ≤ᵐ[P] fun _ => ‖φ‖ := by
      refine ae_le_of_forall_setIntegral_le (dens_integrable hp φ hpos) (integrable_const _)
        (fun s hs _ => ?_)
      rw [setIntegral_dens hp φ hpos hs, setIntegral_const, smul_eq_mul, mul_comm]
      refine (functional_le φ _).trans (le_of_eq ?_)
      congr 1
      unfold indL
      rw [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
      simp
    refine memLp_top_of_bound hZmeas.aestronglyMeasurable ‖φ‖ ?_
    filter_upwards [hle] with x hx
    rw [Real.norm_of_nonneg (hZnn x)]
    exact hx
  · have hR : p.toReal.HolderConjugate q.toReal :=
      ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    set r := q.toReal with hr
    set pr := p.toReal with hpr
    have hr1 : 1 < r := hR.symm.lt
    have hrpos : 0 < r := by linarith
    have hprpos : 0 < pr := hR.pos
    have hmul : (r - 1) * pr = r := hR.symm.sub_one_mul_conj
    have hinv : pr⁻¹ + r⁻¹ = 1 := hR.inv_add_inv_eq_one
    have key : ∀ n : ℕ, ∫ x, ({x | Z x ≤ n}).indicator (fun x => Z x ^ r) x ∂P ≤ ‖φ‖ ^ r := by
      intro n
      set F := {x | Z x ≤ (n:ℝ)} with hFdef
      have hF : MeasurableSet F := measurableSet_le hZmeas measurable_const
      set f := F.indicator (fun x => Z x ^ (r - 1)) with hfdef
      have hfm : MemLp f p P := by
        refine MemLp.of_bound ((hZmeas.pow_const _).indicator hF).aestronglyMeasurable
          ((n:ℝ) ^ (r-1)) (ae_of_all _ fun x => ?_)
        by_cases hx : x ∈ F
        · simp only [f, Set.indicator_of_mem hx]
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (hZnn x) _)]
          exact Real.rpow_le_rpow (hZnn x) hx (by linarith)
        · simp only [f, Set.indicator_of_notMem hx, norm_zero]
          positivity
      set Y := hfm.toLp f
      have hTY : mulInd hF Y = Y := by
        apply Lp.ext
        filter_upwards [mulInd_ae hF Y, (hfm.coeFn_toLp : (Y : Ω → ℝ) =ᵐ[P] f)] with x h1 h2
        rw [h1]
        by_cases hx : x ∈ F
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx]
          refine (Eq.trans ?_ h2.symm)
          simp [f, Set.indicator_of_notMem hx]
      set I := ∫ x, F.indicator (fun x => Z x ^ r) x ∂P with hIdef
      have hI0 : 0 ≤ I := by
        apply integral_nonneg
        intro x
        by_cases hx : x ∈ F
        · simp only [Set.indicator_of_mem hx]; exact Real.rpow_nonneg (hZnn x) _
        · simp [Set.indicator_of_notMem hx]
      have hφY : φ Y = I := by
        have := rep_trunc q hp φ hpos hF n (Nat.cast_nonneg n) (fun x hx => hx) Y
        rw [hTY] at this
        rw [this]
        apply integral_congr_ae
        filter_upwards [(hfm.coeFn_toLp : (Y : Ω → ℝ) =ᵐ[P] f)] with x hx
        rw [hx]
        by_cases hxF : x ∈ F
        · simp only [f, Set.indicator_of_mem hxF]
          conv_rhs => rw [show r = (r - 1) + 1 by ring]
          rw [Real.rpow_add' (hZnn x) (by linarith), Real.rpow_one]
        · simp [f, hxF]
      have hYnorm : ‖Y‖ = I ^ pr⁻¹ := by
        rw [Lp.norm_toLp, hfm.eLpNorm_eq_integral_rpow_norm
          (ENNReal.HolderConjugate.ne_zero p q) hp, ENNReal.toReal_ofReal (by positivity)]
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        by_cases hxF : x ∈ F
        · simp only [f, Set.indicator_of_mem hxF]
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (hZnn x) _), ← Real.rpow_mul (hZnn x), hmul]
        · simp only [f, Set.indicator_of_notMem hxF, norm_zero]
          exact Real.zero_rpow hprpos.ne'
      have hineq : I ≤ ‖φ‖ * I ^ pr⁻¹ := by
        calc I = φ Y := hφY.symm
          _ ≤ ‖φ‖ * ‖Y‖ := functional_le φ Y
          _ = _ := by rw [hYnorm]
      rcases hI0.eq_or_lt with h | h
      · rw [← h]; positivity
      · have hsplit : I = I ^ pr⁻¹ * I ^ r⁻¹ := by
          rw [← Real.rpow_add h, hinv, Real.rpow_one]
        have hpos' : 0 < I ^ pr⁻¹ := Real.rpow_pos_of_pos h _
        have h2 : I ^ r⁻¹ ≤ ‖φ‖ := by
          have : I ^ pr⁻¹ * I ^ r⁻¹ ≤ I ^ pr⁻¹ * ‖φ‖ := by
            rw [← hsplit, mul_comm]; exact hineq
          exact le_of_mul_le_mul_left this hpos'
        calc I = (I ^ r⁻¹) ^ r := by
              rw [← Real.rpow_mul h.le, inv_mul_cancel₀ hrpos.ne', Real.rpow_one]
          _ ≤ ‖φ‖ ^ r := Real.rpow_le_rpow (by positivity) h2 hrpos.le
    set g : ℕ → Ω → ℝ := fun n => {x | Z x ≤ (n:ℝ)}.indicator Z with hgdef
    have hgm : ∀ n : ℕ, MemLp (g n) q P := by
      intro n
      refine MemLp.of_bound
        (hZmeas.indicator (measurableSet_le hZmeas measurable_const)).aestronglyMeasurable
        (n:ℝ) (ae_of_all _ fun x => ?_)
      by_cases hx : x ∈ {x | Z x ≤ (n:ℝ)}
      · simp only [g, Set.indicator_of_mem hx]
        rw [Real.norm_of_nonneg (hZnn x)]; exact hx
      · simp only [g, Set.indicator_of_notMem hx, norm_zero]; positivity
    have hgnorm : ∀ n : ℕ, eLpNorm (g n) q P ≤ ENNReal.ofReal ‖φ‖ := by
      intro n
      rw [(hgm n).eLpNorm_eq_integral_rpow_norm (ENNReal.HolderConjugate.ne_zero q p) hq]
      apply ENNReal.ofReal_le_ofReal
      have heq : ∫ x, ‖g n x‖ ^ r ∂P = ∫ x, ({x | Z x ≤ n}).indicator (fun x => Z x ^ r) x ∂P := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ {x | Z x ≤ (n:ℝ)}
        · simp only [g, Set.indicator_of_mem hx]
          rw [Real.norm_of_nonneg (hZnn x)]
        · simp only [g, Set.indicator_of_notMem hx, norm_zero]
          exact Real.zero_rpow hrpos.ne'
      rw [heq]
      calc _ ≤ (‖φ‖ ^ r) ^ r⁻¹ :=
            Real.rpow_le_rpow (integral_nonneg fun x => by
              by_cases hx : x ∈ {x | Z x ≤ (n:ℝ)}
              · simp only [Set.indicator_of_mem hx]; exact Real.rpow_nonneg (hZnn x) _
              · simp [Set.indicator_of_notMem hx]) (key n) (inv_nonneg.2 hrpos.le)
        _ = ‖φ‖ := by
            rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hrpos.ne', Real.rpow_one]
    have hlim : ∀ᵐ x ∂P, Tendsto (fun n => g n x) atTop (𝓝 (Z x)) := ae_of_all _ fun x => by
      obtain ⟨N, hN⟩ := exists_nat_ge (Z x)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : x ∈ {x | Z x ≤ (n:ℝ)} := hN.trans (Nat.cast_le.2 hn)
      simp only [g, Set.indicator_of_mem hx]
    have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := q) (fun n => (hgm n).1) Z hlim
    have hlimf : atTop.liminf (fun n => eLpNorm (g n) q P) ≤ ENNReal.ofReal ‖φ‖ :=
      liminf_le_of_frequently_le' (Frequently.of_forall hgnorm)
    exact ⟨hZmeas.aestronglyMeasurable, lt_of_le_of_lt (hfat.trans hlimf) ENNReal.ofReal_lt_top⟩


/-- Riesz representation of a continuous linear functional on `L_p(P)`, `1 ≤ p < ∞`, which is
nonnegative on indicators, by an element of `L_q(P)`. -/
theorem exists_rep (q : ℝ≥0∞) [hpq : p.HolderConjugate q] (hp : p ≠ ∞)
    (φ : Lp ℝ p P →L[ℝ] ℝ)
    (hpos : ∀ {E : Set Ω} (hE : MeasurableSet E), 0 ≤ φ (indL p P hE)) :
    ∃ Z : Lp ℝ q P, ∀ Y : Lp ℝ p P, φ Y = ∫ x, Y x * Z x ∂P := by
  have hZ := dens_memLp q hp φ hpos
  haveI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  refine ⟨hZ.toLp _, ?_⟩
  let ψ : Lp ℝ p P →L[ℝ] ℝ := ((ContinuousLinearMap.mul ℝ ℝ).lpPairing P p q).flip (hZ.toLp _)
  have hψ : ∀ Y : Lp ℝ p P, ψ Y = ∫ x, Y x * (hZ.toLp _ : Ω → ℝ) x ∂P := by
    intro Y
    simp only [ψ, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral,
      ContinuousLinearMap.mul_apply']
  intro Y
  rw [← hψ]
  induction Y using Lp.induction hp with
  | @indicatorConst c s hs hμs =>
    rw [Lp.simpleFunc.coe_indicatorConst, hψ, integral_indicatorConstLp_mul,
      indicatorConstLp_eq_smul, map_smul, smul_eq_mul, ← setIntegral_dens hp φ hpos hs]
    congr 1
    apply setIntegral_congr_ae hs
    filter_upwards [hZ.coeFn_toLp] with x hx _
    rw [hx]
  | add hf hg _ h1 h2 => rw [map_add, map_add, h1, h2]
  | isClosed => exact isClosed_eq φ.continuous ψ.continuous

end CondRepAux




namespace CondRepAux

/-- Hahn–Banach: a concave upper semicontinuous real function on a normed space is majorized by
a continuous affine function which is `ε`-close at a given point. -/
theorem exists_affine_majorant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → ℝ)
    (hc : ConcaveOn ℝ Set.univ h) (hu : UpperSemicontinuous h) (y : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : E →L[ℝ] ℝ) (c : ℝ), (∀ x, h x ≤ φ x + c) ∧ φ y + c < h y + ε := by
  set S : Set (E × ℝ) := {z | z.2 ≤ h z.1} with hSdef
  have hSc : Convex ℝ S := by
    have := hc.convex_hypograph
    convert this using 1
    ext z
    simp [S]
  have hScl : IsClosed S := hu.IsClosed_hypograph
  have hnot : (y, h y + ε) ∉ S := by simp [S]; linarith
  obtain ⟨f, u, hfS, hfu⟩ := geometric_hahn_banach_closed_point hSc hScl hnot
  set a := f ((0 : E), (1 : ℝ)) with hadef
  set φ0 : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ0
  have hf : ∀ x t, f (x, t) = φ0 x + t * a := by
    intro x t
    have : ((x, t) : E × ℝ) = (x, (0:ℝ)) + t • ((0:E), (1:ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have h1 := hfS (y, h y) (by simp [S])
  rw [hf] at h1 hfu
  have ha : 0 < a := by nlinarith
  refine ⟨-(1 / a) • φ0, u / a, fun x => ?_, ?_⟩
  · have h2 := hfS (x, h x) (by simp [S])
    rw [hf] at h2
    have key : (-(1 / a) • φ0) x + u / a = (u - φ0 x) / a := by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [key, le_div_iff₀ ha]
    linarith
  · have key : (-(1 / a) • φ0) y + u / a = (u - φ0 y) / a := by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [key, div_lt_iff₀ ha]
    linarith

lemma ereal_aux {a y : ℝ} {d : EReal} (hd : d ≤ ((a - y : ℝ) : EReal)) :
    ((y : ℝ) : EReal) ≤ ((a : ℝ) : EReal) - d := by
  induction d using EReal.rec with
  | bot => rw [EReal.coe_sub_bot]; exact le_top
  | coe d =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [EReal.coe_le_coe_iff] at hd
    linarith
  | top => exact absurd (top_le_iff.mp hd) (EReal.coe_ne_top _)

end CondRepAux

namespace RiskFunctionals.Conditional

open CondRepAux

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]
  {p : ENNReal} [hp1 : Fact (1 ≤ p)]

lemma integrable_Lp (Y : Lp ℝ p P) : Integrable (Y : Ω → ℝ) P :=
  (Lp.memLp Y).integrable hp1.out

lemma hB_concave (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (B : Set Ω) :
    ConcaveOn ℝ Set.univ (fun Y : Lp ℝ p P => ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P) := by
  refine ⟨convex_univ, fun Y _ Y' _ a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hc := hA.concave Y Y' a ha (by linarith)
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · exact setIntegral_mono_ae (((integrable_Lp _).const_mul _).add
      ((integrable_Lp _).const_mul _)).integrableOn (integrable_Lp _).integrableOn hc
  · exact ((integrable_Lp _).const_mul _).integrableOn
  · exact ((integrable_Lp _).const_mul _).integrableOn

lemma hB_mono (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (B : Set Ω) (Y Y' : Lp ℝ p P) (hle : ∀ᵐ ω ∂P, Y ω ≤ Y' ω) :
    ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P ≤ ∫ ω in B, (A Y' : Lp ℝ p P) ω ∂P :=
  setIntegral_mono_ae (integrable_Lp _).integrableOn (integrable_Lp _).integrableOn
    (hA.monotone Y Y' hle)

lemma hB_translation (A : Lp ℝ p P → lpMeas ℝ ℝ m p P)
    (hA : IsConditionalAcceptabilityMapping A) (B : Set Ω) (Y : Lp ℝ p P)
    (Y₁ : lpMeas ℝ ℝ m p P) :
    ∫ ω in B, (A (Y + (Y₁ : Lp ℝ p P)) : Lp ℝ p P) ω ∂P
      = ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P + ∫ ω in B, (Y₁ : Lp ℝ p P) ω ∂P := by
  rw [← integral_add (integrable_Lp _).integrableOn (integrable_Lp _).integrableOn]
  exact integral_congr_ae (ae_restrict_of_ae (hA.translation Y Y₁))


theorem fenchel_step_pf (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤) [p.HolderConjugate q]
    (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (husc : IsUpperSemicontinuousMapping A)
    (B : Set Ω) (hB : MeasurableSet[m] B) (Y : Lp ℝ p P) :
    ((∫ ω in B, (A Y : Lp ℝ p P) ω ∂P : ℝ) : EReal)
      = ⨅ Z : Lp ℝ q P, ((pairing Y Z : ℝ) : EReal) - dualFunction A B Z := by
  set h : Lp ℝ p P → ℝ := fun Y => ∫ ω in B, (A Y : Lp ℝ p P) ω ∂P with hh
  apply le_antisymm
  · refine le_iInf fun Z => ?_
    exact ereal_aux (iInf_le (fun X => ((pairing X Z - h X : ℝ) : EReal)) Y)
  · rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    rw [EReal.coe_lt_coe_iff] at hz
    obtain ⟨φ, c, hmaj, hclose⟩ :=
      exists_affine_majorant h (hB_concave A hA B) (husc B hB) Y (sub_pos.2 hz)
    have hpos : ∀ {E : Set Ω} (hE : MeasurableSet[mΩ] E), 0 ≤ φ (indL p P hE) := by
      intro E hE
      by_contra hneg
      push_neg at hneg
      set t := (φ Y + c - h Y + 1) / (-φ (indL p P hE)) with htdef
      have hYm := hmaj Y
      have ht : 0 < t := div_pos (by linarith) (by linarith)
      have hmono : h Y ≤ h (Y + t • indL p P hE) := by
        apply hB_mono A hA B
        have h3 : (indL p P hE : Ω → ℝ) =ᵐ[P] E.indicator fun _ => (1:ℝ) :=
          indicatorConstLp_coeFn
        filter_upwards [Lp.coeFn_add Y (t • indL p P hE), Lp.coeFn_smul t (indL p P hE), h3]
          with ω h1 h2 h3
        rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul]
        have : 0 ≤ E.indicator (fun _ => (1:ℝ)) ω :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) ω
        nlinarith
      have hmaj' := hmaj (Y + t • indL p P hE)
      rw [map_add, map_smul, smul_eq_mul] at hmaj'
      have htφ : t * φ (indL p P hE) = -(φ Y + c - h Y + 1) := by
        rw [htdef, div_mul_eq_mul_div, div_neg, mul_div_assoc,
          div_self (ne_of_lt hneg), mul_one]
      linarith
    obtain ⟨Z, hZ⟩ := exists_rep q hp φ hpos
    have hd : ((-c : ℝ) : EReal) ≤ dualFunction A B Z := by
      refine le_iInf fun X => ?_
      rw [EReal.coe_le_coe_iff]
      have := hmaj X
      have hpX : pairing X Z = φ X := (hZ X).symm
      rw [hpX]
      linarith
    have hpY : pairing Y Z = φ Y := (hZ Y).symm
    calc ⨅ Z' : Lp ℝ q P, ((pairing Y Z' : ℝ) : EReal) - dualFunction A B Z'
        ≤ ((pairing Y Z : ℝ) : EReal) - dualFunction A B Z := iInf_le _ Z
      _ ≤ ((pairing Y Z : ℝ) : EReal) - ((-c : ℝ) : EReal) := EReal.sub_le_sub le_rfl hd
      _ = ((φ Y + c : ℝ) : EReal) := by
          rw [← EReal.coe_sub, hpY]
          congr 1
          ring
      _ ≤ z := by
          rw [EReal.coe_le_coe_iff]
          linarith

end RiskFunctionals.Conditional

open RiskFunctionals.Conditional

theorem solution {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤) [p.HolderConjugate q]
    (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (husc : IsUpperSemicontinuousMapping A)
    (B : Set Ω) (hB : MeasurableSet[m] B) (Y : Lp ℝ p P) :
    ((∫ ω in B, (A Y : Lp ℝ p P) ω ∂P : ℝ) : EReal)
      = ⨅ Z : Lp ℝ q P, ((pairing Y Z : ℝ) : EReal) - dualFunction A B Z :=
  fenchel_step_pf hm P p q hp A hA husc B hB Y
