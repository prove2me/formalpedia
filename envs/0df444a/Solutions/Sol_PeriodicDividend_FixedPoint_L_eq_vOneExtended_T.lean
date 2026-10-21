-- Prove2me | solution 1 for PeriodicDividend.FixedPoint.L_eq_vOneExtended_T
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:09:05.668546+00:00
-- url     : https://prove2.me/submissions/0236bddd-c9b6-449e-8d9e-3d1b5544f8f6

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace PDSolLink
open PeriodicDividend.FixedPoint

variable {Ω : Type*}

lemma paidThrough_zero (p : Params) (t : ℝ) (ω : Ω) :
    paidThrough p (noDividends Ω) t ω = 0 := by
  simp [paidThrough, noDividends]

/-- Cumulative issues do not change across a window containing no issue time. -/
lemma iss_eq (I : Issuance Ω) (ω : Ω) (s t : ℝ) (hst : s ≤ t)
    (hno : ∀ k, ¬ (ENNReal.ofReal s < I.τ k ω ∧ I.τ k ω ≤ ENNReal.ofReal t)) :
    issuedThrough I s ω = issuedThrough I t ω := by
  unfold issuedThrough
  congr 1
  funext k
  by_cases h1 : I.τ k ω ≤ ENNReal.ofReal s
  · have h2 : I.τ k ω ≤ ENNReal.ofReal t := h1.trans (ENNReal.ofReal_le_ofReal hst)
    rw [if_pos h1, if_pos h2]
  · have h2 : ¬ I.τ k ω ≤ ENNReal.ofReal t := fun h2 => hno k ⟨lt_of_not_ge h1, h2⟩
    rw [if_neg h1, if_neg h2]

lemma iss_summable (I : Issuance Ω) (ω : Ω) (t : ℝ)
    (hfin : {k | I.τ k ω ≤ ENNReal.ofReal t}.Finite) :
    Summable (fun k => if I.τ k ω ≤ ENNReal.ofReal t then I.ζ k ω else 0) := by
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro k hk
  by_contra hc
  exact hk (if_neg hc)

lemma iss_mono (I : Issuance Ω) (ω : Ω) (s t : ℝ) (hst : s ≤ t)
    (hfin : {k | I.τ k ω ≤ ENNReal.ofReal t}.Finite) (hζ : ∀ k, 0 ≤ I.ζ k ω) :
    issuedThrough I s ω ≤ issuedThrough I t ω := by
  have hfin' : {k | I.τ k ω ≤ ENNReal.ofReal s}.Finite :=
    hfin.subset (fun k hk => le_trans hk (ENNReal.ofReal_le_ofReal hst))
  unfold issuedThrough
  apply Summable.tsum_le_tsum _ (iss_summable I ω s hfin') (iss_summable I ω t hfin)
  intro k
  by_cases h1 : I.τ k ω ≤ ENNReal.ofReal s
  · have h2 : I.τ k ω ≤ ENNReal.ofReal t := h1.trans (ENNReal.ofReal_le_ofReal hst)
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h1]
    split_ifs
    · exact hζ k
    · exact le_rfl

/-- The grid of times `s_m = T - T/(m+2)` approaching `T` from below. -/
noncomputable def sgrid (T : ℝ) (m : ℕ) : ℝ := T - T / ((m : ℝ) + 2)

/-- Pathwise: if ruin happens exactly at the deterministic time `T`, the reserve just before
`T` vanishes, in the form `x + C_T + (issues up to s_m) = 0` for some grid time `s_m`. -/
lemma ruin_eq_T_imp (C : ℝ → Ω → ℝ) (p : Params) (hT : 0 < p.T) (x : ℝ≥0) (I : Issuance Ω)
    (ω : Ω) (hcont : ContinuousOn (fun t => C t ω) (Ici 0))
    (hfin : ∀ t, 0 ≤ t → {k | I.τ k ω ≤ ENNReal.ofReal t}.Finite)
    (hζ : ∀ k, 0 ≤ I.ζ k ω)
    (hθ : ruin C p x (noDividends Ω) I ω = ENNReal.ofReal p.T) :
    ∃ m : ℕ, (x : ℝ) + C p.T ω + issuedThrough I (sgrid p.T m) ω = 0 := by
  set T := p.T with hTdef
  set R : ℝ → ℝ := fun t => reserve C p x (noDividends Ω) I t ω with hR
  have hRe : ∀ t, R t = (x : ℝ) + C t ω + issuedThrough I t ω := by
    intro t; simp only [hR, reserve, paidThrough_zero]; ring
  set Iss : ℝ → ℝ := fun t => issuedThrough I t ω with hIss
  -- (a) nonnegative reserve before T
  have ha : ∀ t, 0 < t → t < T → 0 ≤ R t := by
    intro t ht htT
    by_contra hneg
    push_neg at hneg
    have : ruin C p x (noDividends Ω) I ω ≤ ENNReal.ofReal t := by
      unfold ruin
      exact sInf_le ⟨t, ⟨ht, hneg⟩, rfl⟩
    rw [hθ] at this
    have := (ENNReal.ofReal_le_ofReal_iff ht.le).mp this
    linarith
  -- (b) negative reserve just after T
  have hb : ∀ ε, 0 < ε → ∃ t, T ≤ t ∧ t < T + ε ∧ R t < 0 := by
    intro ε hε
    have hlt : ruin C p x (noDividends Ω) I ω < ENNReal.ofReal (T + ε) := by
      rw [hθ]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    unfold ruin at hlt
    obtain ⟨b, ⟨t, ⟨ht, hRt⟩, rfl⟩, hbt⟩ := sInf_lt_iff.mp hlt
    have hle : ruin C p x (noDividends Ω) I ω ≤ ENNReal.ofReal t := by
      unfold ruin; exact sInf_le ⟨t, ⟨ht, hRt⟩, rfl⟩
    rw [hθ] at hle
    refine ⟨t, (ENNReal.ofReal_le_ofReal_iff ht.le).mp hle, ?_, hRt⟩
    exact ((ENNReal.ofReal_lt_ofReal_iff' ).mp hbt).1
  -- (c) a window around T free of issue times (except possibly at T)
  set F := {k | I.τ k ω ≤ ENNReal.ofReal (T + 1)} with hF
  have hFfin : F.Finite := hfin _ (by linarith)
  let Pk : ℕ → ℝ → Prop := fun k δ =>
    ¬ (ENNReal.ofReal (T - δ) < I.τ k ω ∧ I.τ k ω < ENNReal.ofReal T) ∧
    ¬ (ENNReal.ofReal T < I.τ k ω ∧ I.τ k ω < ENNReal.ofReal (T + δ))
  have hPk : ∀ k ∈ F, ∀ᶠ δ in 𝓝[>] (0 : ℝ), Pk k δ := by
    intro k hk
    have hne : I.τ k ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hk
    set r := (I.τ k ω).toReal with hr
    have hτ : I.τ k ω = ENNReal.ofReal r := (ENNReal.ofReal_toReal hne).symm
    have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
    by_cases hrT : r = T
    · refine Eventually.of_forall fun δ => ⟨fun h => ?_, fun h => ?_⟩
      · rw [hτ, hrT] at h; exact lt_irrefl _ h.2
      · rw [hτ, hrT] at h; exact lt_irrefl _ h.1
    · have hpos : 0 < |r - T| := abs_pos.mpr (sub_ne_zero.mpr hrT)
      filter_upwards [(eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds] with δ hδ
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [hτ] at h
        have h1 := ((ENNReal.ofReal_lt_ofReal_iff').mp h.1).1
        have h2 := (ENNReal.ofReal_lt_ofReal_iff hT).mp h.2
        rw [abs_sub_comm, abs_of_pos (show 0 < T - r by linarith)] at hδ
        linarith
      · rw [hτ] at h
        have h1 := ((ENNReal.ofReal_lt_ofReal_iff').mp h.1).1
        have h2 := ((ENNReal.ofReal_lt_ofReal_iff').mp h.2).1
        rw [abs_of_pos (show 0 < r - T by linarith)] at hδ
        linarith
  have hall := (Filter.eventually_all_finite hFfin).mpr hPk
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 ∧ δ < T := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with δ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨δ, hδF, hδ0, hδ1, hδT⟩ := (hall.and hsmall).exists
  have hP : ∀ k, Pk k δ := by
    intro k
    by_cases hk : k ∈ F
    · exact hδF k hk
    · have hgt : ENNReal.ofReal (T + 1) < I.τ k ω := lt_of_not_ge hk
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have : ENNReal.ofReal T ≤ ENNReal.ofReal (T + 1) := ENNReal.ofReal_le_ofReal (by linarith)
        exact absurd (lt_trans hgt h.2) (not_lt.mpr this)
      · have : ENNReal.ofReal (T + δ) ≤ ENNReal.ofReal (T + 1) :=
          ENNReal.ofReal_le_ofReal (by linarith)
        exact absurd (lt_trans hgt h.2) (not_lt.mpr this)
  -- continuity of C at T
  have hcT : ContinuousAt (fun t => C t ω) T :=
    hcont.continuousAt (Ici_mem_nhds hT)
  -- (d) right side: R T ≤ 0
  have hright : ∀ t, T ≤ t → t < T + δ → Iss t = Iss T := by
    intro t h1 h2
    symm
    apply iss_eq I ω T t h1
    intro k hk
    exact (hP k).2 ⟨hk.1, lt_of_le_of_lt hk.2 ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr h2)⟩
  have hRT : (x : ℝ) + C T ω + Iss T ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have hca : ContinuousAt (fun t => (x : ℝ) + C t ω + Iss T) T :=
      (continuousAt_const.add hcT).add continuousAt_const
    have hev : ∀ᶠ t in 𝓝 T, 0 < (x : ℝ) + C t ω + Iss T := hca.eventually (eventually_gt_nhds hpos)
    obtain ⟨η, hη, hηt⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨t, h1, h2, h3⟩ := hb (min δ η) (lt_min hδ0 hη)
    have := hηt (show dist t T < η by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith [min_le_right δ η])
    rw [hRe, show issuedThrough I t ω = Iss t from rfl,
      hright t h1 (by linarith [min_le_left δ η])] at h3
    linarith
  -- (e) left side: x + C T + Iss (T - δ) ≥ 0
  have hleft : ∀ t, T - δ ≤ t → t < T → Iss t = Iss (T - δ) := by
    intro t h1 h2
    apply (iss_eq I ω (T - δ) t h1 _).symm
    intro k hk
    exact (hP k).1 ⟨hk.1, lt_of_le_of_lt hk.2 ((ENNReal.ofReal_lt_ofReal_iff hT).mpr h2)⟩
  have hLT : 0 ≤ (x : ℝ) + C T ω + Iss (T - δ) := by
    by_contra hneg
    push_neg at hneg
    have hca : ContinuousAt (fun t => (x : ℝ) + C t ω + Iss (T - δ)) T :=
      (continuousAt_const.add hcT).add continuousAt_const
    have hev : ∀ᶠ t in 𝓝 T, (x : ℝ) + C t ω + Iss (T - δ) < 0 :=
      hca.eventually (eventually_lt_nhds hneg)
    obtain ⟨η, hη, hηt⟩ := Metric.eventually_nhds_iff.mp hev
    set t := T - min δ η / 2 with ht
    have hm := lt_min hδ0 hη
    have h1 := hηt (show dist t T < η by
      rw [Real.dist_eq, ht, abs_of_neg (by linarith)]
      linarith [min_le_right δ η])
    have h2 := ha t (by linarith [min_le_left δ η]) (by linarith)
    rw [hRe, show issuedThrough I t ω = Iss t from rfl,
      hleft t (by linarith [min_le_left δ η]) (by linarith)] at h2
    linarith
  -- (f) monotonicity of issues
  have hmono : Iss (T - δ) ≤ Iss T := iss_mono I ω _ _ (by linarith) (hfin T hT.le) hζ
  -- (g) pick a grid point in (T - δ, T)
  obtain ⟨m, hm⟩ := exists_nat_gt (T / δ)
  refine ⟨m, ?_⟩
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hgrid1 : T - δ ≤ sgrid T m := by
    unfold sgrid
    have : T / ((m : ℝ) + 2) ≤ δ := by
      rw [div_le_iff₀ hm2]
      rw [div_lt_iff₀ hδ0] at hm
      nlinarith
    linarith
  have hgrid2 : sgrid T m < T := by
    unfold sgrid
    have : 0 < T / ((m : ℝ) + 2) := div_pos hT hm2
    linarith
  have := hleft (sgrid T m) hgrid1 hgrid2
  show (x : ℝ) + C T ω + Iss (sgrid T m) = 0
  rw [this]
  linarith

lemma iss_sm {mΩ : MeasurableSpace Ω} (𝔽 : Filtration ℝ mΩ) (I : Issuance Ω) (s : ℝ)
    (h2 : ∀ k, StronglyMeasurable[𝔽 s]
      (fun ω => if I.τ k ω ≤ ENNReal.ofReal s then I.ζ k ω else 0))
    (hfin : ∀ ω, {k | I.τ k ω ≤ ENNReal.ofReal s}.Finite) :
    StronglyMeasurable[𝔽 s] (fun ω => issuedThrough I s ω) := by
  refine @stronglyMeasurable_of_tendsto _ _ _ (𝔽 s) _ _ atTop _ _
    (fun N ω => ∑ k ∈ Finset.range N,
      (if I.τ k ω ≤ ENNReal.ofReal s then I.ζ k ω else 0)) _
    (fun N => Finset.stronglyMeasurable_fun_sum _ (fun k _ => h2 k)) ?_
  rw [tendsto_pi_nhds]
  intro ω
  exact (iss_summable I ω s (hfin ω)).hasSum.tendsto_sum_nat

lemma sgrid_mem (T : ℝ) (hT : 0 < T) (m : ℕ) : 0 ≤ sgrid T m ∧ sgrid T m < T := by
  unfold sgrid
  have hm2 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have := m.cast_nonneg (α := ℝ); linarith
  have h1 : T / ((m : ℝ) + 2) ≤ T := div_le_self hT.le hm2
  have h2 : 0 < T / ((m : ℝ) + 2) := div_pos hT (by linarith)
  constructor <;> linarith

lemma null_grid {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : Params) (hS : p.Standing)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma)
    (x : ℝ≥0) (I : Issuance Ω) (hI : Admissible 𝔽 C p x (noDividends Ω) I)
    (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < p.T) :
    P {ω | (x : ℝ) + C p.T ω + issuedThrough I s ω = 0} = 0 := by
  have hσ : 0 < p.sigma := hS.2.2.1
  set Y : Ω → ℝ := fun ω => (x : ℝ) + C s ω + issuedThrough I s ω with hY
  set Z : Ω → ℝ := fun ω => C p.T ω - C s ω with hZ
  have hYsm : StronglyMeasurable[𝔽 s] Y :=
    (stronglyMeasurable_const.add (hC.2.2.1 s hs0)).add
      (iss_sm 𝔽 I s (fun k => hI.2.1 k s hs0) (fun ω => hI.2.2.2.2.1 ω s hs0))
  have hYm : Measurable Y := hYsm.measurable.mono (𝔽.le s) le_rfl
  have hCm : ∀ t, 0 ≤ t → Measurable (C t) := fun t ht =>
    (hC.2.2.1 t ht).measurable.mono (𝔽.le t) le_rfl
  have hZm : Measurable Z := (hCm p.T (by linarith)).sub (hCm s hs0)
  obtain ⟨hind, hlaw⟩ := hC.2.2.2 s p.T hs0 hsT.le
  have hYZ : IndepFun Y Z P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind.symm hYsm.measurable.comap_le
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hZm.aemeasurable).mp hYZ
  have hv : (p.sigma ^ 2 * (p.T - s)).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    have : 0 < p.T - s := by linarith
    positivity
  have hZlaw : P.map Z = gaussianReal (p.mu * (p.T - s)) (p.sigma ^ 2 * (p.T - s)).toNNReal := hlaw
  haveI := nullSingletonClass_gaussianReal (μ := p.mu * (p.T - s)) hv
  have hmeas : MeasurableSet {q : ℝ × ℝ | q.1 + q.2 = 0} :=
    measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const
  have hset : {ω | (x : ℝ) + C p.T ω + issuedThrough I s ω = 0} =
      (fun ω => (Y ω, Z ω)) ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hY, hZ]
    constructor <;> intro h <;> linarith
  rw [hset, ← Measure.map_apply (hYm.prodMk hZm) hmeas, hprod, Measure.prod_apply hmeas]
  have : ∀ y : ℝ, (P.map Z) (Prod.mk y ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0}) = 0 := by
    intro y
    have : Prod.mk y ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0} = {-y} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [this, hZlaw]
    exact measure_singleton _
  exact (lintegral_congr (fun y => this y)).trans lintegral_zero

end PDSolLink

open PDSolLink PeriodicDividend.FixedPoint in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (C : ℝ → Ω → ℝ) (p : PeriodicDividend.FixedPoint.Params)
    (hS : p.Standing)
    (hU : PeriodicDividend.FixedPoint.UsualConditions P 𝔽)
    (hC : AtaBarjesteh23.Workload.IsDriftBM 𝔽 P C p.mu p.sigma)
    (A : ℝ) (φ : ℝ≥0 → ℝ) (hφ : PeriodicDividend.FixedPoint.CA p A φ) (x : ℝ≥0) :
    PeriodicDividend.FixedPoint.Lop P 𝔽 C p φ x =
      PeriodicDividend.FixedPoint.vOneExtended P 𝔽 C p φ p.T x := by
  have hT : 0 < p.T := hS.2.2.2.2.2
  have key : ∀ I, Admissible 𝔽 C p x (noDividends Ω) I →
      onePayoff P C p φ x I = Jt P C p φ p.T x I := by
    intro I hI
    have hnull : ∀ᵐ ω ∂P, ruin C p x (noDividends Ω) I ω ≠ ENNReal.ofReal p.T := by
      rw [ae_iff]
      apply measure_mono_null (t := ⋃ m : ℕ,
        {ω | (x : ℝ) + C p.T ω + issuedThrough I (sgrid p.T m) ω = 0})
      · intro ω hω
        have hω' : ruin C p x (noDividends Ω) I ω = ENNReal.ofReal p.T := by
          simpa using hω
        obtain ⟨m, hm⟩ := ruin_eq_T_imp C p hT x I ω (hC.2.1 ω)
          (fun t ht => hI.2.2.2.2.1 ω t ht) (fun k => hI.2.2.1 k ω) hω'
        exact Set.mem_iUnion.mpr ⟨m, hm⟩
      · exact measure_iUnion_null (fun m => null_grid P 𝔽 C p hS hC x I hI (sgrid p.T m)
          (sgrid_mem p.T hT m).1 (sgrid_mem p.T hT m).2)
    have hTR : terminalReward P C p φ x I p.T true = terminalReward P C p φ x I p.T false := by
      unfold terminalReward
      apply lintegral_congr_ae
      filter_upwards [hnull] with ω hω
      have hiff : (ENNReal.ofReal p.T < ruin C p x (noDividends Ω) I ω) ↔
          (ENNReal.ofReal p.T ≤ ruin C p x (noDividends Ω) I ω) :=
        ⟨le_of_lt, fun h => lt_of_le_of_ne h (Ne.symm hω)⟩
      simp only [if_true, Bool.false_eq_true, if_false, hiff]
    unfold onePayoff Jt
    rw [hTR]
  unfold Lop vOneExtended
  congr 1
  ext y
  constructor
  · rintro ⟨I, hI, rfl⟩; exact ⟨I, hI, key I hI⟩
  · rintro ⟨I, hI, rfl⟩; exact ⟨I, hI, (key I hI).symm⟩
