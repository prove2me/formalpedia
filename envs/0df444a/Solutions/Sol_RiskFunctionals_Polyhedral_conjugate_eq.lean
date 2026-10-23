-- Prove2me | solution 1 for RiskFunctionals.Polyhedral.conjugate_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:33:32.559634+00:00
-- url     : https://prove2.me/submissions/1994b73a-eefe-4a08-98b5-31a182b400c5

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_MultiPeriod
-- ===== module A

noncomputable section
open scoped BigOperators Matrix
set_option linter.unusedSectionVars false
open MeasureTheory RiskFunctionals.Polyhedral RiskFunctionals.Polyhedral.MultiPeriodData

namespace X5CE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `Σ_{τ ∈ [max s 1, T]} E[Z τ | F s] • W τ s`. -/
def xv (P : Measure Ω) (D : MultiPeriodData) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω)
    (Z : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) : Fin (D.k s) → ℝ :=
  ∑ τ ∈ Finset.Icc (max s 1) T, (P[Z τ | 𝓕 s] ω) • D.W τ s

lemma dot_memLp {P : Measure Ω} {p : ENNReal} {k : ℕ} {f : Ω → Fin k → ℝ} (hf : MemLp f p P)
    (w : Fin k → ℝ) : MemLp (fun ω => w ⬝ᵥ f ω) p P := by
  have : (fun ω => w ⬝ᵥ f ω) = fun ω => ∑ i, w i * f ω i := by
    funext ω; simp [dotProduct]
  rw [this]
  exact memLp_finsetSum _ fun i _ => (hf.eval i).const_mul (w i)

lemma dot_meas {m : MeasurableSpace Ω} {k : ℕ} {f : Ω → Fin k → ℝ} (hf : Measurable[m] f)
    (w : Fin k → ℝ) : StronglyMeasurable[m] (fun ω => w ⬝ᵥ f ω) := by
  have hc : Continuous fun x : Fin k → ℝ => w ⬝ᵥ x := by
    simp only [dotProduct]; fun_prop
  exact (hc.measurable.comp hf).stronglyMeasurable

/-- Pull-out: `∫ f * g = ∫ E[g|m] * f` for `f` `m`-measurable. -/
lemma pull_out {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hf : StronglyMeasurable[m] f) (hfg : Integrable (f * g) P)
    (hg : Integrable g P) :
    Integrable (fun ω => P[g | m] ω * f ω) P ∧
      ∫ ω, f ω * g ω ∂P = ∫ ω, P[g | m] ω * f ω ∂P := by
  have h := condExp_mul_of_stronglyMeasurable_left (μ := P) hf hfg hg
  have h' : (fun ω => P[g | m] ω * f ω) =ᵐ[P] P[f * g | m] := by
    filter_upwards [h] with ω hω
    rw [hω]; simp [mul_comm]
  refine ⟨(integrable_condExp).congr h'.symm, ?_⟩
  rw [integral_congr_ae h', integral_condExp hm]
  rfl

end X5CE

-- ===== module B

noncomputable section
open scoped BigOperators Matrix
set_option linter.unusedSectionVars false
open MeasureTheory RiskFunctionals.Polyhedral RiskFunctionals.Polyhedral.MultiPeriodData

namespace X5CE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma one_le_q' {p q : ENNReal} (hpq : p⁻¹ + q⁻¹ = 1) : 1 ≤ q := by
  have h : q⁻¹ ≤ 1 := hpq ▸ le_add_self
  rwa [ENNReal.inv_le_one] at h

/-- Weak-duality identity. -/
lemma key {P : Measure Ω} [IsProbabilityMeasure P] {p q : ENNReal} (hp : 1 ≤ p)
    (hpq : p⁻¹ + q⁻¹ = 1) {T : ℕ} {𝓕 : ℕ → MeasurableSpace Ω}
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) {Z Y : ℕ → Ω → ℝ}
    (hZ : IsAdaptedLp P q T 𝓕 Z) {v : (t : ℕ) → Ω → Fin (D.k t) → ℝ}
    (hv : D.Feasible P p T 𝓕 Y v) :
    (∀ s ≤ T, Integrable (fun ω => (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ v s ω) P) ∧
    D.objective P T v - pairing P T Y Z =
      ∑ s ∈ Finset.range (T + 1), ∫ ω, (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ v s ω ∂P := by
  have : ENNReal.HolderTriple p q 1 := ⟨by simpa using hpq⟩
  have hq : 1 ≤ q := one_le_q' hpq
  -- basic pieces
  have hf : ∀ t s, s ≤ T → MemLp (fun ω => D.W t s ⬝ᵥ v s ω) p P := fun t s hs =>
    dot_memLp (hv.1 s hs).2.1 _
  have hfm : ∀ t s, s ≤ T → StronglyMeasurable[𝓕 s] (fun ω => D.W t s ⬝ᵥ v s ω) :=
    fun t s hs => dot_meas (hv.1 s hs).1 _
  have hZi : ∀ t ∈ Finset.Icc 1 T, Integrable (Z t) P := fun t ht =>
    (hZ t ht).2.integrable hq
  have hpo : ∀ t ∈ Finset.Icc 1 T, ∀ s ≤ t,
      Integrable (fun ω => P[Z t | 𝓕 s] ω * (D.W t s ⬝ᵥ v s ω)) P ∧
      ∫ ω, (D.W t s ⬝ᵥ v s ω) * Z t ω ∂P =
        ∫ ω, P[Z t | 𝓕 s] ω * (D.W t s ⬝ᵥ v s ω) ∂P := by
    intro t ht s hst
    have hT : t ≤ T := (Finset.mem_Icc.mp ht).2
    exact pull_out (h𝓕.2.2 s (hst.trans hT)) (hfm t s (hst.trans hT))
      ((hf t s (hst.trans hT)).integrable_mul (hZ t ht).2) (hZi t ht)
  -- the pairing
  have hpair : pairing P T Y Z = ∑ s ∈ Finset.range (T + 1),
      ∫ ω, xv P D T 𝓕 Z s ω ⬝ᵥ v s ω ∂P := by
    have h1 : ∀ t ∈ Finset.Icc 1 T, ∫ ω, Y t ω * Z t ω ∂P =
        ∑ s ∈ Finset.range (t + 1), ∫ ω, P[Z t | 𝓕 s] ω * (D.W t s ⬝ᵥ v s ω) ∂P := by
      intro t ht
      have hT : t ≤ T := (Finset.mem_Icc.mp ht).2
      have hae : (fun ω => Y t ω * Z t ω) =ᵐ[P]
          fun ω => ∑ s ∈ Finset.range (t + 1), (D.W t s ⬝ᵥ v s ω) * Z t ω := by
        filter_upwards [hv.2 t ht] with ω hω
        rw [← hω, Finset.sum_mul]
      rw [integral_congr_ae hae, integral_finsetSum]
      · refine Finset.sum_congr rfl fun s hs => ?_
        exact (hpo t ht s (by simp at hs; omega)).2
      · intro s hs
        have hs' : s ≤ T := by simp at hs; omega
        exact (hf t s hs').integrable_mul (hZ t ht).2
    unfold pairing
    rw [Finset.sum_congr rfl h1]
    rw [Finset.sum_comm' (t' := Finset.range (T + 1)) (s' := fun s => Finset.Icc (max s 1) T)]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [← integral_finsetSum]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only [xv, sum_dotProduct, smul_dotProduct, smul_eq_mul]
      · intro t ht
        exact (hpo t (by simp at ht ⊢; omega) s (by simp at ht; omega)).1
    · intro t s
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
  have hci : ∀ s ≤ T, Integrable (fun ω => D.c s ⬝ᵥ v s ω) P := fun s hs =>
    (dot_memLp (hv.1 s hs).2.1 _).integrable hp
  have hxi : ∀ s ≤ T, Integrable (fun ω => xv P D T 𝓕 Z s ω ⬝ᵥ v s ω) P := by
    intro s hs
    have : (fun ω => xv P D T 𝓕 Z s ω ⬝ᵥ v s ω) = fun ω =>
        ∑ t ∈ Finset.Icc (max s 1) T, P[Z t | 𝓕 s] ω * (D.W t s ⬝ᵥ v s ω) := by
      funext ω
      simp only [xv, sum_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [this]
    exact integrable_finsetSum _ fun t ht =>
      (hpo t (by simp at ht ⊢; omega) s (by simp at ht; omega)).1
  have hint : ∀ s ≤ T, Integrable (fun ω => (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ v s ω) P := by
    intro s hs
    simp only [sub_dotProduct]
    exact (hci s hs).sub (hxi s hs)
  refine ⟨hint, ?_⟩
  rw [hpair, objective, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s ≤ T := by simp at hs; omega
  simp only [sub_dotProduct]
  rw [integral_sub (hci s hs') (hxi s hs')]

end X5CE

-- ===== module C

noncomputable section
open scoped BigOperators Matrix
set_option linter.unusedSectionVars false
open MeasureTheory RiskFunctionals.Polyhedral RiskFunctionals.Polyhedral.MultiPeriodData

namespace X5CE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma xv_zero {P : Measure Ω} [IsProbabilityMeasure P] {T : ℕ} {𝓕 : ℕ → MeasurableSpace Ω}
    (h0 : 𝓕 0 = ⊥) (D : MultiPeriodData) (Z : ℕ → Ω → ℝ) (ω : Ω) :
    xv P D T 𝓕 Z 0 ω = ∑ τ ∈ Finset.Icc 1 T, (∫ ω, Z τ ω ∂P) • D.W τ 0 := by
  simp [xv, h0]

lemma xv_pos {P : Measure Ω} {T : ℕ} {𝓕 : ℕ → MeasurableSpace Ω}
    (D : MultiPeriodData) (Z : ℕ → Ω → ℝ) {s : ℕ} (hs : 1 ≤ s) (ω : Ω) :
    xv P D T 𝓕 Z s ω = ∑ τ ∈ Finset.Icc s T, (P[Z τ | 𝓕 s] ω) • D.W τ s := by
  simp [xv, max_eq_left hs]

lemma dual_iff {P : Measure Ω} [IsProbabilityMeasure P] {q : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} (h0 : 𝓕 0 = ⊥) (D : MultiPeriodData) {Z : ℕ → Ω → ℝ}
    (hZ : IsAdaptedLp P q T 𝓕 Z) :
    Z ∈ D.dualSet P q T 𝓕 ↔
      ∀ s ≤ T, ∀ᵐ ω ∂P, D.c s - xv P D T 𝓕 Z s ω ∈ polarCone (D.V s) := by
  constructor
  · rintro ⟨_, hz0, hzt⟩ s hs
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · exact Filter.Eventually.of_forall fun ω => by rw [xv_zero h0]; exact hz0
    · filter_upwards [hzt s (Finset.mem_Icc.mpr ⟨hpos, hs⟩)] with ω hω
      rw [xv_pos D Z hpos]; exact hω
  · intro h
    refine ⟨hZ, ?_, fun t ht => ?_⟩
    · obtain ⟨ω, hω⟩ := (h 0 (Nat.zero_le _)).exists
      rw [xv_zero h0] at hω; exact hω
    · have ht' := Finset.mem_Icc.mp ht
      filter_upwards [h t ht'.2] with ω hω
      rw [xv_pos D Z ht'.1] at hω; exact hω

lemma zero_mem_cone {k : ℕ} {V : Set (Fin k → ℝ)} (h : IsPolyhedralCone V) : (0 : Fin k → ℝ) ∈ V := by
  obtain ⟨m, a, rfl⟩ := h
  intro j; simp

lemma smul_mem_cone {k : ℕ} {V : Set (Fin k → ℝ)} (h : IsPolyhedralCone V) {r : ℝ} (hr : 0 ≤ r)
    {e : Fin k → ℝ} (he : e ∈ V) : r • e ∈ V := by
  obtain ⟨m, a, rfl⟩ := h
  intro j
  rw [dotProduct_smul, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos hr (he j)

/-- Part 1: on the dual set the conjugate vanishes. -/
lemma part1 {P : Measure Ω} [IsProbabilityMeasure P] {p q : ENNReal} (hp : 1 ≤ p)
    (hpq : p⁻¹ + q⁻¹ = 1) {T : ℕ} {𝓕 : ℕ → MeasurableSpace Ω}
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) (hi : D.CompleteRecourse T)
    {Z : ℕ → Ω → ℝ} (hZ : IsAdaptedLp P q T 𝓕 Z) (hZd : Z ∈ D.dualSet P q T 𝓕) :
    D.conjugate P p T 𝓕 Z = 0 := by
  have hpol := (dual_iff h𝓕.1 D hZ).mp hZd
  -- weak duality
  have hwd : ∀ Y, D.functional P p T 𝓕 Y ≤ (pairing P T Y Z : EReal) := by
    intro Y
    refine sSup_le ?_
    rintro x ⟨v, hv, rfl⟩
    obtain ⟨_, hk⟩ := key hp hpq h𝓕 D hZ hv
    have : D.objective P T v - pairing P T Y Z ≤ 0 := by
      rw [hk]
      refine Finset.sum_nonpos fun s hs => ?_
      have hs' : s ≤ T := by simp at hs; omega
      refine integral_nonpos_of_ae ?_
      filter_upwards [hpol s hs', (hv.1 s hs').2.2] with ω h1 h2
      exact h1 _ h2
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  apply le_antisymm
  · -- take Y = 0
    have hY : IsAdaptedLp P p T 𝓕 (0 : ℕ → Ω → ℝ) := fun t ht =>
      ⟨measurable_const, MemLp.zero⟩
    have hF : (0 : EReal) ≤ D.functional P p T 𝓕 0 := by
      refine le_sSup ⟨0, ⟨fun t ht => ⟨measurable_const, MemLp.zero, ?_⟩, ?_⟩, ?_⟩
      · exact Filter.Eventually.of_forall fun ω => zero_mem_cone (hi.1 t ht)
      · intro t ht
        exact Filter.Eventually.of_forall fun ω => by simp
      · simp [objective]
    refine sInf_le_of_le ⟨0, hY, rfl⟩ ?_
    have : pairing P T 0 Z = 0 := by simp [pairing]
    rw [this]
    calc ((0 : ℝ) : EReal) - D.functional P p T 𝓕 0 ≤ ((0 : ℝ) : EReal) - 0 :=
          EReal.sub_le_sub le_rfl hF
      _ = 0 := by simp
  · refine le_sInf ?_
    rintro x ⟨Y, hY, rfl⟩
    exact (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))).mpr
      (hwd Y)

end X5CE

-- ===== module D

noncomputable section
open scoped BigOperators Matrix
set_option linter.unusedSectionVars false
open MeasureTheory RiskFunctionals.Polyhedral RiskFunctionals.Polyhedral.MultiPeriodData

namespace X5CE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma xv_meas {P : Measure Ω} {T : ℕ} {𝓕 : ℕ → MeasurableSpace Ω} (D : MultiPeriodData)
    (Z : ℕ → Ω → ℝ) (s : ℕ) (e : Fin (D.k s) → ℝ) :
    StronglyMeasurable[𝓕 s] (fun ω => (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ e) := by
  have : (fun ω => (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ e) = fun ω =>
      D.c s ⬝ᵥ e - ∑ τ ∈ Finset.Icc (max s 1) T, P[Z τ | 𝓕 s] ω * (D.W τ s ⬝ᵥ e) := by
    funext ω
    simp [xv, sub_dotProduct, sum_dotProduct, smul_dotProduct]
  rw [this]
  refine stronglyMeasurable_const.sub ?_
  refine Finset.stronglyMeasurable_fun_sum _ fun τ _ => ?_
  exact stronglyMeasurable_condExp.mul stronglyMeasurable_const

/-- A countable family of witnesses for non-membership in the polar of a closed cone. -/
lemma exists_witness {P : Measure Ω} {k : ℕ} {V : Set (Fin k → ℝ)} {x : Ω → Fin k → ℝ}
    (h : ¬ ∀ᵐ ω ∂P, x ω ∈ polarCone V) :
    ∃ e ∈ V, P {ω | 0 < x ω ⬝ᵥ e} ≠ 0 := by
  obtain ⟨S, hSV, hSc, hVS⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace V).exists_countable_dense_subset
  have hsub : {ω | ¬ x ω ∈ polarCone V} ⊆ ⋃ e ∈ S, {ω | 0 < x ω ⬝ᵥ e} := by
    intro ω hω
    simp only [polarCone, Set.mem_setOf_eq, not_forall, not_le, exists_prop] at hω
    obtain ⟨e', he'V, he'⟩ := hω
    have hc : Continuous fun y : Fin k → ℝ => x ω ⬝ᵥ y := by
      simp only [dotProduct]; fun_prop
    have hopen : IsOpen ((fun y => x ω ⬝ᵥ y) ⁻¹' Set.Ioi 0) := isOpen_Ioi.preimage hc
    obtain ⟨e, he, heS⟩ := mem_closure_iff.mp (hVS he'V) _ hopen he'
    exact Set.mem_biUnion heS he
  have hne : P {ω | ¬ x ω ∈ polarCone V} ≠ 0 := by
    intro h0; exact h (ae_iff.mpr h0)
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply hne
  refine measure_mono_null hsub ((measure_biUnion_null_iff hSc).mpr fun e he => hcon e (hSV he))

end X5CE

-- ===== module E

noncomputable section
open scoped BigOperators Matrix
set_option linter.unusedSectionVars false
open MeasureTheory RiskFunctionals.Polyhedral RiskFunctionals.Polyhedral.MultiPeriodData

namespace X5CE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Part 2: off the dual set the conjugate is `⊥`. -/
lemma part2 {P : Measure Ω} [IsProbabilityMeasure P] {p q : ENNReal} (hp : 1 ≤ p)
    (hpq : p⁻¹ + q⁻¹ = 1) {T : ℕ} {𝓕 : ℕ → MeasurableSpace Ω}
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) (hi : D.CompleteRecourse T)
    {Z : ℕ → Ω → ℝ} (hZ : IsAdaptedLp P q T 𝓕 Z) (hZd : Z ∉ D.dualSet P q T 𝓕) :
    D.conjugate P p T 𝓕 Z = ⊥ := by
  rw [dual_iff h𝓕.1 D hZ] at hZd
  simp only [not_forall] at hZd
  obtain ⟨s, hs, hns⟩ := hZd
  obtain ⟨e, heV, hBpos⟩ := exists_witness hns
  set B : Set Ω := {ω | 0 < (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ e} with hBdef
  have hBF : MeasurableSet[𝓕 s] B :=
    measurableSet_lt measurable_const (xv_meas (P := P) (T := T) D Z s e).measurable
  have hB : MeasurableSet B := h𝓕.2.2 s hs _ hBF
  have hcone := hi.1 s hs
  let g : ℝ → Ω → Fin (D.k s) → ℝ := fun r ω => r • B.indicator (fun _ => e) ω
  let v : ℝ → (t : ℕ) → Ω → Fin (D.k t) → ℝ := fun r => Pi.single s (g r)
  let Y : ℝ → ℕ → Ω → ℝ := fun r t ω =>
    ∑ u ∈ Finset.range (t + 1), D.W t u ⬝ᵥ v r u ω
  have hv : ∀ r, 0 ≤ r → D.Feasible P p T 𝓕 (Y r) (v r) := by
    intro r hr
    refine ⟨fun t ht => ?_, fun t ht => Filter.Eventually.of_forall fun ω => rfl⟩
    by_cases hts : t = s
    · subst hts
      simp only [v, Pi.single_eq_same, g]
      refine ⟨(measurable_const.indicator hBF).const_smul r,
        (memLp_indicator_const p hB e (Or.inr (measure_ne_top _ _))).const_smul r,
        Filter.Eventually.of_forall fun ω => ?_⟩
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω]; exact smul_mem_cone hcone hr heV
      · rw [Set.indicator_of_notMem hω, smul_zero]; exact zero_mem_cone hcone
    · simp only [v, Pi.single_eq_of_ne hts]
      exact ⟨measurable_const, MemLp.zero, Filter.Eventually.of_forall fun ω =>
        zero_mem_cone (hi.1 t ht)⟩
  have hY : ∀ r, 0 ≤ r → IsAdaptedLp P p T 𝓕 (Y r) := by
    intro r hr t ht
    have ht' := Finset.mem_Icc.mp ht
    refine ⟨?_, ?_⟩
    · refine Finset.measurable_fun_sum _ fun u hu => ?_
      have hu' : u ≤ t := by simp at hu; omega
      exact (dot_meas ((hv r hr).1 u (hu'.trans ht'.2)).1 _).measurable.mono
        (h𝓕.2.1 u t hu' ht'.2) le_rfl
    · exact memLp_finsetSum _ fun u hu => by
        have hu' : u ≤ t := by simp at hu; omega
        exact dot_memLp ((hv r hr).1 u (hu'.trans ht'.2)).2.1 _
  -- the value of objective - pairing
  have hval : ∀ r, 0 ≤ r → D.objective P T (v r) - pairing P T (Y r) Z =
      r * ∫ ω, (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ B.indicator (fun _ => e) ω ∂P := by
    intro r hr
    rw [(key hp hpq h𝓕 D hZ (hv r hr)).2]
    rw [Finset.sum_eq_single s]
    · simp only [v, Pi.single_eq_same, g, dotProduct_smul, smul_eq_mul]
      exact integral_const_mul r _
    · intro u _ hus
      simp [v, Pi.single_eq_of_ne hus]
    · intro hs'; exact absurd (Finset.mem_range.mpr (by omega)) hs'
  set δ := ∫ ω, (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ B.indicator (fun _ => e) ω ∂P with hδ
  have hδpos : 0 < δ := by
    have hint := (key hp hpq h𝓕 D hZ (hv 1 zero_le_one)).1 s hs
    simp only [v, Pi.single_eq_same, g, one_smul] at hint
    have hnn : ∀ ω, 0 ≤ (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ B.indicator (fun _ => e) ω := by
      intro ω
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω]; exact hω.le
      · rw [Set.indicator_of_notMem hω, dotProduct_zero]
    rw [hδ, integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint]
    have hsupp : Function.support
        (fun ω => (D.c s - xv P D T 𝓕 Z s ω) ⬝ᵥ B.indicator (fun _ => e) ω) = B := by
      ext ω
      by_cases hω : ω ∈ B
      · simp only [Function.mem_support, Set.indicator_of_mem hω]
        exact ⟨fun _ => hω, fun _ => (ne_of_gt hω)⟩
      · simp only [Function.mem_support, Set.indicator_of_notMem hω, dotProduct_zero]
        exact ⟨fun h => absurd rfl h, fun h => absurd h hω⟩
    rw [hsupp]
    exact pos_iff_ne_zero.mpr hBpos
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  set r := (|y| + 1) / δ with hr
  have hr0 : 0 ≤ r := div_nonneg (by positivity) hδpos.le
  have hrδ : r * δ = |y| + 1 := div_mul_cancel₀ _ hδpos.ne'
  have h1 : D.conjugate P p T 𝓕 Z ≤
      (pairing P T (Y r) Z : EReal) - D.functional P p T 𝓕 (Y r) :=
    sInf_le ⟨Y r, hY r hr0, rfl⟩
  have h2 : (D.objective P T (v r) : EReal) ≤ D.functional P p T 𝓕 (Y r) :=
    le_sSup ⟨v r, hv r hr0, rfl⟩
  have h3 := hval r hr0
  calc D.conjugate P p T 𝓕 Z ≤ (pairing P T (Y r) Z : EReal) - D.objective P T (v r) :=
        h1.trans (EReal.sub_le_sub le_rfl h2)
    _ = ((pairing P T (Y r) Z - D.objective P T (v r) : ℝ) : EReal) := by
        rw [EReal.coe_sub]
    _ < y := by
        rw [EReal.coe_lt_coe_iff]
        have := neg_abs_le y
        linarith

end X5CE

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (T : ℕ) (hT : 1 ≤ T) (𝓕 : ℕ → MeasurableSpace Ω)
    (h𝓕 : RiskFunctionals.Polyhedral.IsFiltrationUpTo mΩ T 𝓕)
    (D : RiskFunctionals.Polyhedral.MultiPeriodData) (hD : D.IsPolyhedral T)
    (hi : D.CompleteRecourse T) (hii : D.DualFeasible T) :
    ∀ Z : ℕ → Ω → ℝ, RiskFunctionals.Polyhedral.IsAdaptedLp P q T 𝓕 Z →
      (Z ∈ D.dualSet P q T 𝓕 → D.conjugate P p T 𝓕 Z = 0) ∧
      (Z ∉ D.dualSet P q T 𝓕 → D.conjugate P p T 𝓕 Z = ⊥) := by
  intro Z hZ
  exact ⟨X5CE.part1 hp hpq h𝓕 D hi hZ, X5CE.part2 hp hpq h𝓕 D hi hZ⟩

