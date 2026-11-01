-- Prove2me | solution 1 for StochKolmogorov.Persist.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T20:34:09.490595+00:00
-- url     : https://prove2.me/submissions/f31e61d1-66c7-4309-a78a-73e6a20bdd6f

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
import Theorems.Thm_StochKolmogorov_Persist_markov_property
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_face_invariance
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_3
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_face_box_tv_overlap
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_4
-- ===== P =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10h
/-! M10h (b9/b11): local Lipschitz on compact sets, coordinate clamps, truncation families,
and the Kolmogorov coefficients. -/

variable {d : ℕ}

end M10h

section M10i
open StochKolmogorov.Persist
variable {n : ℕ}

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

end M10j

end ItoLib

-- ===== F41 =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41
/-! F41 (eq_4_1 work, 986b9ae0, 2026-10-30): zero coordinates stay zero; per-time face invariance. -/
open StochKolmogorov.Persist
variable {n : ℕ}

theorem faceOpen_measurableSet (I : Finset (Fin n)) : MeasurableSet (faceOpen I) := by
  have e : faceOpen I = orthant n ∩ ((⋂ i ∈ (Iᶜ : Finset (Fin n)), {x : SDEState n | x i = 0}) ∩
      (⋂ i ∈ I, {x : SDEState n | 0 < x i})) := by
    ext x; simp [faceOpen]; tauto
  rw [e]
  refine orthant_isClosed.measurableSet.inter (MeasurableSet.inter ?_ ?_)
  · exact Finset.measurableSet_biInter _ fun i _ =>
      (isClosed_eq (PiLp.continuous_apply 2 _ i) continuous_const).measurableSet
  · exact Finset.measurableSet_biInter _ fun i _ =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).measurableSet

/-- Per-time face invariance (lemma_3_1 clause 3 at a fixed time). -/
theorem face_inv1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x₀ : SDEState n} (hx₀ : x₀ ∈ faceOpen I) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω ∈ faceOpen I := by
  exact (StochKolmogorov.Persist.kolmogorov_sde_face_invariance C hB hC hx₀ hY).mono fun ω h => h t
/-- The glue form: `P_X(t, x, (ℝ^{I,◦}₊)ᶜ) = 0` for `x ∈ ℝ^{I,◦}₊`. -/
theorem trans_faceOpen_compl {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ faceOpen I) (t : ℝ≥0) :
    StochKolmogorov.Persist.trans P X t x (faceOpen I)ᶜ = 0 := by
  obtain ⟨hP, hB, hX⟩ := hfam
  have hY := hX x hx.1
  unfold StochKolmogorov.Persist.trans
  rw [Measure.map_apply (hY.1 t) (faceOpen_measurableSet I).compl]
  have h := face_inv1 P C B hB hC hx hY t
  rw [ae_iff] at h
  exact h

end F41
end ItoLib

-- ===== HA =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HA (Harris route, s29): abstract Hairer-Mattingly contraction ("Yet another look at Harris'
ergodic theorem", Thm 3.1) in function form. Drift `QV ≤ γ V + K` plus pairwise overlap
`tvDist (Q x) (Q y) ≤ 1 - α` on `{V x + V y ≤ R}` (`R > 2K/(1-γ)`) make `Q` a strict contraction
for the weighted oscillation `|φ x - φ y| ≤ M (2 + β V x + β V y)`. -/

section HA
variable {X : Type*} [MeasurableSpace X]

theorem abs_sub_le_tvDist (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set X} (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν := by
  refine le_csSup ⟨1, ?_⟩ ⟨A, hA, rfl⟩
  rintro _ ⟨B, -, rfl⟩
  have h1 : (μ B).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := B)); simpa using this
  have h2 : (ν B).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ν) (s := B)); simpa using this
  rw [abs_sub_le_iff]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := μ B), ENNReal.toReal_nonneg (a := ν B)]

end HA
end ItoLib

-- ===== F41b =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! F41b (eq_4_1 work, 986b9ae0, 2026-10-30): uniqueness of invariant probability measures from a
local overlap (Doeblin-on-compacts) condition, via the Jordan parts of `μ - ν`. Pure measure theory. -/

section F41b
variable {X : Type*} [MeasurableSpace X]

/-- Hahn decomposition in restriction form. -/
theorem hahn_restrict_le (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ S : Set X, MeasurableSet S ∧ ν.restrict S ≤ μ.restrict S ∧
      μ.restrict Sᶜ ≤ ν.restrict Sᶜ := by
  obtain ⟨S, hS, hpos, hneg⟩ :=
    (μ.toSignedMeasure - ν.toSignedMeasure).exists_compl_positive_negative
  refine ⟨S, hS, ?_, ?_⟩
  · rw [Measure.le_iff]
    intro A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    have h := VectorMeasure.nonneg_of_zero_le_restrict _
      (VectorMeasure.zero_le_restrict_subset _ hS (Set.inter_subset_right : A ∩ S ⊆ S) hpos)
    rw [Measure.toSignedMeasure_sub_apply (hA.inter hS), measureReal_def, measureReal_def] at h
    rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
    linarith
  · rw [Measure.le_iff]
    intro A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    have h := VectorMeasure.nonpos_of_restrict_le_zero _
      (VectorMeasure.restrict_le_zero_subset _ hS.compl (Set.inter_subset_right : A ∩ Sᶜ ⊆ Sᶜ) hneg)
    rw [Measure.toSignedMeasure_sub_apply (hA.inter hS.compl), measureReal_def,
      measureReal_def] at h
    rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
    linarith

/-- The two Jordan parts satisfy `μ + ζ = ν + η`. -/
theorem jordan_sum (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (hpos : ν.restrict S ≤ μ.restrict S)
    (hneg : μ.restrict Sᶜ ≤ ν.restrict Sᶜ) :
    μ + (ν.restrict Sᶜ - μ.restrict Sᶜ) = ν + (μ.restrict S - ν.restrict S) := by
  have hη : (μ.restrict S - ν.restrict S) + ν.restrict S = μ.restrict S :=
    Measure.sub_add_cancel_of_le hpos
  have hζ : (ν.restrict Sᶜ - μ.restrict Sᶜ) + μ.restrict Sᶜ = ν.restrict Sᶜ :=
    Measure.sub_add_cancel_of_le hneg
  set η := μ.restrict S - ν.restrict S
  set ζ := ν.restrict Sᶜ - μ.restrict Sᶜ
  calc μ + ζ = (μ.restrict S + μ.restrict Sᶜ) + ζ := by
          rw [Measure.restrict_add_restrict_compl hS]
    _ = μ.restrict S + (ζ + μ.restrict Sᶜ) := by ac_rfl
    _ = μ.restrict S + ν.restrict Sᶜ := by rw [hζ]
    _ = (η + ν.restrict S) + ν.restrict Sᶜ := by rw [hη]
    _ = (ν.restrict S + ν.restrict Sᶜ) + η := by ac_rfl
    _ = ν + η := by rw [Measure.restrict_add_restrict_compl hS]

theorem jordan_mass (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (hpos : ν.restrict S ≤ μ.restrict S)
    (hneg : μ.restrict Sᶜ ≤ ν.restrict Sᶜ) :
    (ν.restrict Sᶜ - μ.restrict Sᶜ) univ = (μ.restrict S - ν.restrict S) univ := by
  have h := congrArg (fun m : Measure X => m univ) (jordan_sum μ ν hS hpos hneg)
  simp only [Measure.add_apply, measure_univ] at h
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h

/-- One overlap step: an invariant pair cannot have both Jordan parts charging `K`. -/
theorem jordan_overlap (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (hpos : ν.restrict S ≤ μ.restrict S)
    (hneg : μ.restrict Sᶜ ≤ ν.restrict Sᶜ)
    (κ : Kernel X X) [IsMarkovKernel κ] (hμ : μ.bind κ = μ) (hν : ν.bind κ = ν)
    {K : Set X} (hK : MeasurableSet K) {ε : ℝ} (hε : 0 < ε)
    (hov : ∀ x ∈ K, ∀ y ∈ K, MarkovChainCLT.tvDist (κ x) (κ y) ≤ 1 - ε) :
    (μ.restrict S - ν.restrict S) K = 0 ∨ (ν.restrict Sᶜ - μ.restrict Sᶜ) K = 0 := by
  set η := μ.restrict S - ν.restrict S with hηdef
  set ζ := ν.restrict Sᶜ - μ.restrict Sᶜ with hζdef
  have hη : η + ν.restrict S = μ.restrict S := Measure.sub_add_cancel_of_le hpos
  haveI : IsFiniteMeasure η := isFiniteMeasure_of_le (μ.restrict S) Measure.sub_le
  haveI : IsFiniteMeasure ζ := isFiniteMeasure_of_le (ν.restrict Sᶜ) Measure.sub_le
  have hsum : μ + ζ = ν + η := jordan_sum μ ν hS hpos hneg
  have hmass : ζ univ = η univ := jordan_mass μ ν hS hpos hneg
  set a : X → ℝ := fun x => (κ x S).toReal with hadef
  have ha_meas : Measurable a := (κ.measurable_coe hS).ennreal_toReal
  have ha0 : ∀ x, 0 ≤ a x := fun x => ENNReal.toReal_nonneg
  have ha1 : ∀ x, a x ≤ 1 := fun x => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := κ x) (s := S))
    simpa using this
  have hint : ∀ (m : Measure X) [IsFiniteMeasure m], Integrable a m := fun m _ =>
    Integrable.of_bound ha_meas.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha0 x)]; exact ha1 x)
  have hfin : ∀ (m : Measure X) [IsFiniteMeasure m], ∫⁻ x, κ x S ∂m ≠ ∞ := fun m _ =>
    ne_top_of_le_ne_top (measure_ne_top m univ) (by
      calc ∫⁻ x, κ x S ∂m ≤ ∫⁻ _, 1 ∂m := lintegral_mono fun x => prob_le_one
        _ = m univ := by simp)
  have hIa : ∀ (m : Measure X) [IsFiniteMeasure m], ∫ x, a x ∂m = (∫⁻ x, κ x S ∂m).toReal :=
    fun m _ => integral_toReal (κ.measurable_coe hS).aemeasurable
      (ae_of_all _ fun x => measure_lt_top _ _)
  -- the kernel identity at `S`
  have hk : μ S + ∫⁻ x, κ x S ∂ζ = ν S + ∫⁻ x, κ x S ∂η := by
    have e1 : ∫⁻ x, κ x S ∂μ = μ S := by
      rw [← Measure.bind_apply hS κ.measurable.aemeasurable, hμ]
    have e2 : ∫⁻ x, κ x S ∂ν = ν S := by
      rw [← Measure.bind_apply hS κ.measurable.aemeasurable, hν]
    rw [← e1, ← e2, ← lintegral_add_measure, ← lintegral_add_measure, hsum]
  have hS' : η S + ν S = μ S := by
    have := congrArg (fun m : Measure X => m S) hη
    simpa [Measure.restrict_apply_self] using this
  have hηSc : η Sᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc η Sᶜ ≤ μ.restrict S Sᶜ := Measure.sub_le (μ := μ.restrict S) Sᶜ
      _ = 0 := by rw [Measure.restrict_apply hS.compl, compl_inter_self, measure_empty]
  have hηS : η S = η univ := by
    rw [← measure_add_measure_compl hS, hηSc, add_zero]
  -- real form: m = Iη - Iζ
  set m : ℝ := (η univ).toReal with hmdef
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hreal : m = ∫ x, a x ∂η - ∫ x, a x ∂ζ := by
    rw [hIa η, hIa ζ]
    have h1 := congrArg ENNReal.toReal hk
    rw [ENNReal.toReal_add (measure_ne_top _ _) (hfin ζ),
      ENNReal.toReal_add (measure_ne_top _ _) (hfin η)] at h1
    have h2 := congrArg ENNReal.toReal hS'
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hηS] at h2
    linarith
  -- pointwise bound in `y`
  have hy : ∀ y, ∫ x, a x ∂η - m * a y ≤ m - ε * K.indicator 1 y * (η K).toReal := by
    intro y
    have hpt : ∀ x, a x - a y ≤ 1 - ε * K.indicator 1 y * K.indicator 1 x := by
      intro x
      by_cases hx : x ∈ K
      · by_cases hyK : y ∈ K
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hyK, Pi.one_apply, mul_one]
          have := abs_sub_le_tvDist (κ x) (κ y) hS
          have h2 := hov x hx y hyK
          have h3 := le_abs_self (a x - a y)
          simp only [hadef] at h3 ⊢
          linarith
        · simp only [Set.indicator_of_notMem hyK, mul_zero, zero_mul, sub_zero]
          linarith [ha1 x, ha0 y]
      · simp only [Set.indicator_of_notMem hx, mul_zero, sub_zero]
        linarith [ha1 x, ha0 y]
    have hL : ∫ x, (a x - a y) ∂η = ∫ x, a x ∂η - m * a y := by
      rw [integral_sub (hint η) (integrable_const _), integral_const, smul_eq_mul, measureReal_def]
    have hR : ∫ x, (1 - ε * K.indicator 1 y * K.indicator 1 x) ∂η =
        m - ε * K.indicator 1 y * (η K).toReal := by
      rw [integral_sub (integrable_const _)
        ((integrable_indicator_iff hK).2 (integrable_const _).integrableOn |>.const_mul _),
        integral_const, smul_eq_mul, mul_one, integral_const_mul, integral_indicator_one hK,
        measureReal_def, measureReal_def]
    rw [← hL, ← hR]
    refine integral_mono ((hint η).sub (integrable_const _)) ?_ hpt
    exact (integrable_const _).sub
      ((integrable_indicator_iff hK).2 (integrable_const _).integrableOn |>.const_mul _)
  -- integrate over `ζ`
  have hζm : (ζ univ).toReal = m := by rw [hmass]
  have hint_y : Integrable (fun y => ∫ x, a x ∂η - m * a y) ζ :=
    (integrable_const _).sub ((hint ζ).const_mul _)
  have hint_y2 : Integrable (fun y => m - ε * K.indicator 1 y * (η K).toReal) ζ := by
    refine (integrable_const _).sub ?_
    have : Integrable (fun y => K.indicator (1 : X → ℝ) y) ζ :=
      (integrable_indicator_iff hK).2 (integrable_const _).integrableOn
    simpa [mul_comm, mul_left_comm, mul_assoc] using this.const_mul (ε * (η K).toReal)
  have hI := integral_mono hint_y hint_y2 hy
  have eL : ∫ y, (∫ x, a x ∂η - m * a y) ∂ζ = m * ∫ x, a x ∂η - m * ∫ y, a y ∂ζ := by
    rw [integral_sub (integrable_const _) ((hint ζ).const_mul _), integral_const, smul_eq_mul,
      measureReal_def, hζm, integral_const_mul]
  have eR : ∫ y, (m - ε * K.indicator 1 y * (η K).toReal) ∂ζ =
      m * m - ε * (η K).toReal * (ζ K).toReal := by
    have : (fun y => m - ε * K.indicator 1 y * (η K).toReal) =
        fun y => m - (ε * (η K).toReal) * K.indicator 1 y := by
      funext y; ring
    rw [this, integral_sub (integrable_const _)
      (((integrable_indicator_iff hK).2 (integrable_const _).integrableOn).const_mul _),
      integral_const, smul_eq_mul, measureReal_def, hζm, integral_const_mul,
      integral_indicator_one hK, measureReal_def]
  rw [eL, eR] at hI
  have hprod : ε * ((η K).toReal * (ζ K).toReal) ≤ 0 := by
    have : m * m = m * (∫ x, a x ∂η - ∫ x, a x ∂ζ) := by rw [← hreal]
    nlinarith
  have hp0 : (η K).toReal * (ζ K).toReal = 0 :=
    le_antisymm (by
      by_contra hc
      push_neg at hc
      have := mul_pos hε hc
      linarith) (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  rcases mul_eq_zero.1 hp0 with h | h
  · left; exact ((ENNReal.toReal_eq_zero_iff _).1 h).resolve_right (measure_ne_top _ _)
  · right; exact ((ENNReal.toReal_eq_zero_iff _).1 h).resolve_right (measure_ne_top _ _)

/-- Uniqueness of invariant probability measures concentrated on `F`, given overlap on an
increasing exhaustion `K j` of `F` (each `K j` with its own Markov kernel leaving both invariant). -/
theorem eq_of_overlap (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : Set X} (hμF : μ Fᶜ = 0) (hνF : ν Fᶜ = 0) (K : ℕ → Set X)
    (hKm : ∀ j, MeasurableSet (K j)) (hKmono : Monotone K) (hcov : F ⊆ ⋃ j, K j)
    (hov : ∀ j, ∃ κ : Kernel X X, IsMarkovKernel κ ∧ μ.bind κ = μ ∧ ν.bind κ = ν ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K j, ∀ y ∈ K j, MarkovChainCLT.tvDist (κ x) (κ y) ≤ 1 - ε) :
    μ = ν := by
  obtain ⟨S, hS, hpos, hneg⟩ := hahn_restrict_le μ ν
  set η := μ.restrict S - ν.restrict S with hηdef
  set ζ := ν.restrict Sᶜ - μ.restrict Sᶜ with hζdef
  have hη : η + ν.restrict S = μ.restrict S := Measure.sub_add_cancel_of_le hpos
  have hζ : ζ + μ.restrict Sᶜ = ν.restrict Sᶜ := Measure.sub_add_cancel_of_le hneg
  have hmass : ζ univ = η univ := jordan_mass μ ν hS hpos hneg
  have hj : ∀ j, η (K j) = 0 ∨ ζ (K j) = 0 := fun j => by
    obtain ⟨κ, hκ, h1, h2, ε, hε, hov⟩ := hov j
    exact jordan_overlap μ ν hS hpos hneg κ h1 h2 (hKm j) hε hov
  have hU : (⋃ j, K j)ᶜ ⊆ Fᶜ := Set.compl_subset_compl.2 hcov
  have hηU : η (⋃ j, K j) = η univ := by
    have h0 : η (⋃ j, K j)ᶜ = 0 := by
      refine le_antisymm ?_ zero_le
      calc η (⋃ j, K j)ᶜ ≤ μ.restrict S (⋃ j, K j)ᶜ := Measure.sub_le (μ := μ.restrict S) _
        _ ≤ μ (⋃ j, K j)ᶜ := Measure.restrict_le_self _
        _ ≤ μ Fᶜ := measure_mono hU
        _ = 0 := hμF
    rw [← measure_add_measure_compl (MeasurableSet.iUnion hKm), h0, add_zero]
  have hζU : ζ (⋃ j, K j) = ζ univ := by
    have h0 : ζ (⋃ j, K j)ᶜ = 0 := by
      refine le_antisymm ?_ zero_le
      calc ζ (⋃ j, K j)ᶜ ≤ ν.restrict Sᶜ (⋃ j, K j)ᶜ := Measure.sub_le (μ := ν.restrict Sᶜ) _
        _ ≤ ν (⋃ j, K j)ᶜ := Measure.restrict_le_self _
        _ ≤ ν Fᶜ := measure_mono hU
        _ = 0 := hνF
    rw [← measure_add_measure_compl (MeasurableSet.iUnion hKm), h0, add_zero]
  have htη : Tendsto (fun j => η (K j)) atTop (𝓝 (η univ)) := by
    rw [← hηU]; exact tendsto_measure_iUnion_atTop hKmono
  have htζ : Tendsto (fun j => ζ (K j)) atTop (𝓝 (ζ univ)) := by
    rw [← hζU]; exact tendsto_measure_iUnion_atTop hKmono
  have hzero : η univ = 0 := by
    by_contra hne
    have hp : 0 < η univ := pos_iff_ne_zero.2 hne
    have hq : 0 < ζ univ := hmass ▸ hp
    obtain ⟨j, hj1, hj2⟩ := ((htη.eventually (eventually_gt_nhds hp)).and
      (htζ.eventually (eventually_gt_nhds hq))).exists
    rcases hj j with h | h
    · exact (ne_of_gt hj1) h
    · exact (ne_of_gt hj2) h
  have hη0 : η = 0 := Measure.measure_univ_eq_zero.1 hzero
  have hζ0 : ζ = 0 := Measure.measure_univ_eq_zero.1 (hmass.trans hzero)
  rw [hη0, zero_add] at hη
  rw [hζ0, zero_add] at hζ
  rw [← Measure.restrict_add_restrict_compl (μ := μ) hS,
    ← Measure.restrict_add_restrict_compl (μ := ν) hS, hη, hζ]

end F41b
end ItoLib

-- ===== U =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M11a
/-! M11a (lemma_3_1 clause 2): pathwise uniqueness for all times at once, and for the Kolmogorov
system. -/

open StochKolmogorov.Persist

end M11a

section M11b
/-! M11b (lemma_3_1 clause 4a): `H < ∞`, i.e. `bracket35` is bounded above on the orthant. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M11b

end ItoLib

-- ===== Y =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12a
/-! M12a: the test-function machinery of V.lean for a single C² nonnegative function `ψ` of a
linear form `ℓ(x) = Σ_k cv_k x_k`, `Φ(x) = ψ(ℓ x)` (used with `ψ ≈ log(1+·)`). -/

variable {Ω : Type*} {d : ℕ}

variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end M12a

section M12b
/-! M12b: the Lyapunov function `log(1 + cᵀx)` for (1.1): `E ∫₀ᵗ w(X_u) du ≤ log(1 + cᵀx) + log 2 + K t`
with `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)` and `K = max H 0` (`H` of (3.5)). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M12b

end ItoLib

-- ===== Z =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12c
/-! M12c: invariant measures integrate the weight `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)`:
`∫ w dμ ≤ max H 0`, hence the Lyapunov integrands `fᵢ − σᵢᵢ gᵢ²/2` are `μ`-integrable. -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- The transition kernel at time `t` (universe-polymorphic copy of `markov_stmt_of_inv`, part 1). -/
theorem kernel_of_family {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    (t : ℝ≥0) :
    ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
      ∀ x ∈ orthant n, κ x = trans P X t x := by
  exact (StochKolmogorov.Persist.markov_property P C B X hfam c γb hA11).1 t
/-- `hint` of `eq_4_1_of_finite`: the Lyapunov integrands are integrable under every invariant `μ`. -/
theorem lyap_integrable (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X) (c : SDEState n) (γb δ₀ : ℝ) (hA : Assumption11 C c γb)
    (hδ : IsDelta0 C γb δ₀) {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ) (i : Fin n) :
    Integrable (fun x => C.f i x - C.sig i i * C.g i x ^ 2 / 2) μ := by
  have hμP := hμ.1
  have hC := hA.2.1
  have hc := hA.2.2.1
  have hδ0 := hδ.1
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  obtain ⟨H₁, H₂, -, hH₂, -, h38, -⟩ :=
    StochKolmogorov.Persist.lemma_3_2 hn P C B X hfam c γb hA δ₀ hδ
  have hW := (StochKolmogorov.Persist.lemma_3_3 hn P C B X hfam c γb hA δ₀ hδ H₂ hH₂ h38 μ hμ).1
  have hcont : ContinuousOn (fun x => C.f i x - C.sig i i * C.g i x ^ 2 / 2) (orthant n) :=
    (hC i).1.continuousOn.sub ((continuousOn_const.mul ((hC i).2.continuousOn.pow 2)).div_const 2)
  have hmeas : AEStronglyMeasurable (fun x => C.f i x - C.sig i i * C.g i x ^ 2 / 2) μ := by
    have h := hcont.aestronglyMeasurable (μ := μ) orthant_isClosed.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h
  refine ⟨hmeas, (hasFiniteIntegral_iff_norm _).2 ?_⟩
  have hσ0 := abs_nonneg (C.sig i i)
  calc ∫⁻ x, ENNReal.ofReal ‖C.f i x - C.sig i i * C.g i x ^ 2 / 2‖ ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (1 + |C.sig i i|) * ENNReal.ofReal ((1 + ∑ k, c k * x k) ^ δ₀ *
          (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2))) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with x hx
        rw [← ENNReal.ofReal_mul (by linarith), Real.norm_eq_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        have hS : |C.f i x| + |C.g i x| ^ 2 ≤ ∑ k, (|C.f k x| + |C.g k x| ^ 2) :=
          Finset.single_le_sum (f := fun k => |C.f k x| + |C.g k x| ^ 2)
            (fun k _ => by positivity) (Finset.mem_univ i)
        have hb1 : 1 ≤ (1 + ∑ k, c k * x k) ^ δ₀ :=
          Real.one_le_rpow (le_add_of_nonneg_right
            (Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k))) hδ0.le
        have hS0 : 0 ≤ 1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2) := by positivity
        have hg2 : C.g i x ^ 2 = |C.g i x| ^ 2 := (sq_abs _).symm
        have h1 : |C.f i x - C.sig i i * C.g i x ^ 2 / 2| ≤
            |C.f i x| + |C.sig i i| * |C.g i x| ^ 2 := by
          rw [hg2]
          have e : |C.sig i i * |C.g i x| ^ 2 / 2| = |C.sig i i| * |C.g i x| ^ 2 / 2 := by
            rw [abs_div, abs_mul, abs_pow, abs_abs]; norm_num
          have h2 := abs_sub (C.f i x) (C.sig i i * |C.g i x| ^ 2 / 2)
          have h3 : 0 ≤ |C.sig i i| * |C.g i x| ^ 2 := by positivity
          linarith only [h2, e, h3]
        have h4 : |C.f i x| + |C.sig i i| * |C.g i x| ^ 2 ≤
            (1 + |C.sig i i|) * (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2)) := by
          have h5 : 0 ≤ |C.f i x| := abs_nonneg _
          have h6 : 0 ≤ |C.g i x| ^ 2 := by positivity
          nlinarith only [hS, h5, h6, hσ0]
        have h7 : (1 + |C.sig i i|) * (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2)) ≤
            (1 + |C.sig i i|) * ((1 + ∑ k, c k * x k) ^ δ₀ *
              (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          nlinarith only [hb1, hS0]
        linarith only [h1, h4, h7]
    _ = ENNReal.ofReal (1 + |C.sig i i|) * ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, c k * x k) ^ δ₀ *
          (1 + ∑ k, (|C.f k x| + |C.g k x| ^ 2))) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 + |C.sig i i|) * ENNReal.ofReal H₂ := by gcongr
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
end M12c

end ItoLib

-- ===== F41c =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section F41c
/-! F41c (eq_4_1 work, 986b9ae0, 2026-10-30): boundary ergodic measures live on one open face (E5);
invariant measures on one open face are unique given face overlap (E4 concrete); finiteness of M (E6). -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- The support `{i | 0 < x i}` of a point. -/
noncomputable def supp (x : SDEState n) : Finset (Fin n) := Finset.univ.filter fun i => 0 < x i

theorem mem_faceOpen_supp {x : SDEState n} (hx : x ∈ orthant n) : x ∈ faceOpen (supp x) := by
  refine ⟨hx, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact le_antisymm hi (hx i)
  · simpa [supp] using hi

theorem eq_supp_of_mem_faceOpen {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ faceOpen I) :
    I = supp x := by
  obtain ⟨h0, hz, hp⟩ := hx
  ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact hp i
  · intro h
    by_contra hi
    exact (lt_irrefl _ ((hz i hi) ▸ h))

theorem faceOpen_disjoint {I J : Finset (Fin n)} (hIJ : I ≠ J) : faceOpen I ∩ faceOpen J = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hI hJ
  exact hIJ ((eq_supp_of_mem_faceOpen hI).trans (eq_supp_of_mem_faceOpen hJ).symm)

/-- From a point of the orthant off the face `I`, the face `I` is not charged. -/
theorem trans_face_off {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ orthant n) (hxI : x ∉ faceOpen I) (t : ℝ≥0) :
    trans P X t x (faceOpen I) = 0 := by
  have hJ : supp x ≠ I := fun h => hxI (h ▸ mem_faceOpen_supp hx)
  refine le_antisymm ?_ zero_le
  calc trans P X t x (faceOpen I) ≤ trans P X t x (faceOpen (supp x))ᶜ := by
        refine measure_mono fun y hy hy' => ?_
        have := faceOpen_disjoint hJ
        exact (Set.eq_empty_iff_forall_notMem.1 this) y ⟨hy', hy⟩
    _ = 0 := trans_faceOpen_compl P C B X hfam hC (mem_faceOpen_supp hx) t

/-- Invariance in bind form for a kernel version of `trans`. -/
theorem bind_eq_of_inv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : SDEState n → ℝ≥0 → Ω → SDEState n} {t : ℝ≥0} {κ : Kernel (SDEState n) (SDEState n)}
    (hκx : ∀ x ∈ orthant n, κ x = trans P X t x) {ν : Measure (SDEState n)}
    (hae : ∀ᵐ x ∂ν, x ∈ orthant n)
    (hinv : ∀ A, MeasurableSet A → ∫⁻ x, trans P X t x A ∂ν = ν A) : ν.bind κ = ν := by
  ext A hA
  rw [Measure.bind_apply hA κ.measurable.aemeasurable, ← hinv A hA]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hκx x hx]

/-- The restriction of an invariant measure to an open face is invariant (unnormalized form). -/
theorem restrict_face_inv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ) (I : Finset (Fin n)) (t : ℝ≥0)
    {A : Set (SDEState n)} (hA : MeasurableSet A) :
    ∫⁻ x, trans P X t x A ∂(μ.restrict (faceOpen I)) = μ (A ∩ faceOpen I) := by
  set F := faceOpen I with hF
  have hFm : MeasurableSet F := faceOpen_measurableSet I
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  obtain ⟨κ, hκM, hκx⟩ := kernel_of_family P C B X hfam hC hA11 t
  have hbind : μ.bind κ = μ := bind_eq_of_inv hκx hae (hμ.2.2 t)
  have e1 : ∫⁻ x, trans P X t x A ∂(μ.restrict F) = ∫⁻ x, κ x (A ∩ F) ∂(μ.restrict F) := by
    refine lintegral_congr_ae ((ae_restrict_iff' hFm).2 (ae_of_all _ fun x hx => ?_))
    show trans P X t x A = κ x (A ∩ F)
    rw [hκx x hx.1]
    exact (measure_inter_conull (trans_faceOpen_compl P C B X hfam hC hx t)).symm
  have e2 : ∫⁻ x in Fᶜ, κ x (A ∩ F) ∂μ = 0 := by
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ in Fᶜ, 0 ∂μ by simp]
    refine lintegral_congr_ae ((ae_restrict_iff' hFm.compl).2 ?_)
    filter_upwards [hae] with x hx hxF
    rw [hκx x hx]
    exact le_antisymm ((measure_mono Set.inter_subset_right).trans
      (trans_face_off P C B X hfam hC hx hxF t).le) zero_le
  have e3 : ∫⁻ x, κ x (A ∩ F) ∂μ = μ (A ∩ F) := by
    rw [← Measure.bind_apply (hA.inter hFm) κ.measurable.aemeasurable, hbind]
  have e4 := lintegral_add_compl (μ := μ) (fun x => κ x (A ∩ F)) hFm
  rw [e2, add_zero] at e4
  rw [e1, e4, e3]

theorem restrict_face_compl_inv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ) (I : Finset (Fin n)) (t : ℝ≥0)
    {A : Set (SDEState n)} (hA : MeasurableSet A) :
    ∫⁻ x, trans P X t x A ∂(μ.restrict (faceOpen I)ᶜ) = μ (A ∩ (faceOpen I)ᶜ) := by
  haveI := hμ.1
  have hFm : MeasurableSet (faceOpen I) := faceOpen_measurableSet I
  have h1 := restrict_face_inv P C B X hfam hC hA11 hμ I t hA
  have h2 : ∫⁻ x in faceOpen I, trans P X t x A ∂μ + ∫⁻ x in (faceOpen I)ᶜ, trans P X t x A ∂μ =
      μ A := by rw [lintegral_add_compl _ hFm, hμ.2.2 t A hA]
  rw [h1, ← measure_inter_add_diff A hFm, Set.diff_eq] at h2
  exact (ENNReal.add_right_inj (measure_ne_top _ _)).1 h2

/-- E5: a boundary ergodic measure is concentrated on one open face. -/
theorem bdryErgodic_face {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    {μ : Measure (SDEState n)} (hμM : μ ∈ bdryErgodic P X) :
    ∃ I : Finset (Fin n), μ (faceOpen I)ᶜ = 0 := by
  obtain ⟨⟨hinv, hext⟩, -⟩ := hμM
  haveI := hinv.1
  have hcov : orthant n ⊆ ⋃ I : Finset (Fin n), faceOpen I := fun x hx =>
    Set.mem_iUnion.2 ⟨supp x, mem_faceOpen_supp hx⟩
  obtain ⟨I, hIpos⟩ : ∃ I : Finset (Fin n), μ (faceOpen I) ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : μ (orthant n) = 0 := measure_mono_null hcov (measure_iUnion_null h)
    have h1 : μ (orthant n) + μ (orthant n)ᶜ = 1 := by
      rw [measure_add_measure_compl orthant_isClosed.measurableSet, measure_univ]
    rw [h0, hinv.2.1, add_zero] at h1
    exact zero_ne_one h1
  refine ⟨I, ?_⟩
  set F := faceOpen I with hF
  have hFm : MeasurableSet F := faceOpen_measurableSet I
  by_contra hc
  have hF1 : μ F + μ Fᶜ = 1 := by rw [measure_add_measure_compl hFm, measure_univ]
  have hFt : μ F ≠ ∞ := measure_ne_top _ _
  have hFct : μ Fᶜ ≠ ∞ := measure_ne_top _ _
  set ν1 : Measure (SDEState n) := (μ F)⁻¹ • μ.restrict F with hν1
  set ν2 : Measure (SDEState n) := (μ Fᶜ)⁻¹ • μ.restrict Fᶜ with hν2
  have hprob1 : IsProbabilityMeasure ν1 := ⟨by
    rw [hν1, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hIpos hFt]⟩
  have hprob2 : IsProbabilityMeasure ν2 := ⟨by
    rw [hν2, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hc hFct]⟩
  have hinv1 : IsInvariant P X ν1 := by
    refine ⟨hprob1, ?_, fun t A hA => ?_⟩
    · rw [hν1, Measure.smul_apply, Measure.restrict_apply orthant_isClosed.measurableSet.compl,
        measure_mono_null Set.inter_subset_left hinv.2.1, smul_eq_mul, mul_zero]
    · rw [hν1, lintegral_smul_measure, restrict_face_inv P C B X hfam hC hA11 hinv I t hA,
        Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  have hinv2 : IsInvariant P X ν2 := by
    refine ⟨hprob2, ?_, fun t A hA => ?_⟩
    · rw [hν2, Measure.smul_apply, Measure.restrict_apply orthant_isClosed.measurableSet.compl,
        measure_mono_null Set.inter_subset_left hinv.2.1, smul_eq_mul, mul_zero]
    · rw [hν2, lintegral_smul_measure, restrict_face_compl_inv P C B X hfam hC hA11 hinv I t hA,
        Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  set a : ℝ≥0 := (μ F).toNNReal with ha
  have haF : (a : ℝ≥0∞) = μ F := ENNReal.coe_toNNReal hFt
  have ha0 : 0 < a := by
    rw [← ENNReal.coe_lt_coe, haF, ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hIpos
  have ha1 : a < 1 := by
    rw [← ENNReal.coe_lt_coe, haF, ENNReal.coe_one]
    have : μ Fᶜ ≠ 0 := hc
    have h2 : 0 < μ Fᶜ := pos_iff_ne_zero.2 this
    calc μ F = μ F + 0 := (add_zero _).symm
      _ < μ F + μ Fᶜ := ENNReal.add_lt_add_left hFt h2
      _ = 1 := hF1
  have h1a : ((1 - a : ℝ≥0) : ℝ≥0∞) = μ Fᶜ := by
    rw [ENNReal.coe_sub, ENNReal.coe_one, haF, prob_compl_eq_one_sub hFm]
  have hdec : μ = (a : ℝ≥0∞) • ν1 + ((1 - a : ℝ≥0) : ℝ≥0∞) • ν2 := by
    rw [haF, h1a, hν1, hν2, smul_smul, smul_smul, ENNReal.mul_inv_cancel hIpos hFt,
      ENNReal.mul_inv_cancel hc hFct, one_smul, one_smul, Measure.restrict_add_restrict_compl hFm]
  have heq := hext ν1 ν2 hinv1 hinv2 a ha0 ha1 hdec
  apply hc
  rw [← heq, hν1, Measure.smul_apply, Measure.restrict_apply hFm.compl, Set.compl_inter_self,
    measure_empty, smul_eq_mul, mul_zero]

/-- The compact pieces of an open face. -/
def faceBox (I : Finset (Fin n)) (α β : ℝ) : Set (SDEState n) :=
  {x | x ∈ faceOpen I ∧ ∀ i ∈ I, α ≤ x i ∧ x i ≤ β}

theorem faceBox_measurableSet (I : Finset (Fin n)) (α β : ℝ) : MeasurableSet (faceBox I α β) := by
  have e : faceBox I α β = faceOpen I ∩
      ⋂ i ∈ I, ({x : SDEState n | α ≤ x i} ∩ {x : SDEState n | x i ≤ β}) := by
    ext x; simp [faceBox, Set.mem_iInter₂]
  rw [e]
  exact (faceOpen_measurableSet I).inter (Finset.measurableSet_biInter _ fun i _ =>
    (measurableSet_le measurable_const (PiLp.continuous_apply 2 _ i).measurable).inter
    (measurableSet_le (PiLp.continuous_apply 2 _ i).measurable measurable_const))

theorem tvDist_self' {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) :
    MarkovChainCLT.tvDist μ μ = 0 := by
  unfold MarkovChainCLT.tvDist
  have : {r : ℝ | ∃ A : Set Y, MeasurableSet A ∧ r = |(μ A).toReal - (μ A).toReal|} = {0} := by
    ext r
    simp only [sub_self, abs_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨∅, MeasurableSet.empty, h⟩⟩
  rw [this, csSup_singleton]

theorem eq_zero_of_mem_faceOpen_empty {x : SDEState n} (hx : x ∈ faceOpen (∅ : Finset (Fin n))) :
    x = 0 := by
  ext i
  simpa using hx.2.1 i (Finset.notMem_empty i)

/-- The (trivial) overlap on the vertex face `{0}`. -/
theorem face_overlap_empty {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (α β : ℝ) :
    ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ faceBox (∅ : Finset (Fin n)) α β,
      ∀ y ∈ faceBox (∅ : Finset (Fin n)) α β,
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε := by
  refine ⟨0, 1 / 2, by norm_num, fun x hx y hy => ?_⟩
  rw [eq_zero_of_mem_faceOpen_empty hx.1, eq_zero_of_mem_faceOpen_empty hy.1, tvDist_self']
  norm_num

/-- E4 (concrete): invariant probability measures on one open face coincide, given overlap on
the face boxes. -/
theorem inv_unique_face {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    {I : Finset (Fin n)}
    (hov : ∀ α β : ℝ, 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ faceBox I α β,
      ∀ y ∈ faceBox I α β, MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε)
    {μ ν : Measure (SDEState n)} (hμ : IsInvariant P X μ) (hν : IsInvariant P X ν)
    (hμF : μ (faceOpen I)ᶜ = 0) (hνF : ν (faceOpen I)ᶜ = 0) : μ = ν := by
  haveI := hμ.1
  haveI := hν.1
  have haeμ : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  have haeν : ∀ᵐ x ∂ν, x ∈ orthant n := by rw [ae_iff]; exact hν.2.1
  refine eq_of_overlap μ ν hμF hνF (fun j : ℕ => faceBox I (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1))
    (fun j => faceBox_measurableSet _ _ _) ?_ ?_ ?_
  · intro j k hjk x hx
    have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).2 hjk; linarith
    refine ⟨hx.1, fun i hi => ⟨le_trans ?_ (hx.2 i hi).1, (hx.2 i hi).2.trans hjk'⟩⟩
    exact one_div_le_one_div_of_le (by positivity) hjk'
  · intro x hx
    have hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ I, 1 / ((j : ℝ) + 1) ≤ x i ∧ x i ≤ (j : ℝ) + 1 := by
      refine (Filter.eventually_all_finset I).2 fun i hi => ?_
      have hxi : 0 < x i := hx.2.2 i hi
      refine ((tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hxi)).and
        (tendsto_natCast_atTop_atTop.eventually_ge_atTop (x i))).mono fun j hj => ⟨hj.1.le, ?_⟩
      linarith [hj.2]
    obtain ⟨j, hj⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨j, hx, hj⟩
  · intro j
    have hα : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hαβ : 1 / ((j : ℝ) + 1) ≤ (j : ℝ) + 1 := by
      have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have := (j.cast_nonneg : (0 : ℝ) ≤ j); linarith
      have := (j.cast_nonneg : (0 : ℝ) ≤ j); linarith
    obtain ⟨T, ε, hε, h⟩ := hov _ _ hα hαβ
    obtain ⟨κ, hκM, hκx⟩ := kernel_of_family P C B X hfam hC hA11 T
    refine ⟨κ, hκM, bind_eq_of_inv hκx haeμ (hμ.2.2 T), bind_eq_of_inv hκx haeν (hν.2.2 T),
      ε, hε, fun x hx y hy => ?_⟩
    rw [hκx x hx.1.1, hκx y hy.1.1]
    exact h x hx y hy

/-- E6: `M` is finite, given overlap on the boxes of every nonempty open face. -/
theorem bdryErgodic_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    (hov : ∀ I : Finset (Fin n), I.Nonempty → ∀ α β : ℝ, 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ,
      0 < ε ∧ ∀ x ∈ faceBox I α β, ∀ y ∈ faceBox I α β,
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε) :
    (bdryErgodic P X).Finite := by
  have hsub : bdryErgodic P X ⊆
      ⋃ I : Finset (Fin n), {μ | μ ∈ bdryErgodic P X ∧ μ (faceOpen I)ᶜ = 0} := fun μ hμ => by
    obtain ⟨I, hI⟩ := bdryErgodic_face P C B X hfam hC hA11 hμ
    exact Set.mem_iUnion.2 ⟨I, hμ, hI⟩
  refine Set.Finite.subset (Set.finite_iUnion fun I => Set.Subsingleton.finite ?_) hsub
  rintro μ ⟨hμ, hμF⟩ ν ⟨hν, hνF⟩
  have hovI : ∀ α β : ℝ, 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ faceBox I α β,
      ∀ y ∈ faceBox I α β, MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε := by
    intro α β hα hαβ
    by_cases hI : I.Nonempty
    · exact hov I hI α β hα hαβ
    · rw [Finset.not_nonempty_iff_eq_empty.1 hI]
      exact face_overlap_empty P X α β
  exact inv_unique_face P C B X hfam hC hA11 hovI hμ.1.1 hν.1.1 hμF hνF

end F41c
end ItoLib


-- ===== L41 =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L41
/-! L41 (lemma_4_1, 0c64895b, 2026-10-31): occupation measures from the boundary are tight
(lemma_3_2 (3.8)), their weak limits are invariant (Feller + Markov property) and live on the
boundary (face invariance); every invariant measure on the boundary splits over the open faces
into ergodic pieces (face overlap), so `∑ pᵢ λᵢ(π) ≥ 2ρ*`; lemma_3_3 gives `∫ cBracket dπ = 0` and
lemma_3_4 the convergence of `∫ Φ dΠ`. -/
open StochKolmogorov.Persist
variable {n : ℕ}

theorem pp_apply' (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem pp_mem' (x : SDEState n) : posPart x ∈ orthant n := fun i => by
  rw [pp_apply']; exact le_max_right _ _

theorem pp_of_mem' {x : SDEState n} (hx : x ∈ orthant n) : posPart x = x := by
  ext i; rw [pp_apply']; exact max_eq_left (hx i)

theorem pp_cont' : Continuous (posPart (n := n)) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (PiLp.continuous_apply 2 _ i).max continuous_const)

theorem openOrthant_isOpen : IsOpen (openOrthant n) := by
  have : openOrthant n = ⋂ i, {y : SDEState n | 0 < y i} := by ext y; simp [openOrthant]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)

theorem bdry_compl_isOpen : IsOpen (bdry n)ᶜ := by
  have : bdry n = orthant n ∩ (openOrthant n)ᶜ := rfl
  rw [this, isOpen_compl_iff]
  exact orthant_isClosed.inter openOrthant_isOpen.isClosed_compl

/-- The weight `(1 + cᵀx)^δ₀ (1 + ∑ᵢ(|fᵢ(x)| + |gᵢ(x)|²))` of (3.8). -/
noncomputable def Wt (C : Coeffs n) (c : SDEState n) (δ₀ : ℝ) (x : SDEState n) : ℝ :=
  (1 + ∑ i, c i * x i) ^ δ₀ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))

theorem one_le_W {c x : SDEState n} (hc : c ∈ openOrthant n) (hx : x ∈ orthant n) :
    1 ≤ 1 + ∑ i, c i * x i := by
  have : 0 ≤ ∑ i, c i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hx i)
  linarith

theorem one_le_U (C : Coeffs n) (x : SDEState n) :
    1 ≤ 1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2) := by
  have : 0 ≤ ∑ i, (|C.f i x| + |C.g i x| ^ 2) :=
    Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) 2)
  linarith

theorem Wt_nonneg (C : Coeffs n) {c x : SDEState n} (hc : c ∈ openOrthant n)
    (hx : x ∈ orthant n) (δ₀ : ℝ) : 0 ≤ Wt C c δ₀ x :=
  mul_nonneg (Real.rpow_nonneg (by linarith [one_le_W hc hx]) _) (by linarith [one_le_U C x])

theorem Wt_pp_cont (C : Coeffs n) (c : SDEState n) (δ₀ : ℝ) (hδ : 0 ≤ δ₀)
    (hf : ∀ i, ContinuousOn (C.f i) (orthant n)) (hg : ∀ i, ContinuousOn (C.g i) (orthant n)) :
    Continuous (fun x => Wt C c δ₀ (posPart x)) := by
  have fc : ∀ i, Continuous fun x => C.f i (posPart x) := fun i =>
    (hf i).comp_continuous pp_cont' pp_mem'
  have gc : ∀ i, Continuous fun x => C.g i (posPart x) := fun i =>
    (hg i).comp_continuous pp_cont' pp_mem'
  unfold Wt
  refine Continuous.mul ?_ ?_
  · exact (continuous_const.add (continuous_finsetSum _ fun i _ => continuous_const.mul
      ((PiLp.continuous_apply 2 _ i).comp pp_cont'))).rpow_const (fun _ => Or.inr hδ)
  · exact continuous_const.add (continuous_finsetSum _ fun i _ =>
      (fc i).abs.add ((gc i).abs.pow 2))

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

/-! ### Occupation measures -/

theorem occ_jointMeas {Ω : Type*} [MeasurableSpace Ω]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) :
    Measurable (fun q : ℝ × Ω => X x q.1.toNNReal q.2) :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ) (ω : Ω) => X x s.toNNReal ω)
    (fun ω => (hc ω).comp continuous_real_toNNReal) (fun s => hm _)

theorem occ_lint {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) (T : ℝ) (g : SDEState n → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂(occMean P X x T) =
      (ENNReal.ofReal T)⁻¹ * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, g (X x s.toNNReal ω)) ∂P := by
  have hF := occ_jointMeas X x hm hc
  unfold occMean
  rw [lintegral_smul_measure, lintegral_map hg hF,
    lintegral_prod_symm (fun q : ℝ × Ω => g (X x q.1.toNNReal q.2)) ((hg.comp hF).aemeasurable),
    smul_eq_mul]

theorem occ_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) {T : ℝ} (hT : 0 < T) :
    IsProbabilityMeasure (occMean P X x T) := by
  constructor
  have := occ_lint P X x hm hc T (fun _ => 1) measurable_const
  simp only [lintegral_one, lintegral_const, measure_univ, mul_one, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero] at this
  rw [this]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hT).ne' ENNReal.ofReal_ne_top

theorem occ_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) (T : ℝ) {S : Set (SDEState n)}
    (hS : MeasurableSet S) (hinv : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ S) :
    occMean P X x T Sᶜ = 0 := by
  have := occ_lint P X x hm hc T (Sᶜ.indicator 1) (measurable_one.indicator hS.compl)
  rw [lintegral_indicator_one hS.compl] at this
  rw [this]
  have h0 : (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      Sᶜ.indicator 1 (X x s.toNNReal ω)) =ᵐ[P] 0 := by
    filter_upwards [hinv] with ω hω
    simp [Set.indicator_apply, hω]
  rw [lintegral_congr_ae h0]
  simp

theorem occ_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) {T : ℝ} (hT : 0 < T) {g : SDEState n → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) :
    ∫ y, g y ∂(occMean P X x T) =
      T⁻¹ * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, g (X x s.toNNReal ω) ∂P := by
  have hF := occ_jointMeas X x hm hc
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  unfold occMean
  rw [integral_smul_measure, integral_map hF.aemeasurable hg.aestronglyMeasurable,
    integral_prod (fun q : ℝ × Ω => g (X x q.1.toNNReal q.2))
      (Integrable.of_bound (f := fun q : ℝ × Ω => g (X x q.1.toNNReal q.2))
        (hg.comp hF).aestronglyMeasurable K
        (ae_of_all _ fun q => by rw [Real.norm_eq_abs]; exact hK _)),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hT.le, smul_eq_mul]

/-- Time averages of a bounded continuous function are almost shift invariant. -/
theorem tavg_shift {F : ℝ → ℝ} (hF : Continuous F) {K : ℝ} (hK : ∀ u, |F u| ≤ K) {T t : ℝ}
    (hT : 0 < T) (ht : 0 ≤ t) :
    |T⁻¹ * (∫ s in Set.Icc (0 : ℝ) T, F (s + t)) - T⁻¹ * ∫ s in Set.Icc (0 : ℝ) T, F s| ≤
      2 * t * K / T := by
  have c1 : ∫ s in Set.Icc (0 : ℝ) T, F (s + t) = ∫ u in t..(T + t), F u := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
    have := intervalIntegral.integral_comp_add_right F t (a := 0) (b := T)
    rw [zero_add] at this
    exact this
  have c2 : ∫ s in Set.Icc (0 : ℝ) T, F s = ∫ u in (0 : ℝ)..T, F u := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  rw [c1, c2]
  have hi : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hF.intervalIntegrable a b
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 t) (hi t (T + t))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi 0 T) (hi T (T + t))
  have b1 : ‖∫ u in (0 : ℝ)..t, F u‖ ≤ K * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
      rw [Real.norm_eq_abs]; exact hK u
  have b2 : ‖∫ u in T..(T + t), F u‖ ≤ K * |T + t - T| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
      rw [Real.norm_eq_abs]; exact hK u
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at b1
  rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg ht] at b2
  have e : T⁻¹ * (∫ u in t..(T + t), F u) - T⁻¹ * ∫ u in (0 : ℝ)..T, F u =
      T⁻¹ * ((∫ u in T..(T + t), F u) - ∫ u in (0 : ℝ)..t, F u) := by
    rw [← mul_sub]; congr 1; linarith
  rw [e, abs_mul, abs_inv, abs_of_pos hT]
  have h3 : |(∫ u in T..(T + t), F u) - ∫ u in (0 : ℝ)..t, F u| ≤ 2 * t * K := by
    have := abs_sub (∫ u in T..(T + t), F u) (∫ u in (0 : ℝ)..t, F u)
    linarith
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hT.le)

theorem integral_bind_markov {κ : Kernel (SDEState n) (SDEState n)} [IsMarkovKernel κ]
    {π : Measure (SDEState n)} [IsProbabilityMeasure π] (f : SDEState n →ᵇ ℝ) :
    ∫ z, f z ∂(π.bind κ) = ∫ y, ∫ z, f z ∂(κ y) ∂π := by
  have e : π.bind κ = (κ ∘ₖ Kernel.const Unit π) () := by
    rw [Kernel.comp_apply, Kernel.const_apply]
  rw [e, Kernel.integral_comp (f.integrable _), Kernel.const_apply]

/-- Chapman-Kolmogorov in integral form. -/
theorem ck_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    {x : SDEState n} (hx : x ∈ orthant n) (s t : ℝ≥0) (f : SDEState n →ᵇ ℝ) :
    ∫ ω, (∫ ω', f (X (posPart (X x s ω)) t ω') ∂P) ∂P = ∫ ω, f (X x (s + t) ω) ∂P := by
  haveI := hfam.1
  obtain ⟨hK, hCK, horth, -⟩ := markov_property P C B X hfam c γb hA
  obtain ⟨κ, hκM, hκ⟩ := hK t
  have hsol := hfam.2.2
  have hms : ∀ y, y ∈ orthant n → ∀ u, Measurable (X y u) := fun y hy u => (hsol y hy).1 u
  have hbind : StochKolmogorov.Persist.trans P X (s + t) x = (StochKolmogorov.Persist.trans P X s x).bind κ := by
    ext A hA
    rw [Measure.bind_apply hA κ.aemeasurable, hCK s t x hx A hA]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ y ∂(StochKolmogorov.Persist.trans P X s x), y ∈ orthant n := by rw [ae_iff]; exact horth s x hx
    filter_upwards [hae] with y hy
    rw [hκ y hy]
  have hstay : ∀ᵐ ω ∂P, X x s ω ∈ orthant n := by
    have h := horth s x hx
    unfold StochKolmogorov.Persist.trans at h
    rw [Measure.map_apply (hms x hx s) orthant_isClosed.measurableSet.compl] at h
    rw [ae_iff]; exact h
  haveI : IsProbabilityMeasure (StochKolmogorov.Persist.trans P X s x) := by
    unfold StochKolmogorov.Persist.trans; exact Measure.isProbabilityMeasure_map (hms x hx s).aemeasurable
  have lhs : ∫ ω, f (X x (s + t) ω) ∂P = ∫ z, f z ∂(StochKolmogorov.Persist.trans P X (s + t) x) := by
    unfold StochKolmogorov.Persist.trans
    rw [integral_map (hms x hx _).aemeasurable f.continuous.aestronglyMeasurable]
  rw [lhs, hbind, integral_bind_markov]
  have hsm : StronglyMeasurable fun y => ∫ z, f z ∂(κ y) :=
    f.continuous.stronglyMeasurable.integral_kernel
  unfold StochKolmogorov.Persist.trans
  rw [integral_map (hms x hx s).aemeasurable hsm.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hstay] with ω hω
  rw [hκ _ hω, pp_of_mem' hω]
  unfold StochKolmogorov.Persist.trans
  rw [integral_map (hms _ hω t).aemeasurable f.continuous.aestronglyMeasurable]

/-- A probability measure on `ℝⁿ₊` with `∫ Pₜh dπ = ∫ h dπ` for all bounded continuous `h` is
invariant at time `t`. -/
theorem inv_of_bcf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    {π : Measure (SDEState n)} [IsProbabilityMeasure π] (hπo : π (orthant n)ᶜ = 0) (t : ℝ≥0)
    (h : ∀ f : SDEState n →ᵇ ℝ, ∫ y, (∫ ω, f (X (posPart y) t ω) ∂P) ∂π = ∫ y, f y ∂π)
    {A : Set (SDEState n)} (hA' : MeasurableSet A) :
    ∫⁻ x, StochKolmogorov.Persist.trans P X t x A ∂π = π A := by
  haveI := hfam.1
  obtain ⟨hK, -, -, -⟩ := markov_property P C B X hfam c γb hA
  obtain ⟨κ, hκM, hκ⟩ := hK t
  have hsol := hfam.2.2
  have hae : ∀ᵐ y ∂π, y ∈ orthant n := by rw [ae_iff]; exact hπo
  have heq : π.bind κ = π := by
    haveI : IsProbabilityMeasure (π.bind κ) := by
      have e : π.bind κ = (κ ∘ₖ Kernel.const Unit π) () := by
        rw [Kernel.comp_apply, Kernel.const_apply]
      rw [e]; infer_instance
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_bind_markov, ← h f]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hκ y hy, pp_of_mem' hy]
    unfold StochKolmogorov.Persist.trans
    rw [integral_map ((hsol y hy).1 t).aemeasurable f.continuous.aestronglyMeasurable]
  calc ∫⁻ x, StochKolmogorov.Persist.trans P X t x A ∂π = ∫⁻ x, κ x A ∂π := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with y hy
        rw [hκ y hy]
    _ = (π.bind κ) A := (Measure.bind_apply hA' κ.aemeasurable).symm
    _ = π A := by rw [heq]

end L41
end ItoLib

-- ===== L41b =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L41b
open StochKolmogorov.Persist
variable {n : ℕ}

theorem bdry_isClosed : IsClosed (bdry n) := isOpen_compl_iff.1 bdry_compl_isOpen

/-- The normalized restriction of a boundary invariant measure to an open face is in `M`. -/
theorem face_restrict_mem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X) {c : SDEState n} {γb : ℝ} (hA11 : Assumption11 C c γb)
    {π : Measure (SDEState n)} (hπ : IsInvariant P X π) (hπo : π (openOrthant n) = 0)
    (I : Finset (Fin n)) (hI : π (faceOpen I) ≠ 0) :
    (π (faceOpen I))⁻¹ • π.restrict (faceOpen I) ∈ bdryErgodic P X := by
  haveI := hπ.1
  have hC := hA11.2.1
  set F := faceOpen I with hF
  have hFm : MeasurableSet F := faceOpen_measurableSet I
  have hFt : π F ≠ ∞ := measure_ne_top _ _
  set ν1 : Measure (SDEState n) := (π F)⁻¹ • π.restrict F with hν1
  have hprob1 : IsProbabilityMeasure ν1 := ⟨by
    rw [hν1, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hI hFt]⟩
  have hinv1 : IsInvariant P X ν1 := by
    refine ⟨hprob1, ?_, fun t A hA => ?_⟩
    · rw [hν1, Measure.smul_apply, Measure.restrict_apply orthant_isClosed.measurableSet.compl,
        measure_mono_null Set.inter_subset_left hπ.2.1, smul_eq_mul, mul_zero]
    · rw [hν1, lintegral_smul_measure, restrict_face_inv P C B X hfam hC hA11 hπ I t hA,
        Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  have hν1F : ν1 Fᶜ = 0 := by
    rw [hν1, Measure.smul_apply, Measure.restrict_apply hFm.compl, Set.compl_inter_self,
      measure_empty, smul_eq_mul, mul_zero]
  have hovI : ∀ α β : ℝ, 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ faceBox I α β,
      ∀ y ∈ faceBox I α β, MarkovChainCLT.tvDist (StochKolmogorov.Persist.trans P X T x)
        (StochKolmogorov.Persist.trans P X T y) ≤ 1 - ε := by
    intro α β hα hαβ
    obtain ⟨T, ε, hε, h⟩ :=
      StochKolmogorov.Persist.kolmogorov_face_box_tv_overlap P C B X hfam hC hA11.1 I hα hαβ
    exact ⟨T, ε, hε, fun x hx y hy => h x hx.1 hx.2 y hy.1 hy.2⟩
  refine ⟨⟨hinv1, fun ν₁ ν₂ h1 h2 a ha0 ha1 hdec => ?_⟩, ?_⟩
  · have hν₁F : ν₁ Fᶜ = 0 := by
      have h := congrArg (fun m : Measure (SDEState n) => m Fᶜ) hdec
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at h
      rw [hν1F] at h
      have h' := (add_eq_zero.1 h.symm).1
      rcases mul_eq_zero.1 h' with h0 | h0
      · exact absurd h0 (by simpa using ha0.ne')
      · exact h0
    exact inv_unique_face P C B X hfam hC hA11 hovI h1 hinv1 hν₁F hν1F
  · rw [hν1, Measure.smul_apply, Measure.restrict_apply openOrthant_isOpen.measurableSet,
      measure_mono_null Set.inter_subset_left hπo, smul_eq_mul, mul_zero]

/-- Every invariant probability measure on the boundary has weighted invasion rate `≥ 2ρ`. -/
theorem inv_bdry_lyap (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X) (c : SDEState n) (γb δ₀ : ℝ) (hA : Assumption11 C c γb)
    (hδ : IsDelta0 C γb δ₀) (p : SDEState n) (ρ : ℝ)
    (h41 : ∀ μ ∈ bdryErgodic P X, 2 * ρ ≤ ∑ i, p i * lyap C i μ)
    {π : Measure (SDEState n)} (hπ : IsInvariant P X π) (hπo : π (openOrthant n) = 0) :
    Integrable (fun x => ∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2)) π ∧
      2 * ρ ≤ ∫ x, ∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2) ∂π := by
  haveI := hπ.1
  have hLint : ∀ {μ : Measure (SDEState n)}, IsInvariant P X μ →
      Integrable (fun x => ∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2)) μ :=
    fun hμ => integrable_finset_sum _ fun i _ =>
      (lyap_integrable hn P C B X hfam c γb δ₀ hA hδ hμ i).const_mul (p i)
  have hLeq : ∀ {μ : Measure (SDEState n)}, IsInvariant P X μ →
      ∫ x, ∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2) ∂μ = ∑ i, p i * lyap C i μ := by
    intro μ hμ
    rw [integral_finset_sum _ fun i _ =>
      (lyap_integrable hn P C B X hfam c γb δ₀ hA hδ hμ i).const_mul (p i)]
    simp only [integral_const_mul, lyap]
  refine ⟨hLint hπ, ?_⟩
  have hcov : (⋃ I ∈ (Finset.univ : Finset (Finset (Fin n))), faceOpen I) = orthant n := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
    exact ⟨fun ⟨I, h⟩ => h.1, fun h => ⟨supp x, mem_faceOpen_supp h⟩⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Finset (Fin n))))
      (faceOpen (n := n)) := fun I _ J _ hIJ =>
    Set.disjoint_iff_inter_eq_empty.2 (faceOpen_disjoint hIJ)
  have hae : ∀ᵐ x ∂π, x ∈ orthant n := by rw [ae_iff]; exact hπ.2.1
  have hint_eq : ∫ x, ∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2) ∂π =
      ∑ I, ∫ x in faceOpen I, ∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2) ∂π := by
    rw [← integral_biUnion_finset Finset.univ (fun I _ => faceOpen_measurableSet I) hdisj
      (fun I _ => (hLint hπ).integrableOn), hcov, Measure.restrict_eq_self_of_ae_mem hae]
  have hface : ∀ I : Finset (Fin n), (π (faceOpen I)).toReal * (2 * ρ) ≤
      ∫ x in faceOpen I, ∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2) ∂π := by
    intro I
    by_cases hI : π (faceOpen I) = 0
    · rw [hI, Measure.restrict_eq_zero.2 hI, integral_zero_measure]; simp
    · have hmem := face_restrict_mem P C B X hfam hA hπ hπo I hI
      have e : π.restrict (faceOpen I) =
          π (faceOpen I) • ((π (faceOpen I))⁻¹ • π.restrict (faceOpen I)) := by
        rw [smul_smul, ENNReal.mul_inv_cancel hI (measure_ne_top _ _), one_smul]
      rw [e, integral_smul_measure, hLeq hmem.1.1, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (h41 _ hmem) ENNReal.toReal_nonneg
  have hsum : ∑ I : Finset (Fin n), (π (faceOpen I)).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun I _ => measure_ne_top _ _),
      ← measure_biUnion_finset hdisj (fun I _ => faceOpen_measurableSet I), hcov,
      (prob_compl_eq_zero_iff orthant_isClosed.measurableSet).1 hπ.2.1, ENNReal.toReal_one]
  calc 2 * ρ = ∑ I : Finset (Fin n), (π (faceOpen I)).toReal * (2 * ρ) := by
        rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun I _ => hface I
    _ = _ := hint_eq.symm

theorem cBracket_contOn (C : Coeffs n) {c : SDEState n} (hc : c ∈ openOrthant n)
    (hf : ∀ i, ContinuousOn (C.f i) (orthant n)) (hg : ∀ i, ContinuousOn (C.g i) (orthant n)) :
    ContinuousOn (cBracket C c) (orthant n) := by
  have hco : ∀ i, Continuous fun x : SDEState n => x i := fun i => PiLp.continuous_apply 2 _ i
  have hD : ContinuousOn (fun x : SDEState n => 1 + ∑ i, c i * x i) (orthant n) :=
    (continuous_const.add (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (hco i))).continuousOn
  have hDpos : ∀ x ∈ orthant n, 0 < 1 + ∑ i, c i * x i := fun x hx => by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_nonneg (hc i).le (hx i)
    linarith
  have h1 : ContinuousOn (fun x : SDEState n => ∑ i, c i * x i * C.f i x) (orthant n) :=
    continuousOn_finsetSum _ fun i _ => (continuousOn_const.mul (hco i).continuousOn).mul (hf i)
  have h2 : ContinuousOn (fun x : SDEState n => ∑ i, ∑ j, C.sig i j * c i * c j * x i * x j *
      C.g i x * C.g j x) (orthant n) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      (((((continuousOn_const.mul continuousOn_const).mul continuousOn_const).mul
        (hco i).continuousOn).mul (hco j).continuousOn).mul (hg i)).mul (hg j)
  exact (h1.div hD fun x hx => (hDpos x hx).ne').sub
    ((continuousOn_const.mul h2).div (hD.pow 2) fun x hx => pow_ne_zero 2 (hDpos x hx).ne')

theorem phi_contOn (C : Coeffs n) {c : SDEState n} (hc : c ∈ openOrthant n) (p : SDEState n)
    (hf : ∀ i, ContinuousOn (C.f i) (orthant n)) (hg : ∀ i, ContinuousOn (C.g i) (orthant n)) :
    ContinuousOn (Phi C c p) (orthant n) :=
  (cBracket_contOn C hc hf hg).sub (continuousOn_finsetSum _ fun i _ =>
    continuousOn_const.mul ((hf i).sub ((continuousOn_const.mul ((hg i).pow 2)).div_const 2)))

theorem phi_growth (C : Coeffs n) {c p : SDEState n} (hc : c ∈ openOrthant n)
    (hp : p ∈ openOrthant n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ orthant n, |Phi C c p x| <
      K * (1 + ∑ i, c i * x i) ^ (0 : ℝ) * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2)) := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  set Pm : ℝ := ∑ i, p i with hPm
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hPm0 : 0 ≤ Pm := Finset.sum_nonneg fun i _ => (hp i).le
  refine ⟨(1 + Pm) * (1 + S), by positivity, fun x hx => ?_⟩
  rw [Real.rpow_zero, mul_one]
  unfold Phi cBracket
  set D : ℝ := 1 + ∑ i, c i * x i with hD
  set F : ℝ := ∑ i, |C.f i x| with hF
  set G : ℝ := ∑ i, C.g i x ^ 2 with hG
  have hu : ∀ i, 0 ≤ c i * x i := fun i => mul_nonneg (hc i).le (hx i)
  have hD1 : 1 ≤ D := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hu i
    linarith
  have hD0 : 0 < D := by linarith
  have hui : ∀ i, c i * x i ≤ D := fun i => by
    have := Finset.single_le_sum (f := fun j => c j * x j) (fun j _ => hu j) (Finset.mem_univ i)
    linarith
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hgi : ∀ i, C.g i x ^ 2 ≤ G := fun i =>
    Finset.single_le_sum (f := fun j => C.g j x ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hgij : ∀ i j, |C.g i x * C.g j x| ≤ G := fun i j => by
    rw [abs_mul]
    have h1 := two_mul_le_add_sq |C.g i x| |C.g j x|
    rw [sq_abs, sq_abs] at h1
    have := hgi i
    have := hgi j
    linarith
  have hsij : ∀ i j, |C.sig i j| ≤ S := fun i j =>
    (Finset.single_le_sum (f := fun j => |C.sig i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, |C.sig i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have t1 : |(∑ i, c i * x i * C.f i x) / D| ≤ F := by
    rw [abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
    calc |∑ i, c i * x i * C.f i x| ≤ ∑ i, |c i * x i * C.f i x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, D * |C.f i x| := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hu i)]
          exact mul_le_mul_of_nonneg_right (hui i) (abs_nonneg _)
      _ = F * D := by rw [← Finset.mul_sum, mul_comm]
  have hsum2 : |∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x| ≤
      S * (G * D ^ 2) := by
    calc _ ≤ ∑ i, |∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |C.sig i j| * (G * D ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            have e : C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x =
                C.sig i j * ((c i * x i) * (c j * x j)) * (C.g i x * C.g j x) := by ring
            rw [e, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hu i), abs_of_nonneg (hu j)]
            have h1 : c i * x i * (c j * x j) ≤ D * D := mul_le_mul (hui i) (hui j) (hu j) hD0.le
            have h3 : 0 ≤ |C.sig i j| := abs_nonneg _
            calc |C.sig i j| * (c i * x i * (c j * x j)) * |C.g i x * C.g j x|
                ≤ |C.sig i j| * (D * D) * G :=
                  mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) (hgij i j) (abs_nonneg _)
                    (by positivity)
              _ = |C.sig i j| * (G * D ^ 2) := by ring
      _ = S * (G * D ^ 2) := by simp only [← Finset.sum_mul, hS]
  have t2 : |(1 / 2) * (∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x) / D ^ 2|
      ≤ S * G := by
    have hD2 : 0 < D ^ 2 := by positivity
    rw [abs_div, abs_of_pos hD2, div_le_iff₀ hD2, abs_mul]
    have : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
    rw [this]
    have h0 := abs_nonneg (∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x)
    nlinarith
  have t3 : |∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2)| ≤ Pm * (F + S * G) := by
    calc _ ≤ ∑ i, |p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, Pm * (|C.f i x| + S * C.g i x ^ 2) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_pos (hp i)]
          have hpi : p i ≤ Pm := Finset.single_le_sum (f := fun j => p j) (fun j _ => (hp j).le)
            (Finset.mem_univ i)
          have h1 : |C.f i x - C.sig i i * C.g i x ^ 2 / 2| ≤ |C.f i x| + S * C.g i x ^ 2 := by
            have h2 := abs_sub (C.f i x) (C.sig i i * C.g i x ^ 2 / 2)
            have h3 : |C.sig i i * C.g i x ^ 2 / 2| ≤ S * C.g i x ^ 2 := by
              rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (C.g i x)), abs_two]
              have := hsij i i
              have := sq_nonneg (C.g i x)
              nlinarith
            linarith
          exact mul_le_mul hpi h1 (abs_nonneg _) hPm0
      _ = Pm * (F + S * G) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hU : 1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2) = 1 + F + G := by
    rw [Finset.sum_add_distrib]
    simp only [sq_abs]
    ring
  rw [hU]
  have a1 := abs_sub ((∑ i, c i * x i * C.f i x) / D -
    (1 / 2) * (∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x) / D ^ 2)
    (∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2))
  have a2 := abs_sub ((∑ i, c i * x i * C.f i x) / D)
    ((1 / 2) * (∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x) / D ^ 2)
  have e : (1 + Pm) * (1 + S) * (1 + F + G) - (F + S * G + Pm * (F + S * G)) =
      (1 + Pm) * (1 + S + S * F + G) := by ring
  have hpos : 0 < (1 + Pm) * (1 + S + S * F + G) := by positivity
  linarith

/-- Tightness from a uniform moment bound with a coercive weight. -/
theorem tight_of_lint {S : Set (Measure (SDEState n))} {W : SDEState n → ℝ} (hWm : Measurable W)
    {Kb : ℝ} (hb : ∀ μ ∈ S, ∫⁻ y, ENNReal.ofReal (W y) ∂μ ≤ ENNReal.ofReal Kb)
    (hgrow : ∀ L : ℝ, ∃ r : ℝ, ∀ μ ∈ S, ∀ᵐ y ∂μ, r < ‖y‖ → L ≤ W y) : IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun μ _ => by rw [htop]; exact le_top⟩
  set e := ε.toReal with he_def
  have he : 0 < e := ENNReal.toReal_pos hε.ne' htop
  set L : ℝ := (|Kb| + 1) / e with hL_def
  have hL : 0 < L := by positivity
  obtain ⟨r, hr⟩ := hgrow L
  refine ⟨Metric.closedBall 0 r, isCompact_closedBall 0 r, fun μ hμ => ?_⟩
  have hsub : (Metric.closedBall (0 : SDEState n) r)ᶜ ≤ᵐ[μ]
      {y | ENNReal.ofReal L ≤ ENNReal.ofReal (W y)} := by
    filter_upwards [hr μ hμ] with y hy hyc
    have hyc' : y ∉ Metric.closedBall (0 : SDEState n) r := hyc
    have : r < ‖y‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hyc'
    exact ENNReal.ofReal_le_ofReal (hy this)
  have hmk := mul_meas_ge_le_lintegral₀ (hWm.ennreal_ofReal.aemeasurable (μ := μ))
    (ENNReal.ofReal L)
  have h1 : μ (Metric.closedBall (0 : SDEState n) r)ᶜ ≤
      μ {y | ENNReal.ofReal L ≤ ENNReal.ofReal (W y)} := measure_mono_ae hsub
  have h2 : μ {y | ENNReal.ofReal L ≤ ENNReal.ofReal (W y)} ≤
      ENNReal.ofReal Kb / ENNReal.ofReal L := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hL).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hmk.trans (hb μ hμ)
  have hKL : Kb / L ≤ e := by
    rw [div_le_iff₀ hL]
    have : e * L = |Kb| + 1 := by rw [hL_def]; field_simp
    linarith [le_abs_self Kb]
  calc μ (Metric.closedBall (0 : SDEState n) r)ᶜ ≤ ENNReal.ofReal Kb / ENNReal.ofReal L :=
        h1.trans h2
    _ = ENNReal.ofReal (Kb / L) := (ENNReal.ofReal_div_of_pos hL).symm
    _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal hKL
    _ = ε := ENNReal.ofReal_toReal htop

theorem occ_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (c : SDEState n) (δ₀ : ℝ)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) {T : ℝ} (hT : 1 < T)
    (hinv : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n)
    (hWm : Measurable fun y => Wt C c δ₀ (posPart y)) (H₂ a A : ℝ) (hH₂ : 0 < H₂)
    (ha0 : 0 ≤ a) (haA : a ≤ A)
    (h38 : ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (Wt C c δ₀ (X x s.toNNReal ω))) ∂P ≤ ENNReal.ofReal (H₂ * (a + T))) :
    ∫⁻ y, ENNReal.ofReal (Wt C c δ₀ (posPart y)) ∂(occMean P X x T) ≤
      ENNReal.ofReal (H₂ * (A + 1)) := by
  have hT0 : 0 < T := by linarith
  rw [occ_lint P X x hm hc T _ hWm.ennreal_ofReal]
  have heq : (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (Wt C c δ₀ (posPart (X x s.toNNReal ω)))) =ᵐ[P]
      (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Wt C c δ₀ (X x s.toNNReal ω))) := by
    filter_upwards [hinv] with ω hω
    simp only [pp_of_mem' (hω _)]
  rw [lintegral_congr_ae heq]
  calc (ENNReal.ofReal T)⁻¹ * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (Wt C c δ₀ (X x s.toNNReal ω))) ∂P
      ≤ (ENNReal.ofReal T)⁻¹ * ENNReal.ofReal (H₂ * (a + T)) := by gcongr
    _ = ENNReal.ofReal (H₂ * (a + T) / T) := by
        rw [ENNReal.ofReal_div_of_pos hT0, ENNReal.div_eq_inv_mul]
    _ ≤ ENNReal.ofReal (H₂ * (A + 1)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_iff₀ hT0]
        have h1 : a ≤ A * T := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hH₂.le]

end L41b
end ItoLib

-- ===== L41c =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L41c
open StochKolmogorov.Persist
variable {n : ℕ}

theorem faceOpen_supp_sub_bdry {x : SDEState n} (hx : x ∈ bdry n) :
    faceOpen (supp x) ⊆ bdry n := by
  intro y hy
  refine ⟨hy.1, fun hyo => hx.2 fun i => ?_⟩
  by_contra hxi
  have hi : i ∉ supp x := by simpa [supp] using hxi
  have h1 := hy.2.1 i hi
  have h2 := hyo i
  rw [h1] at h2
  exact lt_irrefl _ h2

/-- Weak limits of mean occupation measures (`T → ∞`) are invariant (Feller + Markov). -/
theorem occ_limit_inv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (hfel : ∀ (t : ℝ≥0) (h : SDEState n →ᵇ ℝ),
      ContinuousOn (fun x => ∫ ω, h (X x t ω) ∂P) (orthant n))
    (xs : ℕ → SDEState n) (hxo : ∀ k, xs k ∈ orthant n) (Ts : ℕ → ℝ) (hT0 : ∀ k, 0 < Ts k)
    (hTlim : Tendsto Ts atTop atTop)
    (π : Measure (SDEState n)) [IsProbabilityMeasure π] (hπo : π (orthant n)ᶜ = 0)
    (hweak : ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occMean P X (xs k) (Ts k))) atTop (𝓝 (∫ y, h y ∂π))) :
    IsInvariant P X π := by
  haveI hP : IsProbabilityMeasure P := hX.1
  have hsol := hX.2.2
  refine ⟨inferInstance, hπo, fun t A hA' => inv_of_bcf P C B X hX c γb hA hπo t (fun f => ?_) hA'⟩
  have hGc : Continuous fun y => ∫ ω, f (X (posPart y) t ω) ∂P :=
    (hfel t f).comp_continuous pp_cont' pp_mem'
  have hbnd : ∀ (Y : Ω → SDEState n), |∫ ω, f (Y ω) ∂P| ≤ ‖f‖ := fun Y => by
    have := norm_integral_le_of_norm_le_const (μ := P) (C := ‖f‖) (f := fun ω => f (Y ω))
      (ae_of_all _ fun ω => f.norm_coe_le_norm _)
    rw [Real.norm_eq_abs] at this
    simpa using this
  set G : SDEState n →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun y => ∫ ω, f (X (posPart y) t ω) ∂P, hGc⟩ (2 * ‖f‖) (fun y z => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := abs_le.1 (hbnd fun ω => X (posPart y) t ω)
      have h2 := abs_le.1 (hbnd fun ω => X (posPart z) t ω)
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]) with hG
  have hGk : ∀ k, |∫ y, G y ∂(occMean P X (xs k) (Ts k)) -
      ∫ y, f y ∂(occMean P X (xs k) (Ts k))| ≤ 2 * (t : ℝ) * ‖f‖ / Ts k := by
    intro k
    have hx := hxo k
    have hm := (hsol _ hx).1
    have hc := (hsol _ hx).2.1
    set Fu : ℝ → ℝ := fun u => ∫ ω, f (X (xs k) u.toNNReal ω) ∂P with hFu
    have hFc : Continuous Fu := continuous_of_dominated (bound := fun _ => ‖f‖)
      (fun u => (f.continuous.measurable.comp (hm _)).aestronglyMeasurable)
      (fun u => ae_of_all _ fun ω => f.norm_coe_le_norm _) (integrable_const _)
      (ae_of_all _ fun ω => f.continuous.comp ((hc ω).comp continuous_real_toNNReal))
    have hFb : ∀ u, |Fu u| ≤ ‖f‖ := fun u => hbnd fun ω => X (xs k) u.toNNReal ω
    have e1 : ∫ y, G y ∂(occMean P X (xs k) (Ts k)) =
        (Ts k)⁻¹ * ∫ s in Set.Icc (0 : ℝ) (Ts k), Fu (s + t) := by
      rw [occ_integral P X (xs k) hm hc (hT0 k) G.continuous.measurable
        (fun y => hbnd fun ω => X (posPart y) t ω)]
      congr 1
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      have hck := ck_integral P C B X hX c γb hA hx s.toNNReal t f
      show ∫ ω, (∫ ω', f (X (posPart (X (xs k) s.toNNReal ω)) t ω') ∂P) ∂P = Fu (s + t)
      rw [hck, hFu]
      show ∫ ω, f (X (xs k) (s.toNNReal + t) ω) ∂P = ∫ ω, f (X (xs k) (s + (t : ℝ)).toNNReal ω) ∂P
      rw [Real.toNNReal_add hs.1 t.coe_nonneg, Real.toNNReal_coe]
    have e2 : ∫ y, f y ∂(occMean P X (xs k) (Ts k)) =
        (Ts k)⁻¹ * ∫ s in Set.Icc (0 : ℝ) (Ts k), Fu s :=
      occ_integral P X (xs k) hm hc (hT0 k) f.continuous.measurable (fun y => by
        have := f.norm_coe_le_norm y; rwa [Real.norm_eq_abs] at this)
    rw [e1, e2]
    exact tavg_shift hFc hFb (hT0 k) t.coe_nonneg
  have hd : Tendsto (fun k => ∫ y, G y ∂(occMean P X (xs k) (Ts k)) -
      ∫ y, f y ∂(occMean P X (xs k) (Ts k))) atTop (𝓝 0) := by
    have hb : Tendsto (fun k => 2 * (t : ℝ) * ‖f‖ / Ts k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hTlim
    exact squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact hGk k) hb
  have hlimG := hweak G
  have hlimG' : Tendsto (fun k => ∫ y, G y ∂(occMean P X (xs k) (Ts k))) atTop
      (𝓝 (∫ y, f y ∂π)) := by
    have := (hweak f).add hd
    simp only [add_zero] at this
    exact this.congr fun k => by ring
  show ∫ y, G y ∂π = ∫ y, f y ∂π
  exact tendsto_nhds_unique hlimG hlimG'

theorem lemma_4_1_main (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M) (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (p : SDEState n) (hp : p ∈ openOrthant n) (ρ : ℝ) (hρ : 0 < ρ)
    (h41 : ∀ μ ∈ bdryErgodic P X, 2 * ρ ≤ ∑ i, p i * lyap C i μ) :
    ∃ Tstar : ℝ, 0 < Tstar ∧ ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      Integrable (Phi C c p) (occMean P X x T) ∧ ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ := by
  haveI hP : IsProbabilityMeasure P := hX.1
  by_contra hcon
  have hk : ∀ k : ℕ, ∃ T : ℝ, (k : ℝ) + 1 < T ∧ ∃ x, x ∈ bdry n ∧ l1 x ≤ M ∧
      (Integrable (Phi C c p) (occMean P X x T) →
        -ρ < ∫ y, Phi C c p y ∂(occMean P X x T)) := by
    intro k
    by_contra hk
    apply hcon
    refine ⟨(k : ℝ) + 1, by positivity, fun T hT x hx hxM => ?_⟩
    by_contra hbad
    apply hk
    refine ⟨T, hT, x, hx, hxM, fun hi => ?_⟩
    by_contra hle
    exact hbad ⟨hi, not_lt.1 hle⟩
  choose Ts hTs xs hxs using hk
  have hsol := hX.2.2
  have hxo : ∀ k, xs k ∈ orthant n := fun k => (hxs k).1.1
  have hm : ∀ k t, Measurable (X (xs k) t) := fun k => (hsol _ (hxo k)).1
  have hc' : ∀ k ω, Continuous fun t => X (xs k) t ω := fun k => (hsol _ (hxo k)).2.1
  have hT1 : ∀ k, 1 < Ts k := fun k => by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith [hTs k]
  have hT0 : ∀ k, 0 < Ts k := fun k => by linarith [hT1 k]
  have hTlim : Tendsto Ts atTop atTop :=
    tendsto_atTop_mono (fun k => (hTs k).le)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hprob : ∀ k, IsProbabilityMeasure (occMean P X (xs k) (Ts k)) := fun k =>
    occ_prob P X (xs k) (hm k) (hc' k) (hT0 k)
  have hstay : ∀ k, ∀ᵐ ω ∂P, ∀ t, X (xs k) t ω ∈ bdry n := fun k => by
    filter_upwards [kolmogorov_sde_face_invariance C hX.2.1 hA.2.1 (mem_faceOpen_supp (hxo k))
      (hsol _ (hxo k))] with ω hω t
    exact faceOpen_supp_sub_bdry (hxs k).1 (hω t)
  have hnullB : ∀ k, occMean P X (xs k) (Ts k) (bdry n)ᶜ = 0 := fun k =>
    occ_null P X (xs k) (hm k) (hc' k) _ bdry_isClosed.measurableSet (hstay k)
  have hnullO : ∀ k, occMean P X (xs k) (Ts k) (orthant n)ᶜ = 0 := fun k =>
    measure_mono_null (Set.compl_subset_compl.2
      (Set.diff_subset : orthant n \ openOrthant n ⊆ orthant n)) (hnullB k)
  obtain ⟨H₁, H₂, hH₁, hH₂, -, h38, hfel⟩ := lemma_3_2 hn P C B X hX c γb hA δ₀ hδ₀
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hδ0 : 0 < δ₀ := hδ₀.1
  have hfc : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hA.2.1 i).1.continuousOn
  have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hA.2.1 i).2.continuousOn
  have hWc : Continuous fun y => Wt C c δ₀ (posPart y) := Wt_pp_cont C c δ₀ hδ0.le hfc hgc
  have hinvO : ∀ k, ∀ᵐ ω ∂P, ∀ t, X (xs k) t ω ∈ orthant n := fun k =>
    (hstay k).mono fun ω h t => (h t).1
  have hsc0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => (hc i).le
  have hμb : ∀ k, ∫⁻ y, ENNReal.ofReal (Wt C c δ₀ (posPart y)) ∂(occMean P X (xs k) (Ts k)) ≤
      ENNReal.ofReal (H₂ * ((1 + (∑ i, c i) * M) ^ δ₀ + 1)) := by
    intro k
    have hx := hxo k
    have hT := hT1 k
    have hT0' : 0 ≤ Ts k := by linarith
    have h38k := h38 (xs k) hx (Ts k).toNNReal (Real.toNNReal_pos.2 (by linarith))
    rw [Real.coe_toNNReal _ hT0'] at h38k
    refine occ_bound P C c δ₀ X (xs k) (hm k) (hc' k) hT (hinvO k) hWc.measurable H₂ _ _ hH₂
      (Real.rpow_nonneg (by linarith [one_le_W hc hx]) _) ?_ h38k
    apply Real.rpow_le_rpow (by linarith [one_le_W hc hx]) _ hδ0.le
    have : ∑ i, c i * xs k i ≤ (∑ i, c i) * M := by
      calc ∑ i, c i * xs k i ≤ ∑ i, c i * l1 (xs k) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
              ((le_abs_self (xs k i)).trans (Finset.single_le_sum (f := fun j => |xs k j|)
                (fun j _ => abs_nonneg _) (Finset.mem_univ i))) (hc i).le
        _ = (∑ i, c i) * l1 (xs k) := by rw [Finset.sum_mul]
        _ ≤ (∑ i, c i) * M := mul_le_mul_of_nonneg_left (hxs k).2.1 hsc0
    linarith
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fun i => c i)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hm0 : 0 < c i0 := hc i0
  have hpt : ∀ L : ℝ, ∃ r : ℝ, ∀ y ∈ orthant n, r < ‖y‖ → L ≤ Wt C c δ₀ (posPart y) := by
    intro L
    refine ⟨(max L 1) ^ δ₀⁻¹ / c i0, fun y hy hr => ?_⟩
    rw [pp_of_mem' hy]
    have hL1 : 0 ≤ max L 1 := le_trans zero_le_one (le_max_right _ _)
    have hsum : c i0 * ‖y‖ ≤ ∑ i, c i * y i := by
      calc c i0 * ‖y‖ ≤ c i0 * ∑ i, |y i| := mul_le_mul_of_nonneg_left (euc_norm_le_sum' y) hm0.le
        _ = ∑ i, c i0 * y i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [abs_of_nonneg (hy i)]
        _ ≤ ∑ i, c i * y i := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hi0 i (Finset.mem_univ i)) (hy i)
    have h1 : (max L 1) ^ δ₀⁻¹ ≤ 1 + ∑ i, c i * y i := by
      have := (div_lt_iff₀ hm0).1 hr
      nlinarith
    have h2 : max L 1 ≤ (1 + ∑ i, c i * y i) ^ δ₀ := by
      calc max L 1 = ((max L 1) ^ δ₀⁻¹) ^ δ₀ := (Real.rpow_inv_rpow hL1 hδ0.ne').symm
        _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hL1 _) h1 hδ0.le
    unfold Wt
    have hU := one_le_U C y
    have hW0 : 0 ≤ (1 + ∑ i, c i * y i) ^ δ₀ :=
      Real.rpow_nonneg (by linarith [one_le_W hc hy]) _
    have : (1 + ∑ i, c i * y i) ^ δ₀ ≤
        (1 + ∑ i, c i * y i) ^ δ₀ * (1 + ∑ i, (|C.f i y| + |C.g i y| ^ 2)) :=
      le_mul_of_one_le_right hW0 hU
    linarith [le_max_left L 1]
  set μs : ℕ → ProbabilityMeasure (SDEState n) := fun k => ⟨occMean P X (xs k) (Ts k), hprob k⟩
    with hμs
  have hS : IsTightMeasureSet {x | ∃ μ ∈ Set.range μs, (μ : Measure (SDEState n)) = x} := by
    refine tight_of_lint hWc.measurable (Kb := H₂ * ((1 + (∑ i, c i) * M) ^ δ₀ + 1)) ?_ ?_
    · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact hμb k
    · intro L
      obtain ⟨r, hr⟩ := hpt L
      refine ⟨r, ?_⟩
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have hae : ∀ᵐ y ∂(occMean P X (xs k) (Ts k)), y ∈ orthant n := by
        rw [ae_iff]; exact hnullO k
      filter_upwards [hae] with y hy using hr y hy
  obtain ⟨π₀, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hS).tendsto_subseq
    (fun k => subset_closure (Set.mem_range_self k))
  set π : Measure (SDEState n) := (π₀ : Measure (SDEState n)) with hπdef
  haveI hπP : IsProbabilityMeasure π := by rw [hπdef]; infer_instance
  have hweak : ∀ h : SDEState n →ᵇ ℝ, Tendsto
      (fun k => ∫ y, h y ∂(occMean P X (xs (φ k)) (Ts (φ k)))) atTop (𝓝 (∫ y, h y ∂π)) :=
    fun h => (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) h
  have hπB : π (bdry n)ᶜ = 0 := by
    have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim bdry_compl_isOpen
    have h0 : (fun i => ((μs ∘ φ) i : Measure (SDEState n)) (bdry n)ᶜ) = fun _ => 0 :=
      funext fun i => hnullB (φ i)
    rw [h0, liminf_const] at h
    exact nonpos_iff_eq_zero.1 h
  have hπO : π (orthant n)ᶜ = 0 := measure_mono_null (Set.compl_subset_compl.2
    (Set.diff_subset : orthant n \ openOrthant n ⊆ orthant n)) hπB
  have hπo : π (openOrthant n) = 0 := measure_mono_null
    (fun y hy hyb => (show y ∈ orthant n \ openOrthant n from hyb).2 hy) hπB
  have hφT : Tendsto (fun k => Ts (φ k)) atTop atTop := hTlim.comp hφ.tendsto_atTop
  have hπinv : IsInvariant P X π := occ_limit_inv P C B X hX c γb hA hfel (fun k => xs (φ k))
    (fun k => hxo _) (fun k => Ts (φ k)) (fun k => hT0 _) hφT π hπO hweak
  obtain ⟨K, hK0, hgrowth⟩ := phi_growth C hc hp
  obtain ⟨hintk, -, hconv⟩ := lemma_3_4 hn P C B X hX c γb hA M hMpos hM δ₀ hδ₀
    (fun k => xs (φ k)) (fun k => ⟨hxo _, (hxs _).2.1⟩) (fun k => Ts (φ k)) (fun k => hT1 _)
    hφT π hπinv hweak (Phi C c p) (phi_contOn C hc p hfc hgc) K 0 hK0 hδ0 hgrowth
  obtain ⟨-, hcBi, hcB0⟩ := lemma_3_3 hn P C B X hX c γb hA δ₀ hδ₀ H₂ hH₂ h38 π hπinv
  obtain ⟨hLi, hL2⟩ := inv_bdry_lyap hn P C B X hX c γb δ₀ hA hδ₀ p ρ h41 hπinv hπo
  have hPhi : ∫ y, Phi C c p y ∂π = ∫ y, cBracket C c y ∂π -
      ∫ x, ∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2) ∂π := integral_sub hcBi hLi
  have hlow : -ρ ≤ ∫ y, Phi C c p y ∂π :=
    ge_of_tendsto hconv (Eventually.of_forall fun k => ((hxs (φ k)).2.2 (hintk k)).le)
  linarith

end L41c
end ItoLib

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open StochKolmogorov.Persist in
open EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n) (hpδ : l1 p = δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (h41 : IsWeightedInvasionMin P C X p ρ) :
    ∃ Tstar : ℝ, 0 < Tstar ∧ ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      Integrable (Phi C c p) (occMean P X x T) ∧
        ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ := by
  exact ItoLib.lemma_4_1_main hn P C B X hX c γb hA M hMpos hM δ₀ hδ₀ p hp ρ hρ h41.1
