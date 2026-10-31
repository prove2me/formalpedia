-- Prove2me | solution 1 for Sherlocking.InfoPolicy.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:32:30.080905+00:00
-- url     : https://prove2.me/submissions/9f6b9031-51fd-47ea-b6c4-a858dae35e87

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

open MeasureTheory Sherlocking.InfoPolicy

namespace SherlockL1

variable {K δ r : ℝ}

/-- the platform's gain from entering -/
def gP (K δ r θ : ℝ) : ℝ := δ * (1 - r) * θ - K

lemma pP_eq (b θ : ℝ) : platformPayoff K δ r b θ = r * θ + b * gP K δ r θ := by
  unfold platformPayoff gP; ring

lemma integrable_bdd {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (β : X → ℝ) (hβ : Measurable β) (hβ01 : ∀ x, β x ∈ Set.Icc (0:ℝ) 1) : Integrable β μ :=
  Integrable.of_bound hβ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => by
      have := hβ01 x; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]))

lemma inner_eq {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (β : X → ℝ) (hβ : Measurable β) (hβ01 : ∀ x, β x ∈ Set.Icc (0:ℝ) 1) (θ : ℝ) :
    ∫ x, platformPayoff K δ r (β x) θ ∂μ = r * θ + (∫ x, β x ∂μ) * gP K δ r θ := by
  simp_rw [pP_eq]
  have hi := integrable_bdd μ β hβ hβ01
  rw [integral_add (integrable_const _) (hi.mul_const _), integral_const, integral_mul_const]
  simp

lemma value_eq {X : Type} [MeasurableSpace X] (σ : ℝ → Measure X) (hσ : IsInfoPolicy σ)
    (β : X → ℝ) (hβ : Measurable β) (hβ01 : ∀ x, β x ∈ Set.Icc (0:ℝ) 1) (E : Set ℝ) :
    platformValue K δ r σ β E =
      ∫ θ in E ∩ Set.Icc (0:ℝ) 1, (r * θ + entryProb σ β θ * gP K δ r θ) := by
  unfold platformValue
  congr 1; ext θ
  haveI := hσ.2 θ
  rw [inner_eq (σ θ) β hβ hβ01 θ]; rfl

lemma split (q : ℝ → ℝ) (hq : Measurable q) (hq01 : ∀ θ, q θ ∈ Set.Icc (0:ℝ) 1) (S : Set ℝ)
    (hS : S ⊆ Set.Icc (0:ℝ) 1) (b1 b0 : ℝ) :
    (∫ θ in S, (r * θ + (q θ * b1 + (1 - q θ) * b0) * gP K δ r θ)) =
      (∫ θ in S, r * θ) + b1 * (∫ θ in S, q θ * gP K δ r θ)
        + b0 * ∫ θ in S, (1 - q θ) * gP K δ r θ := by
  have hg : Continuous (gP K δ r) := by unfold gP; fun_prop
  have iq : IntegrableOn q (Set.Icc (0:ℝ) 1) := by
    apply Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne hq.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      have := hq01 x; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2])
  have i1 : IntegrableOn (fun θ => q θ * gP K δ r θ) S :=
    (iq.mul_continuousOn hg.continuousOn isCompact_Icc).mono_set hS
  have i0' : IntegrableOn (fun θ => 1 - q θ) (Set.Icc (0:ℝ) 1) :=
    (integrableOn_const (by simp)).sub iq
  have i0 : IntegrableOn (fun θ => (1 - q θ) * gP K δ r θ) S :=
    (i0'.mul_continuousOn hg.continuousOn isCompact_Icc).mono_set hS
  have ir : IntegrableOn (fun θ : ℝ => r * θ) S :=
    ((continuous_const.mul continuous_id).integrableOn_Icc (a := 0) (b := 1)).mono_set hS
  have e : (fun θ => r * θ + (q θ * b1 + (1 - q θ) * b0) * gP K δ r θ) =
      fun θ => (r * θ + b1 * (q θ * gP K δ r θ)) + b0 * ((1 - q θ) * gP K δ r θ) := by
    ext θ; ring
  rw [e, integral_add (f := fun θ => r * θ + b1 * (q θ * gP K δ r θ))
      (g := fun θ => b0 * ((1 - q θ) * gP K δ r θ))
      (ir.add (i1.const_mul b1)) (i0.const_mul b0),
    integral_add (f := fun θ : ℝ => r * θ)
      (g := fun θ => b1 * (q θ * gP K δ r θ)) ir (i1.const_mul b1),
    integral_const_mul b1, integral_const_mul b0]

/-- the binary signal recommending entry with probability `p θ` -/
noncomputable def binSig (p : ℝ → ℝ) (θ : ℝ) : Measure Bool :=
  ENNReal.ofReal (p θ) • Measure.dirac true + ENNReal.ofReal (1 - p θ) • Measure.dirac false

lemma int_binSig (p : ℝ → ℝ) (hp01 : ∀ θ, p θ ∈ Set.Icc (0:ℝ) 1) (f : Bool → ℝ) (θ : ℝ) :
    ∫ x, f x ∂(binSig p θ) = p θ * f true + (1 - p θ) * f false := by
  have h0 := (hp01 θ).1
  have h1 : 0 ≤ 1 - p θ := by linarith [(hp01 θ).2]
  have : IsFiniteMeasure (ENNReal.ofReal (p θ) • Measure.dirac true) :=
    ⟨by simp [ENNReal.ofReal_lt_top]⟩
  have : IsFiniteMeasure (ENNReal.ofReal (1 - p θ) • Measure.dirac false) :=
    ⟨by simp [ENNReal.ofReal_lt_top]⟩
  unfold binSig
  rw [integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h1, smul_eq_mul, smul_eq_mul]

lemma binSig_info (p : ℝ → ℝ) (hp : Measurable p) (hp01 : ∀ θ, p θ ∈ Set.Icc (0:ℝ) 1) :
    IsInfoPolicy (binSig p) := by
  refine ⟨?_, fun θ => ⟨?_⟩⟩
  · refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp only [binSig, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ((ENNReal.measurable_ofReal.comp hp).mul_const _).add
      ((ENNReal.measurable_ofReal.comp (hp.const_sub 1)).mul_const _)
  · have h0 := (hp01 θ).1
    have h1 : 0 ≤ 1 - p θ := by linarith [(hp01 θ).2]
    simp only [binSig, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add h0 h1]; simp

lemma entry_binSig (p : ℝ → ℝ) (hp01 : ∀ θ, p θ ∈ Set.Icc (0:ℝ) 1) (θ : ℝ) :
    entryProb (binSig p) recommend θ = p θ := by
  unfold entryProb; rw [int_binSig p hp01]; simp [recommend]

lemma entry_meas {X : Type} [MeasurableSpace X] (σ : ℝ → Measure X) (hσ : IsInfoPolicy σ)
    (β : X → ℝ) (hβ : Measurable β) (hβ01 : ∀ x, β x ∈ Set.Icc (0:ℝ) 1) :
    Measurable (entryProb σ β) ∧ ∀ θ, entryProb σ β θ ∈ Set.Icc (0:ℝ) 1 := by
  have e : entryProb σ β = fun θ => (∫⁻ x, ENNReal.ofReal (β x) ∂(σ θ)).toReal := by
    ext θ
    haveI := hσ.2 θ
    unfold entryProb
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => (hβ01 x).1))
      hβ.aestronglyMeasurable]
  refine ⟨?_, fun θ => ?_⟩
  · rw [e]
    exact ENNReal.measurable_toReal.comp
      ((Measure.measurable_lintegral hβ.ennreal_ofReal).comp hσ.1)
  · haveI := hσ.2 θ
    have hi := integrable_bdd (σ θ) β hβ hβ01
    unfold entryProb
    constructor
    · exact integral_nonneg (fun x => (hβ01 x).1)
    · calc (∫ x, β x ∂(σ θ)) ≤ ∫ _x, (1:ℝ) ∂(σ θ) :=
            integral_mono hi (integrable_const _) (fun x => (hβ01 x).2)
        _ = 1 := by simp

end SherlockL1

open SherlockL1 in
theorem solution (K δ r : ℝ) {X : Type} [MeasurableSpace X] (σ : ℝ → Measure X) (β : X → ℝ)
    (E : Set ℝ) (hσ : IsInfoPolicy σ) (hβ : Measurable β) (hβ01 : ∀ x, β x ∈ Set.Icc (0:ℝ) 1)
    (hE : MeasurableSet E) (heq : IsEquilibrium K δ r σ β E) :
    ∃ σ' : ℝ → Measure Bool, IsInfoPolicy σ' ∧ IsEquilibrium K δ r σ' recommend E ∧
      ∀ θ, entryProb σ' recommend θ = entryProb σ β θ := by
  obtain ⟨hpm, hp01⟩ := entry_meas σ hσ β hβ hβ01
  set p := entryProb σ β with hpdef
  have hS : E ∩ Set.Icc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := Set.inter_subset_right
  have hrec : ∀ x, recommend x ∈ Set.Icc (0:ℝ) 1 := by
    intro x; cases x <;> simp [recommend]
  have hentry := entry_binSig p hp01
  -- original equilibrium against the two constant deviations
  have c01 : ∀ c : ℝ, c ∈ Set.Icc (0:ℝ) 1 → ∀ _ : X, c ∈ Set.Icc (0:ℝ) 1 := fun c h _ => h
  have vβ : platformValue K δ r σ β E = (∫ θ in E ∩ Set.Icc (0:ℝ) 1, r * θ) +
      1 * (∫ θ in E ∩ Set.Icc (0:ℝ) 1, p θ * gP K δ r θ)
        + 0 * ∫ θ in E ∩ Set.Icc (0:ℝ) 1, (1 - p θ) * gP K δ r θ := by
    rw [value_eq σ hσ β hβ hβ01 E, ← split p hpm hp01 _ hS]
    congr 1; ext θ; ring
  have vconst : ∀ c : ℝ, c ∈ Set.Icc (0:ℝ) 1 →
      platformValue K δ r σ (fun _ => c) E = (∫ θ in E ∩ Set.Icc (0:ℝ) 1, r * θ) +
      c * (∫ θ in E ∩ Set.Icc (0:ℝ) 1, p θ * gP K δ r θ)
        + c * ∫ θ in E ∩ Set.Icc (0:ℝ) 1, (1 - p θ) * gP K δ r θ := by
    intro c hc
    rw [value_eq σ hσ (fun _ => c) measurable_const (c01 c hc) E, ← split p hpm hp01 _ hS]
    congr 1; ext θ
    haveI := hσ.2 θ
    simp only [entryProb, integral_const, smul_eq_mul, probReal_univ, one_mul]
    ring
  have d0 := heq.platform_opt (fun _ => 0) measurable_const (c01 0 ⟨le_rfl, zero_le_one⟩)
  have d1 := heq.platform_opt (fun _ => 1) measurable_const (c01 1 ⟨zero_le_one, le_rfl⟩)
  rw [vconst 0 ⟨le_rfl, zero_le_one⟩, vβ] at d0
  rw [vconst 1 ⟨zero_le_one, le_rfl⟩, vβ] at d1
  have hJ1 : 0 ≤ ∫ θ in E ∩ Set.Icc (0:ℝ) 1, p θ * gP K δ r θ := by linarith
  have hJ0 : (∫ θ in E ∩ Set.Icc (0:ℝ) 1, (1 - p θ) * gP K δ r θ) ≤ 0 := by linarith
  have vσ' : ∀ β' : Bool → ℝ, (∀ x, β' x ∈ Set.Icc (0:ℝ) 1) →
      platformValue K δ r (binSig p) β' E = (∫ θ in E ∩ Set.Icc (0:ℝ) 1, r * θ) +
      β' true * (∫ θ in E ∩ Set.Icc (0:ℝ) 1, p θ * gP K δ r θ)
        + β' false * ∫ θ in E ∩ Set.Icc (0:ℝ) 1, (1 - p θ) * gP K δ r θ := by
    intro β' hβ'
    rw [value_eq _ (binSig_info p hpm hp01) β' (measurable_of_finite β') hβ' E,
      ← split p hpm hp01 _ hS]
    congr 1; ext θ
    unfold entryProb; rw [int_binSig p hp01]
  refine ⟨binSig p, binSig_info p hpm hp01, ⟨fun θ h1 h2 => ?_, fun θ h1 h2 => ?_, ?_⟩, hentry⟩
  · rw [hentry]; exact heq.seller_in θ h1 h2
  · rw [hentry]; exact heq.seller_out θ h1 h2
  · intro β' _ hβ'
    rw [vσ' β' hβ', vσ' recommend hrec]
    have a1 := hβ' true; have a0 := hβ' false
    simp only [Set.mem_Icc] at a1 a0
    simp only [recommend, if_true, Bool.false_eq_true, if_false]
    nlinarith
