-- Prove2me | solution 1 for RiskFunctionals.MultiPeriod.dual_extension_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:59:46.236934+00:00
-- url     : https://prove2.me/submissions/72cb5704-0b4e-4153-a713-8e05fdfe95c9

import Mathlib
import Definitions.Def_RiskFunctionals_MultiPeriod_DualExtension

open RiskFunctionals.MultiPeriod

open MeasureTheory

theorem g79t_iInf_add {ι : Type*} (S : Set ι) (f : ι → EReal) (c : ℝ) :
    ⨅ i ∈ S, ((c : EReal) + f i) = (c : EReal) + ⨅ i ∈ S, f i := by
  apply le_antisymm
  · have h1 : ((-c : ℝ) : EReal) + ⨅ i ∈ S, ((c : EReal) + f i) ≤ ⨅ i ∈ S, f i :=
      le_iInf₂ fun i hi => by
        calc _ ≤ ((-c : ℝ) : EReal) + ((c : EReal) + f i) := add_le_add le_rfl (iInf₂_le i hi)
          _ = f i := by rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
    calc ⨅ i ∈ S, ((c : EReal) + f i)
        = (c : EReal) + (((-c : ℝ) : EReal) + ⨅ i ∈ S, ((c : EReal) + f i)) := by
          rw [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add]
      _ ≤ _ := add_le_add le_rfl h1
  · exact le_iInf₂ fun i hi => add_le_add le_rfl (iInf₂_le i hi)

theorem g79t_pull {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0) {P : Measure[m0] Ω}
    [IsProbabilityMeasure P] {p q : ENNReal} [p.HolderConjugate q]
    (Y : Lp ℝ p P) (Z : Lp ℝ q P) (hY : AEStronglyMeasurable[m] (Y : Ω → ℝ) P)
    (hZ : P[(Z : Ω → ℝ)|m] =ᵐ[P] fun _ => (1 : ℝ)) :
    ∫ ω, (Y : Ω → ℝ) ω * (Z : Ω → ℝ) ω ∂P = ∫ ω, (Y : Ω → ℝ) ω ∂P := by
  have hq : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  have hYZ : Integrable ((Y : Ω → ℝ) * (Z : Ω → ℝ)) P := (Lp.memLp Y).integrable_mul (Lp.memLp Z)
  have hZi : Integrable (Z : Ω → ℝ) P := (Lp.memLp Z).integrable hq
  calc ∫ ω, (Y : Ω → ℝ) ω * (Z : Ω → ℝ) ω ∂P
      = ∫ ω, ((Y : Ω → ℝ) * (Z : Ω → ℝ)) ω ∂P := rfl
    _ = ∫ ω, (P[(Y : Ω → ℝ) * (Z : Ω → ℝ)|m]) ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, ((Y : Ω → ℝ) * P[(Z : Ω → ℝ)|m]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_aestronglyMeasurable_left hY hYZ hZi)
    _ = ∫ ω, (Y : Ω → ℝ) ω ∂P := integral_congr_ae (hZ.mono fun ω hω => by
        simp only [Pi.mul_apply, hω, mul_one])

theorem g79t_int_one {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0) {P : Measure[m0] Ω}
    [IsProbabilityMeasure P] (Z : Ω → ℝ)
    (hZ : P[Z|m] =ᵐ[P] fun _ => (1 : ℝ)) : ∫ ω, Z ω ∂P = 1 := by
  rw [← integral_condExp hm, integral_congr_ae hZ]; simp

theorem solution {Ω : Type*} (m₁ : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    (hm₁ : m₁ ≤ m0) (P : Measure Ω) [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)]
    [p.HolderConjugate q] (A : Lp ℝ q P → EReal) :
    IsInformationMonotoneSP (fun m (Y : Lp ℝ p P) => dualExtension A m Y) ∧
    (∀ Y : Lp ℝ p P, dualForm A Y = dualExtension A ⊥ Y) ∧
    (IsIsotonicCCD A →
      ∀ Y : Lp ℝ p P, Y ∈ lpMeas ℝ ℝ m₁ p P →
        dualExtension A m₁ Y = ((∫ ω, (Y : Ω → ℝ) ω ∂P : ℝ) : EReal) - A (Lp.const q P 1)) ∧
    (∀ Y C : Lp ℝ p P, C ∈ lpMeas ℝ ℝ m₁ p P →
        dualExtension A m₁ (Y + C) =
          ((∫ ω, (C : Ω → ℝ) ω ∂P : ℝ) : EReal) + dualExtension A m₁ Y) := by
  have hq : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m' m'' hle hm Y
    unfold dualExtension
    apply biInf_mono
    rintro Z ⟨hA, hc⟩
    refine ⟨hA, ?_⟩
    have h1 := (condExp_condExp_of_le (μ := P) (f := (Z : Ω → ℝ)) hle hm).symm
    refine (h1.trans (condExp_congr_ae hc)).trans ?_
    rw [condExp_const (hle.trans hm)]
  · intro Y
    unfold dualForm dualExtension
    refine iInf_congr fun Z => iInf_congr_Prop ?_ fun _ => rfl
    simp only [Set.mem_setOf_eq]
    rw [condExp_bot]
    refine and_congr_right fun _ => ⟨fun h => Filter.Eventually.of_forall fun _ => h,
      fun h => ?_⟩
    obtain ⟨_, h'⟩ := h.exists
    exact h'
  · intro hiso Y hY
    have hYm : AEStronglyMeasurable[m₁] (Y : Ω → ℝ) P := mem_lpMeas_iff_aestronglyMeasurable.1 hY
    unfold dualExtension
    have hval : ∀ Z ∈ {Z : Lp ℝ q P | Z ∈ supergradientSet A ∧
        condExp m₁ P (Z : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ)},
        ((∫ ω, (Y : Ω → ℝ) ω * (Z : Ω → ℝ) ω ∂P : ℝ) : EReal) - A Z
          = ((∫ ω, (Y : Ω → ℝ) ω ∂P : ℝ) : EReal) - A Z := by
      intro Z hZ
      rw [g79t_pull hm₁ Y Z hYm hZ.2]
    rw [iInf_congr fun Z => iInf_congr fun hZ => hval Z hZ]
    have hc1 : P[(Lp.const q P (1 : ℝ) : Ω → ℝ)|m₁] =ᵐ[P] fun _ => (1 : ℝ) := by
      refine (condExp_congr_ae (Lp.coeFn_const q P (1 : ℝ))).trans ?_
      rw [show (Function.const Ω (1 : ℝ)) = fun _ => (1 : ℝ) from rfl, condExp_const hm₁]
    have hle : ∀ Z ∈ {Z : Lp ℝ q P | Z ∈ supergradientSet A ∧
        condExp m₁ P (Z : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ)}, A Z ≤ A (Lp.const q P 1) := by
      intro Z hZ
      apply hiso
      intro U hU hi1 hi2
      have hZi : Integrable (Z : Ω → ℝ) P := (Lp.memLp Z).integrable hq
      have hJ := hU.le_map_integral (hU.continuousOn isOpen_univ) isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hZi hi1
      rw [g79t_int_one hm₁ _ hZ.2] at hJ
      have h2 : ∫ ω, U ((Lp.const q P (1 : ℝ) : Ω → ℝ) ω) ∂P = U 1 := by
        rw [integral_congr_ae ((Lp.coeFn_const q P (1 : ℝ)).mono fun ω h => by rw [h])]
        simp
      rw [h2]; exact hJ
    apply le_antisymm
    · by_cases h1 : ⊥ < A (Lp.const q P 1)
      · exact iInf₂_le (Lp.const q P 1) ⟨h1, hc1⟩
      · rw [not_lt, le_bot_iff] at h1
        rw [h1]; simp
    · exact le_iInf₂ fun Z hZ => EReal.sub_le_sub le_rfl (hle Z hZ)
  · intro Y C hC
    have hCm : AEStronglyMeasurable[m₁] (C : Ω → ℝ) P := mem_lpMeas_iff_aestronglyMeasurable.1 hC
    unfold dualExtension
    have hval : ∀ Z ∈ {Z : Lp ℝ q P | Z ∈ supergradientSet A ∧
        condExp m₁ P (Z : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ)},
        ((∫ ω, ((Y + C : Lp ℝ p P) : Ω → ℝ) ω * (Z : Ω → ℝ) ω ∂P : ℝ) : EReal) - A Z
          = ((∫ ω, (C : Ω → ℝ) ω ∂P : ℝ) : EReal) +
            (((∫ ω, (Y : Ω → ℝ) ω * (Z : Ω → ℝ) ω ∂P : ℝ) : EReal) - A Z) := by
      intro Z hZ
      have hsum : ∫ ω, ((Y + C : Lp ℝ p P) : Ω → ℝ) ω * (Z : Ω → ℝ) ω ∂P
          = ∫ ω, (Y : Ω → ℝ) ω * (Z : Ω → ℝ) ω ∂P + ∫ ω, (C : Ω → ℝ) ω ∂P := by
        rw [← g79t_pull hm₁ C Z hCm hZ.2]
        rw [← integral_add (f := fun ω => (Y : Ω → ℝ) ω * (Z : Ω → ℝ) ω)
          (g := fun ω => (C : Ω → ℝ) ω * (Z : Ω → ℝ) ω) ((Lp.memLp Y).integrable_mul (Lp.memLp Z))
          ((Lp.memLp C).integrable_mul (Lp.memLp Z))]
        refine integral_congr_ae ((Lp.coeFn_add Y C).mono fun ω h => ?_)
        simp only [Pi.add_apply] at h ⊢
        rw [h]; ring
      rw [hsum, EReal.coe_add, sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_comm, add_assoc]
      congr 1
      rw [add_comm]
    rw [iInf_congr fun Z => iInf_congr fun hZ => hval Z hZ, g79t_iInf_add]
