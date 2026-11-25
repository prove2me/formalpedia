-- Prove2me | solution 1 for PI.AprimeInfA.modChar_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:43.695798+00:00
-- url     : https://prove2.me/submissions/275e0c82-5612-41d8-908e-bf9fd57fadc1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Theorems.Thm_PI_AprimeInfA_measurable_modChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfA
open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.AprimeInfA
theorem _root_.solution (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (k : H) : Measure.modularCharacterFun (k : G) = 1 := by

  haveI : MeasurableMul H := by
    first
    | infer_instance
    | exact ⟨fun c => ((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk,
        fun c => ((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk⟩
  obtain ⟨D, hD⟩ : ∃ D : H → ℝ, ∀ h, D h = (Measure.modularCharacterFun (h : G) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hDm : Measurable D := by
    rw [show D = fun h : H => (Measure.modularCharacterFun (h : G) : ℝ) from funext hD]
    exact measurable_coe_nnreal_real.comp
      ((measurable_coe_nnreal_ennreal_iff.1 measurable_modChar).comp measurable_subtype_coe)
  have hmul : ∀ a b : H, D (a * b) = D a * D b := by
    intro a b
    have e : Measure.modularCharacterFun ((a : G) * b) =
        Measure.modularCharacterFun (a : G) * Measure.modularCharacterFun (b : G) :=
      map_mul (Measure.modularCharacter (G := G)) (a : G) (b : G)
    rw [hD, hD, hD, Subgroup.coe_mul, e, NNReal.coe_mul]
  have hone : D 1 = 1 := by
    have e : Measure.modularCharacterFun (1 : G) = 1 := map_one (Measure.modularCharacter (G := G))
    rw [hD, OneMemClass.coe_one, e, NNReal.coe_one]
  have hpos : ∀ a : H, 0 < D a := by
    intro a
    have e : D a * D a⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    have hne0 : D a ≠ 0 := left_ne_zero_of_mul_eq_one e
    rw [hD] at hne0 ⊢
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hne0)
  by_contra hne
  have hc : D k ≠ 1 := by
    intro e
    rw [hD] at e
    exact hne (by exact_mod_cast e)
  obtain ⟨t, ht_def⟩ : ∃ t, t = Real.log (D k) := ⟨_, rfl⟩
  have ht : t ≠ 0 := by
    intro e
    rw [ht_def] at e
    rcases Real.log_eq_zero.1 e with h | h | h
    · exact (hpos k).ne' h
    · exact hc h
    · linarith [hpos k]
  have hinv : D k⁻¹ = (D k)⁻¹ := by
    have e := hmul k⁻¹ k
    rw [inv_mul_cancel, hone] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have hN : ∀ h : H, ⌊Real.log (D (k⁻¹ * h)) / t⌋ = ⌊Real.log (D h) / t⌋ - 1 := by
    intro h
    have e2 : Real.log (D (k⁻¹ * h)) / t = Real.log (D h) / t - 1 := by
      rw [hmul, hinv, Real.log_mul (inv_ne_zero (hpos k).ne') (hpos h).ne', Real.log_inv, ← ht_def,
        add_div, neg_div, div_self ht]
      ring
    rw [e2, Int.floor_sub_one]
  have hA : ∀ m : ℤ, ν {h : H | ⌊Real.log (D h) / t⌋ = m + 1} =
      ν {h : H | ⌊Real.log (D h) / t⌋ = m} := by
    intro m
    have e : {h : H | ⌊Real.log (D h) / t⌋ = m + 1} =
        (fun h => k⁻¹ * h) ⁻¹' {h : H | ⌊Real.log (D h) / t⌋ = m} := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hN]
      constructor <;> intro hh <;> omega
    rw [e, measure_preimage_mul]
  have hall : ∀ m : ℤ, ν {h : H | ⌊Real.log (D h) / t⌋ = m} =
      ν {h : H | ⌊Real.log (D h) / t⌋ = 0} := by
    intro m
    induction m using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hA, ih]
    | pred n ih => rw [← ih, ← hA, sub_add_cancel]
  have hU : (⋃ m : ℤ, {h : H | ⌊Real.log (D h) / t⌋ = m}) = Set.univ := by
    ext h
    simp
  have hdisj : Pairwise (Function.onFun Disjoint fun m : ℤ => {h : H | ⌊Real.log (D h) / t⌋ = m}) := by
    intro i j hij
    exact Set.disjoint_left.2 (fun h hi hj => hij (hi.symm.trans hj))
  have hmeas : ∀ m : ℤ, MeasurableSet {h : H | ⌊Real.log (D h) / t⌋ = m} := fun m =>
    (Int.measurable_floor.comp ((Real.measurable_log.comp hDm).div_const t))
      (measurableSet_singleton m)
  have htot : ν univ = ∑' _m : ℤ, ν {h : H | ⌊Real.log (D h) / t⌋ = 0} := by
    rw [← hU, measure_iUnion hdisj hmeas]
    exact tsum_congr hall
  by_cases hz : ν {h : H | ⌊Real.log (D h) / t⌋ = 0} = 0
  · rw [hz, tsum_zero] at htot
    exact h0 htot
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero hz] at htot
    exact hfin htot
end PI.AprimeInfA
