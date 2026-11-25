-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:35:47.242801+00:00
-- url     : https://prove2.me/submissions/8e348b2c-4619-44db-99dc-87f0f9e8f165

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_dhc_unif
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_dhc_unit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped ENNReal NNReal Pointwise
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
section Char
variable [LocallyCompactSpace (Fv F v)]
private theorem exists_unif_lemma : ∃ ϖ : Fv F v, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer F v
  exact ⟨(π : Fv F v), by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]⟩
private theorem exp_zpow_lemma_2 (k : ℤ) :
    (WithZero.exp (-1 : ℤ)) ^ k = WithZero.exp (-k) := by
  have hne : (WithZero.exp (-1 : ℤ)) ≠ 0 := by
    first
    | exact WithZero.exp_ne_zero
    | exact WithZero.coe_ne_zero
  refine Int.induction_on k ?_ (fun i ih => ?_) (fun i ih => ?_)
  · simp [WithZero.exp_zero]
  · rw [zpow_add_one₀ hne, ih, ← WithZero.exp_add]
    congr 1
    ring
  · rw [zpow_sub_one₀ hne, ih, ← WithZero.exp_neg, ← WithZero.exp_add]
    congr 1
    ring
end Char
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped ENNReal NNReal Pointwise
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable [LocallyCompactSpace (Fv F v)]
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
theorem _root_.solution (a : Fv F v) (ha : a ≠ 0) :
    PI.NglqJacSplitW.modF (Fv F v) a = ENNReal.ofReal (absV v a) := by
  obtain ⟨ϖ, hϖ⟩ := exists_unif_lemma v
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    first
    | exact WithZero.exp_ne_zero hϖ.symm
    | exact WithZero.coe_ne_zero hϖ.symm
  have hva : Valued.v a ≠ 0 := by
    first
    | exact (map_ne_zero _).mpr ha
    | exact (Valuation.ne_zero_iff _).mpr ha
  unfold PI.NglqJacSplitW.modF PI.LocJacTyp.absV
  simp only [dif_neg ha, dif_neg hva]
  obtain ⟨m, hm, hmdef⟩ : ∃ m : ℤ, Valued.v a = WithZero.exp m ∧
      Multiplicative.toAdd (WithZero.unzero hva) = m :=
    ⟨_, (WithZero.coe_unzero hva).symm, rfl⟩
  rw [hmdef]
  have hW : Valued.v ((Units.mk0 a ha * (Units.mk0 ϖ hϖ0) ^ m : (Fv F v)ˣ) : Fv F v) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0, map_mul,
      map_zpow₀, hϖ, exp_zpow_lemma_2, hm, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hsplit : Units.mk0 a ha =
      (Units.mk0 a ha * (Units.mk0 ϖ hϖ0) ^ m) * (Units.mk0 ϖ hϖ0) ^ (-m) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have h1 := dhc_unit v _ hW (Units.ne_zero _)
  rw [Units.mk0_val] at h1
  have h2 := dhc_unif v ϖ hϖ hϖ0
  rw [hsplit, map_mul, map_zpow, h1, h2, one_mul, inv_zpow', neg_neg, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  all_goals first
    | norm_cast
    | simp
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
