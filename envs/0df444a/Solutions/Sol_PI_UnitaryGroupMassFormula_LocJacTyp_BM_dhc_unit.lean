-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:42.018563+00:00
-- url     : https://prove2.me/submissions/641d058c-bf1d-4566-8e0a-3fe7b04bb4c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_borel_Fv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_mem_Ov
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_isOpen_Ov
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_isCompact_Ov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped ENNReal NNReal Pointwise
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable [LocallyCompactSpace (Fv F v)]
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
theorem _root_.solution (u : Fv F v) (hu : Valued.v u = 1) (hu0 : u ≠ 0) :
    distribHaarChar (Fv F v) (Units.mk0 u hu0) = 1 := by
  haveI := borel_Fv v
  have hset : (Units.mk0 u hu0) • Ov v = Ov v := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, mem_Ov, mem_Ov]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, map_mul, map_inv₀, hu, inv_one, one_mul]
  have h1 := distribHaarChar_mul (MeasureTheory.Measure.addHaar : Measure (Fv F v))
    (Units.mk0 u hu0) (Ov v)
  rw [hset] at h1
  have h0 : (MeasureTheory.Measure.addHaar : Measure (Fv F v)) (Ov v) ≠ 0 :=
    (isOpen_Ov v).measure_ne_zero _ ⟨0, (mem_Ov v).2 (by simp)⟩
  have htop : (MeasureTheory.Measure.addHaar : Measure (Fv F v)) (Ov v) ≠ ⊤ :=
    (isCompact_Ov v).measure_lt_top.ne
  have h2 : ((distribHaarChar (Fv F v) (Units.mk0 u hu0) : ℝ≥0) : ℝ≥0∞) = 1 := by
    first
    | exact (ENNReal.mul_eq_mul_right h0 htop).mp (by rw [one_mul]; exact h1)
    | exact (ENNReal.mul_left_inj h0 htop).mp (by rw [one_mul]; exact h1)
  exact_mod_cast h2
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
