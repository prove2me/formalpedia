-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.BM.isOpen_Ov
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:16.427726+00:00
-- url     : https://prove2.me/submissions/7859a9a6-d3d4-47fd-aa7c-ec4f12efa723

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_mem_Ov

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
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
theorem _root_.solution : IsOpen (Ov v) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Valued.mem_nhds]
  refine ⟨1, fun y hy => ?_⟩
  have hy' : Valued.v (y - x) < 1 := by simpa using hy
  have hx' : Valued.v x ≤ 1 := (mem_Ov v).1 hx
  refine (mem_Ov v).2 ?_
  calc Valued.v y = Valued.v ((y - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (Valued.v (y - x)) (Valued.v x) := Valuation.map_add _ _ _
    _ ≤ 1 := max_le hy'.le hx'
end PI.UnitaryGroupMassFormula.LocJacTyp.BM
