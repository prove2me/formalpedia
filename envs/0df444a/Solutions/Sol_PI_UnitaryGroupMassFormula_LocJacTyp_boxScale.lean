-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.boxScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:07:24.740919+00:00
-- url     : https://prove2.me/submissions/889a2357-c1d1-40b8-b1a7-32f8645d45bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitScale
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_norm_sc
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_box_measure_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution {ι : Type} [Fintype ι] (hfin : Module.finrank F E = 2)
    (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure] (x : ι → Fv F v) (hx : ∀ i, x i ≠ 0) :
    (μ (Set.univ.pi fun i => {c | sc (E := E) v (x i) * c ∈ OEv (E := E) v})).toReal =
      (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (x i) ^ 2)⁻¹ := by
  have hu : ∀ i, IsUnit (sc (E := E) v (x i)) := fun i =>
    (isUnit_iff_ne_zero.2 (hx i)).map (algebraMap (Fv F v) (Fv F v ⊗[F] E))
  rw [BM.box_measure_mul (E := E) v ι μ _ hu]
  simp only [norm_sc v hfin, absV_pow]
end PI.UnitaryGroupMassFormula.LocJacTyp
