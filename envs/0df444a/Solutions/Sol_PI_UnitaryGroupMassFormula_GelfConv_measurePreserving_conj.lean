-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfConv.measurePreserving_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:22.59177+00:00
-- url     : https://prove2.me/submissions/5a88ab35-08ad-4e42-a983-4cbebf4e92af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_Unimod
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_measurePreserving_of_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfConv
open MeasureTheory Measure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.GelfConv
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (h : G) :
    MeasurePreserving (fun x => h * x * h⁻¹) μ μ := by
  let c : G →* G :=
    { toFun := fun x => h * x * h⁻¹
      map_one' := by simp
      map_mul' := fun x y => by group }
  exact measurePreserving_of_hom μ c (by simp only [c, MonoidHom.coe_mk, OneHom.coe_mk]; fun_prop)
    (fun y => ⟨h⁻¹ * y * h, by simp only [c, MonoidHom.coe_mk, OneHom.coe_mk]; group⟩)
end PI.UnitaryGroupMassFormula.GelfConv
