-- Prove2me | solution 1 for P2M_PI_CntNotIntW_t2Space_of_nonarchimedeanLocalField__ad798eed03bb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:20.897256+00:00
-- url     : https://prove2.me/submissions/c8ef5dcb-faed-43e6-9e99-a7df767ef1bb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_DSurjDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_T2SpaceOfNonarchimedeanLocalField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open scoped TensorProduct
open ValuativeRel
namespace PI.CntNotIntW
theorem _root_.solution (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] :
    T2Space Fp := by
  have : T0Space Fp := by
    refine ⟨fun x y hxy => ?_⟩
    by_contra hne
    have hv : valuation Fp (y - x) ≠ 0 :=
      (valuation Fp).ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have hs : {z : Fp | z ≠ y} ∈ nhds x := by
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨Units.mk0 _ hv, ?_⟩
      rintro _ ⟨z, hz, rfl⟩ h
      have h' : x + z = y := h
      have hz' : valuation Fp z < valuation Fp (y - x) := hz
      have hzy : z = y - x := by rw [← h']; ring
      rw [hzy] at hz'
      exact lt_irrefl _ hz'
    rw [hxy.nhds_eq] at hs
    exact (mem_of_mem_nhds hs : y ≠ y) rfl
  infer_instance
end PI.CntNotIntW
