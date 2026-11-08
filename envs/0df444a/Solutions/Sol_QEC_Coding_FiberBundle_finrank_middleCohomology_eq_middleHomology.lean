-- Prove2me | solution 1 for QEC.Coding.FiberBundle.finrank_middleCohomology_eq_middleHomology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:38:27.875963+00:00
-- url     : https://prove2.me/submissions/770e46d6-4ed0-4ba1-8f48-33b0ee2e5ea6

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
import Theorems.Thm_QEC_Coding_ChainComplexData_length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {ι κ lambda : Type u} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι)
      (Word (ZMod 2) lambda)) :
    Module.finrank (ZMod 2) K.middleCohomology =
      Module.finrank (ZMod 2) K.middleHomology := by
  have hQuotient :=
    K.middleCoboundaryInCocycles.finrank_quotient_add_finrank
  have hDenominator :
      Module.finrank (ZMod 2) K.middleCoboundaryInCocycles =
        Dimension K.firstCoboundaryCheckCode := by
    rw [Dimension_eq_finrank_carrier]
    exact K.middleCoboundaryInCocyclesEquiv.finrank_eq
  have hCocycle :
      Module.finrank (ZMod 2) K.middleCocycleCode.carrier =
        Length (ZMod 2) ι - Dimension K.middleBoundaryCode := by
    calc
      Module.finrank (ZMod 2) K.middleCocycleCode.carrier =
          Dimension K.middleBoundaryCode.dual := by
        rw [Dimension_eq_finrank_carrier]
        rw [K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
      _ = Length (ZMod 2) ι - Dimension K.middleBoundaryCode :=
        K.middleBoundaryCode.dual_dimension_eq_length_sub_dimension
  have hHomology :=
    K.length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
  rw [hDenominator, hCocycle] at hQuotient
  have hCohomology := Nat.eq_sub_of_add_eq hQuotient
  calc
    Module.finrank (ZMod 2) K.middleCohomology =
        (Length (ZMod 2) ι - Dimension K.middleBoundaryCode) -
          Dimension K.firstCoboundaryCheckCode := hCohomology
    _ = Length (ZMod 2) ι -
        (Dimension K.middleBoundaryCode +
          Dimension K.firstCoboundaryCheckCode) := by
      rw [Nat.sub_sub]
    _ = Length (ZMod 2) ι -
        (Dimension K.firstCoboundaryCheckCode +
          Dimension K.middleBoundaryCode) := by
      rw [Nat.add_comm]
    _ = (Length (ZMod 2) ι -
          Dimension K.firstCoboundaryCheckCode) -
        Dimension K.middleBoundaryCode := by
      rw [Nat.sub_sub]
    _ = Module.finrank (ZMod 2) K.middleHomology := hHomology
end QEC.Coding.FiberBundle
