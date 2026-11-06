-- Prove2me | solution 1 for QEC.Coding.ChainComplexData.length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:17.525824+00:00
-- url     : https://prove2.me/submissions/90da9a10-8b35-450d-8a91-966299b0703b

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
import Theorems.Thm_QEC_Coding_ChainComplexData_finrank_middleHomology_eq

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.ChainComplexData
variable {F : Type u} {ι : Type v} {C0 C2 : Type (max u v)} [Field F] [Fintype F]
    [Fintype ι] [AddCommGroup C0] [Module F C0] [AddCommGroup C2] [Module F C2]
namespace QEC.Coding.ChainComplexData
theorem _root_.solution
    {ι κ lambda : Type u} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι)
      (Word (ZMod 2) lambda)) :
    Length (ZMod 2) ι
      - Dimension K.firstCoboundaryCheckCode
      - Dimension K.middleBoundaryCode =
    Module.finrank (ZMod 2) K.middleHomology := by
  have hcycle : Length (ZMod 2) ι - Dimension K.firstCoboundaryCheckCode =
      Dimension K.middleCycleCode := by
    calc
      Length (ZMod 2) ι - Dimension K.firstCoboundaryCheckCode =
          Dimension K.firstCoboundaryCheckCode.dual := by
        rw [LinearCode.dual_dimension_eq_length_sub_dimension]
      _ = Dimension K.middleCycleCode := by
        rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier]
        rw [firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode K]
  rw [hcycle, ← K.finrank_middleHomology_eq]
end QEC.Coding.ChainComplexData
