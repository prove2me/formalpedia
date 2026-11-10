-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryFamily_selected_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:37:50.167211+00:00
-- url     : https://prove2.me/submissions/28769563-310f-484a-b997-1b5b027ac755

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryFamily
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryLength_eq_card
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binarySelectedSites_global_density


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    (binaryLength i : ℚ) / 512 ≤ (binarySelectedSites (f256SourceInput i).PivotComplement).card := by
  rw [binaryLength_eq_card]
  exact binarySelectedSites_global_density _
end QEC.Distillation.Ngu24Binary
