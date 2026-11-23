-- Prove2me | solution 1 for P2M_GlobalTheory_Reg_Transfer_vV_zero__d1cc3821e421
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:43.296123+00:00
-- url     : https://prove2.me/submissions/4b055074-f507-42a6-a390-9064c9f9100d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    vV (K' := FractionRing V) V 0 = 0 := by
  simp [vV, valV]
end GlobalTheory.Reg.Transfer
