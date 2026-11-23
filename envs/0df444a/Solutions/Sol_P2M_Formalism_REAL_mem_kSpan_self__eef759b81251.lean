-- Prove2me | solution 1 for P2M_Formalism_REAL_mem_kSpan_self__eef759b81251
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:52.642393+00:00
-- url     : https://prove2.me/submissions/801990f4-a27e-4140-95fe-2079fba72646

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution : u ∈ kSpan ε E u := by
  unfold kSpan
  exact Submodule.mem_sInf.mpr fun S hS => hS.1
end Formalism.REAL
