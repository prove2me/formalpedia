-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_fcoord_stdF_248b5eb06528
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:33.704451+00:00
-- url     : https://prove2.me/submissions/27b0292b-5951-41cc-9c51-5153f31f27f9

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (v : InfinitePlace K) (x : Fin n → K) (i : Fin n) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v x i =
      v.embedding (x i) := by
  simp [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt]
end Formalism.BasicNotions.Examples₂.NZ
