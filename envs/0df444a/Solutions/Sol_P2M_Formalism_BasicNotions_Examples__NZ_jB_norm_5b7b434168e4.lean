-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_jB_norm_5b7b434168e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:04.280992+00:00
-- url     : https://prove2.me/submissions/4ce59f58-93e6-4873-ba95-46a31b0db537

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_norm_jB_63d3a4e60aa1
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_fcoord_stdF_248b5eb06528
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
theorem _root_.solution (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (stdH K n).b (stdH K n).X (InfinitePlace.mk σ) x = ‖jB σ b x‖ := by
  rw [norm_jB]
  show Real.sqrt (∑ i, ‖Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) (fun _ => 1) _ x i‖ ^ 2) = _
  simp only [fcoord_stdF, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
end Formalism.BasicNotions.Examples₂.NZ
