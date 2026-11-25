-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_norm_jB_63d3a4e60aa1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:59.802073+00:00
-- url     : https://prove2.me/submissions/cfce6739-a2c4-488c-be6b-b71e7befb15b

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_repr_jB_8730e632e624
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
variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (x : Fin n → K) : ‖jB σ b x‖ = Real.sqrt (∑ i, ‖σ (x i)‖ ^ 2) := by
  rw [← b.repr.norm_map, EuclideanSpace.norm_eq]
  simp only [repr_jB]
end Formalism.BasicNotions.Examples₂.NZ
