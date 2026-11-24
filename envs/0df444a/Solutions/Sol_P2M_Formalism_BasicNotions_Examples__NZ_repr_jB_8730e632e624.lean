-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_repr_jB_8730e632e624
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:18:51.237888+00:00
-- url     : https://prove2.me/submissions/1b8855ce-bb32-4eac-8df5-2031e8f694c8

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_apply_eaf8db158c18
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
theorem _root_.solution (x : Fin n → K) (i : Fin n) : b.repr (jB σ b x) i = σ (x i) := by
  rw [jB_apply, map_sum, WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, b.repr_self]; simp
  · intro k _ hk
    rw [map_smul, b.repr_self]; simp [hk]
  · simp
end Formalism.BasicNotions.Examples₂.NZ
