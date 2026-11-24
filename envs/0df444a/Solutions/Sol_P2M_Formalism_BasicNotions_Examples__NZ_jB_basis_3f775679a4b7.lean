-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_jB_basis_3f775679a4b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:59.850944+00:00
-- url     : https://prove2.me/submissions/15ed57f6-8ed3-42a5-a030-9de3a8118da1

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_single_5e18f8ca6be9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution : LinearIndependent ℂ (fun i => jB σ b ((stdH K n).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jB σ b ((stdH K n).b i))) = ⊤ := by
  have h : (fun i => jB σ b ((stdH K n).b i)) = b := funext fun i => jB_single σ b i
  rw [h]
  exact ⟨b.orthonormal.linearIndependent, by
    have := b.toBasis.span_eq
    rwa [b.coe_toBasis] at this⟩
end Formalism.BasicNotions.Examples₂.NZ
