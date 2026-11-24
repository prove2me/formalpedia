-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_c_invol_cedc9596829d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:47.539019+00:00
-- url     : https://prove2.me/submissions/56760181-c022-487a-87d4-c70fbf7f4705

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_OFam_card_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) :
    c (c x) = x := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) := by
    rw [← Finset.card_pair (Ne.symm hc)]
    exact Finset.card_le_univ _
  have hsq : c ^ 2 = 1 := by
    rw [← le_antisymm hle hge]
    exact pow_card_eq_one
  have := congrArg (fun g : E ≃ₐ[F] E => g x) hsq
  simpa [pow_two] using this
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
