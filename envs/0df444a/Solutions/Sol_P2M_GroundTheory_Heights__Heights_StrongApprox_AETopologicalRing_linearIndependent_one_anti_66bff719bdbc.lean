-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_linearIndependent_one_anti_66bff719bdbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:20:20.483516+00:00
-- url     : https://prove2.me/submissions/3627d7bc-2443-4c26-adce-7591afc2e426

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAETopologicalRing
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
omit [NumberField F]
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace AETopologicalRing
theorem _root_.solution (c : E ≃ₐ[F] E) {δ : E} (hδ : c δ = -δ)
    (h0 : δ ≠ 0) : LinearIndependent F ![(1 : E), δ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  have h' := congrArg c hst
  simp only [map_add, map_mul, AlgEquiv.commutes, hδ, map_zero] at h'
  have ht : algebraMap F E t = 0 := by
    have : (2 * δ) * algebraMap F E t = 0 := by linear_combination hst - h'
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero h0)
  have ht' : t = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).1 ht
  subst ht'
  simp only [map_zero, zero_mul, add_zero] at hst
  exact ⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 hst, rfl⟩
end AETopologicalRing
end GroundTheory.Heights₂.Heights.StrongApprox
