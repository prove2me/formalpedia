-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finrank_eq_add_of_exact_5e4bdf738ebe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:44.358987+00:00
-- url     : https://prove2.me/submissions/5f642c03-9fb5-479c-bfc9-a9fa855ccc8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {A B C : Type*} [AddCommGroup A] [Module (𝓞 K) A] [AddCommGroup B] [Module (𝓞 K) B]
  [AddCommGroup C] [Module (𝓞 K) C] {i : A →ₗ[𝓞 K] B} {p : B →ₗ[𝓞 K] C}
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [Module.Finite (𝓞 K) A] [Module.Finite (𝓞 K) B]
    [Module.Finite (𝓞 K) C] (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) :
    Module.finrank (𝓞 K) B = Module.finrank (𝓞 K) A + Module.finrank (𝓞 K) C := by
  have h1 := rank_quotient_add_rank_of_isDomain (LinearMap.range i)
  have hker : LinearMap.ker p = LinearMap.range i := hex.linearMap_ker_eq
  let e1 : (B ⧸ LinearMap.range i) ≃ₗ[𝓞 K] C :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (p.quotKerEquivOfSurjective hp)
  let e2 : A ≃ₗ[𝓞 K] LinearMap.range i := LinearEquiv.ofInjective i hi
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h1
  norm_cast at h1
  rw [e1.finrank_eq, ← e2.finrank_eq] at h1
  omega
end GroundTheory.Heights₂.Heights
