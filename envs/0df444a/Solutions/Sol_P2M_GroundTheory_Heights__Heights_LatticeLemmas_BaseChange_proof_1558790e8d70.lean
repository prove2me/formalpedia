-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_BaseChange_proof_1558790e8d70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:03:47.146255+00:00
-- url     : https://prove2.me/submissions/26451e1f-0278-4a8b-b4ef-00957b3135db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_baseChange_968fd6092864
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_tensor_integers_9dd4231f1425
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_sum_comp_algebraMap_c5de2bfea3bb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct ComplexAt GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace BaseChange
theorem _root_.solution : BaseChange.Statement := by
  intro K _ _ L _ _ _ M
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  set N := Submodule.span (𝓞 K) (Set.range s)
  have hrank : Module.finrank (𝓞 L) (𝓞 L ⊗[𝓞 K] M.carrier) = Module.finrank (𝓞 K) M.carrier :=
    (TensorProduct.isBaseChange (𝓞 K) M.carrier (𝓞 L)).finrank_eq

  let b : Module.Basis (Fin (Module.finrank (𝓞 K) M.carrier)) (𝓞 K) N := Module.Basis.span hs
  let bL := Algebra.TensorProduct.basis (𝓞 L) b
  let f : 𝓞 L ⊗[𝓞 K] N →ₗ[𝓞 L] 𝓞 L ⊗[𝓞 K] M.carrier :=
    AlgebraTensorModule.lTensor (𝓞 L) (𝓞 L) N.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
  have hfb : (f ∘ bL) = fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i := by
    funext i
    simp only [Function.comp_apply, bL, f, b, Algebra.TensorProduct.basis_apply,
      AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  have ht : LinearIndependent (𝓞 L) (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) := by
    rw [← hfb]
    exact bL.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hspan : Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) =
      LinearMap.range f := by
    rw [LinearMap.range_eq_map, ← bL.span_eq, Submodule.map_span, ← Set.range_comp, hfb]

  have hfin : Finite (M.carrier ⧸ N) := finite_quotient_span hs (Fintype.card_fin _)
  have hidx : Nat.card ((𝓞 L ⊗[𝓞 K] M.carrier) ⧸
      Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i)) =
      Nat.card (M.carrier ⧸ N) ^ Module.finrank K L := by
    rw [hspan, ← card_tensor_integers L]
    exact Nat.card_congr (AlgebraTensorModule.tensorQuotientEquiv (𝓞 L) (𝓞 K) (𝓞 L) N).toEquiv.symm

  have hn : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  show arithDegree (M.metric.baseChange L) / Module.finrank ℚ L =
    arithDegree M.metric / Module.finrank ℚ K
  rw [arithDegree_eq (M.metric.baseChange L) ht (by rw [Fintype.card_fin]; exact hrank.symm),
    arithDegree_eq M.metric hs (Fintype.card_fin _), ← Module.finrank_mul_finrank ℚ K L]
  simp only [degreeWith, gramDet_baseChange]
  rw [hidx, sum_comp_algebraMap L (fun σ ↦ Real.log (gramDet M.metric σ s)), Nat.cast_pow,
    Real.log_pow, Nat.cast_mul]
  field_simp
  ring
end BaseChange
end GroundTheory.Heights₂.Heights.LatticeLemmas
