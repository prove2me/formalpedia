-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chart_form_7a9a4f7ad469
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:36.749586+00:00
-- url     : https://prove2.me/submissions/f60328f2-9bc0-48c9-8890-0f0f6d279c9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_vdeg_add_4f8428746a98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chartMonoZ_homog_94b18e153b90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_chartMonoZ_7388c339ad0d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) {u : Ω} (hu : u ∈ chartRing O (segreVec y) c) :
    ∃ (n : ℕ) (U : MRing (bundleIdx (bundleIdx ι M) M') O), IsMultiHomog U (vdeg fun _ => n) ∧
      aeval (pairProjCoord y e φ φ' t) U = algebraMap Ω Φ (u * segreVec y c ^ n) := by
  have hQ : ∀ (j : ∀ k, ι k) (n : ℕ), aeval (pairProjCoord y e φ φ' t) (chartMonoZ O M M' j (fun _ => n)) =
      algebraMap Ω Φ (segreVec y j ^ n) := by
    intro j n
    rw [aeval_chartMonoZ, segreVec, Finset.prod_pow]
  have hlift : ∀ n n' : ℕ, vdeg (K := K) (fun _ => n + n') = vdeg (fun _ => n) + vdeg (fun _ => n') :=
    fun n n' => vdeg_add _ _
  induction hu using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨j, rfl⟩ := hz
    refine ⟨1, chartMonoZ O M M' j (fun _ => 1), chartMonoZ_homog j _, ?_⟩
    rw [hQ, pow_one, pow_one, div_mul_cancel₀ _ hc]
  | algebraMap r =>
    refine ⟨0, C r, ?_, ?_⟩
    · have h0 : vdeg (K := K) (fun _ => 0) = 0 := by
        funext o
        rcases o with _ | _ | k <;> rfl
      rw [h0]
      exact isWeightedHomogeneous_C _ _
    · rw [aeval_C, pow_zero, mul_one, IsScalarTower.algebraMap_apply O Ω Φ]
  | add z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * chartMonoZ O M M' c (fun _ => n') + U' * chartMonoZ O M M' c (fun _ => n), ?_, ?_⟩
    · rw [hlift]
      refine (IsWeightedHomogeneous.mul hU (chartMonoZ_homog c _)).add ?_
      rw [add_comm]
      exact IsWeightedHomogeneous.mul hU' (chartMonoZ_homog c _)
    · rw [map_add, map_mul, map_mul, hUe, hUe', hQ, hQ, ← map_mul, ← map_mul, ← map_add]
      congr 1
      ring
  | mul z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * U', ?_, ?_⟩
    · rw [hlift]
      exact IsWeightedHomogeneous.mul hU hU'
    · rw [map_mul, hUe, hUe', ← map_mul]
      congr 1
      ring
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
