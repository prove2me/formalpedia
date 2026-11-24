-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartRing_forms_a08c172c2f9a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:55.639179+00:00
-- url     : https://prove2.me/submissions/91e23ac7-e1cb-409b-bb34-8c03452b5dfd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartMono_homog_e29ba7e91ef2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_chartMono_b9f77329372f

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
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
theorem _root_.solution (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {u : Ω}
    (hu : u ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (U : MRing (bundleIdx ι M) F), IsMultiHomog U (liftNat fun _ => n) ∧
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) U =
        algebraMap Ω Φ (u * segreVec y c ^ n) := by
  have hlift : ∀ n n' : ℕ, liftNat (K := K) (fun _ => n + n') = liftNat (fun _ => n) + liftNat (fun _ => n') := by
    intro n n'; funext o; cases o <;> simp [liftNat]
  have hQ : ∀ n : ℕ, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t)
      (chartMono M c (fun _ => n)) = algebraMap Ω Φ (segreVec y c ^ n) := by
    intro n
    rw [eval_chartMono, segreVec, Finset.prod_pow]
  induction hu using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨j, rfl⟩ := hz
    refine ⟨1, chartMono M j (fun _ => 1), chartMono_homog M j _, ?_⟩
    rw [eval_chartMono, pow_one, div_mul_cancel₀ _ hc]
    simp [segreVec]
  | algebraMap r =>
    refine ⟨0, C r, ?_, ?_⟩
    · have h0 : liftNat (K := K) (fun _ => 0) = 0 := by funext o; cases o <;> rfl
      rw [h0]
      exact isWeightedHomogeneous_C _ _
    · simp
  | add z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * chartMono M c (fun _ => n') + U' * chartMono M c (fun _ => n), ?_, ?_⟩
    · rw [hlift]
      refine (hU.mul (chartMono_homog M c _)).add ?_
      rw [add_comm]
      exact hU'.mul (chartMono_homog M c _)
    · rw [eval₂_add, eval₂_mul, eval₂_mul, hUe, hUe', hQ, hQ, ← map_mul, ← map_mul, ← map_add]
      congr 1
      ring
  | mul z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * U', ?_, ?_⟩
    · rw [hlift]
      exact hU.mul hU'
    · rw [eval₂_mul, hUe, hUe', ← map_mul]
      congr 1
      ring
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
