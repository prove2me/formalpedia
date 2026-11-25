-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_chart_form_792b75e5fddd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:49.288036+00:00
-- url     : https://prove2.me/submissions/dfd92acc-6f72-4629-984b-940fbaecb139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_segreForm_homog_c595c342bf4f

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
theorem _root_.solution {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F Ω : Type*} [Field F]
    [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {α : Ω}
    (hα : α ∈ chartRing F (segreVec y) c) :
    ∃ (m : ℕ) (A : MRing ι F), IsMultiHomog A (fun _ => m) ∧ α * segreVec y c ^ m = aeval y A := by
  have hσ : aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι F)) = segreVec y c := by
    simp [segreVec, map_prod]
  have hdeg : ∀ m n : ℕ, ((fun _ : K => m) + fun _ : K => n) = fun _ => m + n := fun _ _ => rfl
  have hpow : ∀ n : ℕ, IsMultiHomog ((∏ k, (X ⟨k, c k⟩ : MRing ι F)) ^ n) (fun _ => n) := by
    intro n
    have h := (segreForm_homog (R := F) c).pow n
    have e : (n • fun _ : K => (1 : ℕ)) = fun _ => n := by funext k; simp
    rw [e] at h
    exact h
  induction hα using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨c', rfl⟩ := hz
    refine ⟨1, ∏ k, X ⟨k, c' k⟩, segreForm_homog c', ?_⟩
    rw [pow_one, div_mul_cancel₀ _ hc]
    simp [segreVec, map_prod]
  | algebraMap q =>
    exact ⟨0, C q, isWeightedHomogeneous_C _ _, by simp⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨m, A, hA, hAe⟩ := hz
    obtain ⟨n, B, hB, hBe⟩ := hz'
    refine ⟨m + n, A * (∏ k, X ⟨k, c k⟩) ^ n + B * (∏ k, X ⟨k, c k⟩) ^ m, ?_, ?_⟩
    · have h1 := hA.mul (hpow n)
      have h2 := hB.mul (hpow m)
      rw [hdeg] at h1 h2
      rw [add_comm n m] at h2
      exact h1.add h2
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, hσ, ← hAe, ← hBe]
      ring
  | mul z z' _ _ hz hz' =>
    obtain ⟨m, A, hA, hAe⟩ := hz
    obtain ⟨n, B, hB, hBe⟩ := hz'
    refine ⟨m + n, A * B, ?_, ?_⟩
    · have h1 := hA.mul hB
      rwa [hdeg] at h1
    · rw [map_mul, ← hAe, ← hBe]
      ring
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
