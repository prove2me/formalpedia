-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_family_ced0ca1166a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:26:22.409038+00:00
-- url     : https://prove2.me/submissions/b55fe708-85c1-43e2-bb79-3875fbcab7da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_IsChartForm_pad_50525580a2b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_24bb01e3d3b4

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]
  {F : Type*} [Field F] [Algebra F Ω] {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
  {Φ : Type*} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
theorem _root_.solution (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    {J : Type*} [Fintype J] (a : J → Ω) (ha : ∀ j, a j ∈ chartRing F (segreVec y) c) :
    ∃ n : ℕ, ∀ m, n ≤ m → ∀ j, ∃ A : MRing (bundleIdx ι M) F, IsChartForm F M y w φ t c (a j) m A := by
  choose n A hA using fun j => exists_chartForm (M := M) y w φ t c hc (ha j)
  refine ⟨∑ j, n j, fun m hm j => ?_⟩
  have hle : n j ≤ m := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hm
  have := (hA j).pad (m - n j)
  rw [Nat.add_sub_cancel' hle] at this
  exact ⟨_, this⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineSectionProof
