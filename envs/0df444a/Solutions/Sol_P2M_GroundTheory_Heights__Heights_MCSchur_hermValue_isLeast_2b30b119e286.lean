-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_isLeast_2b30b119e286
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:22:48.775927+00:00
-- url     : https://prove2.me/submissions/733528c4-a0d5-4dae-bbc8-809279e52dd0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_eq_qf_16537984ce33
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_qf_isLeast_1f825f941902

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCSchur
open Matrix
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace GroundTheory.Heights₂.Heights.MCSchur
theorem _root_.solution (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : Y.PosDef) (v : n → ℂ) :
    IsLeast (Set.range fun x : m → ℂ => hermValue Y⁻¹ (Sum.elim x v))
      (hermValue (Y.toBlocks₂₂)⁻¹ v) := by
  have hre := qf_isLeast Y hY (fun k => (v k).re)
  have him := qf_isLeast Y hY (fun k => (v k).im)
  have split : ∀ x : m → ℂ, hermValue Y⁻¹ (Sum.elim x v) =
      qf Y⁻¹ (Sum.elim (fun k => (x k).re) (fun k => (v k).re)) +
        qf Y⁻¹ (Sum.elim (fun k => (x k).im) (fun k => (v k).im)) := by
    intro x
    rw [hermValue_eq_qf]
    congr 2 <;> ext k <;> cases k <;> rfl
  obtain ⟨⟨a, ha⟩, hlre⟩ := hre
  obtain ⟨⟨b, hb⟩, hlim⟩ := him
  refine ⟨⟨fun k => ⟨a k, b k⟩, ?_⟩, ?_⟩
  · simp only at ha hb ⊢
    rw [split, hermValue_eq_qf]
    exact congrArg₂ (· + ·) ha hb
  · rintro _ ⟨x, rfl⟩
    simp only
    rw [split, hermValue_eq_qf]
    exact add_le_add (hlre ⟨_, rfl⟩) (hlim ⟨_, rfl⟩)
end GroundTheory.Heights₂.Heights.MCSchur
