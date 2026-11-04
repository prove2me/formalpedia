-- Prove2me | solution 1 for ThreeSumApsp.WordRam.exists_isDataStructure_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:00:24.506113+00:00
-- url     : https://prove2.me/submissions/eb33f9ce-1fde-4dca-8b3b-afef85881011

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Theorems.Thm_ThreeSumApsp_WordRam_Solves_mono
import Theorems.Thm_ThreeSumApsp_WordRam_IsDataStructure_mono
import Theorems.Thm_ThreeSumApsp_Dominated_const_mul_of_nonneg
import Theorems.Thm_ThreeSumApsp_Dominated_trans


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter
namespace ThreeSumApsp.WordRam
theorem _root_.solution {dom dom' : ThinPair → Prop}
    {f f' g g' : ThinPair → ℝ}
    (h : ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ), IsDataStructure P Q qI qJ qOut b []
      dom (fun x => C * f x) (fun x => C * f x) (fun x => C * g x))
    (hdom : ∀ x, dom' x → dom x) (hf : Dominated dom' f f') (hg : Dominated dom' g g')
    (hf0 : ∀ x, dom' x → 0 ≤ f x := by intro _ _; positivity)
    (hg0 : ∀ x, dom' x → 0 ≤ g x := by intro _ _; positivity)
    (hf'0 : ∀ x, dom' x → 0 ≤ f' x := by intro _ _; positivity)
    (hg'0 : ∀ x, dom' x → 0 ≤ g' x := by intro _ _; positivity) :
    ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ), IsDataStructure P Q qI qJ qOut b []
      dom' (fun x => C * f' x) (fun x => C * f' x) (fun x => C * g' x) := by
  obtain ⟨P, Q, qI, qJ, qOut, b, C, h⟩ := h
  obtain ⟨K₁, hK₁, hf⟩ := hf.const_mul_of_nonneg C hf0
  obtain ⟨K₂, hK₂, hg⟩ := hg.const_mul_of_nonneg C hg0
  have hf' : ∀ x, dom' x → C * f x ≤ (K₁ + K₂) * f' x := fun x hx =>
    (hf x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK₂) (hf'0 x hx))
  exact ⟨P, Q, qI, qJ, qOut, b, K₁ + K₂, h.mono le_rfl hdom hf' hf' fun x hx =>
    (hg x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK₁) (hg'0 x hx))⟩
end ThreeSumApsp.WordRam
