-- Prove2me | solution 1 for ThreeSumApsp.FromClaims.exists_solves_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:16.482924+00:00
-- url     : https://prove2.me/submissions/db18565a-72ee-4da6-b551-74870c49d4e8

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_WordRam_IsDataStructure_mono
import Theorems.Thm_ThreeSumApsp_WordRam_Solves_mono


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace ThreeSumApsp.FromClaims
theorem _root_.solution {prob₁ prob₂ : Problem} {dom₁ : prob₁.Inst → Prop}
    {dom₂ : prob₂.Inst → Prop} {X₁ : prob₁.Inst → ℝ} {X₂ : prob₂.Inst → ℝ}
    (h₁ : ∃ (P : List Instr) (b : ℕ) (K : ℝ), 0 ≤ K ∧ Solves prob₁ P b dom₁ fun x => K * X₁ x)
    (h₂ : ∃ (P : List Instr) (b : ℕ) (K : ℝ), 0 ≤ K ∧ Solves prob₂ P b dom₂ fun x => K * X₂ x)
    (hX₁ : ∀ x, dom₁ x → 1 ≤ X₁ x) (hX₂ : ∀ x, dom₂ x → 1 ≤ X₂ x) :
    ∃ (P₁ P₂ : List Instr) (b : ℕ) (K : ℝ),
      Solves prob₁ P₁ b dom₁ (fun x => K * X₁ x) ∧ Solves prob₂ P₂ b dom₂ (fun x => K * X₂ x) := by
  obtain ⟨P₁, b₁, K₁, hK₁, hS₁⟩ := h₁
  obtain ⟨P₂, b₂, K₂, hK₂, hS₂⟩ := h₂
  refine ⟨P₁, P₂, max b₁ b₂, K₁ + K₂, hS₁.mono (le_max_left _ _) (fun _ hx => hx) fun x hx => ?_,
    hS₂.mono (le_max_right _ _) (fun _ hx => hx) fun x hx => ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans (hX₁ x hx))
  · exact mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans (hX₂ x hx))
end ThreeSumApsp.FromClaims
