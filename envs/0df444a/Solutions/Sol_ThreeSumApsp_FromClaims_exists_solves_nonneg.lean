-- Prove2me | solution 1 for ThreeSumApsp.FromClaims.exists_solves_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:45.376919+00:00
-- url     : https://prove2.me/submissions/ae357057-1450-44ec-85b8-4618511f0578

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

section
namespace ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
private theorem mul_add_le_of_le_mul {c C T X : ℝ} (hc : 0 ≤ c) (hT : T ≤ C * X) (hX : 1 ≤ X) :
    c * T + c ≤ (c * |C| + c) * X := by
  have hCX : C * X ≤ |C| * X := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have hcT : c * T ≤ c * (|C| * X) := mul_le_mul_of_nonneg_left (hT.trans hCX) hc
  have hcX : c ≤ c * X := le_mul_of_one_le_right hc hX
  linarith
end ThreeSumApsp.FromClaims
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace ThreeSumApsp.FromClaims
theorem _root_.solution {prob : Problem} {size bound : prob.Inst → ℕ}
    {dom dom' : prob.Inst → Prop} {T X : prob.Inst → ℝ} (hR : RealizedWithin prob size bound dom T)
    (κ : ℕ) {C : ℝ} (hdom : ∀ x, dom' x → dom x ∧ 1 ≤ size x ∧ bound x = size x ^ κ)
    (hT : ∀ x, dom' x → T x ≤ C * X x) (hX : ∀ x, dom' x → 1 ≤ X x) :
    ∃ (P : List Instr) (b : ℕ) (K : ℝ), 0 ≤ K ∧ Solves prob P b dom' fun x => K * X x := by
  obtain ⟨P, b, c, hc, hS⟩ := hR κ
  exact ⟨P, b, c * |C| + c, by positivity,
    hS.mono le_rfl hdom fun x hx => mul_add_le_of_le_mul hc (hT x hx) (hX x hx)⟩
end ThreeSumApsp.FromClaims
