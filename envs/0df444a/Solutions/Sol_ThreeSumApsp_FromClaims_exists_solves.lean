-- Prove2me | solution 1 for ThreeSumApsp.FromClaims.exists_solves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:15.254416+00:00
-- url     : https://prove2.me/submissions/aef35563-f804-43f8-9804-20c15ac7d773

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Theorems.Thm_ThreeSumApsp_FromClaims_exists_solves_nonneg

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace ThreeSumApsp.FromClaims
theorem _root_.solution {prob : Problem} {size bound : prob.Inst → ℕ} {dom dom' : prob.Inst → Prop}
    {T X : prob.Inst → ℝ} (hR : RealizedWithin prob size bound dom T) (κ : ℕ) {C : ℝ}
    (hdom : ∀ x, dom' x → dom x ∧ 1 ≤ size x ∧ bound x = size x ^ κ)
    (hT : ∀ x, dom' x → T x ≤ C * X x) (hX : ∀ x, dom' x → 1 ≤ X x) :
    ∃ (P : List Instr) (b : ℕ) (K : ℝ), Solves prob P b dom' fun x => K * X x := by
  obtain ⟨P, b, K, -, hS⟩ := exists_solves_nonneg hR κ hdom hT hX
  exact ⟨P, b, K, hS⟩
end ThreeSumApsp.FromClaims
