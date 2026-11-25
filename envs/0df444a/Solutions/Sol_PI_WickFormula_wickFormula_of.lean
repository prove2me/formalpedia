-- Prove2me | solution 1 for PI.WickFormula.wickFormula_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:38.116688+00:00
-- url     : https://prove2.me/submissions/5bd7b8e7-d7aa-47a5-b124-399004bd1fbb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
import Theorems.Thm_PI_WickFormula_Asm_xdeg_le_totalDegree
import Theorems.Thm_PI_WickFormula_Asm_phiH_apply
import Theorems.Thm_PI_WickFormula_Asm_claim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
open Asm
namespace PI.WickFormula
theorem _root_.solution (h1 : OrdLin) (h2 : OrdX) (h3 : Base) (h4 : BComm) (g1 : Gen.PowXL)
    (g2 : Gen.CommL) (g3 : Gen.VanL) : PI.WickFormula := by
  intro k AA M _ _ _ _ _ _ r s a b a' b' κ σ₀ e1 e2 e3 e4 e5 e6 P
  have H : Hyp a b a' b' κ σ₀ := ⟨e1, e2, e3, e4, e5, e6⟩
  have h := claim h1 h2 h3 h4 g1 g2 g3 H P.totalDegree P
    (fun m hm => xdeg_le_totalDegree P m hm) (P.totalDegree + 1) (by omega)
  rw [phiH_apply] at h
  rw [h]
  rfl
end PI.WickFormula
