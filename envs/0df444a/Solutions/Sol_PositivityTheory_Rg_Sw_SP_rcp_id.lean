-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.rcp_id
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:51:37.074489+00:00
-- url     : https://prove2.me/submissions/08d6be12-cef3-4d88-8341-8360fcbe6562

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Mathlib



-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
theorem _root_.solution : RCP (LinearMap.id : Fm n →ₗ[ℂ] Fm n) := by
  first
    | (intros; simp [Fm, RCP])
    | (intros; unfold Fm RCP; simp)
    | (intros; simp [Fm, RCP]; done)
    | (intros; ext; simp [Fm, RCP])
    | (intros; simp only [Fm, RCP]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [Fm, RCP])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [Fm, RCP])
    | (intros; unfold Fm RCP; split_ifs <;> simp_all)
    | (intros; unfold Fm RCP; positivity)
    | (intros; unfold Fm RCP; ring)
    | (intros; unfold Fm RCP; exact?)
    | (intros; aesop (add norm simp [Fm, RCP]))
    | (intros; simp [Fm, RCP] <;> aesop)
    | (intros; exact Fm.symm ..)
    | (intros; exact Fm.comm ..)
    | (intros; exact RCP.symm ..)
    | (intros; exact RCP.comm ..)
  trace "HIT_221_0"

end 
