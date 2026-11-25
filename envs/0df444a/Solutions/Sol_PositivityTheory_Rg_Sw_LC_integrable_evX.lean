-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.integrable_evX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:40.722799+00:00
-- url     : https://prove2.me/submissions/4e9c4395-4e91-4b56-ac1c-cb2f7d35fea0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_flip_flip
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_integrable_monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.flip_flip

set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hM : OneMom)
include hM
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (hc : 0 < c) (P : PX m n) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s r => exact integrable_monomial hM c hc s r
  | add P Q hP hQ =>
    have : (fun x => evX (P + Q) x * gs c x) = fun x => evX P x * gs c x + evX Q x * gs c x := by
      funext x; simp [evX, add_mul]
    rw [this]; exact hP.add hQ
end PositivityTheory.Rg.Sw.LC
