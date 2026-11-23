-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.integrable_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:11.159805+00:00
-- url     : https://prove2.me/submissions/b206d403-2491-4e8e-a5a2-230da69ad14a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_gauss_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun y : E n => Complex.exp (-((ε * ip y y : ℝ) : ℂ))) := by
  simp_rw [gauss_prod]
  have h1 : Integrable (fun s : ℝ => Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2)) :=
    integrable_cexp_neg_mul_sq (by simpa using hε)
  have h2 : Integrable (fun w : Fin n → ℝ => ∏ b, Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2)) :=
    Integrable.fintype_prod (f := fun _ (s : ℝ) => Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2)) (fun _ => h1)
  exact Integrable.fintype_prod (f := fun _ (w : Fin n → ℝ) => ∏ b, Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2))
    (fun _ => h2)
end PositivityTheory.Rg.Sw.WR.D.Moll
