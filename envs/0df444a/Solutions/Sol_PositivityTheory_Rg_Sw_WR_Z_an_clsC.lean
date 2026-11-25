-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.an_clsC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:19.169079+00:00
-- url     : https://prove2.me/submissions/ca7a4838-20c7-4787-957e-2e12ae7fd893

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_det
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_entAn_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_entAn_X
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_entAn_Y
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_entAn_sq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B₀ : MC n) (hB : B₀ ∈ OmS s) :
    AnalyticAt ℂ (clsC s z p q R) B₀ := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hu := entAn_inv (entAn_X (Complex.I * s) B₀) h1
  have hv := entAn_inv (entAn_Y (Complex.I * s) B₀) h2
  have hexp : AnalyticAt ℂ (fun B : MC n => Complex.exp (-z * Complex.log (1 + Matrix.of B * Matrix.of B).det)) B₀ :=
    (analyticAt_const.mul ((an_det (entAn_sq B₀)).clog h3)).cexp'
  have hdu : AnalyticAt ℂ (fun B : MC n => ((1 - (Complex.I * s) • Matrix.of B)⁻¹).det ^ p) B₀ := (an_det hu).pow p
  have hdv : AnalyticAt ℂ (fun B : MC n => ((1 + (Complex.I * s) • Matrix.of B)⁻¹).det ^ q) B₀ := (an_det hv).pow q
  have hf : ∀ k : Bool × Fin n × Fin n, AnalyticAt ℂ (fun B : MC n => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) B₀ := by
    rintro ⟨_ | _, a, b⟩
    · simp only [Bool.false_eq_true, if_false]
      exact hu a b
    · simp only [if_true]
      exact hv a b
  have hev := an_eval (fun k B => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) B₀ hf R
  unfold clsC
  exact ((hexp.mul hdu).mul hdv).mul hev
end PositivityTheory.Rg.Sw.WR.Z
