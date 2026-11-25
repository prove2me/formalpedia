-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_comp_real_4d15d05546d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:43:51.387831+00:00
-- url     : https://prove2.me/submissions/4ab76149-acd9-4192-805e-20b520e2acfe

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_comp_real_912f4f8715ef
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (w : ι → ℂ) :
    levi (fun z => G (ψ z)) y w = G₁ (ψ y) * levi ψ y w +
      g₂ * ((fderiv ℝ ψ y w) ^ 2 + (fderiv ℝ ψ y (Complex.I • w)) ^ 2) / 4 := by
  unfold levi
  rw [fderiv2_comp_real hψ hG hG₁, fderiv2_comp_real hψ hG hG₁]
  ring
end GroundTheory.Heights₂.Heights.AnalyticLimit
