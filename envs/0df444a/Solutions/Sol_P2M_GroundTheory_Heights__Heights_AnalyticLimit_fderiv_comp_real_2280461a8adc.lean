-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_comp_real_2280461a8adc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:37.28805+00:00
-- url     : https://prove2.me/submissions/33e94f52-0fd5-4492-b16d-9e61c7fe154e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
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
theorem _root_.solution {ψ : (ι → ℂ) → ℝ} {G : ℝ → ℝ} {g₁ : ℝ} {y : ι → ℂ}
    (hψ : DifferentiableAt ℝ ψ y) (hG : HasDerivAt G g₁ (ψ y)) (v : ι → ℂ) :
    fderiv ℝ (fun z => G (ψ z)) y v = g₁ * fderiv ℝ ψ y v := by
  have h := (hG.comp_hasFDerivAt y hψ.hasFDerivAt).fderiv
  rw [show (fun z => G (ψ z)) = G ∘ ψ from rfl, h]
  simp
end GroundTheory.Heights₂.Heights.AnalyticLimit
