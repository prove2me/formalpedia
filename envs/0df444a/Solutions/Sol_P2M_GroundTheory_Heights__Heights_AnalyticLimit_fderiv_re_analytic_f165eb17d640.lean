-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_re_analytic_f165eb17d640
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:26.246087+00:00
-- url     : https://prove2.me/submissions/a2009d3d-46ea-473f-b0af-9dac802f9d4b

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
theorem _root_.solution {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).re) y v = (fderiv ℂ S y v).re := by
  have hS' : HasFDerivAt S ((fderiv ℂ S y).restrictScalars ℝ) y :=
    hS.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h := (Complex.reCLM.hasFDerivAt.comp y hS').fderiv
  rw [show (fun z => (S z).re) = Complex.reCLM ∘ S from rfl, h]
  simp
end GroundTheory.Heights₂.Heights.AnalyticLimit
