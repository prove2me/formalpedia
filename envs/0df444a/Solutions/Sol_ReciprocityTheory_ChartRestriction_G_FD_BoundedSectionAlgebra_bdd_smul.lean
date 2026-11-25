-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:31:17.523901+00:00
-- url     : https://prove2.me/submissions/3f08ba65-cccc-416c-bc29-49d91726e024

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_pnorm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
theorem _root_.solution {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (a : ℂ) (hP : X.IsBddSec la P) :
    X.IsBddSec la (a • P) := by
  obtain ⟨C, hC⟩ := hP.2
  refine ⟨⟨hP.1.1.const_smul a, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, ‖a‖ * C, fun x hx => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hP.1.2.1 x hx b hb]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul, hP.1.2.2 γ hγ x hx]
    ring
  · have h1 := hC x hx
    rw [pnorm_eq] at h1 ⊢
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg a)
end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
