-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:31:15.060021+00:00
-- url     : https://prove2.me/submissions/4ab3283e-369e-4afe-89bd-1698680f4e67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_pnorm_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_nfac_nonneg

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
theorem _root_.solution {la : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) (hQ : X.IsBddSec la Q) :
    X.IsBddSec la (P + Q) := by
  obtain ⟨C1, hC1⟩ := hP.2
  obtain ⟨C2, hC2⟩ := hQ.2
  refine ⟨⟨hP.1.1.add hQ.1.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, C1 + C2, fun x hx => ?_⟩
  · simp only [Pi.add_apply, hP.1.2.1 x hx b hb, hQ.1.2.1 x hx b hb, mul_add]
  · simp only [Pi.add_apply, hP.1.2.2 γ hγ x hx, hQ.1.2.2 γ hγ x hx, mul_add]
  · have h1 := hC1 x hx
    have h2 := hC2 x hx
    rw [pnorm_eq] at h1 h2 ⊢
    have hn := nfac_nonneg X la x
    calc ‖(P + Q) x‖ * X.nfac la x ≤ (‖P x‖ + ‖Q x‖) * X.nfac la x :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hn
      _ = ‖P x‖ * X.nfac la x + ‖Q x‖ * X.nfac la x := add_mul _ _ _
      _ ≤ C1 + C2 := add_le_add h1 h2
end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
