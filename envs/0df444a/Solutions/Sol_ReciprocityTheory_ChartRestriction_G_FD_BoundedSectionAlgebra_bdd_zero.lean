-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:29:35.76492+00:00
-- url     : https://prove2.me/submissions/70487c77-bdff-4c80-ac88-213c0399986c

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
theorem _root_.solution (la : Wt X.Ψ r) : X.IsBddSec la 0 := by
  refine ⟨⟨?_, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩, 0, fun x _ => by simp [pnorm_eq]⟩
  exact differentiableOn_const 0
end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
