-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.nfac_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:43.989396+00:00
-- url     : https://prove2.me/submissions/268f5708-d8b1-438a-8803-fb097bd23e65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_ratio_pos

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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) : 0 < X.nfac la x :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (ratio_pos X hx τ i) _
end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
