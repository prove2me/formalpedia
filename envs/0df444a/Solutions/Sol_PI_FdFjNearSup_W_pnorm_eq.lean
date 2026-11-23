-- Prove2me | solution 1 for PI.FdFjNearSup.W.pnorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:24.485892+00:00
-- url     : https://prove2.me/submissions/081a3d51-2990-40d2-a605-b56d89c3f9f2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FdFjNearSup PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace PI.FdFjNearSup.W
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la Q x = ‖Q x‖ * X.nfac la x := rfl
end PI.FdFjNearSup.W
