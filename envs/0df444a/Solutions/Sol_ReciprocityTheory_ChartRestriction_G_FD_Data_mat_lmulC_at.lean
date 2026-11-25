-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.mat_lmulC_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:19.999418+00:00
-- url     : https://prove2.me/submissions/b1670794-ff99-4e6d-82d6-48d6d468e88a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantBoundOrthogonalPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.lmulC n x) τ = mat (X.lmulC (fun _ => n τ) x) τ := rfl
end ReciprocityTheory.ChartRestriction.G.FD.Data
