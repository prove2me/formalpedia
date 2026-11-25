-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.ucomp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:26.556116+00:00
-- url     : https://prove2.me/submissions/e9010940-22cd-4239-82fd-34f15cc44f55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsPerpHermitianReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicIndexSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
theorem _root_.solution (x : Frame X.Ψ r) (ξ : Fin r → E) (U : X.Ψ → Fin r → ℂ) (τ : X.Ψ) :
    X.ucomp x ξ U τ = U τ - (X.Hf x τ (U τ) (Data.emb τ.1 ξ) /
      X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := rfl
end ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
