-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.resChar_linInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:27:04.467667+00:00
-- url     : https://prove2.me/submissions/16e4d767-39db-4a9b-baff-42791484012e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (la : Wt X.Ψ r)
namespace ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
theorem _root_.solution :
    LinearIndependent ℂ (fun τ : X.Ψ => ((resChar X τ : (fixF (E := E)) →* ℂ) : (fixF (E := E)) → ℂ)) := by
  have hinj : Function.Injective (fun τ : X.Ψ => resChar X τ) := by
    intro τ τ' h
    apply restrict_inj X
    intro a ha
    have := DFunLike.congr_fun h ⟨a, ha⟩
    exact this
  exact (linearIndependent_monoidHom (fixF (E := E)) ℂ).comp _ hinj
end ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
