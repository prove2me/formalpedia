-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.tu_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:54.980042+00:00
-- url     : https://prove2.me/submissions/3828837c-467b-4762-8967-691e02cea2e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (u : ∀ p, Γ(X, U p)ˣ)
variable {U u}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {V : Y.Opens} {ψ : Y ⟶ X} {p : ι} (h : V ≤ ψ ⁻¹ᵁ U p) :
    tu U u V ψ p = res h (pullU ψ _ (u p)) := by
  unfold tu
  exact dif_pos h
end ReciprocityTheory.ChartRestriction.G.DVR
