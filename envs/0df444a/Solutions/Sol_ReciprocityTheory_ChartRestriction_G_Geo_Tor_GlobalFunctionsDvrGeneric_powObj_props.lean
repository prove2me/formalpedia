-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric.powObj_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:13.253812+00:00
-- url     : https://prove2.me/submissions/392970e3-bd21-4309-b565-c4e9274d00e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrGeneric

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
open ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] :
    ∀ n : ℕ, Smooth (powObj G n).hom ∧ IsSeparated (powObj G n).hom ∧ QuasiCompact (powObj G n).hom
  | 0 => ⟨by show Smooth (𝟙 S); infer_instance, by show IsSeparated (𝟙 S); infer_instance,
      by show QuasiCompact (𝟙 S); infer_instance⟩
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := solution G n
    refine ⟨?_, ?_, ?_⟩
    · show Smooth (G ⊗ powObj G n).hom
      rw [Over.tensorObj_hom, pullback.condition]
      infer_instance
    · show IsSeparated (G ⊗ powObj G n).hom
      rw [Over.tensorObj_hom, pullback.condition]
      infer_instance
    · show QuasiCompact (G ⊗ powObj G n).hom
      rw [Over.tensorObj_hom, pullback.condition]
      infer_instance
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
