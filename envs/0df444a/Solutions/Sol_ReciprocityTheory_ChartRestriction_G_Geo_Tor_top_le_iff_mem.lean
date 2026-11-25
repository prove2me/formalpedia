-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.top_le_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:06.295372+00:00
-- url     : https://prove2.me/submissions/f691e18a-2072-46a7-a20c-bb3566713ae6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {F : Type} [Field F] {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) : ⊤ ≤ x ⁻¹ᵁ U ↔ x z ∈ U := by
  constructor
  · intro hle
    exact hle (show z ∈ (⊤ : (Sp F).Opens) from trivial)
  · intro hz w _
    have hwz : w = z := by
      first
        | exact Subsingleton.elim _ _
        | exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
        | exact PrimeSpectrum.ext (by simp)
    subst hwz
    exact hz
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
