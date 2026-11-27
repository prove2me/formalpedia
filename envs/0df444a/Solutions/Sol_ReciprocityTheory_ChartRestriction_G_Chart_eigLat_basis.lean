-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.eigLat_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:32:28.829885+00:00
-- url     : https://prove2.me/submissions/3cea88fe-856e-4a01-9ba3-66192e376b7d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution [IsDomain R] [IsPrincipalIdealRing R] {O : Type} (act : O → (G ⟶ G)) [∀ a, IsMonHom (act a)]
    (χ : O → R) : ∃ k, Nonempty (Module.Basis (Fin k) R (eigLat hx act χ)) := by
  obtain ⟨k, bk⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin n)) (eigLat hx act χ)
  exact ⟨k, ⟨bk⟩⟩
end ReciprocityTheory.ChartRestriction.G.Chart
