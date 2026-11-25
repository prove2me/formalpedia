-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jP_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:54:34.0551+00:00
-- url     : https://prove2.me/submissions/b8dd4b7c-5a3e-4a29-9c33-4fd157a9d9c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ChartSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jS_zR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (m : ℕ) (p : Q R d n) (j : Fin d) : jP m p (zR m j) = pj m (p.1 j) := jS_zR m p.1 p.2 j
end ReciprocityTheory.ChartRestriction.G.Chart
