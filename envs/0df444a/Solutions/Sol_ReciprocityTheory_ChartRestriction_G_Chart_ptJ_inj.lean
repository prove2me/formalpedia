-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.ptJ_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:47:27.276043+00:00
-- url     : https://prove2.me/submissions/4a0fa42b-5457-4525-899b-a6fc2974386a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ChartSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pj_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jP_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_aug_jS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ptJ_aug
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


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
variable {x} (hx : IsUnivChart G d x)
include hx
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {p q : Q R d n} (h : ∀ m, ptJ x m p = ptJ x m q) : p = q :=
  Subtype.ext (funext fun j => pj_ext fun m => by
    have := (hx.2.2 _ (jetAug R _ m) m (ker_jetAug_pow _ m) _ (ptJ_aug hx m p)).unique ⟨aug_jS hx m p, rfl⟩
      ⟨aug_jS hx m q, h m⟩
    rw [← jP_zR, this, jP_zR])
end ReciprocityTheory.ChartRestriction.G.Chart
