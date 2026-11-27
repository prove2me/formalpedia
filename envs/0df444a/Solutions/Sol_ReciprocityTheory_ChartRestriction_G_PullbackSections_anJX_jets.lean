-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anJX_jets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:26.638046+00:00
-- url     : https://prove2.me/submissions/d4c2ec3d-5127-495e-91de-ec1c65cd9fe1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetOf_comp_anLin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_precompD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetMap


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y : Scheme.{0}}
variable {X : Scheme.{0}} {G : Over X} [MonObj G] {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {u : Sp ℂ ⟶ X} (ex : (Fin g → ℂ) → (Over.mk u ⟶ G)) (hol : IsHolFam fun z => (ex z).left) (m : ℕ)
    (A : (Fin (2 * g) → ℂ) →L[ℂ] (Fin g → ℂ)) (hA : IsHolFam fun v => (ex (A v)).left) :
    spMap ((jetMap (anLin A) (anLin_mem A) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (2 * g)) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (2 * g)) m) ≫ jetPt (fun z => (ex z).left) hol m =
      jetPt (fun v => (ex (A v)).left) hA m := by
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin A) (anLin_mem A)
  refine jetPt_precompD _ _ hol hA (by show (ex (A 0)).left = (ex 0).left; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) A).symm
end ReciprocityTheory.ChartRestriction.G.PullbackSections
