-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.cross_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:44:03.955426+00:00
-- url     : https://prove2.me/submissions/3ce1de63-4249-4020-a741-76c4326c77e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Γ : Type} [CommRing Γ] {Jx Xc : Type} [DecidableEq Xc] (S : Finset Jx) (S'' : Finset Xc)
    (g : Jx → Xc) (hg : Set.InjOn g S) (hS : S.image g ⊆ S'') (W W' : Γˣ) (m n : ℕ) (Z Y : Fin 2 → Γ)
    (P1 : Fin 2 → Xc → Γ) (P2 A : Fin 2 → Jx → Γ) (c : Jx → Γ) (ξ : Γ)
    (E1 : ∀ i, (W : Γ) ^ m * Z i = ∑ β ∈ S'', P1 i β)
    (E2 : ∀ i, (W' : Γ) ^ n * Y i = ∑ α ∈ S, P2 i α)
    (E1' : ∀ i, ∀ χ ∈ S, P1 i (g χ) = A i χ * ξ * c χ)
    (E2' : ∀ i, ∀ α ∈ S, P2 i α = A i α * c α)
    (E5 : ∀ i, ∀ β ∈ S'', β ∉ S.image g → P1 i β = 0) :
    Z 0 * Y 1 - Z 1 * Y 0 = 0 := by
  have key : ∀ i, (W : Γ) ^ m * Z i = ξ * ((W' : Γ) ^ n * Y i) := by
    intro i
    rw [E1 i, E2 i, ← Finset.sum_subset hS (fun β hβ hn => E5 i β hβ hn), Finset.sum_image hg, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun χ hχ => ?_)
    rw [E1' i χ hχ, E2' i χ hχ]
    ring
  have hu : IsUnit ((W : Γ) ^ m) := (Units.isUnit W).pow m
  refine hu.mul_right_eq_zero.mp ?_
  linear_combination (Y 1) * key 0 - (Y 0) * key 1
end ReciprocityTheory.ChartRestriction.G.DVR
