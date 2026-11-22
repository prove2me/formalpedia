-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:05.994844+00:00
-- url     : https://prove2.me/submissions/5906b727-ef23-47a4-a8b0-82531f615e5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc

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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
variable (L : LB X)
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hL : L.IsLB) (z : Z) {K : Type} (ψ : K → (Z ⟶ X)) (j : K → L.ι)
    (hc : ∀ a b, ψ a = ψ b → j a = j b) (hj : ∀ k, ψ k z ∈ L.U (j k)) :
    ∃ J, Good L z J ∧ ∀ k, J (ψ k) = j k := by
  classical
  have hcov : ∀ x : X, ∃ i, x ∈ L.U i := fun x => by
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; simp
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨fun ψ' => if hk : ∃ k, ψ k = ψ' then j hk.choose else (hcov (ψ' z)).choose, ?_, ?_⟩
  · intro ψ'
    dsimp only
    split_ifs with hk
    · have hm := hj hk.choose
      rw [hk.choose_spec] at hm
      exact hm
    · exact (hcov _).choose_spec
  · intro k
    dsimp only
    rw [dif_pos ⟨k, rfl⟩]
    exact hc _ _ (Exists.choose_spec (⟨k, rfl⟩ : ∃ k', ψ k' = ψ k))
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
