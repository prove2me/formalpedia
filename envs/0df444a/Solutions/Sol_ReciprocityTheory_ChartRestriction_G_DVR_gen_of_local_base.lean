-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gen_of_local_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:50.823715+00:00
-- url     : https://prove2.me/submissions/9a17c3e0-caab-4183-9096-daa42927f42e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_of_top

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
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {V : Type} [CommRing V] [IsLocalRing V] (hL : L.IsLB)
    {W : Over (Spec (CommRingCat.of V))} (ψ : K → (W.left ⟶ X)) (ε : K → ℤ)
    (h : ∀ s : Spec (CommRingCat.of V), ∃ U : (Spec (CommRingCat.of V)).Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb L (fun k => (W.hom ⁻¹ᵁ U).ι ≫ ψ k) ε), t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L ψ ε), t'.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := h (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff (R := V) U).1 hU
  exact gen_of_top hL ψ ε t ht
end ReciprocityTheory.ChartRestriction.G.DVR
