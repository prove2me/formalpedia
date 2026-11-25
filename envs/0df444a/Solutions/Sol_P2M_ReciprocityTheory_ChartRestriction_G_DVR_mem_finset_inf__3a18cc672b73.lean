-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_mem_finset_inf__3a18cc672b73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:42.13302+00:00
-- url     : https://prove2.me/submissions/4a4385a0-5403-4616-a085-54d7b6dba899

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
theorem _root_.solution {Y : Scheme.{0}} {κ : Type} (s : Finset κ) (F : κ → Y.Opens) (y : Y)
    (h : ∀ i ∈ s, y ∈ F i) : y ∈ s.inf F := by
  exact Finset.inf_induction (p := fun O : Y.Opens => y ∈ O) (by simp) (fun a ha b hb => ⟨ha, hb⟩) h
end ReciprocityTheory.ChartRestriction.G.DVR
