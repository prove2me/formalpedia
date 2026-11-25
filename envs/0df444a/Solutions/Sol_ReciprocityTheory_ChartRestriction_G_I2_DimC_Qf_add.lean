-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.Qf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:25:53.366156+00:00
-- url     : https://prove2.me/submissions/abe47623-6f20-471a-9f74-e76e6bd2038a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_S_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex Module
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.DimC
variable {ι : Type} [Fintype ι]
variable (Y : GT ι)
variable {Y} (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
include hee
namespace ReciprocityTheory.ChartRestriction.G.I2.DimC
theorem _root_.solution (z w : Fin (Fintype.card ι) → ℂ) :
    Qf e (z + w) = Qf e z + Qf e w + 2 * ∑ i, ∑ l, z i * w l * S e i l := by
  have h : ∑ i, ∑ l, w i * z l * S e i l = ∑ i, ∑ l, z i * w l * S e i l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [S_symm e hee i l]
    ring
  have expand : ∀ i l, (z i + w i) * (z l + w l) * S e i l =
      z i * z l * S e i l + w i * w l * S e i l + z i * w l * S e i l + w i * z l * S e i l := by
    intro i l
    ring
  simp only [Qf, Pi.add_apply, expand, Finset.sum_add_distrib, h]
  ring
end ReciprocityTheory.ChartRestriction.G.I2.DimC
