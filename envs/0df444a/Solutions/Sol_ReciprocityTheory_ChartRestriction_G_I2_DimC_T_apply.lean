-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.T_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:06.415938+00:00
-- url     : https://prove2.me/submissions/7b59bc5d-ceff-400a-ad1e-1e365ed50a90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs

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
variable (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
namespace ReciprocityTheory.ChartRestriction.G.I2.DimC
theorem _root_.solution (q : ℕ) (F : Y.Sec q) (r : Fin (Fintype.card ι) → Fin q) :
    T Y e q F r = DimB.Av (DimB.Pm (hF Y e q F.1) (fun l => ((r l : ℕ) : ℤ))) 0 := rfl
end ReciprocityTheory.ChartRestriction.G.I2.DimC
