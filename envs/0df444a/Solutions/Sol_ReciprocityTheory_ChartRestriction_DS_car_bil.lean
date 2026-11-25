-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.car_bil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:40.985787+00:00
-- url     : https://prove2.me/submissions/9430a4ae-f66c-4ea8-9824-925987ad23a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_bil_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (i a j b k c l d : Fin n) :
    cp i a * cm j b * (cp k c * cm l d) - cp k c * cm l d * (cp i a * cm j b) =
      (if j = k ∧ b = c then cp i a * cm l d else 0) - (if l = i ∧ d = a then cp k c * cm j b else 0) := by
  rw [car_bil_abs _ _ _ _ _ _ (hC j b k c).2.2 (hC l d i a).2.2 (hC i a k c).1
    (hC j b l d).2.1]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS
