-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_colB_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:45.399537+00:00
-- url     : https://prove2.me/submissions/8ec0ae5f-0ee8-4f5c-9a81-0a65101626f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_colB

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
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
variable {k : Type} [CommRing k]
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
theorem _root_.solution (c : ι → ι → k) (b : Fin n) (R : MvPolynomial (ι × Fin n) k)
    (hR : ∀ l : ι, pderiv (l, b) R = 0) :
    ∀ (i : ℕ) (Q : MvPolynomial ι k),
      (secondOrder k (cB c b))^[i] (colE b Q * R) = colE b ((secondOrder k c)^[i] Q) * R
  | 0, _ => rfl
  | i + 1, Q => by
    rw [Function.iterate_succ_apply, so_colB c b Q R hR, solution c b R hR i,
      ← Function.iterate_succ_apply]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
