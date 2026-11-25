-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.pderiv_prod_colE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:00.321541+00:00
-- url     : https://prove2.me/submissions/aa2c2035-3c84-419e-878a-6822b8cedbdd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
variable {k : Type} [CommRing k]
section General
variable {σ : Type} [Fintype σ]
end General
section Columns
variable {ι : Type} [Fintype ι] {n : ℕ}
private theorem pderiv_colE_eq_zero_of_ne (a b : Fin n) (hab : a ≠ b) (l : ι) (P : MvPolynomial ι k) :
    pderiv (l, b) (colE a P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on
  · simp
  · simp [*]
  · rename_i p m hp
    simp [hp, pderiv_X, Pi.single_apply, hab]
end Columns
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
variable {k : Type} [CommRing k]
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
theorem _root_.solution (b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s) (Q : Fin n → MvPolynomial ι k)
    (l : ι) : pderiv (l, b) (∏ b' ∈ s, colE b' (Q b')) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih (fun h => hb (Finset.mem_insert_of_mem h)),
      pderiv_colE_eq_zero_of_ne a b (by rintro rfl; exact hb (Finset.mem_insert_self _ _)) l (Q a)]
    simp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
