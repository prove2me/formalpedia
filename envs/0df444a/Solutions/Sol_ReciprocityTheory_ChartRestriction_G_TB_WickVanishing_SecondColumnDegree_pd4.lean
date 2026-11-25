-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.pd4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:00.628063+00:00
-- url     : https://prove2.me/submissions/18498673-d297-43f4-ac66-10ebc7fa3136

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
private theorem mvPolynomial_pderiv_comm (a b : σ) (P : MvPolynomial σ k) :
    pderiv a (pderiv b P) = pderiv b (pderiv a P) := by
  classical
  induction P using MvPolynomial.induction_on
  · simp
  · simp [*]
  · rename_i p m hp
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp, pderiv_X]
    by_cases ha : a = m <;> by_cases hb : b = m <;> simp [Pi.single_apply, ha, hb] <;> ring
end General
section Columns
variable {ι : Type} [Fintype ι] {n : ℕ}
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
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
theorem _root_.solution (P : MvPolynomial σ k) (a b c d : σ) :
    pderiv a (pderiv b (pderiv c (pderiv d P))) = pderiv c (pderiv d (pderiv a (pderiv b P))) := by
  rw [mvPolynomial_pderiv_comm b c, mvPolynomial_pderiv_comm a c, mvPolynomial_pderiv_comm b d, mvPolynomial_pderiv_comm a d]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
