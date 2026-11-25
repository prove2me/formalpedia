-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_eq_sum_adt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:11:45.652353+00:00
-- url     : https://prove2.me/submissions/81bab775-1607-4526-b283-c019f8b98394

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_HadZSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {D N : ℕ} {S : Type*} [CommRing S] (g : MvPolynomial (Fin (D + 1)) ℤ)
    (hg : g.IsHomogeneous N) (y : Fin (D + 1) → S) :
    aeval y g = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
      ((coeff (Finsupp.equivFunOnFinite.symm a) g : ℤ) : S) * ∏ i, y i ^ a i := by
  classical
  rw [aeval_def, eval₂_eq']
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => Finsupp.equivFunOnFinite.symm a) ?_ ?_ ?_ ?_
  · intro a _ ha
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply ha
    simp [h]
  · intro a _ _ b _ _ h
    exact Finsupp.equivFunOnFinite.symm.injective h
  · intro d hd hne
    refine ⟨Finsupp.equivFunOnFinite d, ?_, ?_, ?_⟩
    · rw [Finset.Nat.mem_antidiagonalTuple]
      have h := hg (MvPolynomial.mem_support_iff.1 hd)
      rw [Finsupp.weight_apply] at h
      simpa [Finsupp.sum_fintype] using h
    · simpa using hne
    · simp
  · intro a _ _
    simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
