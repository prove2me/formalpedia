-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_eq_sum_traceMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:23.349871+00:00
-- url     : https://prove2.me/submissions/858e1b1f-c25a-442d-b418-b9f8159b8fb7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
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
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {S : Type*} [CommRing S] {r δ N : ℕ}
    (g : Fin r → Fin δ → MvPolynomial (Fin (D + 1)) ℤ) (j : Fin r) (l : Fin δ)
    (hg : (g j l).IsHomogeneous N) (y : Fin (D + 1) → S) :
    aeval y (g j l) = ∑ i, ((traceMat D N g (finProdFinEquiv (l, i)) j : ℤ) : S) *
      ∏ t, y t ^ adtEnum D N i t := by
  classical
  have hentry : ∀ i, traceMat D N g (finProdFinEquiv (l, i)) j =
      coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N i)) (g j l) := by
    intro i; simp only [traceMat, Matrix.of_apply, Equiv.symm_apply_apply]
  simp only [hentry]
  have hR : ∑ i, ((coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N i)) (g j l) : ℤ) : S) *
        ∏ t, y t ^ adtEnum D N i t =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
        ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : S) * ∏ t, y t ^ a t := by
    rw [← Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (D + 1) N)]
    exact (Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm.sum_comp
      (fun a : (Finset.Nat.antidiagonalTuple (D + 1) N) =>
        ((coeff (Finsupp.equivFunOnFinite.symm (a : Fin (D + 1) → ℕ)) (g j l) : ℤ) : S) *
          ∏ t, y t ^ (a : Fin (D + 1) → ℕ) t)
  rw [hR, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  let e : (Fin (D + 1) → ℕ) ↪ (Fin (D + 1) →₀ ℕ) :=
    ⟨Finsupp.equivFunOnFinite.symm, Finsupp.equivFunOnFinite.symm.injective⟩
  have hmap : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
        ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : S) * ∏ t, y t ^ a t =
      ∑ d ∈ (Finset.Nat.antidiagonalTuple (D + 1) N).map e,
        algebraMap ℤ S (coeff d (g j l)) * ∏ t, y t ^ d t := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [e]
  rw [hmap]
  refine Finset.sum_subset (fun d hd => ?_) (fun d _ hd => ?_)
  · rw [Finset.mem_map]
    refine ⟨⇑d, ?_, by simp [e]⟩
    have h1 := hg (MvPolynomial.mem_support_iff.mp hd)
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h1
  · rw [MvPolynomial.notMem_support_iff.mp hd, map_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
