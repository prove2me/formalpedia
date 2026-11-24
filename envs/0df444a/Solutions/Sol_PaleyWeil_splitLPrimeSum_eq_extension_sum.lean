-- Prove2me | solution 1 for PaleyWeil.splitLPrimeSum_eq_extension_sum
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:42:50.235655+00:00
-- url     : https://prove2.me/submissions/743f561f-3cf0-40c9-ba09-eb0cbe30f54f

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLSeriesDefs
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitQuadraticWeight
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Theorems.Thm_PaleyWeil_card_minpoly_fiber
import Theorems.Thm_PaleyWeil_mem_minpoly_image_iff
import Theorems.Thm_PaleyWeil_norm_eq_signed_coeff_pow
import Theorems.Thm_PaleyWeil_quadraticChar_norm

namespace Finset
end Finset
namespace IntermediateField
end IntermediateField
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial

section


open Polynomial IntermediateField

namespace PaleyWeil



/-- The norm of a shifted element is the minimal polynomial evaluated at the shift,
with the conventional sign and the ambient-extension multiplicity. -/
theorem norm_sub_algebraMap_eq_minpoly_eval {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (x : L) (a : K) :
    Algebra.norm K (x - algebraMap K L a) =
      ((-1 : K) ^ (minpoly K x).natDegree * (minpoly K x).eval a) ^
        (Module.finrank K L / (minpoly K x).natDegree) := by
  rw [norm_eq_signed_coeff_pow, minpoly.sub_algebraMap,
    Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  congr 2
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  simp




end PaleyWeil

end

section


open Polynomial Finset

namespace PaleyWeil







/-- Extension-field values are powers of the weight of their minimal polynomial.
This is the finite-field character compatibility needed by the Euler-product identity. -/
theorem quadraticChar_split_eq_weight_minpoly_pow {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L]
    (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2) (s : Finset K) (x : L) :
    quadraticChar L (∏ a ∈ s, (x - algebraMap K L a)) =
      splitQuadraticWeight s (minpoly K x) ^
        (Module.finrank K L / (minpoly K x).natDegree) := by
  rw [← quadraticChar_norm hK hL]
  rw [map_prod]
  simp_rw [norm_sub_algebraMap_eq_minpoly_eval]
  rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul]
  rw [Nat.mul_comm (minpoly K x).natDegree s.card, map_pow]
  rfl




end PaleyWeil

end

section


open Polynomial Finset

namespace PaleyWeil



theorem sum_weight_minpoly {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L]
    (w : K[X] → ℤ) :
    ∑ x : L, w (minpoly K x) =
      ∑ P ∈ (Finset.univ.image (minpoly K : L → K[X])), (P.natDegree : ℤ) * w P := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := minpoly K)
    (t := Finset.univ.image (minpoly K : L → K[X]))
    (fun x _ ↦ Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)]
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hP
  rw [Finset.sum_congr rfl (fun y hy ↦ congrArg w (Finset.mem_filter.mp hy).2)]
  rw [Finset.sum_const, card_minpoly_fiber, nsmul_eq_mul]

/-- The extension-field split character sum is the degree-weighted prime-polynomial
sum which occurs in the logarithmic derivative of its L-series. -/
theorem split_character_sum_eq_weighted_minpoly {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L]
    (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2) (s : Finset K) :
    ∑ x : L, quadraticChar L (∏ a ∈ s, (x - algebraMap K L a)) =
      ∑ P ∈ (Finset.univ.image (minpoly K : L → K[X])),
        (P.natDegree : ℤ) * splitQuadraticWeight s P ^
          (Module.finrank K L / P.natDegree) := by
  simp_rw [quadraticChar_split_eq_weight_minpoly_pow hK hL]
  exact sum_weight_minpoly (K := K) (L := L)
    (fun P ↦ splitQuadraticWeight s P ^ (Module.finrank K L / P.natDegree))




end PaleyWeil

end

open Polynomial Finset
open PaleyWeil

theorem solution {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L]
    (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2) (s : Finset K) :
    splitLPrimeSum s (Module.finrank K L) =
      ∑ x : L, quadraticChar L (∏ a ∈ s, (x - algebraMap K L a)) := by
  classical
  rw [split_character_sum_eq_weighted_minpoly hK hL]
  symm
  let n := Module.finrank K L
  let S := Finset.univ.image (minpoly K : L → K[X])
  have hn : n ≠ 0 := (Module.finrank_pos (R := K) (M := L)).ne'
  have hS (P : K[X]) : P ∈ S ↔ P.Monic ∧ Irreducible P ∧ P.natDegree ∣ n :=
    mem_minpoly_image_iff P
  change (∑ P ∈ S, (P.natDegree : ℤ) * splitQuadraticWeight s P ^ (n / P.natDegree)) =
    ∑ d ∈ n.divisors, (d : ℤ) *
      ∑' P : {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d},
        splitQuadraticWeight s P ^ (n / d)
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun P : K[X] ↦ P.natDegree)
    (t := n.divisors) (fun P hP ↦ Nat.mem_divisors.mpr ⟨((hS P).mp hP).2.2, hn⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  rw [Finset.sum_congr rfl (fun P hP ↦ by
    rw [(Finset.mem_filter.mp hP).2])]
  rw [← Finset.mul_sum]
  congr 1
  let T := S.filter (fun P : K[X] ↦ P.natDegree = d)
  let e : T ≃ {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d} :=
    { toFun := fun P ↦ ⟨P.1, ((hS P.1).mp (Finset.mem_filter.mp P.2).1).1,
        ((hS P.1).mp (Finset.mem_filter.mp P.2).1).2.1,
        (Finset.mem_filter.mp P.2).2⟩
      invFun := fun P ↦ ⟨P.1, Finset.mem_filter.mpr
        ⟨(hS P.1).mpr ⟨P.2.1, P.2.2.1, (by rw [P.2.2.2]; exact hdvd)⟩, P.2.2.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  letI := Fintype.ofEquiv T e
  rw [tsum_fintype]
  calc
    _ = ∑ P : T, splitQuadraticWeight s (P : K[X]) ^ (n / d) :=
      (Finset.sum_coe_sort T _).symm
    _ = _ := Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
