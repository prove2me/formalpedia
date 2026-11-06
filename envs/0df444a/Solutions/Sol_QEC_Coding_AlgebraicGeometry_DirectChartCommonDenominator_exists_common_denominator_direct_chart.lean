-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.exists_common_denominator_direct_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:06:10.691201+00:00
-- url     : https://prove2.me/submissions/d58dd7c4-e296-4240-a619-cbe60faec67c

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectChartCommonDenominator_repr_smul_polynomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator
open scoped BigOperators Polynomial
variable {k F ι : Type*}
variable [Field k] [Field F]
variable [Algebra (RatFunc k) F] [Algebra (Polynomial k) F]
  [IsScalarTower (Polynomial k) (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator
theorem _root_.solution
    [Fintype ι] (b : Module.Basis ι (RatFunc k) F) (L : Submodule (Polynomial k) F)
    [Module.Finite (Polynomial k) L] :
    ∃ a : Polynomial k, a ≠ 0 ∧ ∀ x : L, ∀ j : ι,
      b.repr (a • (x : F)) j ∈ Set.range (algebraMap (Polynomial k) (RatFunc k)) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := Polynomial k) (M := L)
  choose p q hq hqrep using fun i : Fin n => fun j : ι =>
    IsFractionRing.div_surjective (Polynomial k) (b.repr ((g i : L) : F) j)
  let a : Polynomial k := ∏ i : Fin n, ∏ j : ι, q i j
  have ha : a ≠ 0 := by
    dsimp [a]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact nonZeroDivisors.ne_zero (hq i j)
  let P : Submodule (Polynomial k) L :=
    (scaledDirectChartSubmodule b a).comap L.subtype
  have hgenerator : ∀ i : Fin n, g i ∈ P := by
    intro i
    change ∀ j : ι, b.repr (a • ((g i : L) : F)) j ∈
      Set.range (algebraMap (Polynomial k) (RatFunc k))
    intro j
    have hqne : algebraMap (Polynomial k) (RatFunc k) (q i j) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hq i j)
    have hclear : algebraMap (Polynomial k) (RatFunc k) (q i j) * b.repr ((g i : L) : F) j =
        algebraMap (Polynomial k) (RatFunc k) (p i j) := by
      simpa [mul_comm] using (div_eq_iff_mul_eq hqne).mp (hqrep i j)
    have hdiv : q i j ∣ a := by
      dsimp [a]
      exact
        (Finset.dvd_prod_of_mem (fun j : ι => q i j) (Finset.mem_univ j)).trans
          (Finset.dvd_prod_of_mem (fun i : Fin n => ∏ j : ι, q i j)
            (Finset.mem_univ i))
    rcases hdiv with ⟨c, hc⟩
    refine ⟨c * p i j, ?_⟩
    symm
    calc
      b.repr (a • ((g i : L) : F)) j =
          algebraMap (Polynomial k) (RatFunc k) a * b.repr ((g i : L) : F) j :=
        repr_smul_polynomial b a ((g i : L) : F) j
      _ = (algebraMap (Polynomial k) (RatFunc k) (q i j) *
          algebraMap (Polynomial k) (RatFunc k) c) *
          b.repr ((g i : L) : F) j := by
        rw [hc, map_mul]
      _ = algebraMap (Polynomial k) (RatFunc k) c *
          (algebraMap (Polynomial k) (RatFunc k) (q i j) * b.repr ((g i : L) : F) j) := by
        ac_rfl
      _ = algebraMap (Polynomial k) (RatFunc k) c *
          algebraMap (Polynomial k) (RatFunc k) (p i j) := by rw [hclear]
      _ = algebraMap (Polynomial k) (RatFunc k) (c * p i j) := by rw [map_mul]
  have htop : (⊤ : Submodule (Polynomial k) L) ≤ P := by
    rw [← hg]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨i, rfl⟩
    exact hgenerator i
  refine ⟨a, ha, ?_⟩
  intro x j
  have hx : x ∈ P := htop (by simp)
  change ∀ j : ι, b.repr (a • (x : F)) j ∈
    Set.range (algebraMap (Polynomial k) (RatFunc k)) at hx
  exact hx j
end QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator
