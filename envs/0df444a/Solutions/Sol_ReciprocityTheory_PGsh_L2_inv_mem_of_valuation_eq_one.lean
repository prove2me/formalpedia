-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.inv_mem_of_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:31:26.636856+00:00
-- url     : https://prove2.me/submissions/30a2c044-c3b8-4c7f-a2c9-fb71de16f342

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_det_map_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
private lemma cols_mul_lemma {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (h : Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j)) :
    ∃ A : Matrix X X R, Q = P * A.map (algebraMap R C) := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => P x i) = fun x => Q x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext x j
  have hx := congrFun (hc j) x
  simp only [Finset.sum_apply, Pi.smul_apply] at hx
  rw [Matrix.mul_apply, ← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]
private lemma cols_le_lemma_2 {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (A : Matrix X X R) (hA : Q = P * A.map (algebraMap R C)) :
    Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hcol : (fun x => Q x j) = ∑ i, A i j • fun x => P x i := by
    ext x
    simp [hA, Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  show (fun x => Q x j) ∈ Submodule.span R _
  rw [hcol]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (A : Submodule R (X → C)) (P : Matrix X X C) (hP : IsUnit P.det)
    (hA : A = Submodule.span R (Set.range fun j x => P x j))
    (one : (1 : X → C) ∈ A) (mul : ∀ f g, f ∈ A → g ∈ A → f * g ∈ A)
    (u : X → C) (hu : u ∈ A) (hunit : ∀ x, v (u x) = 1) : u⁻¹ ∈ A := by
  have hu0 : ∀ x, u x ≠ 0 := fun x h0 => by simpa [h0] using hunit x
  have hPA : ∀ j, (fun x => P x j) ∈ A := fun j => by
    rw [hA]; exact Submodule.subset_span ⟨j, rfl⟩
  have hcolD : ∀ j, (fun x => (Matrix.diagonal u * P) x j) = u * fun x => P x j := by
    intro j; ext x; simp [Matrix.diagonal_mul]
  have hDle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (fun x => (Matrix.diagonal u * P) x j) ∈ Submodule.span R _
    rw [hcolD, ← hA]
    exact mul u _ hu (hPA j)
  obtain ⟨T, hT⟩ := cols_mul_lemma hDle
  have hdT : algebraMap R C T.det = ∏ x, u x := by
    have e := congrArg Matrix.det hT
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_map_algebraMap] at e
    exact mul_left_cancel₀ hP.ne_zero (by rw [← e]; ring)
  have hvT : v (algebraMap R C T.det) = 1 := by
    rw [hdT, map_prod]
    exact Finset.prod_eq_one fun x _ => hunit x
  have hy : algebraMap R C T.det ≠ 0 := by
    rw [hdT]; exact Finset.prod_ne_zero_iff.2 fun x _ => hu0 x
  obtain ⟨s, hs⟩ := hv.exists_of_le_one
    (show v (algebraMap R C T.det)⁻¹ ≤ 1 from le_of_eq (by rw [map_inv₀, hvT, inv_one]))
  have hTs : T.det * s = 1 := hv.hom_inj (by rw [map_mul, hs, mul_inv_cancel₀ hy, map_one])
  have hTu : IsUnit T.det := ⟨⟨T.det, s, hTs, by rw [mul_comm]; exact hTs⟩, rfl⟩
  have hPD : P = (Matrix.diagonal u * P) * (T⁻¹).map (algebraMap R C) := by
    rw [hT, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv T hTu]
    simp
  have hPle := cols_le_lemma_2 _ hPD
  have hmem : (1 : X → C) ∈
      Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) :=
    hPle (by rw [← hA]; exact one)
  have hle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      A.comap (LinearMap.mulLeft R u⁻¹) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    convert hPA j using 1
    ext x
    simp [Matrix.diagonal_mul, hu0 x]
  simpa using hle hmem
end ReciprocityTheory.PGsh.L2
