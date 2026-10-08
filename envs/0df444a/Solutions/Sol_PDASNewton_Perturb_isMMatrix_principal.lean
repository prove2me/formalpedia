-- Prove2me | solution 1 for PDASNewton.Perturb.isMMatrix_principal
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:46:58.37971+00:00
-- url     : https://prove2.me/submissions/69062afb-a551-4745-bf24-90da96e03505

import Mathlib
import Definitions.Def_PDASNewton_Perturb_Setting

namespace Paper87
open Matrix

theorem positive_witness {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hu : IsUnit A.det)
    (hz : ∀ i j, i ≠ j → A i j ≤ 0) (hi : ∀ i j, 0 ≤ A⁻¹ i j) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∀ i, 0 < (A *ᵥ w) i := by
  let w : ι → ℝ := A⁻¹ *ᵥ (fun _ => 1)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact Finset.sum_nonneg (fun j _ => by simpa using hi i j)
  have he : A *ᵥ w = (fun _ => 1) := by
    dsimp [w]
    rw [mulVec_mulVec, mul_nonsing_inv A hu, one_mulVec]
  refine ⟨w, ?_, fun i => by rw [he]; norm_num⟩
  intro i
  by_contra hn
  have hzero : w i = 0 := le_antisymm (le_of_not_gt hn) (hw i)
  have hsum : (A *ᵥ w) i ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases h : i = j
    · subst j; simp [hzero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hz i j h) (hw j)
  rw [he] at hsum
  norm_num at hsum

theorem comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hz : ∀ i j, i ≠ j → A i j ≤ 0)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (haw : ∀ i, 0 < (A *ᵥ w) i)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i → (A *ᵥ v) i ≤ 0) :
    ∀ i, v i ≤ 0 := by
  intro l
  by_contra hn
  have hl : 0 < v l := lt_of_not_ge hn
  obtain ⟨i, _, himax⟩ := Finset.exists_max_image Finset.univ
    (fun j => v j / w j) ⟨l, Finset.mem_univ l⟩
  let t := v i / w i
  have ht : 0 < t := lt_of_lt_of_le (div_pos hl (hw l)) (himax l (Finset.mem_univ l))
  have hvi : v i = t * w i := by dsimp [t]; rw [div_mul_cancel₀ _ (ne_of_gt (hw i))]
  have hbound : ∀ j, v j ≤ t * w j := by
    intro j
    exact (div_le_iff₀ (hw j)).mp (himax j (Finset.mem_univ j))
  have hsum : t * (A *ᵥ w) i ≤ (A *ᵥ v) i := by
    simp only [mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases h : i = j
    · subst j; rw [hvi]; exact le_of_eq (by ring)
    · have hm := mul_le_mul_of_nonpos_left (hbound j) (hz i j h)
      nlinarith
  have hip : 0 < v i := by rw [hvi]; exact mul_pos ht (hw i)
  have := hv i hip
  have := mul_pos ht (haw i)
  linarith

theorem principal_properties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hu : IsUnit A.det)
    (hz : ∀ i j, i ≠ j → A i j ≤ 0) (hi : ∀ i j, 0 ≤ A⁻¹ i j)
    (S : Finset ι) :
    IsUnit (A.submatrix (fun i : S => (i : ι)) (fun i : S => (i : ι))).det ∧
      ∀ i j, 0 ≤ (A.submatrix (fun i : S => (i : ι)) (fun i : S => (i : ι)))⁻¹ i j := by
  classical
  let B : Matrix S S ℝ := A.submatrix Subtype.val Subtype.val
  obtain ⟨w, hw, haw⟩ := positive_witness A hu hz hi
  have hbz : ∀ i j : S, i ≠ j → B i j ≤ 0 := by
    intro i j hij
    exact hz i j (fun h => hij (Subtype.ext h))
  let ws : S → ℝ := fun i => w i
  have hbw : ∀ i : S, 0 < (B *ᵥ ws) i := by
    intro i
    have hle : (A *ᵥ w) i ≤ (B *ᵥ ws) i := by
      change (∑ j, A i j * w j) ≤ ∑ j : S, A i j * w j
      rw [Finset.sum_coe_sort S (fun j : ι => A (i : ι) j * w j)]
      apply Finset.sum_le_sum_of_subset_of_nonpos' (Finset.subset_univ S)
      intro j _ hj
      exact mul_nonpos_of_nonpos_of_nonneg
        (hz i j (fun he => hj (he ▸ i.property))) (hw j).le
    exact lt_of_lt_of_le (haw i) hle
  have cmp := comparison B hbz ws (fun i => hw i) hbw
  have binj : Function.Injective B.mulVec := by
    intro x z hxz
    have he : B *ᵥ (x-z) = 0 := by rw [mulVec_sub, hxz, sub_self]
    have hn : B *ᵥ (z-x) = 0 := by rw [mulVec_sub, hxz, sub_self]
    have hx := cmp (x-z) (fun i _ => by rw [he]; simp)
    have hz' := cmp (z-x) (fun i _ => by rw [hn]; simp)
    funext i
    have := hx i
    have := hz' i
    simp only [Pi.sub_apply] at *
    linarith
  have hbu : IsUnit B.det := (isUnit_iff_isUnit_det B).mp
    (mulVec_injective_iff_isUnit.mp binj)
  refine ⟨hbu, ?_⟩
  intro i j
  let v : S → ℝ := fun l => B⁻¹ l j
  have he : B *ᵥ v = fun l => (1 : Matrix S S ℝ) l j := by
    funext l
    exact congrArg (fun C : Matrix S S ℝ => C l j) (mul_nonsing_inv B hbu)
  have hn : ∀ l, (B *ᵥ (-v)) l ≤ 0 := by
    rw [mulVec_neg, he]
    intro l
    simp only [Pi.neg_apply, one_apply]
    split_ifs <;> norm_num
  have hneg := cmp (-v) (fun l _ => hn l)
  have := hneg i
  simpa [v] using neg_nonpos.mp this
end Paper87

namespace PDASNewton.Perturb

theorem isMMatrix_principal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsMMatrix M) :
    ∀ S : Finset (Fin n), IsMMatrix (PDASNewton.MMatrix.principal M S) := by
  intro S
  obtain ⟨hu, hi⟩ := Paper87.principal_properties M hM.1 hM.2.1 hM.2.2 S
  refine ⟨hu, ?_, hi⟩
  intro i j hij
  exact hM.2.1 i j (fun h => hij (Subtype.ext h))

end PDASNewton.Perturb


theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : PDASNewton.Perturb.IsMMatrix M) :
    ∀ S : Finset (Fin n), PDASNewton.Perturb.IsMMatrix (PDASNewton.MMatrix.principal M S) :=
  PDASNewton.Perturb.isMMatrix_principal M hM

#print axioms solution
