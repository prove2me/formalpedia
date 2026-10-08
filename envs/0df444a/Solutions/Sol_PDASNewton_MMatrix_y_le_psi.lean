-- Prove2me | solution 1 for PDASNewton.MMatrix.y_le_psi
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:53:50.896975+00:00
-- url     : https://prove2.me/submissions/195b021e-fef0-4c5d-b792-08cfe16672fc

import Mathlib
import Definitions.Def_PDASNewton_MMatrix_Setting

open Filter Topology Matrix

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

namespace PDASNewton.MMatrix

theorem complementarity_A1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → ∀ i, lam k i = 0 ∨ y k i = ψ i := by
  intro k hk i
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hs := hrun j
  by_cases h : 0 < lam j i + c * (y j i - ψ i)
  · exact Or.inr (hs.2.1 i h)
  · exact Or.inl (hs.2.2 i (le_of_not_gt h))

end PDASNewton.MMatrix

namespace PDASNewton.MMatrix

theorem y_antitone {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → y (k + 1) ≤ y k := by
  intro k hk
  obtain ⟨w, hw, haw⟩ := Paper87.positive_witness A hA.1 hA.2.1 hA.2.2
  have hs := hrun k
  have hcpl := complementarity_A1 A f ψ c y lam hrun k hk
  have heq := (hrun (k-1)).1
  have hkeq : k-1+1=k := by omega
  rw [hkeq] at heq
  have hv : ∀ i, 0 < (y (k+1)-y k) i → (A *ᵥ (y (k+1)-y k)) i ≤ 0 := by
    intro i hip
    have hnot : lam k i + c * (y k i - ψ i) ≤ 0 := by
      by_contra hn
      have hay := hs.2.1 i (lt_of_not_ge hn)
      rcases hcpl i with hl | hy
      · have hp : 0 < c * (y k i-ψ i) := by simpa [hl] using lt_of_not_ge hn
        have hpos := (mul_pos_iff_of_pos_left hc).mp hp
        simp only [Pi.sub_apply] at hip
        linarith
      · simp only [Pi.sub_apply] at hip
        linarith
    have hlam := hs.2.2 i hnot
    have hl : lam k i ≤ 0 := by
      rcases hcpl i with hl | hy
      · rw [hl]
      · simpa [hy] using hnot
    have he1 := congrFun hs.1 i
    have he0 := congrFun heq i
    rw [mulVec_sub]
    simp only [Pi.add_apply, Pi.sub_apply] at *
    linarith
  have hcmp := Paper87.comparison A hA.2.1 w hw haw (y (k+1)-y k) hv
  intro i
  have := hcmp i
  simpa using (sub_nonpos.mp this)


end PDASNewton.MMatrix

namespace PDASNewton.MMatrix

theorem y_le_psi {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 2 ≤ k → y k ≤ ψ := by
  intro k hk i
  have hprev : 1 ≤ k-1 := by omega
  have heq : k-1+1=k := by omega
  have hmono := y_antitone A f ψ c hc hA y lam hrun (k-1) hprev i
  rw [heq] at hmono
  by_cases h : y (k-1) i ≤ ψ i
  · exact hmono.trans h
  · have hgt : ψ i < y (k-1) i := lt_of_not_ge h
    have hl : lam (k-1) i = 0 := by
      rcases complementarity_A1 A f ψ c y lam hrun (k-1) hprev i with hl | hy
      · exact hl
      · linarith
    have hp : 0 < lam (k-1) i + c * (y (k-1) i-ψ i) := by
      rw [hl, zero_add]
      exact mul_pos hc (sub_pos.mpr hgt)
    have hy := (hrun (k-1)).2.1 i hp
    rw [heq] at hy
    exact hy.le


end PDASNewton.MMatrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : PDASNewton.MMatrix.IsMMatrix A) (y lam : ℕ → Fin n → ℝ)
    (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 2 ≤ k → y k ≤ ψ := PDASNewton.MMatrix.y_le_psi A f ψ c hc hA y lam hrun
#print axioms solution
