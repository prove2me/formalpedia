-- Prove2me | solution 1 for ScholtesStab.multipliers_unique
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:24:08.001082+00:00
-- url     : https://prove2.me/submissions/eda02b8b-3fd7-4a45-93bf-c5d6224d3b3a

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_MPCCLICQ
import Definitions.Def_ScholtesStab_MPCC_IsCStationary

namespace ScholtesStab.Aux_SS

open ScholtesStab ScholtesStab.MPCC

theorem sum_coe_union_ite {n κ : ℕ} (A B : Finset (Fin κ)) (hAB : Disjoint A B)
    (x y : Fin κ → ℝ) (v : Fin κ → (E n →L[ℝ] ℝ)) :
    ∑ j : ↥(A ∪ B), (if (j : Fin κ) ∈ A then x j else y j) • v j =
      ∑ j ∈ A, x j • v j + ∑ j ∈ B, y j • v j := by
  rw [Finset.sum_coe_sort (A ∪ B) (fun j => (if j ∈ A then x j else y j) • v j),
    Finset.sum_union hAB]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos hj]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg (Finset.disjoint_right.mp hAB hj)]

end ScholtesStab.Aux_SS

open ScholtesStab ScholtesStab.MPCC ScholtesStab.Aux_SS in
theorem solution {n κ : ℕ} (P : MPCC n κ) (xbar : E n) (m m' : MPCCMult κ)
    (hxbar : xbar ∈ P.M) (hLICQ : P.MPCCLICQ xbar)
    (hm : P.StatEq xbar m) (hm' : P.StatEq xbar m') :
    P.SameMult xbar m m' := by
  classical
  set A := P.a01 xbar with hA
  set B := P.a00 xbar with hB
  set C := P.a10 xbar with hC
  have hdAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro j hjA hjB
    simp only [hA, hB, MPCC.a01, MPCC.a00, Finset.mem_filter, Finset.mem_univ, true_and] at hjA hjB
    linarith [hjA.2, hjB.2]
  have hdCB : Disjoint C B := by
    rw [Finset.disjoint_left]
    intro j hjC hjB
    simp only [hC, hB, MPCC.a10, MPCC.a00, Finset.mem_filter, Finset.mem_univ, true_and] at hjC hjB
    linarith [hjC.1, hjB.1]
  have hdiff : ∑ j ∈ A, (m.σ₁ j - m'.σ₁ j) • fderiv ℝ (P.F₁ j) xbar +
      ∑ j ∈ C, (m.σ₂ j - m'.σ₂ j) • fderiv ℝ (P.F₂ j) xbar +
      (∑ j ∈ B, (m.ϱ₁ j - m'.ϱ₁ j) • fderiv ℝ (P.F₁ j) xbar +
        ∑ j ∈ B, (m.ϱ₂ j - m'.ϱ₂ j) • fderiv ℝ (P.F₂ j) xbar) = 0 := by
    have h := hm.symm.trans hm'
    rw [← sub_eq_zero] at h
    rw [← hA, ← hB, ← hC] at h
    have e : ∀ (T : Finset (Fin κ)) (a a' : Fin κ → ℝ) (v : Fin κ → (E n →L[ℝ] ℝ)),
        ∑ j ∈ T, (a j - a' j) • v j = ∑ j ∈ T, a j • v j - ∑ j ∈ T, a' j • v j := by
      intro T a a' v
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact sub_smul (a j) (a' j) (v j)
    rw [e A, e C, e B, e B, ← h, Finset.sum_add_distrib, Finset.sum_add_distrib]
    abel
  let g : ↥(A ∪ B) ⊕ ↥(C ∪ B) → ℝ :=
    Sum.elim (fun j => if (j : Fin κ) ∈ A then m.σ₁ j - m'.σ₁ j else m.ϱ₁ j - m'.ϱ₁ j)
      (fun j => if (j : Fin κ) ∈ C then m.σ₂ j - m'.σ₂ j else m.ϱ₂ j - m'.ϱ₂ j)
  have hli := (Fintype.linearIndependent_iff.mp hLICQ) g
  have hzero : ∑ i, g i • (Sum.elim (fun j : ↥(P.a01 xbar ∪ P.a00 xbar) => fderiv ℝ (P.F₁ j) xbar)
      (fun j : ↥(P.a10 xbar ∪ P.a00 xbar) => fderiv ℝ (P.F₂ j) xbar)) i = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [g, Sum.elim_inl, Sum.elim_inr]
    have e1 := sum_coe_union_ite A B hdAB (fun j => m.σ₁ j - m'.σ₁ j) (fun j => m.ϱ₁ j - m'.ϱ₁ j)
      (fun j => fderiv ℝ (P.F₁ j) xbar)
    have e2 := sum_coe_union_ite C B hdCB (fun j => m.σ₂ j - m'.σ₂ j) (fun j => m.ϱ₂ j - m'.ϱ₂ j)
      (fun j => fderiv ℝ (P.F₂ j) xbar)
    rw [e1, e2, ← hdiff]
    abel
  have hg := hli hzero
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have := hg (Sum.inl ⟨j, Finset.mem_union_left _ hj⟩)
    dsimp only [g, Sum.elim_inl] at this
    rw [if_pos hj, sub_eq_zero] at this
    exact this
  · intro j hj
    have := hg (Sum.inr ⟨j, Finset.mem_union_left _ hj⟩)
    dsimp only [g, Sum.elim_inr] at this
    rw [if_pos hj, sub_eq_zero] at this
    exact this
  · intro j hj
    have h1 := hg (Sum.inl ⟨j, Finset.mem_union_right _ hj⟩)
    have h2 := hg (Sum.inr ⟨j, Finset.mem_union_right _ hj⟩)
    dsimp only [g, Sum.elim_inl, Sum.elim_inr] at h1 h2
    rw [if_neg (Finset.disjoint_right.mp hdAB hj), sub_eq_zero] at h1
    rw [if_neg (Finset.disjoint_right.mp hdCB hj), sub_eq_zero] at h2
    exact ⟨h1, h2⟩
