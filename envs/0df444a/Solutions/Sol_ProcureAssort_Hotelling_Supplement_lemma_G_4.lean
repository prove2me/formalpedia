-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.lemma_G_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:42:00.430637+00:00
-- url     : https://prove2.me/submissions/4858e892-8b20-46dc-9634-230e71779cdd

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f) (θ : Profile Θ)
    (hActive : affQ M Θ f θ = Finset.univ) :
    let A := M.faceA (affQ M Θ f θ)
    A.IsSymm ∧ A.rank = n - 1 := by
      intro A
      have hcard : Fintype.card (affQ M Θ f θ) = n := by
        rw [Fintype.card_coe, hActive]; simp
      show (M.faceA (affQ M Θ f θ)).IsSymm ∧ (M.faceA (affQ M Θ f θ)).rank = n - 1
      generalize affQ M Θ f θ = Q at hcard ⊢
      have hne : Nonempty Q := by
        rw [← Fintype.card_pos_iff, hcard]; exact hn
      set F := M.faceF Q with hFdef
      have hD : M.D.PosDef := hM.2.1.inv
      have hF : F.PosDef := (hD.submatrix Subtype.val_injective).inv
      have hFs : ∀ i j, F i j = F j i := by
        intro i j
        have := hF.isHermitian.apply i j
        simpa using this.symm
      set S : ℝ := ∑ i : Q, ∑ j : Q, F i j with hSdef
      have hS : 0 < S := by
        have h1 : (fun _ : Q => (1:ℝ)) ≠ 0 := by
          intro h
          obtain ⟨q⟩ := hne
          have := congrFun h q
          simp at this
        have := hF.dotProduct_mulVec_pos h1
        simpa [dotProduct, Matrix.mulVec, hSdef] using this
      have key : ∀ i j, M.faceA Q i j = -F i j + (∑ k, F i k) * (∑ k, F j k) / S := by
        intro i j
        simp only [QuadraticMarket.faceA, QuadraticMarket.faceDemand, ← hFdef, ← hSdef, Pi.zero_apply,
          sub_zero]
        rw [← Finset.sum_sub_distrib]
        simp only [Subtype.val_inj]
        have h1 : ∑ x : Q, ∑ y : Q, F x y * (M.c y - if y = j then 1 else 0)
            = ∑ x : Q, ∑ y : Q, F x y * M.c y - ∑ x : Q, F x j := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp [mul_sub, Finset.sum_sub_distrib]
        rw [h1]
        have h2 : ∀ x ∈ (Finset.univ : Finset Q),
            F i x * ((M.c x - if x = j then 1 else 0) +
                (1 - (∑ x : Q, ∑ y : Q, F x y * M.c y - ∑ x : Q, F x j)) / S) -
              F i x * (M.c x + (1 - ∑ x : Q, ∑ y : Q, F x y * M.c y) / S)
            = F i x * ((∑ y : Q, F y j) / S) - (if x = j then F i x else 0) := by
          intro x _
          split_ifs <;> ring
        rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← Finset.sum_mul]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have h3 : ∑ y : Q, F y j = ∑ k : Q, F j k := Finset.sum_congr rfl (fun y _ => hFs y j)
        rw [h3]
        ring
      constructor
      · rw [Matrix.IsSymm.ext_iff]
        intro i j
        rw [key, key, hFs i j]
        ring
      · set B := M.faceA Q with hBdef
        have hker : LinearMap.ker B.mulVecLin = Submodule.span ℝ {(fun _ : Q => (1:ℝ))} := by
          apply le_antisymm
          · intro x hx
            rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
            rw [Submodule.mem_span_singleton]
            set t : ℝ := (∑ k : Q, (∑ l : Q, F k l) * x k) / S with ht
            refine ⟨t, ?_⟩
            have hinj : Function.Injective F.mulVec :=
              Matrix.mulVec_injective_iff_isUnit.mpr hF.isUnit
            apply hinj
            funext i
            have hi : ∑ k : Q, B i k * x k = 0 := by
              have := congrFun hx i
              simpa [Matrix.mulVec, dotProduct] using this
            simp only [key] at hi
            show ∑ k : Q, F i k * (t • fun _ : Q => (1:ℝ)) k = ∑ k : Q, F i k * x k
            simp only [Pi.smul_apply, smul_eq_mul, mul_one]
            rw [← Finset.sum_mul]
            have e1 : ∑ k : Q, (-F i k + (∑ l : Q, F i l) * (∑ l : Q, F k l) / S) * x k
                = -∑ k : Q, F i k * x k + (∑ l : Q, F i l) * t := by
              rw [ht, Finset.sum_div, Finset.mul_sum, ← Finset.sum_neg_distrib,
                ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun k _ => ?_)
              ring
            rw [e1] at hi
            linarith
          · rw [Submodule.span_le, Set.singleton_subset_iff]
            show _ ∈ LinearMap.ker B.mulVecLin
            rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
            funext i
            show ∑ k : Q, B i k * (fun _ : Q => (1:ℝ)) k = 0
            simp only [key, mul_one]
            rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum]
            rw [← hSdef]
            field_simp
            ring
        have h1ne : (fun _ : Q => (1:ℝ)) ≠ 0 := by
          intro h
          obtain ⟨q⟩ := hne
          have := congrFun h q
          simp at this
        have hfk : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1 := by
          rw [hker]; exact finrank_span_singleton h1ne
        have hrn := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
        rw [hfk, Module.finrank_fintype_fun_eq_card, hcard] at hrn
        show Module.finrank ℝ (LinearMap.range B.mulVecLin) = n - 1
        omega
