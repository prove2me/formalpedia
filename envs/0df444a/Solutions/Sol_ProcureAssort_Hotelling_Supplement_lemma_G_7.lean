-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.lemma_G_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:42:08.254986+00:00
-- url     : https://prove2.me/submissions/e44ce6af-43b0-4fb4-9286-dec0f2b3bcea

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f)
    (a : Profile Θ → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (hDep : RowDependence f (affQ M Θ f) (affX M Θ f) (affA M Θ f) a b) :
    ∀ θ : Profile Θ, ∑ i ∈ affQ M Θ f θ, (b i (θ i) / f i (θ i)) * affX M Θ f θ i = 0 := by
      classical
      -- generic algebra: row sums of faceA vanish when the total sum of F is nonzero
      have hrow : ∀ (Q : Finset (Fin n)), (∑ k : Q, ∑ l : Q, M.faceF Q k l) ≠ 0 →
          ∀ i : Q, ∑ m : Q, M.faceA Q i m = 0 := by
        intro Q hS i
        set F := M.faceF Q with hF
        set S := ∑ k : Q, ∑ l : Q, F k l with hSdef
        have hgen : ∀ p : Fin n → ℝ, M.faceDemand Q p i =
            (∑ j : Q, F i j * M.c j) - (∑ j : Q, F i j * p j) +
              (∑ j : Q, F i j) * ((1 - ∑ k : Q, ∑ l : Q, F k l * M.c l
                  + ∑ k : Q, ∑ l : Q, F k l * p l) / S) := by
          intro p
          simp only [QuadraticMarket.faceDemand]
          rw [← hF]
          have h1 : ∀ k : Q, ∑ l : Q, F k l * (M.c l - p l) =
              ∑ l : Q, F k l * M.c l - ∑ l : Q, F k l * p l := by
            intro k; rw [← Finset.sum_sub_distrib]; congr 1; ext l; ring
          simp only [h1]
          rw [Finset.sum_sub_distrib, ← hSdef]
          simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
          ring
        have he : ∀ (m : Q) (j : Q), ((fun k : Fin n => if k = m.val then (1:ℝ) else 0) j.val)
            = if j = m then 1 else 0 := by
          intro m j; simp
        simp only [QuadraticMarket.faceA, hgen, he, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          add_zero, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        calc _ = ∑ m : Q, (-F i m + (∑ j, F i j) * (∑ x, F x m) / S) := by
              apply Finset.sum_congr rfl; intro m _; field_simp; ring
          _ = 0 := by
              rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_comm (f := fun m x => F x m),
                ← hSdef, Finset.sum_neg_distrib, mul_div_assoc, div_self hS, mul_one, neg_add_cancel]
      have hSpos : ∀ Q : Finset (Fin n), Q.Nonempty → 0 < ∑ k : Q, ∑ l : Q, M.faceF Q k l := by
        intro Q hQ
        have hP : (M.faceF Q).PosDef := by
          unfold QuadraticMarket.faceF QuadraticMarket.D
          exact ((hM.2.1.inv).submatrix Subtype.val_injective).inv
        obtain ⟨q, hq⟩ := hQ
        have hne : (fun _ : Q => (1:ℝ)) ≠ 0 := by
          intro h; have := congrFun h ⟨q, hq⟩; simp at this
        have := hP.dotProduct_mulVec_pos hne
        simpa [dotProduct, Matrix.mulVec] using this
      intro θ
      set Q := affQ M Θ f θ with hQdef
      rcases Q.eq_empty_or_nonempty with hQ | hQ
      · simp [hQ]
      have hrowA : ∀ i ∈ Q, ∑ j ∈ Q, affA M Θ f θ i j = 0 := by
        intro i hi
        have := hrow Q (ne_of_gt (hSpos Q hQ)) ⟨i, hi⟩
        rw [← this, ← Finset.sum_coe_sort Q]
        apply Finset.sum_congr rfl
        intro j _
        simp only [affA, ← hQdef, dif_pos hi, dif_pos j.2]
        rfl
      have hsum : ∑ j ∈ Q, b j (θ j) * probOthers f j θ * affX M Θ f θ j = 0 := by
        have h0 := Finset.sum_eq_zero (hDep θ)
        rw [Finset.sum_add_distrib, Finset.sum_comm] at h0
        have h1 : ∑ y ∈ Q.filter (fun i => ReducedRow Q i), ∑ x ∈ Q, a θ y * affA M Θ f θ y x = 0 := by
          apply Finset.sum_eq_zero
          intro y hy
          rw [← Finset.mul_sum, hrowA y (Finset.mem_filter.1 hy).1, mul_zero]
        rw [h1, zero_add] at h0
        exact h0
      have hprob : 0 < prob f θ := by
        unfold prob
        exact Finset.prod_pos (fun j _ => hTypes.2.2.1 j (θ j) (θ j).2)
      have key : prob f θ * ∑ i ∈ Q, (b i (θ i) / f i (θ i)) * affX M Θ f θ i =
          ∑ j ∈ Q, b j (θ j) * probOthers f j θ * affX M Θ f θ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have hf : 0 < f j (θ j) := hTypes.2.2.1 j (θ j) (θ j).2
        have : prob f θ = f j (θ j) * probOthers f j θ := by
          unfold prob probOthers
          exact (Finset.mul_prod_erase _ (fun k => f k (θ k)) (Finset.mem_univ j)).symm
        rw [this]
        field_simp
      rw [hsum] at key
      exact (mul_eq_zero.1 key).resolve_left (ne_of_gt hprob)
