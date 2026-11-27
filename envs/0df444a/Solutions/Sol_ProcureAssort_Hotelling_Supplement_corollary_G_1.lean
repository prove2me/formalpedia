-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.corollary_G_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:41:52.229201+00:00
-- url     : https://prove2.me/submissions/c69267fb-92dc-4eeb-afab-6c40cc776e76

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f) (θ : Profile Θ) :
    let Q := affQ M Θ f θ
    let F := M.faceF Q
    ∀ i j : Q, M.faceA Q i j = -F i j +
      ((∑ k : Q, F k j) * (∑ k : Q, F i k)) / (∑ k : Q, ∑ l : Q, F k l) := by
        intro Q F i j
        have hp : ∀ k : Q, (if (k : Fin n) = (j : Fin n) then (1:ℝ) else 0) = if k = j then 1 else 0 := by
          intro k
          by_cases h : k = j
          · simp [h]
          · have : (k : Fin n) ≠ j := fun h' => h (Subtype.ext h')
            simp [h, this]
        simp only [QuadraticMarket.faceA, QuadraticMarket.faceDemand, Pi.zero_apply, sub_zero]
        simp only [hp]
        change (∑ k : Q, F i k * (M.c k - (if k = j then 1 else 0) +
            (1 - ∑ a : Q, ∑ b : Q, F a b * (M.c b - (if b = j then 1 else 0))) / (∑ a : Q, ∑ b : Q, F a b))) -
          (∑ k : Q, F i k * (M.c k +
            (1 - ∑ a : Q, ∑ b : Q, F a b * M.c b) / (∑ a : Q, ∑ b : Q, F a b))) = _
        set S := ∑ a : Q, ∑ b : Q, F a b
        have h1 : ∑ a : Q, ∑ b : Q, F a b * (M.c b - (if b = j then 1 else 0))
            = (∑ a : Q, ∑ b : Q, F a b * M.c b) - ∑ a : Q, F a j := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          simp [mul_sub, Finset.sum_sub_distrib]
        rw [h1]
        set C := ∑ a : Q, ∑ b : Q, F a b * M.c b
        have h2 : ∀ L : ℝ, ∑ k : Q, F i k * (M.c k - (if k = j then 1 else 0) + L)
            = ∑ k : Q, F i k * (M.c k + L) - F i j := by
          intro L
          have : ∀ k : Q, F i k * (M.c k - (if k = j then 1 else 0) + L)
              = F i k * (M.c k + L) - F i k * (if k = j then 1 else 0) := by intro k; ring
          simp only [this, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
        rw [h2]
        have h4 : ∀ L : ℝ, ∑ k : Q, F i k * (M.c k + L) = ∑ k : Q, F i k * M.c k + (∑ k : Q, F i k) * L := by
          intro L
          simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
        rw [h4, h4]
        have h5 : (1 - (C - ∑ a : Q, F a j)) / S - (1 - C) / S = (∑ a : Q, F a j) / S := by ring
        linear_combination (∑ k : Q, F i k) * h5
