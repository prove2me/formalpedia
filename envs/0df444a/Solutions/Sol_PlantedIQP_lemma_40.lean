-- Prove2me | solution 1 for PlantedIQP.lemma_40
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:58:23.226118+00:00
-- url     : https://prove2.me/submissions/ac380122-7a7d-4441-9d87-baff3b6960b7

import Mathlib
import Definitions.Def_PlantedIQP_IsVertexCover
import Definitions.Def_PlantedIQP_restrictCover
import Definitions.Def_PlantedIQP_amplitude
import Definitions.Def_PlantedIQP_mobiusCoeff

set_option autoImplicit false

namespace AuxLemma40

open PlantedIQP

lemma prod_indicatorVec {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (∏ i ∈ S, indicatorVec T i) = if S ⊆ T then 1 else 0 := by
  by_cases h : S ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [indicatorVec, h hi]
  · rw [if_neg h]
    rw [Finset.not_subset] at h
    rcases h with ⟨i, hiS, hiT⟩
    exact Finset.prod_eq_zero hiS (by simp [indicatorVec, hiT])

lemma mobiusCoeff_add {ι : Type*} [DecidableEq ι]
    (F G : (ι → ZMod 2) → ZMod 2) (S : Finset ι) :
    mobiusCoeff (fun x => F x + G x) S = mobiusCoeff F S + mobiusCoeff G S := by
  simp [mobiusCoeff, Finset.sum_add_distrib]

lemma mobiusCoeff_sum {ι α : Type*} [DecidableEq ι] (s : Finset α)
    (F : α → (ι → ZMod 2) → ZMod 2) (S : Finset ι) :
    mobiusCoeff (fun x => ∑ a ∈ s, F a x) S = ∑ a ∈ s, mobiusCoeff (F a) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mobiusCoeff]
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [mobiusCoeff_add, ih]

lemma mobiusCoeff_const_mul {ι : Type*} [DecidableEq ι]
    (c : ZMod 2) (F : (ι → ZMod 2) → ZMod 2) (S : Finset ι) :
    mobiusCoeff (fun x => c * F x) S = c * mobiusCoeff F S := by
  simp [mobiusCoeff, Finset.mul_sum]

lemma mobiusCoeff_monomial_eq_zero_of_lt {ι : Type*} [DecidableEq ι]
    (U S : Finset ι) (h : U.card < S.card) :
    mobiusCoeff (fun x => ∏ i ∈ U, x i) S = 0 := by
  classical
  simp only [mobiusCoeff, prod_indicatorVec]
  by_cases hUS : U ⊆ S
  · rw [Finset.sum_boole]
    have hcard : (S.powerset.filter (fun T => U ⊆ T)).card = 2 ^ (S \ U).card := by
      have hbij : (S.powerset.filter (fun T => U ⊆ T)).card = (S \ U).powerset.card := by
        refine Finset.card_bij (fun T _ => T \ U) ?_ ?_ ?_
        · intro T hT
          simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
          exact Finset.sdiff_subset_sdiff hT.1 subset_rfl
        · intro T₁ hT₁ T₂ hT₂ hEq
          simp only [Finset.mem_filter, Finset.mem_powerset] at hT₁ hT₂
          rw [← Finset.sdiff_union_of_subset hT₁.2, ← Finset.sdiff_union_of_subset hT₂.2, hEq]
        · intro W hW
          rw [Finset.mem_powerset] at hW
          refine ⟨W ∪ U, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finset.union_subset (hW.trans Finset.sdiff_subset) hUS, Finset.subset_union_right⟩
          · apply Finset.ext
            intro x
            simp only [Finset.mem_sdiff, Finset.mem_union]
            constructor
            · rintro ⟨hx | hx, hnx⟩
              · exact hx
              · exact absurd hx hnx
            · intro hx
              exact ⟨Or.inl hx, (Finset.mem_sdiff.mp (hW hx)).2⟩
      rw [hbij, Finset.card_powerset]
    rw [hcard]
    have hpos : 0 < (S \ U).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUS]
      omega
    rcases Nat.exists_eq_succ_of_ne_zero hpos.ne' with ⟨m, hm⟩
    rw [hm]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [pow_succ, h2]
  · apply Finset.sum_eq_zero
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [if_neg (fun hUT => hUS (hUT.trans hT))]

def uncoveredMonomial {n : ℕ} (C : Finset (Fin n)) (A : Finset (Fin n)) :
    Finset {i : Fin n // i ∉ C} :=
  (A \ C).attach.image fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).2⟩

lemma card_uncoveredMonomial_le {n : ℕ} (C A : Finset (Fin n)) :
    (uncoveredMonomial C A).card ≤ (A \ C).card := by
  calc (uncoveredMonomial C A).card
    _ ≤ (A \ C).attach.card := Finset.card_image_le
    _ = (A \ C).card := Finset.card_attach

lemma prod_merge_eq {n : ℕ} (C A : Finset (Fin n))
    (z : {i // i ∈ C} → ZMod 2) (y : {i // i ∉ C} → ZMod 2) :
    (∏ i ∈ A, merge C z y i) =
      (∏ i ∈ (A ∩ C).attach, z ⟨i.1, (Finset.mem_inter.mp i.2).2⟩) *
        (∏ j ∈ uncoveredMonomial C A, y j) := by
  classical
  have hpart : A = (A ∩ C) ∪ (A \ C) := by
    ext i; by_cases hi : i ∈ C <;> simp [hi]
  have hdisj : Disjoint (A ∩ C) (A \ C) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
  conv_lhs => rw [hpart]
  rw [Finset.prod_union hdisj]
  congr 1
  · rw [← Finset.prod_attach (A ∩ C)]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hiC : i.1 ∈ C := (Finset.mem_inter.mp i.2).2
    simp [merge, hiC]
  · simp only [uncoveredMonomial]
    rw [Finset.prod_image]
    · rw [← Finset.prod_attach (A \ C)]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hiC : i.1 ∉ C := (Finset.mem_sdiff.mp i.2).2
      simp [merge, hiC]
    · intro a _ b _ hab
      exact Subtype.ext (congr_arg (fun q : {i // i ∉ C} => q.1) hab)

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> rfl

def equivMerge {n : ℕ} (C : Finset (Fin n)) :
    (({i // i ∈ C} → ZMod 2) × ({i // i ∉ C} → ZMod 2)) ≃ Vec n where
  toFun p := merge C p.1 p.2
  invFun w := (fun i => w i.1, fun i => w i.1)
  left_inv p := by
    rcases p with ⟨z, y⟩
    ext i
    · simp [merge, i.2]
    · simp [merge, i.2]
  right_inv w := by
    ext i
    by_cases hi : i ∈ C <;> simp [merge, hi]

lemma sum_vec_merge {n : ℕ} (C : Finset (Fin n)) (x : Vec n)
    (z : {i // i ∈ C} → ZMod 2) (y : {i // i ∉ C} → ZMod 2) :
    (∑ i : Fin n, x i * merge C z y i) =
      (∑ i : {i // i ∈ C}, x i.1 * z i) + (∑ i : {i // i ∉ C}, x i.1 * y i) := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)) = C ∪ Cᶜ := by
    ext i; simp
  rw [huniv, Finset.sum_union disjoint_compl_right]
  congr 1
  · rw [← Finset.sum_coe_sort C]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [merge, i.2]
  · rw [← Finset.sum_coe_sort Cᶜ]
    refine Finset.sum_bij (fun i _ => ⟨i.1, Finset.mem_compl.mp i.2⟩) ?_ ?_ ?_ ?_
    · intro i _; simp
    · intro i _ j _ h; exact Subtype.ext (congr_arg (fun q : {i // i ∉ C} => q.1) h)
    · intro j _; exact ⟨⟨j.1, Finset.mem_compl.mpr j.2⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hi : i.1 ∉ C := Finset.mem_compl.mp i.2
      simp [merge, hi]

end AuxLemma40

open PlantedIQP AuxLemma40

theorem solution {n : ℕ} (f : CubicPoly n) (C : Finset (Fin n))
    (hC : IsVertexCover (polyHypergraph f) C) :
    (∀ z : {i // i ∈ C} → ZMod 2, DegLE (restrictCover f C z) 2) ∧
      ∀ x : Vec n, amp f x = (1 / (2 : ℝ) ^ C.card) *
        ∑ z : {i // i ∈ C} → ZMod 2,
          ngap (fun y => restrictCover f C z y + ∑ i : {i // i ∉ C}, x i.1 * y i) *
            (sgn (∑ i : {i // i ∈ C}, x i.1 * z i) : ℝ) := by
  refine ⟨?_, ?_⟩
  · intro z U hU
    change mobiusCoeff (fun y => (CubicPoly.eval f) (merge C z y)) U = 0
    simp only [CubicPoly.eval]
    rw [mobiusCoeff_add, mobiusCoeff_add, mobiusCoeff_sum, mobiusCoeff_sum, mobiusCoeff_sum]
    have h3 : ∑ m : Mono n 3, mobiusCoeff (fun y => f.c3 m * ∏ i ∈ m.1, merge C z y i) U = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      rcases zmod2_eq_zero_or_one (f.c3 m) with hc0 | hc1
      · simp [hc0, mobiusCoeff]
      · have hmem : m.1 ∈ polyHypergraph f := ⟨m, hc1, rfl⟩
        rcases hC m.1 hmem with ⟨v, hvm, hvC⟩
        have hfn : (fun y : {i // i ∉ C} → ZMod 2 => f.c3 m * ∏ i ∈ m.1, merge C z y i) =
            fun y => (f.c3 m * ∏ i ∈ (m.1 ∩ C).attach, z ⟨i.1, (Finset.mem_inter.mp i.2).2⟩) *
              ∏ j ∈ uncoveredMonomial C m.1, y j := by
          ext y; rw [prod_merge_eq, mul_assoc]
        rw [hfn, mobiusCoeff_const_mul]
        have hlt : (uncoveredMonomial C m.1).card < U.card := by
          have hpos : 0 < (C ∩ m.1).card := Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hvC, hvm⟩⟩
          have hsdiff : (m.1 \ C).card ≤ 2 := by
            rw [Finset.card_sdiff, m.2]
            omega
          exact lt_of_le_of_lt ((card_uncoveredMonomial_le C m.1).trans hsdiff) hU
        rw [mobiusCoeff_monomial_eq_zero_of_lt _ _ hlt, mul_zero]
    have h2 : ∑ m : Mono n 2, mobiusCoeff (fun y => f.c2 m * ∏ i ∈ m.1, merge C z y i) U = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      have hfn : (fun y : {i // i ∉ C} → ZMod 2 => f.c2 m * ∏ i ∈ m.1, merge C z y i) =
          fun y => (f.c2 m * ∏ i ∈ (m.1 ∩ C).attach, z ⟨i.1, (Finset.mem_inter.mp i.2).2⟩) *
            ∏ j ∈ uncoveredMonomial C m.1, y j := by
        ext y; rw [prod_merge_eq, mul_assoc]
      rw [hfn, mobiusCoeff_const_mul]
      have hlt : (uncoveredMonomial C m.1).card < U.card := by
        have hsdiff : (m.1 \ C).card ≤ 2 := by
          calc (m.1 \ C).card ≤ m.1.card := Finset.card_le_card Finset.sdiff_subset
            _ = 2 := m.2
        exact lt_of_le_of_lt ((card_uncoveredMonomial_le C m.1).trans hsdiff) hU
      rw [mobiusCoeff_monomial_eq_zero_of_lt _ _ hlt, mul_zero]
    have h1 : ∑ i : Fin n, mobiusCoeff (fun y => f.c1 i * merge C z y i) U = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hfn : (fun y : {i // i ∉ C} → ZMod 2 => f.c1 i * merge C z y i) =
          fun y => (f.c1 i * ∏ a ∈ (({i} : Finset (Fin n)) ∩ C).attach,
              z ⟨a.1, (Finset.mem_inter.mp a.2).2⟩) *
            ∏ j ∈ uncoveredMonomial C ({i} : Finset (Fin n)), y j := by
        ext y
        have hp := prod_merge_eq C ({i} : Finset (Fin n)) z y
        simp only [Finset.prod_singleton] at hp
        rw [hp, mul_assoc]
      rw [hfn, mobiusCoeff_const_mul]
      have hlt : (uncoveredMonomial C ({i} : Finset (Fin n))).card < U.card := by
        have hsdiff : (({i} : Finset (Fin n)) \ C).card ≤ 1 := by
          calc (({i} : Finset (Fin n)) \ C).card ≤ ({i} : Finset (Fin n)).card :=
              Finset.card_le_card Finset.sdiff_subset
            _ = 1 := Finset.card_singleton i
        exact lt_of_le_of_lt ((card_uncoveredMonomial_le C {i}).trans hsdiff) (by omega)
      rw [mobiusCoeff_monomial_eq_zero_of_lt _ _ hlt, mul_zero]
    rw [h3, h2, h1, add_zero, add_zero]
  · intro x
    simp only [amp, ngap, gap, Fintype.card_fin]
    have hsum :
        (∑ w : Vec n, sgn (f.eval w + ∑ i : Fin n, x i * w i)) =
          ∑ z : {i // i ∈ C} → ZMod 2,
            (∑ y : {i // i ∉ C} → ZMod 2,
              sgn (restrictCover f C z y + ∑ i : {i // i ∉ C}, x i.1 * y i)) *
            sgn (∑ i : {i // i ∈ C}, x i.1 * z i) := by
      rw [← Equiv.sum_comp (equivMerge C), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [equivMerge, Equiv.coe_fn_mk, restrictCover]
      rw [sum_vec_merge C x z y]
      have h_rearrange :
          f.eval (merge C z y) + ((∑ i : {i // i ∈ C}, x i.1 * z i) + ∑ i : {i // i ∉ C}, x i.1 * y i) =
            (f.eval (merge C z y) + ∑ i : {i // i ∉ C}, x i.1 * y i) + ∑ i : {i // i ∈ C}, x i.1 * z i := by
        ring
      rw [h_rearrange, sgn_add]
    rw [hsum]
    push_cast
    have hcard : n = C.card + Fintype.card {i : Fin n // i ∉ C} := by
      have hc1 : Fintype.card {i : Fin n // i ∈ C} = C.card := Fintype.card_coe C
      have hc2 := Fintype.card_subtype_compl (fun i : Fin n => i ∈ C)
      simp only [Fintype.card_fin] at hc2
      have hle : C.card ≤ n := by
        calc C.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ C
          _ = n := Finset.card_fin n
      omega
    have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ Fintype.card {i : Fin n // i ∉ C} * (2 : ℝ) ^ C.card := by
      rw [← pow_add, add_comm, ← hcard]
    rw [hpow, div_mul_eq_div_div, div_eq_inv_mul, one_div]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
