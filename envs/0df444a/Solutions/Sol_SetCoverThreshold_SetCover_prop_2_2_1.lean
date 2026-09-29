-- Prove2me | solution 1 for SetCoverThreshold.SetCover.prop_2_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:51:45.944001+00:00
-- url     : https://prove2.me/submissions/3bef982e-d545-4fe8-9ce3-a7ab0f199ba5

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem

namespace SetCoverThreshold.SetCover

theorem aux_pp221_card_eq (φ : Formula5) (P₁ : φ.Prover1Strategy 1) (P₂ : φ.Prover2Strategy 1) :
    (Finset.univ.filter (fun r : φ.RandomString 1 => φ.TwoProverAccepts P₁ P₂ r)).card =
      ∑ c : Fin φ.M, (Finset.univ.filter (fun p : Fin 3 =>
        φ.ClauseSatBy c (P₁ (fun _ => c) 0) ∧
          P₁ (fun _ => c) 0 p = P₂ (fun _ => φ.var c p) 0)).card := by
  have key : ∀ cp : Fin φ.M × Fin 3, φ.TwoProverAccepts P₁ P₂ (fun _ => cp) ↔
      (φ.ClauseSatBy cp.1 (P₁ (fun _ => cp.1) 0) ∧
        P₁ (fun _ => cp.1) 0 cp.2 = P₂ (fun _ => φ.var cp.1 cp.2) 0) := by
    intro cp
    simp only [Formula5.TwoProverAccepts, Fin.forall_fin_one]
    exact Iff.rfl
  have hr : ∀ r : φ.RandomString 1, r = fun _ => r 0 := by
    intro r; funext j; rw [Fin.fin_one_eq_zero j]
  have h1 : (Finset.univ.filter (fun r : φ.RandomString 1 => φ.TwoProverAccepts P₁ P₂ r)).card =
      (Finset.univ.filter (fun cp : Fin φ.M × Fin 3 =>
        φ.ClauseSatBy cp.1 (P₁ (fun _ => cp.1) 0) ∧
          P₁ (fun _ => cp.1) 0 cp.2 = P₂ (fun _ => φ.var cp.1 cp.2) 0)).card := by
    refine Finset.card_bij' (fun r _ => r 0) (fun cp _ => fun _ => cp) ?_ ?_ ?_ ?_
    · intro r hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      rw [hr r] at hmem
      exact (key (r 0)).1 hmem
    · intro cp hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      exact (key cp).2 hmem
    · intro r _
      exact (hr r).symm
    · intro cp _
      rfl
  rw [h1, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.card_filter]

theorem aux_pp221_clause_le (φ : Formula5) (c : Fin φ.M) (b s : Fin 3 → Bool) :
    (Finset.univ.filter (fun p : Fin 3 => φ.ClauseSatBy c b ∧ b p = s p)).card ≤
      2 + (if φ.ClauseSatBy c s then 1 else 0) := by
  by_cases hs : φ.ClauseSatBy c s
  · rw [if_pos hs]
    calc _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_univ _
      _ = 2 + 1 := by simp
  · rw [if_neg hs]
    by_cases hb : φ.ClauseSatBy c b
    · have hne : b ≠ s := by
        rintro rfl; exact hs hb
      obtain ⟨p, hp⟩ : ∃ p, b p ≠ s p := by
        by_contra h
        push Not at h
        exact hne (funext h)
      calc _ ≤ (Finset.univ.erase p).card := by
            apply Finset.card_le_card
            intro q hq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            rintro rfl
            exact hp hq.2
        _ = 2 + 0 := by simp
    · have : (Finset.univ.filter (fun p : Fin 3 => φ.ClauseSatBy c b ∧ b p = s p)) = ∅ := by
        ext p; simp [hb]
      rw [this]; simp

theorem aux_pp221_card_rs (φ : Formula5) :
    (Fintype.card (φ.RandomString 1) : ℝ) = 3 * φ.M := by
  simp [Formula5.RandomString]
  ring

theorem aux_pp221_exact (φ : Formula5) (c : Fin φ.M) (t : Fin 3 → Bool) :
    (Finset.univ.filter (fun p : Fin 3 =>
      φ.ClauseSatBy c (fun q => if q = 0 ∧ ¬ φ.ClauseSatBy c t then !t q else t q) ∧
        (fun q => if q = 0 ∧ ¬ φ.ClauseSatBy c t then !t q else t q) p = t p)).card =
      2 + (if φ.ClauseSatBy c t then 1 else 0) := by
  by_cases ht : φ.ClauseSatBy c t
  · simp only [ht, not_true_eq_false, and_false, if_false, true_and, if_true]
    simp
  · have hsat : φ.ClauseSatBy c
        (fun q => if q = 0 ∧ ¬ φ.ClauseSatBy c t then !t q else t q) := by
      refine ⟨0, ?_⟩
      simp only [ht, not_false_eq_true, and_true, if_true]
      have : t 0 ≠ (φ.clause c 0).1 := fun h => ht ⟨0, h⟩
      cases h1 : t 0 <;> cases h2 : (φ.clause c 0).1 <;> simp_all
    have hf : (Finset.univ.filter (fun p : Fin 3 =>
        φ.ClauseSatBy c (fun q => if q = 0 ∧ ¬ φ.ClauseSatBy c t then !t q else t q) ∧
          (fun q => if q = 0 ∧ ¬ φ.ClauseSatBy c t then !t q else t q) p = t p)) = {1, 2} := by
      simp only [ht, not_false_eq_true, and_true] at hsat ⊢
      ext p
      fin_cases p <;> simp [hsat]
    rw [hf, if_neg ht]
    rfl

theorem aux_pp221_sum (φ : Formula5) (P : Fin φ.M → Prop) [DecidablePred P] :
    ∑ c : Fin φ.M, (2 + if P c then 1 else 0) = 2 * φ.M + (Finset.univ.filter P).card := by
  rw [Finset.sum_add_distrib, Finset.card_filter]
  simp [mul_comm]

end SetCoverThreshold.SetCover

open SetCoverThreshold.SetCover

theorem solution (φ : Formula5) (τ : Fin φ.n → Bool)
    (hτ : ∀ τ' : Fin φ.n → Bool,
      (Finset.univ.filter (fun c => φ.ClauseSatBy c (fun p => τ' (φ.var c p)))).card ≤
        (Finset.univ.filter (fun c => φ.ClauseSatBy c (fun p => τ (φ.var c p)))).card)
    (ε : ℝ)
    (hε : ε = 1 - ((Finset.univ.filter
      (fun c => φ.ClauseSatBy c (fun p => τ (φ.var c p)))).card : ℝ) / φ.M) :
    (∃ (P₁ : φ.Prover1Strategy 1) (P₂ : φ.Prover2Strategy 1),
        φ.twoProverAcceptFrac 1 P₁ P₂ = 1 - ε / 3) ∧
      ∀ (P₁ : φ.Prover1Strategy 1) (P₂ : φ.Prover2Strategy 1),
        φ.twoProverAcceptFrac 1 P₁ P₂ ≤ 1 - ε / 3 := by
  have hM : (0:ℝ) < φ.M := by exact_mod_cast φ.M_pos
  have htarget : 1 - ε / 3 = ((2 * φ.M +
      (Finset.univ.filter (fun c => φ.ClauseSatBy c (fun p => τ (φ.var c p)))).card : ℕ) : ℝ) /
        (3 * φ.M) := by
    rw [hε]; push_cast; field_simp; ring
  refine ⟨?_, ?_⟩
  · refine ⟨fun q j p => if p = 0 ∧ ¬ φ.ClauseSatBy (q j) (fun p => τ (φ.var (q j) p))
        then !τ (φ.var (q j) p) else τ (φ.var (q j) p), fun q j => τ (q j), ?_⟩
    unfold Formula5.twoProverAcceptFrac
    rw [aux_pp221_card_eq, aux_pp221_card_rs, htarget]
    congr 2
    rw [← aux_pp221_sum]
    exact Finset.sum_congr rfl fun c _ => aux_pp221_exact φ c (fun p => τ (φ.var c p))
  · intro P₁ P₂
    unfold Formula5.twoProverAcceptFrac
    rw [aux_pp221_card_eq, aux_pp221_card_rs, htarget]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hA : ∑ c : Fin φ.M, (Finset.univ.filter (fun p : Fin 3 =>
        φ.ClauseSatBy c (P₁ (fun _ => c) 0) ∧
          P₁ (fun _ => c) 0 p = P₂ (fun _ => φ.var c p) 0)).card ≤
        2 * φ.M + (Finset.univ.filter
          (fun c => φ.ClauseSatBy c (fun p => τ (φ.var c p)))).card := by
      calc _ ≤ ∑ c : Fin φ.M,
            (2 + if φ.ClauseSatBy c (fun p => P₂ (fun _ => φ.var c p) 0) then 1 else 0) :=
            Finset.sum_le_sum fun c _ => aux_pp221_clause_le φ c _ _
        _ = 2 * φ.M + (Finset.univ.filter
            (fun c => φ.ClauseSatBy c (fun p => P₂ (fun _ => φ.var c p) 0))).card :=
            aux_pp221_sum φ _
        _ ≤ _ := by
            have := hτ (fun v => P₂ (fun _ => v) 0)
            omega
    exact_mod_cast hA
