-- Prove2me | solution 1 for SetCoverThreshold.SetCover.lemma_2_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:36:52.908354+00:00
-- url     : https://prove2.me/submissions/7f5e1cd0-b3e9-499c-9ef2-d2b6320a3f3c

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem

namespace SetCoverThreshold.SetCover

open Finset

theorem aux_sc_code_bound {ℓ k : ℕ} {code : Fin k → Fin ℓ → Bool} (hcode : IsCode ℓ k code)
    {i i' : Fin k} (hii : i ≠ i') :
    ℓ ≤ 6 * (univ.filter (fun j => code i j = true ∧ code i' j = false)).card := by
  obtain ⟨hw, hd⟩ := hcode
  have h1 := hw i
  have h2 := hw i'
  have h3 := hd i i' hii
  have hdist : hammingDist (code i) (code i') =
      (univ.filter (fun j => code i j ≠ code i' j)).card := rfl
  have key : (univ.filter (fun j => code i j ≠ code i' j)).card +
      (univ.filter (fun j => code i j = true)).card
      = 2 * (univ.filter (fun j => code i j = true ∧ code i' j = false)).card +
        (univ.filter (fun j => code i' j = true)).card := by
    simp only [card_filter, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    cases code i j <;> cases code i' j <;> simp
  omega

namespace Formula5

variable (φ : Formula5)

/-- Generalized question: on `S` given by `u`, outside `S` as prover `i` would get from `y`. -/
noncomputable def aux_sc_Q {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (S : Finset (Fin ℓ)) (i : Fin k)
    (u : Fin S.card → φ.QCoord) (y : {j // j ∉ S} → Fin φ.M × Fin 3) : Fin ℓ → φ.QCoord :=
  fun j => if h : j ∈ S then u (S.equivFin ⟨j, h⟩) else
    (if code i j then Sum.inl (y ⟨j, h⟩).1 else Sum.inr (φ.var (y ⟨j, h⟩).1 (y ⟨j, h⟩).2))

theorem aux_sc_question_eq {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (S : Finset (Fin ℓ))
    (i : Fin k) (r : φ.RandomString ℓ) (y : {j // j ∉ S} → Fin φ.M × Fin 3)
    (hout : ∀ j (h : j ∉ S), r j = y ⟨j, h⟩)
    (u : Fin S.card → φ.QCoord)
    (hu : ∀ j (h : j ∈ S), (if code i j then Sum.inl (r j).1 else
      Sum.inr (φ.var (r j).1 (r j).2)) = u (S.equivFin ⟨j, h⟩)) :
    φ.question code r i = φ.aux_sc_Q code S i u y := by
  funext j
  unfold question aux_sc_Q
  by_cases h : j ∈ S
  · rw [dif_pos h, ← hu j h]
  · rw [dif_neg h, hout j h]

open Classical in
theorem aux_sc_pair (c₀ : ℝ)
    (hR : ∀ (m : ℕ) (P₁ : φ.Prover1Strategy m) (P₂ : φ.Prover2Strategy m),
      φ.twoProverAcceptFrac m P₁ P₂ ≤ (2:ℝ) ^ (-(c₀ * m)))
    {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k) (i i' : Fin k)
    (S : Finset (Fin ℓ)) (hS : ∀ j ∈ S, code i j = true ∧ code i' j = false) :
    ((univ.filter (fun r : φ.RandomString ℓ => φ.Consistent code A r i i')).card : ℝ) ≤
      (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (φ.RandomString ℓ) := by
  let f := S.equivFin
  let E : (Fin ℓ → Fin φ.M × Fin 3) ≃
      (Fin S.card → Fin φ.M × Fin 3) × ({j // j ∉ S} → Fin φ.M × Fin 3) :=
    (Equiv.piEquivPiSubtypeProd (fun j => j ∈ S) (fun _ => Fin φ.M × Fin 3)).trans
      (Equiv.prodCongr (Equiv.arrowCongr f (Equiv.refl _)) (Equiv.refl _))
  have hEin : ∀ x y j (h : j ∈ S), E.symm (x, y) j = x (f ⟨j, h⟩) := by
    intro x y j h
    simp [E, Equiv.piEquivPiSubtypeProd, Equiv.arrowCongr, h]
  have hEout : ∀ x y j (h : j ∉ S), E.symm (x, y) j = y ⟨j, h⟩ := by
    intro x y j h
    simp [E, Equiv.piEquivPiSubtypeProd, Equiv.arrowCongr, h]
  let P₁ : ({j // j ∉ S} → Fin φ.M × Fin 3) → φ.Prover1Strategy S.card := fun y cs j' =>
    (A i (φ.aux_sc_Q code S i (fun j'' => Sum.inl (cs j'')) y)).1 (f.symm j').1
  let P₂ : ({j // j ∉ S} → Fin φ.M × Fin 3) → φ.Prover2Strategy S.card := fun y vs j' =>
    (A i' (φ.aux_sc_Q code S i' (fun j'' => Sum.inr (vs j'')) y)).1 (f.symm j').1 0
  have hsub : ∀ y, (univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
      φ.Consistent code A (E.symm (x, y)) i i')) ⊆
      univ.filter (fun x => φ.TwoProverAccepts (P₁ y) (P₂ y) x) := by
    intro y x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have hq1 : φ.question code (E.symm (x, y)) i =
        φ.aux_sc_Q code S i (fun j'' => Sum.inl (φ.clausesOf x j'')) y := by
      apply φ.aux_sc_question_eq code S i _ y (hEout x y)
      intro j h
      simp [(hS j h).1, hEin x y j h, clausesOf, f]
    have hq2 : φ.question code (E.symm (x, y)) i' =
        φ.aux_sc_Q code S i' (fun j'' => Sum.inr (φ.distVars x j'')) y := by
      apply φ.aux_sc_question_eq code S i' _ y (hEout x y)
      intro j h
      simp [(hS j h).2, hEin x y j h, distVars, f]
    intro j'
    have hjj : (f.symm j').1 ∈ S := (f.symm j').2
    have hfj : f ⟨(f.symm j').1, hjj⟩ = j' := by simp
    have hrj : E.symm (x, y) (f.symm j').1 = x j' := by rw [hEin x y _ hjj, hfj]
    constructor
    · have hcan := (A i (φ.aux_sc_Q code S i (fun j'' => Sum.inl (φ.clausesOf x j'')) y)).2
        (f.symm j').1
      have hQ : φ.aux_sc_Q code S i (fun j'' => Sum.inl (φ.clausesOf x j'')) y (f.symm j').1 =
          Sum.inl (x j').1 := by
        unfold aux_sc_Q
        rw [dif_pos hjj]
        simp only [f] at hfj
        rw [hfj]
        rfl
      rw [hQ] at hcan
      exact hcan
    · unfold Consistent at hx
      have hc := congrFun hx (f.symm j').1
      rw [hq1, hq2] at hc
      unfold inducedAssignment at hc
      rw [if_pos (hS _ hjj).1, if_neg (by simp [(hS _ hjj).2]), hrj] at hc
      exact hc
  have hN : (0:ℝ) < Fintype.card (Fin S.card → Fin φ.M × Fin 3) := by
    have : Nonempty (Fin S.card → Fin φ.M × Fin 3) := ⟨fun _ => (⟨0, φ.M_pos⟩, 0)⟩
    exact_mod_cast Fintype.card_pos
  have hy : ∀ y, ((univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
      φ.Consistent code A (E.symm (x, y)) i i')).card : ℝ) ≤
      (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (Fin S.card → Fin φ.M × Fin 3) := by
    intro y
    have h1 := hR S.card (P₁ y) (P₂ y)
    unfold twoProverAcceptFrac at h1
    rw [div_le_iff₀ hN] at h1
    refine le_trans ?_ h1
    exact_mod_cast card_le_card (hsub y)
  have hcount : (univ.filter (fun r : φ.RandomString ℓ => φ.Consistent code A r i i')).card =
      ∑ y : {j // j ∉ S} → Fin φ.M × Fin 3, (univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
        φ.Consistent code A (E.symm (x, y)) i i')).card := by
    rw [card_filter]
    rw [Fintype.sum_equiv E _ (fun p => if φ.Consistent code A (E.symm p) i i' then 1 else 0)
      (by intro r; simp)]
    rw [Fintype.sum_prod_type_right]
    simp only [card_filter]
  calc ((univ.filter (fun r : φ.RandomString ℓ => φ.Consistent code A r i i')).card : ℝ)
      = ∑ y : {j // j ∉ S} → Fin φ.M × Fin 3,
          ((univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
            φ.Consistent code A (E.symm (x, y)) i i')).card : ℝ) := by
        rw [hcount]; push_cast; rfl
    _ ≤ ∑ y : {j // j ∉ S} → Fin φ.M × Fin 3,
          (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (Fin S.card → Fin φ.M × Fin 3) :=
        sum_le_sum (fun y _ => hy y)
    _ = (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (φ.RandomString ℓ) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        rw [show Fintype.card (φ.RandomString ℓ) =
          Fintype.card ((Fin S.card → Fin φ.M × Fin 3) × ({j // j ∉ S} → Fin φ.M × Fin 3)) from
            Fintype.card_congr E, Fintype.card_prod]
        push_cast; ring

/-- Canonical answer bits from a truth assignment. -/
def aux_sc_cb (τ : ℕ → Bool) : φ.QCoord → Fin 3 → Bool
  | Sum.inl c => fun p => τ (φ.var c p : ℕ)
  | Sum.inr v => fun p => if p = 0 then τ (v : ℕ) else false

theorem aux_sc_cb_can (τ : ℕ → Bool) (hτ : ∀ C ∈ φ.toCNF, ∃ l ∈ C, τ l.2 = l.1)
    (x : φ.QCoord) : φ.CoordCanonical x (φ.aux_sc_cb τ x) := by
  cases x with
  | inl c =>
    have hmem : (List.ofFn fun p : Fin 3 => ((φ.clause c p).1, ((φ.clause c p).2 : ℕ))) ∈
        φ.toCNF := by
      unfold toCNF
      exact List.mem_ofFn.mpr ⟨c, rfl⟩
    obtain ⟨l, hl, hl'⟩ := hτ _ hmem
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hl
    exact ⟨p, hl'⟩
  | inr v => exact ⟨rfl, rfl⟩

theorem aux_sc_ind (τ : ℕ → Bool) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (r : φ.RandomString ℓ) (i : Fin k) :
    φ.inducedAssignment code r i (fun j => φ.aux_sc_cb τ (φ.question code r i j)) =
      fun j => τ (φ.var (r j).1 (r j).2 : ℕ) := by
  funext j
  unfold inducedAssignment question
  cases h : code i j <;> simp [h, aux_sc_cb]

end Formula5

end SetCoverThreshold.SetCover

open SetCoverThreshold.SetCover

theorem solution (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode ℓ k code →
        (φ.toCNF.Satisfiable → ∃ A : φ.KStrategy ℓ k, ∀ r, φ.StrongAccept code A r) ∧
          (AtMostFracSat (1 - ε) φ.toCNF → ∀ A : φ.KStrategy ℓ k,
            φ.weakAcceptFrac code A ≤ (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ))) := by
  classical
  obtain ⟨c₀, hc₀, hR⟩ := hRaz ε hε
  refine ⟨c₀ / 6, by positivity, ?_⟩
  intro φ ℓ k code hcode
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨fun i q => ⟨fun j => φ.aux_sc_cb τ (q j), fun j => φ.aux_sc_cb_can τ hτ (q j)⟩, ?_⟩
    intro r i i'
    unfold Formula5.Consistent
    exact (φ.aux_sc_ind τ code r i).trans (φ.aux_sc_ind τ code r i').symm
  · intro hφ A
    have hN : (0:ℝ) < Fintype.card (φ.RandomString ℓ) := by
      have : Nonempty (φ.RandomString ℓ) := ⟨fun _ => (⟨0, φ.M_pos⟩, 0)⟩
      exact_mod_cast Fintype.card_pos
    have hpair : ∀ p ∈ (Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)),
        ((Finset.univ.filter (fun r : φ.RandomString ℓ =>
          φ.Consistent code A r p.1 p.2)).card : ℝ) ≤
          (2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have h1 := φ.aux_sc_pair c₀ (hR φ hφ) code A p.1 p.2
        (Finset.univ.filter (fun j => code p.1 j = true ∧ code p.2 j = false))
        (fun j hj => by simpa using hj)
      have h2 := aux_sc_code_bound hcode hp
      refine le_trans (le_of_eq_of_le ?_ h1) (mul_le_mul_of_nonneg_right ?_ hN.le)
      · congr 1
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (ℓ:ℝ) ≤ 6 * ((Finset.univ.filter
          (fun j => code p.1 j = true ∧ code p.2 j = false)).card : ℝ) := by
        exact_mod_cast h2
      nlinarith
    unfold Formula5.weakAcceptFrac
    rw [div_le_iff₀ hN]
    calc ((Finset.univ.filter (fun r : φ.RandomString ℓ => φ.WeakAccept code A r)).card : ℝ)
        ≤ (((Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)).biUnion
            (fun p => Finset.univ.filter (fun r : φ.RandomString ℓ =>
              φ.Consistent code A r p.1 p.2))).card : ℝ) := by
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          intro r hr
          rw [Finset.mem_filter] at hr
          obtain ⟨_, i, i', hne, hc⟩ := hr
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(i, i'), hne, hc⟩
      _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2),
            ((Finset.univ.filter (fun r : φ.RandomString ℓ =>
              φ.Consistent code A r p.1 p.2)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2),
            (2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ) :=
          Finset.sum_le_sum hpair
      _ = ((Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)).card : ℝ) *
            ((2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) ^ 2 * ((2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)).card ≤ k ^ 2 := by
            refine le_trans (Finset.card_filter_le _ _) ?_
            simp [Finset.card_univ, Fintype.card_prod, sq]
          exact_mod_cast this
      _ = (k : ℝ) ^ 2 * (2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (φ.RandomString ℓ) := by ring
