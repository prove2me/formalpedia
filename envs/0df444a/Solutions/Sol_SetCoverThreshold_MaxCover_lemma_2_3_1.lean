-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.lemma_2_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:06:43.290267+00:00
-- url     : https://prove2.me/submissions/32b9faef-1a9b-4f49-8c2c-5668e6edf93c

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem

namespace SetCoverThreshold.MaxCover

open CookPvsNP Finset

theorem aux_mc_code_bound {ℓ k : ℕ} {code : Fin k → Fin ℓ → Bool} (hcode : IsCode code)
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

/-- Generalized question: on `S` given by `u`, outside `S` as prover `i` would get from `y`. -/
noncomputable def aux_mc_Q (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (S : Finset (Fin ℓ)) (i : Fin k)
    (u : Fin S.card → Fin φ.M ⊕ ℕ) (y : {j // j ∉ S} → Fin φ.M × Fin 3) : Question φ ℓ :=
  fun j => if h : j ∈ S then u (S.equivFin ⟨j, h⟩) else
    (if code i j then Sum.inl (y ⟨j, h⟩).1 else Sum.inr (φ.var (y ⟨j, h⟩).1 (y ⟨j, h⟩).2))

theorem aux_mc_question_eq (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (S : Finset (Fin ℓ))
    (i : Fin k) (r : RandString φ ℓ) (y : {j // j ∉ S} → Fin φ.M × Fin 3)
    (hout : ∀ j (h : j ∉ S), r j = y ⟨j, h⟩)
    (u : Fin S.card → Fin φ.M ⊕ ℕ)
    (hu : ∀ j (h : j ∈ S), (if code i j then Sum.inl (r j).1 else
      Sum.inr (φ.var (r j).1 (r j).2)) = u (S.equivFin ⟨j, h⟩)) :
    question φ code r i = aux_mc_Q φ code S i u y := by
  funext j
  unfold question aux_mc_Q
  by_cases h : j ∈ S
  · rw [dif_pos h, ← hu j h]
  · rw [dif_neg h, hout j h]

theorem aux_mc_sat (φ : Formula5) (x : Fin φ.M ⊕ ℕ) (a : CoordAnswer φ x) (c : Fin φ.M)
    (hx : x = Sum.inl c) : φ.LocalSat c (fun p => CoordAnswer.bit p x a) := by
  subst hx
  exact a.2

theorem aux_mc_bit_inr (φ : Formula5) (x : Fin φ.M ⊕ ℕ) (a : CoordAnswer φ x) (v : ℕ)
    (p p' : Fin 3) (hx : x = Sum.inr v) : CoordAnswer.bit p x a = CoordAnswer.bit p' x a := by
  subst hx
  rfl

open Classical in
theorem aux_mc_pair (φ : Formula5) (c₀ : ℝ)
    (hR : ∀ (m : ℕ) (P₁ : (Fin m → Fin φ.M) → Fin m → Fin 3 → Bool)
      (P₂ : (Fin m → ℕ) → Fin m → Bool),
      twoProverAcceptFrac φ P₁ P₂ ≤ (2:ℝ) ^ (-(c₀ * m)))
    {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (strat : Fin k → Strategy φ ℓ) (i i' : Fin k)
    (S : Finset (Fin ℓ)) (hS : ∀ j ∈ S, code i j = true ∧ code i' j = false) :
    ((univ.filter (fun r : RandString φ ℓ =>
      induced φ code strat r i = induced φ code strat r i')).card : ℝ) ≤
      (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (RandString φ ℓ) := by
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
  let P₁ : ({j // j ∉ S} → Fin φ.M × Fin 3) → (Fin S.card → Fin φ.M) → Fin S.card → Fin 3 → Bool :=
    fun y cs j' p =>
      CoordAnswer.bit p _ (strat i (aux_mc_Q φ code S i (fun j'' => Sum.inl (cs j'')) y)
        (f.symm j').1)
  let P₂ : ({j // j ∉ S} → Fin φ.M × Fin 3) → (Fin S.card → ℕ) → Fin S.card → Bool :=
    fun y vs j' =>
      CoordAnswer.bit 0 _ (strat i' (aux_mc_Q φ code S i' (fun j'' => Sum.inr (vs j'')) y)
        (f.symm j').1)
  have hsub : ∀ y, (univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
      induced φ code strat (E.symm (x, y)) i = induced φ code strat (E.symm (x, y)) i')) ⊆
      univ.filter (fun x => twoProverAccepts φ (P₁ y) (P₂ y) x) := by
    intro y x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have hq1 : question φ code (E.symm (x, y)) i =
        aux_mc_Q φ code S i (fun j'' => Sum.inl (x j'').1) y := by
      apply aux_mc_question_eq φ code S i _ y (hEout x y)
      intro j h
      simp [(hS j h).1, hEin x y j h, f]
    have hq2 : question φ code (E.symm (x, y)) i' =
        aux_mc_Q φ code S i' (fun j'' => Sum.inr (φ.var (x j'').1 (x j'').2)) y := by
      apply aux_mc_question_eq φ code S i' _ y (hEout x y)
      intro j h
      simp [(hS j h).2, hEin x y j h, f]
    intro j'
    have hjj : (f.symm j').1 ∈ S := (f.symm j').2
    have hfj : f ⟨(f.symm j').1, hjj⟩ = j' := by simp
    have hrj : E.symm (x, y) (f.symm j').1 = x j' := by rw [hEin x y _ hjj, hfj]
    constructor
    · apply aux_mc_sat
      unfold aux_mc_Q
      rw [dif_pos hjj]
      simp only [f] at hfj
      rw [hfj]
    · have hc := congrFun hx (f.symm j').1
      unfold induced answerBits at hc
      rw [hq1, hq2] at hc
      simp only [hrj] at hc
      show CoordAnswer.bit (x j').2 _ _ = CoordAnswer.bit 0 _ _
      rw [hc]
      apply aux_mc_bit_inr φ _ _ (φ.var (x j').1 (x j').2)
      unfold aux_mc_Q
      rw [dif_pos hjj]
      simp only [f] at hfj
      rw [hfj]
  have hy : ∀ y, ((univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
      induced φ code strat (E.symm (x, y)) i = induced φ code strat (E.symm (x, y)) i')).card
        : ℝ) ≤
      (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (Fin S.card → Fin φ.M × Fin 3) := by
    intro y
    rcases Nat.eq_zero_or_pos (Fintype.card (Fin S.card → Fin φ.M × Fin 3)) with h0 | hpos
    · have : (univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
          induced φ code strat (E.symm (x, y)) i =
            induced φ code strat (E.symm (x, y)) i')).card = 0 := by
        apply Nat.eq_zero_of_le_zero
        calc _ ≤ (univ : Finset (Fin S.card → Fin φ.M × Fin 3)).card := card_filter_le _ _
          _ = 0 := by rw [card_univ, h0]
      rw [this]
      push_cast
      positivity
    · have hN : (0:ℝ) < Fintype.card (Fin S.card → Fin φ.M × Fin 3) := by exact_mod_cast hpos
      have h1 := hR S.card (P₁ y) (P₂ y)
      unfold twoProverAcceptFrac at h1
      rw [div_le_iff₀ hN] at h1
      refine le_trans ?_ h1
      exact_mod_cast card_le_card (hsub y)
  have hcount : (univ.filter (fun r : RandString φ ℓ =>
      induced φ code strat r i = induced φ code strat r i')).card =
      ∑ y : {j // j ∉ S} → Fin φ.M × Fin 3, (univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
        induced φ code strat (E.symm (x, y)) i =
          induced φ code strat (E.symm (x, y)) i')).card := by
    rw [card_filter]
    rw [Fintype.sum_equiv E _ (fun p => if induced φ code strat (E.symm p) i =
      induced φ code strat (E.symm p) i' then 1 else 0) (by intro r; simp)]
    rw [Fintype.sum_prod_type_right]
    simp only [card_filter]
  calc ((univ.filter (fun r : RandString φ ℓ =>
        induced φ code strat r i = induced φ code strat r i')).card : ℝ)
      = ∑ y : {j // j ∉ S} → Fin φ.M × Fin 3,
          ((univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
            induced φ code strat (E.symm (x, y)) i =
              induced φ code strat (E.symm (x, y)) i')).card : ℝ) := by
        rw [hcount]; push_cast; rfl
    _ ≤ ∑ y : {j // j ∉ S} → Fin φ.M × Fin 3,
          (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (Fin S.card → Fin φ.M × Fin 3) :=
        sum_le_sum (fun y _ => hy y)
    _ = (2:ℝ) ^ (-(c₀ * S.card)) * Fintype.card (RandString φ ℓ) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        rw [show Fintype.card (RandString φ ℓ) =
          Fintype.card ((Fin S.card → Fin φ.M × Fin 3) × ({j // j ∉ S} → Fin φ.M × Fin 3)) from
            Fintype.card_congr E, Fintype.card_prod]
        push_cast; ring

/-- Canonical answer from a satisfying truth assignment. -/
def aux_mc_cb (φ : Formula5) (τ : ℕ → Bool)
    (hτ : ∀ c : Fin φ.M, φ.LocalSat c (fun p => τ (φ.var c p))) :
    (x : Fin φ.M ⊕ ℕ) → CoordAnswer φ x
  | Sum.inl c => (⟨fun p => τ (φ.var c p), hτ c⟩ : {b : Fin 3 → Bool // φ.LocalSat c b})
  | Sum.inr v => (τ v : Bool)

theorem aux_mc_loc (φ : Formula5) (τ : ℕ → Bool) (hτ : ∀ C ∈ φ.toCNF, ∃ l ∈ C, τ l.2 = l.1)
    (c : Fin φ.M) : φ.LocalSat c (fun p => τ (φ.var c p)) := by
  have hmem : List.ofFn (φ.clause c) ∈ φ.toCNF := by
    unfold Formula5.toCNF
    exact List.mem_ofFn.mpr ⟨c, rfl⟩
  obtain ⟨l, hl, hl'⟩ := hτ _ hmem
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hl
  exact ⟨p, hl'⟩

theorem aux_mc_cb_bit (φ : Formula5) (τ : ℕ → Bool)
    (hτ : ∀ c : Fin φ.M, φ.LocalSat c (fun p => τ (φ.var c p))) (x : Fin φ.M ⊕ ℕ) (p : Fin 3) :
    CoordAnswer.bit p x (aux_mc_cb φ τ hτ x) = Sum.elim (fun c => τ (φ.var c p)) τ x := by
  cases x <;> rfl

theorem aux_mc_ind (φ : Formula5) (τ : ℕ → Bool)
    (hτ : ∀ c : Fin φ.M, φ.LocalSat c (fun p => τ (φ.var c p)))
    {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (r : RandString φ ℓ) (i : Fin k) :
    induced φ code (fun _ q j => aux_mc_cb φ τ hτ (q j)) r i =
      fun j => τ (φ.var (r j).1 (r j).2) := by
  funext j
  show CoordAnswer.bit (r j).2 (question φ code r i j)
    (aux_mc_cb φ τ hτ (question φ code r i j)) = _
  rw [aux_mc_cb_bit]
  unfold question
  cases h : code i j <;> simp

end SetCoverThreshold.MaxCover

open SetCoverThreshold.MaxCover
open CookPvsNP

theorem solution (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode code →
        (φ.toCNF.Satisfiable →
            ∃ strat : Fin k → Strategy φ ℓ, ∀ r, StrongAccept φ code strat r) ∧
        (AtMostFracSat (1 - ε) φ.toCNF →
            ∀ strat : Fin k → Strategy φ ℓ,
              weakAcceptFrac φ code strat ≤ (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ))) := by
  classical
  obtain ⟨c₀, hc₀, hR⟩ := hRaz ε hε
  refine ⟨c₀ / 6, by positivity, ?_⟩
  intro φ ℓ k code hcode
  constructor
  · rintro ⟨τ, hτ⟩
    have hloc := aux_mc_loc φ τ hτ
    refine ⟨fun _ q j => aux_mc_cb φ τ hloc (q j), ?_⟩
    intro r i i'
    exact (aux_mc_ind φ τ hloc code r i).trans (aux_mc_ind φ τ hloc code r i').symm
  · intro hφ strat
    unfold weakAcceptFrac weakAcceptCount
    rcases Nat.eq_zero_or_pos (Fintype.card (RandString φ ℓ)) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, div_zero]
      positivity
    have hN : (0:ℝ) < Fintype.card (RandString φ ℓ) := by exact_mod_cast hpos
    have hpair : ∀ p ∈ (Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)),
        ((Finset.univ.filter (fun r : RandString φ ℓ =>
          induced φ code strat r p.1 = induced φ code strat r p.2)).card : ℝ) ≤
          (2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (RandString φ ℓ) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have h1 := aux_mc_pair φ c₀ (hR φ hφ) code strat p.1 p.2
        (Finset.univ.filter (fun j => code p.1 j = true ∧ code p.2 j = false))
        (fun j hj => by simpa using hj)
      have h2 := aux_mc_code_bound hcode hp
      refine le_trans (le_of_eq_of_le ?_ h1) (mul_le_mul_of_nonneg_right ?_ hN.le)
      · congr 1
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (ℓ:ℝ) ≤ 6 * ((Finset.univ.filter
          (fun j => code p.1 j = true ∧ code p.2 j = false)).card : ℝ) := by
        exact_mod_cast h2
      nlinarith
    rw [div_le_iff₀ hN]
    calc ((Finset.univ.filter (fun r : RandString φ ℓ => WeakAccept φ code strat r)).card : ℝ)
        ≤ (((Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)).biUnion
            (fun p => Finset.univ.filter (fun r : RandString φ ℓ =>
              induced φ code strat r p.1 = induced φ code strat r p.2))).card : ℝ) := by
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          intro r hr
          rw [Finset.mem_filter] at hr
          obtain ⟨_, i, i', hne, hc⟩ := hr
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(i, i'), hne, hc⟩
      _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2),
            ((Finset.univ.filter (fun r : RandString φ ℓ =>
              induced φ code strat r p.1 = induced φ code strat r p.2)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2),
            (2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (RandString φ ℓ) :=
          Finset.sum_le_sum hpair
      _ = ((Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)).card : ℝ) *
            ((2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (RandString φ ℓ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) ^ 2 * ((2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (RandString φ ℓ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)).card ≤ k ^ 2 := by
            refine le_trans (Finset.card_filter_le _ _) ?_
            simp [Finset.card_univ, Fintype.card_prod, sq]
          exact_mod_cast this
      _ = (k : ℝ) ^ 2 * (2:ℝ) ^ (-(c₀ / 6 * ℓ)) * Fintype.card (RandString φ ℓ) := by ring
