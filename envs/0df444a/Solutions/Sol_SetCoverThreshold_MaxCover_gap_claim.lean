-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.gap_claim
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:26:37.331047+00:00
-- url     : https://prove2.me/submissions/3fcaa843-3f7e-4f9b-a011-35f7278f3513

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

section PartA


open CookPvsNP Finset

theorem aux_gcA_code_bound {ℓ k : ℕ} {code : Fin k → Fin ℓ → Bool} (hcode : IsCode code)
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
noncomputable def aux_gcA_Q (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (S : Finset (Fin ℓ)) (i : Fin k)
    (u : Fin S.card → Fin φ.M ⊕ ℕ) (y : {j // j ∉ S} → Fin φ.M × Fin 3) : Question φ ℓ :=
  fun j => if h : j ∈ S then u (S.equivFin ⟨j, h⟩) else
    (if code i j then Sum.inl (y ⟨j, h⟩).1 else Sum.inr (φ.var (y ⟨j, h⟩).1 (y ⟨j, h⟩).2))

theorem aux_gcA_question_eq (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (S : Finset (Fin ℓ))
    (i : Fin k) (r : RandString φ ℓ) (y : {j // j ∉ S} → Fin φ.M × Fin 3)
    (hout : ∀ j (h : j ∉ S), r j = y ⟨j, h⟩)
    (u : Fin S.card → Fin φ.M ⊕ ℕ)
    (hu : ∀ j (h : j ∈ S), (if code i j then Sum.inl (r j).1 else
      Sum.inr (φ.var (r j).1 (r j).2)) = u (S.equivFin ⟨j, h⟩)) :
    question φ code r i = aux_gcA_Q φ code S i u y := by
  funext j
  unfold question aux_gcA_Q
  by_cases h : j ∈ S
  · rw [dif_pos h, ← hu j h]
  · rw [dif_neg h, hout j h]

theorem aux_gcA_sat (φ : Formula5) (x : Fin φ.M ⊕ ℕ) (a : CoordAnswer φ x) (c : Fin φ.M)
    (hx : x = Sum.inl c) : φ.LocalSat c (fun p => CoordAnswer.bit p x a) := by
  subst hx
  exact a.2

theorem aux_gcA_bit_inr (φ : Formula5) (x : Fin φ.M ⊕ ℕ) (a : CoordAnswer φ x) (v : ℕ)
    (p p' : Fin 3) (hx : x = Sum.inr v) : CoordAnswer.bit p x a = CoordAnswer.bit p' x a := by
  subst hx
  rfl

open Classical in
theorem aux_gcA_pair (φ : Formula5) (c₀ : ℝ)
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
      CoordAnswer.bit p _ (strat i (aux_gcA_Q φ code S i (fun j'' => Sum.inl (cs j'')) y)
        (f.symm j').1)
  let P₂ : ({j // j ∉ S} → Fin φ.M × Fin 3) → (Fin S.card → ℕ) → Fin S.card → Bool :=
    fun y vs j' =>
      CoordAnswer.bit 0 _ (strat i' (aux_gcA_Q φ code S i' (fun j'' => Sum.inr (vs j'')) y)
        (f.symm j').1)
  have hsub : ∀ y, (univ.filter (fun x : Fin S.card → Fin φ.M × Fin 3 =>
      induced φ code strat (E.symm (x, y)) i = induced φ code strat (E.symm (x, y)) i')) ⊆
      univ.filter (fun x => twoProverAccepts φ (P₁ y) (P₂ y) x) := by
    intro y x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have hq1 : question φ code (E.symm (x, y)) i =
        aux_gcA_Q φ code S i (fun j'' => Sum.inl (x j'').1) y := by
      apply aux_gcA_question_eq φ code S i _ y (hEout x y)
      intro j h
      simp [(hS j h).1, hEin x y j h, f]
    have hq2 : question φ code (E.symm (x, y)) i' =
        aux_gcA_Q φ code S i' (fun j'' => Sum.inr (φ.var (x j'').1 (x j'').2)) y := by
      apply aux_gcA_question_eq φ code S i' _ y (hEout x y)
      intro j h
      simp [(hS j h).2, hEin x y j h, f]
    intro j'
    have hjj : (f.symm j').1 ∈ S := (f.symm j').2
    have hfj : f ⟨(f.symm j').1, hjj⟩ = j' := by simp
    have hrj : E.symm (x, y) (f.symm j').1 = x j' := by rw [hEin x y _ hjj, hfj]
    constructor
    · apply aux_gcA_sat
      unfold aux_gcA_Q
      rw [dif_pos hjj]
      simp only [f] at hfj
      rw [hfj]
    · have hc := congrFun hx (f.symm j').1
      unfold induced answerBits at hc
      rw [hq1, hq2] at hc
      simp only [hrj] at hc
      show CoordAnswer.bit (x j').2 _ _ = CoordAnswer.bit 0 _ _
      rw [hc]
      apply aux_gcA_bit_inr φ _ _ (φ.var (x j').1 (x j').2)
      unfold aux_gcA_Q
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
def aux_gcA_cb (φ : Formula5) (τ : ℕ → Bool)
    (hτ : ∀ c : Fin φ.M, φ.LocalSat c (fun p => τ (φ.var c p))) :
    (x : Fin φ.M ⊕ ℕ) → CoordAnswer φ x
  | Sum.inl c => (⟨fun p => τ (φ.var c p), hτ c⟩ : {b : Fin 3 → Bool // φ.LocalSat c b})
  | Sum.inr v => (τ v : Bool)

theorem aux_gcA_loc (φ : Formula5) (τ : ℕ → Bool) (hτ : ∀ C ∈ φ.toCNF, ∃ l ∈ C, τ l.2 = l.1)
    (c : Fin φ.M) : φ.LocalSat c (fun p => τ (φ.var c p)) := by
  have hmem : List.ofFn (φ.clause c) ∈ φ.toCNF := by
    unfold Formula5.toCNF
    exact List.mem_ofFn.mpr ⟨c, rfl⟩
  obtain ⟨l, hl, hl'⟩ := hτ _ hmem
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hl
  exact ⟨p, hl'⟩

theorem aux_gcA_cb_bit (φ : Formula5) (τ : ℕ → Bool)
    (hτ : ∀ c : Fin φ.M, φ.LocalSat c (fun p => τ (φ.var c p))) (x : Fin φ.M ⊕ ℕ) (p : Fin 3) :
    CoordAnswer.bit p x (aux_gcA_cb φ τ hτ x) = Sum.elim (fun c => τ (φ.var c p)) τ x := by
  cases x <;> rfl

theorem aux_gcA_ind (φ : Formula5) (τ : ℕ → Bool)
    (hτ : ∀ c : Fin φ.M, φ.LocalSat c (fun p => τ (φ.var c p)))
    {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (r : RandString φ ℓ) (i : Fin k) :
    induced φ code (fun _ q j => aux_gcA_cb φ τ hτ (q j)) r i =
      fun j => τ (φ.var (r j).1 (r j).2) := by
  funext j
  show CoordAnswer.bit (r j).2 (question φ code r i j)
    (aux_gcA_cb φ τ hτ (question φ code r i j)) = _
  rw [aux_gcA_cb_bit]
  unfold question
  cases h : code i j <;> simp


theorem aux_gcA_main (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
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
    have hloc := aux_gcA_loc φ τ hτ
    refine ⟨fun _ q j => aux_gcA_cb φ τ hloc (q j), ?_⟩
    intro r i i'
    exact (aux_gcA_ind φ τ hloc code r i).trans (aux_gcA_ind φ τ hloc code r i').symm
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
      have h1 := aux_gcA_pair φ c₀ (hR φ hφ) code strat p.1 p.2
        (Finset.univ.filter (fun j => code p.1 j = true ∧ code p.2 j = false))
        (fun j hj => by simpa using hj)
      have h2 := aux_gcA_code_bound hcode hp
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

end PartA

section PartB


open Classical in
theorem aux_gcB_fib_card (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode code) (i : Fin k) (r₀ : RandString φ ℓ) :
    (Finset.univ.filter (fun r : RandString φ ℓ =>
        question φ code r i = question φ code r₀ i)).card = 3 ^ (ℓ / 2) * 5 ^ (ℓ / 2) := by
  set q := question φ code r₀ i with hqdef
  have hset : Finset.univ.filter (fun r : RandString φ ℓ => question φ code r i = q) =
      Fintype.piFinset (fun j => Finset.univ.filter (fun y : Fin φ.M × Fin 3 =>
        (if code i j then Sum.inl y.1 else Sum.inr (φ.var y.1 y.2)) = q j)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j; rw [← h]; rfl
    · intro h; funext j; exact h j
  rw [hset, Fintype.card_piFinset]
  have hA : ∀ j, (Finset.univ.filter (fun y : Fin φ.M × Fin 3 =>
        (if code i j then Sum.inl y.1 else Sum.inr (φ.var y.1 y.2)) = q j)).card =
        if code i j then 3 else 5 := by
    intro j
    by_cases hc : code i j = true
    · have hqj : q j = Sum.inl (r₀ j).1 := by simp [hqdef, question, hc]
      simp only [hc, if_true, hqj, Sum.inl.injEq]
      have : Finset.univ.filter (fun y : Fin φ.M × Fin 3 => y.1 = (r₀ j).1) =
          {(r₀ j).1} ×ˢ (Finset.univ : Finset (Fin 3)) := by
        ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_singleton, and_true]
      rw [this, Finset.card_product]; simp
    · have hqj : q j = Sum.inr (φ.var (r₀ j).1 (r₀ j).2) := by simp [hqdef, question, hc]
      simp only [hc, hqj]
      simp only [Bool.false_eq_true, if_false, Sum.inr.injEq]
      set v := φ.var (r₀ j).1 (r₀ j).2
      set s := Finset.univ.filter (fun y : Fin φ.M × Fin 3 => φ.var y.1 y.2 = v)
      have hinj : Set.InjOn Prod.fst (s : Set (Fin φ.M × Fin 3)) := by
        intro y hy y' hy' hyy
        simp only [s, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
        have h2 : y.2 = y'.2 := by
          apply φ.distinct_vars y.1
          show (φ.clause y.1 y.2).2 = (φ.clause y.1 y'.2).2
          have := hy.trans hy'.symm
          rw [hyy] at this ⊢
          simpa [Formula5.var, hyy] using this
        exact Prod.ext hyy h2
      rw [← Finset.card_image_of_injOn hinj]
      have himg : s.image Prod.fst =
          Finset.univ.filter (fun c => ∃ p, (φ.clause c p).2 = v) := by
        ext c
        simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Prod.exists, exists_and_right, exists_eq_right]
        exact Iff.rfl
      rw [himg]
      exact φ.five v ⟨(r₀ j).1, (r₀ j).2, rfl⟩
  rw [Finset.prod_congr rfl (fun j _ => hA j), Finset.prod_ite, Finset.prod_const,
    Finset.prod_const]
  have h1 := hcode.1 i
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin ℓ)))
    (fun j => code i j = true)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have e1 : (Finset.univ.filter (fun j => code i j = true)).card = ℓ / 2 := by omega
  have e2 : (Finset.univ.filter (fun j => ¬ code i j = true)).card = ℓ / 2 := by omega
  rw [e1, e2]

theorem aux_gcB_sum_weight (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode code) (C : Finset (SetIdx φ code)) (hC : C.card ≤ coverBudget φ code) :
    ∑ r, setWeight φ code C r ≤ k * Fintype.card (RandString φ ℓ) := by
  classical
  set F := 3 ^ (ℓ / 2) * 5 ^ (ℓ / 2) with hF
  have hfib : ∀ i (q : Question φ ℓ), q ∈ possibleQuestions φ code i →
      (Finset.univ.filter (fun r : RandString φ ℓ => question φ code r i = q)).card = F := by
    intro i q hq
    simp only [possibleQuestions, Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨r₀, rfl⟩ := hq
    convert aux_gcB_fib_card φ code hcode i r₀
  have hR : ∀ i, Fintype.card (RandString φ ℓ) = (possibleQuestions φ code i).card * F := by
    intro i
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := fun r => question φ code r i) (t := possibleQuestions φ code i)]
    · rw [Finset.sum_congr rfl (fun q hq => hfib i q hq), Finset.sum_const, smul_eq_mul]
    · intro r _; simp [possibleQuestions]
  have h1 : ∑ r, setWeight φ code C r = C.card * F := by
    have : ∀ r, setWeight φ code C r = ∑ s ∈ C, if s.2.1.1 = question φ code r s.1 then 1 else 0 := by
      intro r; rw [setWeight, Finset.card_filter]
    simp only [this]
    rw [Finset.sum_comm, Finset.card_eq_sum_ones C, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [one_mul, ← Finset.card_filter, ← hfib s.1 s.2.1.1 s.2.1.2]
    congr 1
    ext r; simp [eq_comm]
  calc ∑ r, setWeight φ code C r = C.card * F := h1
    _ ≤ coverBudget φ code * F := Nat.mul_le_mul_right _ hC
    _ = ∑ i : Fin k, Fintype.card (RandString φ ℓ) := by
        rw [coverBudget, Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => (hR i).symm)
    _ = k * Fintype.card (RandString φ ℓ) := by simp

open Classical in
theorem aux_gcB_fiber_bound (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) (hk : 1 ≤ k)
    (C : Finset (SetIdx φ code)) (r : RandString φ ℓ)
    (hcol : ¬ ∃ s ∈ C, ∃ s' ∈ C, s.1 ≠ s'.1 ∧ s.2.1.1 = question φ code r s.1 ∧
      s'.2.1.1 = question φ code r s'.1 ∧
      answerBits (fun j => (r j).2) s.2.2 = answerBits (fun j => (r j).2) s'.2.2) :
    (Fintype.card ((Fin ℓ → Bool) → Fin k) : ℝ) * (1 - 1 / (k:ℝ)) ^ (setWeight φ code C r) ≤
      (Fintype.card ((Fin ℓ → Bool) → Fin k) : ℝ) -
      ((Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k => ∃ s ∈ C,
          s.2.1.1 = question φ code r s.1 ∧
          x (answerBits (fun j => (r j).2) s.2.2) = s.1)).card : ℝ) := by
  set lab : SetIdx φ code → (Fin ℓ → Bool) := fun s => answerBits (fun j => (r j).2) s.2.2
    with hlab
  set P := C.filter (fun s => s.2.1.1 = question φ code r s.1) with hP
  have hw : setWeight φ code C r = P.card := rfl
  set T : (Fin ℓ → Bool) → Finset (Fin k) :=
    fun L => Finset.univ.filter (fun i => ∀ s ∈ P, lab s = L → i ≠ s.1) with hT
  set n : (Fin ℓ → Bool) → ℕ := fun L => (P.filter (fun s => lab s = L)).card with hn
  have hsum : ∑ L, n L = P.card :=
    (Finset.card_eq_sum_card_fiberwise (f := lab) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have ha0 : 0 ≤ 1 - 1 / (k:ℝ) := by
    rw [sub_nonneg, div_le_one hkpos]; exact_mod_cast hk
  have ha1 : 1 - 1 / (k:ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k:ℝ) := by positivity
    linarith
  have hTL : ∀ L, (k:ℝ) * (1 - 1 / (k:ℝ)) ^ (n L) ≤ ((T L).card : ℝ) := by
    intro L
    by_cases h0 : n L = 0
    · have hTu : T L = Finset.univ := by
        ext i
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        intro s hs hsL
        exfalso
        have hmem : s ∈ P.filter (fun s => lab s = L) := Finset.mem_filter.mpr ⟨hs, hsL⟩
        have : (P.filter (fun s => lab s = L)).card = 0 := h0
        rw [Finset.card_eq_zero] at this
        rw [this] at hmem
        exact absurd hmem (Finset.notMem_empty _)
      rw [h0, hTu]; simp
    · obtain ⟨s₀, hs₀⟩ : (P.filter (fun s => lab s = L)).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
      rw [Finset.mem_filter] at hs₀
      have hsub : Finset.univ.erase s₀.1 ⊆ T L := by
        intro i hi
        rw [Finset.mem_erase] at hi
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
        intro s hs hsL hEq
        apply hcol
        refine ⟨s, (Finset.mem_filter.mp hs).1, s₀, (Finset.mem_filter.mp hs₀.1).1, ?_,
          (Finset.mem_filter.mp hs).2, (Finset.mem_filter.mp hs₀.1).2, ?_⟩
        · rw [← hEq]; exact hi.1
        · have e1 : lab s = L := hsL
          have e2 : lab s₀ = L := hs₀.2
          exact e1.trans e2.symm
      have hcard : (k:ℝ) - 1 ≤ (T L).card := by
        have h := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin] at h
        have h' : ((k - 1 : ℕ) : ℝ) ≤ (T L).card := by exact_mod_cast h
        rw [Nat.cast_sub hk] at h'; simpa using h'
      have hpow : (1 - 1 / (k:ℝ)) ^ (n L) ≤ 1 - 1 / (k:ℝ) := pow_le_of_le_one ha0 ha1 h0
      calc (k:ℝ) * (1 - 1 / (k:ℝ)) ^ (n L) ≤ k * (1 - 1 / (k:ℝ)) :=
            mul_le_mul_of_nonneg_left hpow hkpos.le
        _ = k - 1 := by field_simp
        _ ≤ _ := hcard
  have hpi : Fintype.piFinset T ⊆ Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k =>
      ¬ ∃ s ∈ C, s.2.1.1 = question φ code r s.1 ∧ x (lab s) = s.1) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    intro s hs hq hx'
    have := hx (lab s)
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this s (Finset.mem_filter.mpr ⟨hs, hq⟩) rfl hx'
  have hadd := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : (Fin ℓ → Bool) → Fin k => ∃ s ∈ C, s.2.1.1 = question φ code r s.1 ∧
      x (lab s) = s.1)
  have hK : (Fintype.card ((Fin ℓ → Bool) → Fin k) : ℝ) = ∏ _L : Fin ℓ → Bool, (k:ℝ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  have hprod : (Fintype.card ((Fin ℓ → Bool) → Fin k) : ℝ) * (1 - 1 / (k:ℝ)) ^ P.card =
      ∏ L, ((k:ℝ) * (1 - 1 / (k:ℝ)) ^ (n L)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, hK]
  rw [hw, hprod]
  calc ∏ L, ((k:ℝ) * (1 - 1 / (k:ℝ)) ^ (n L)) ≤ ∏ L, ((T L).card : ℝ) :=
        Finset.prod_le_prod (fun L _ => mul_nonneg hkpos.le (pow_nonneg ha0 _))
          (fun L _ => hTL L)
    _ = ((Fintype.piFinset T).card : ℝ) := by rw [Fintype.card_piFinset]; push_cast; rfl
    _ ≤ ((Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k =>
      ¬ ∃ s ∈ C, s.2.1.1 = question φ code r s.1 ∧ x (lab s) = s.1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hpi
    _ = _ := by
        show _ = _ - ((Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k => ∃ s ∈ C,
          s.2.1.1 = question φ code r s.1 ∧ x (lab s) = s.1)).card : ℝ)
        rw [Finset.card_univ] at hadd
        rw [← hadd]; push_cast; ring

theorem aux_gcB_tangent (a : ℝ) (ha : 0 < a) (w k : ℕ) :
    a ^ k + a ^ k * Real.log a * ((w:ℝ) - k) ≤ a ^ w := by
  have hw : a ^ w = Real.exp (w * Real.log a) := by rw [Real.exp_nat_mul, Real.exp_log ha]
  have hk : a ^ k = Real.exp (k * Real.log a) := by rw [Real.exp_nat_mul, Real.exp_log ha]
  have hsplit : Real.exp (w * Real.log a) =
      Real.exp (k * Real.log a) * Real.exp (((w:ℝ) - k) * Real.log a) := by
    rw [← Real.exp_add]; ring_nf
  have h1 := Real.add_one_le_exp (((w:ℝ) - k) * Real.log a)
  have hpos := Real.exp_pos (k * Real.log a)
  rw [hw, hsplit, hk]
  nlinarith

theorem aux_gcB_limit (ε : ℝ) (hε : 0 < ε) : ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k →
    Real.exp (-1) - ε / 3 < (1 - 1 / (k:ℝ)) ^ k := by
  have h := Real.tendsto_one_add_div_pow_exp (-1)
  have h2 := h.eventually (lt_mem_nhds (show Real.exp (-1) - ε / 3 < Real.exp (-1) by linarith))
  rw [Filter.eventually_atTop] at h2
  obtain ⟨N, hN⟩ := h2
  refine ⟨N, fun k hk => ?_⟩
  have := hN k hk
  simpa [sub_eq_add_neg, neg_div] using this


theorem aux_gcB_main (ε : ℝ) (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (ℓ : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode code →
      ∀ (φ : Formula5) (C : Finset (SetIdx φ code)), C.card ≤ coverBudget φ code →
        (1 - Real.exp (-1) + ε) *
            (Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) : ℝ) ≤
          ((coveredMaxCover φ code C).card : ℝ) →
        ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) ≤ (goodCount φ code ε C : ℝ) := by
  classical
  obtain ⟨k₁, hk₁⟩ := aux_gcB_limit ε hε
  refine ⟨max k₁ 2, ?_⟩
  intro k hk ℓ code hcode φ C hC hcov
  have hk1 : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set a : ℝ := 1 - 1 / (k:ℝ) with ha
  have ha0 : 0 < a := by
    rw [ha, sub_pos, div_lt_one hkpos]; exact_mod_cast (by omega : 1 < k)
  have ha1 : a ≤ 1 := by
    have : 0 ≤ 1 / (k:ℝ) := by positivity
    linarith
  have hlog : Real.log a ≤ 0 := Real.log_nonpos ha0.le ha1
  set R := Fintype.card (RandString φ ℓ) with hR
  set K := Fintype.card ((Fin ℓ → Bool) → Fin k) with hK
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hKpos : (0:ℝ) < K := by
    rw [hK]; exact_mod_cast Fintype.card_pos
  set w : RandString φ ℓ → ℕ := fun r => setWeight φ code C r with hw
  set Col : RandString φ ℓ → Prop := fun r => ∃ s ∈ C, ∃ s' ∈ C, s.1 ≠ s'.1 ∧
      s.2.1.1 = question φ code r s.1 ∧ s'.2.1.1 = question φ code r s'.1 ∧
      answerBits (fun j => (r j).2) s.2.2 = answerBits (fun j => (r j).2) s'.2.2 with hCol
  set Fr : RandString φ ℓ → Finset ((Fin ℓ → Bool) → Fin k) := fun r =>
    Finset.univ.filter (fun x : (Fin ℓ → Bool) → Fin k => ∃ s ∈ C,
          s.2.1.1 = question φ code r s.1 ∧
          x (answerBits (fun j => (r j).2) s.2.2) = s.1) with hFr
  -- Step 1: the covered points, counted copy by copy
  have hcovcard : (coveredMaxCover φ code C).card = ∑ r, (Fr r).card := by
    have : coveredMaxCover φ code C = Finset.univ.filter
        (fun p : RandString φ ℓ × ((Fin ℓ → Bool) → Fin k) => p.2 ∈ Fr p.1) := by
      ext p
      simp [coveredMaxCover, reductionSet, cubeSystem, hFr, eq_comm]
    rw [this, Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r _
    simp
  -- Step 2: bound in each copy
  have hstep2 : ∀ r, ((Fr r).card : ℝ) ≤ (if Col r then (K:ℝ) else 0) + K * (1 - a ^ (w r)) := by
    intro r
    have hpow : a ^ (w r) ≤ 1 := pow_le_one₀ ha0.le ha1
    by_cases hc : Col r
    · rw [if_pos hc]
      have h1 : ((Fr r).card : ℝ) ≤ K := by
        rw [hK]; exact_mod_cast Finset.card_le_univ _
      have h2 : 0 ≤ (K:ℝ) * (1 - a ^ (w r)) := mul_nonneg hKpos.le (by linarith)
      linarith
    · rw [if_neg hc]
      have := aux_gcB_fiber_bound φ code (by omega) C r hc
      linarith
  -- Step 3: averaging the coverage bound
  have hsw : ((∑ r, w r : ℕ) : ℝ) ≤ k * R := by
    exact_mod_cast aux_gcB_sum_weight φ code hcode C hC
  have hstep3 : ∑ r, (1 - a ^ (w r)) ≤ (R:ℝ) * (1 - a ^ k) := by
    have ht : ∀ r, 1 - a ^ (w r) ≤ (1 - a ^ k) - a ^ k * Real.log a * ((w r : ℝ) - k) := by
      intro r; have := aux_gcB_tangent a ha0 (w r) k; linarith
    have hsum_eq : ∑ r, ((1 - a ^ k) - a ^ k * Real.log a * ((w r : ℝ) - k)) =
        R * (1 - a ^ k) - a ^ k * Real.log a * ((∑ r, (w r : ℝ)) - k * R) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
      simp [hR]
      ring
    have h1 : (∑ r, (w r : ℝ)) - k * R ≤ 0 := by push_cast at hsw; linarith
    have h2 : a ^ k * Real.log a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha0.le _) hlog
    calc ∑ r, (1 - a ^ (w r)) ≤ ∑ r, ((1 - a ^ k) - a ^ k * Real.log a * ((w r : ℝ) - k)) :=
          Finset.sum_le_sum (fun r _ => ht r)
      _ = _ := hsum_eq
      _ ≤ R * (1 - a ^ k) := by
          have : 0 ≤ (a ^ k * Real.log a) * ((∑ r, (w r : ℝ)) - k * R) :=
            mul_nonneg_of_nonpos_of_nonpos h2 h1
          linarith
  -- Step 4: collisions are good or heavy
  set B1 := Finset.univ.filter (fun r => (3 * k / ε : ℝ) < w r) with hB1
  have hstep4 : (Finset.univ.filter Col).card ≤ goodCount φ code ε C + B1.card := by
    have hsub : Finset.univ.filter Col ⊆ Finset.univ.filter (IsGood φ code ε C) ∪ B1 := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Finset.mem_union]
      by_cases hb : (3 * k / ε : ℝ) < w r
      · right; simp [hB1, hb]
      · left
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨le_of_not_gt hb, ?_⟩
        obtain ⟨s, hs, s', hs', h1, h2, h3, h4⟩ := hr
        exact ⟨s, hs, s', hs', h1, h2, h3, h4⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ = _ := by rw [goodCount]
  -- Step 5: Markov
  have hstep5 : (B1.card : ℝ) * (3 * k / ε) ≤ k * R := by
    calc (B1.card : ℝ) * (3 * k / ε) = ∑ r ∈ B1, (3 * k / ε : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ B1, (w r : ℝ) :=
          Finset.sum_le_sum (fun r hr => le_of_lt (Finset.mem_filter.mp hr).2)
      _ ≤ ∑ r, (w r : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ k * R := by push_cast at hsw; exact hsw
  have hB1le : (B1.card : ℝ) ≤ ε * R / 3 := by
    have hpos : 0 < ε / (3 * k) := by positivity
    have := mul_le_mul_of_nonneg_right hstep5 hpos.le
    have e1 : (B1.card : ℝ) * (3 * k / ε) * (ε / (3 * k)) = B1.card := by field_simp
    have e2 : (k:ℝ) * R * (ε / (3 * k)) = ε * R / 3 := by field_simp
    linarith
  -- Step 6: the limit
  have hstep6 : 1 - a ^ k ≤ 1 - Real.exp (-1) + ε / 3 := by
    have := hk₁ k hk1; linarith
  -- Combine
  have hcov' : (K:ℝ) * ((1 - Real.exp (-1) + ε) * R) ≤ ∑ r, ((Fr r).card : ℝ) := by
    have : (Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) : ℝ) = R * K := by
      rw [Fintype.card_prod]; push_cast; rfl
    rw [this, hcovcard] at hcov
    push_cast at hcov
    linarith
  have hsum2 : ∑ r, ((Fr r).card : ℝ) ≤
      (Finset.univ.filter Col).card * K + K * ∑ r, (1 - a ^ (w r)) := by
    calc ∑ r, ((Fr r).card : ℝ) ≤ ∑ r, ((if Col r then (K:ℝ) else 0) + K * (1 - a ^ (w r))) :=
          Finset.sum_le_sum (fun r _ => hstep2 r)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
            ← Finset.mul_sum, nsmul_eq_mul, add_zero]
  have hmain : (K:ℝ) * ((1 - Real.exp (-1) + ε) * R) ≤
      K * ((goodCount φ code ε C : ℝ) + B1.card + R * (1 - a ^ k)) := by
    have h4 : ((Finset.univ.filter Col).card : ℝ) ≤ goodCount φ code ε C + B1.card := by
      exact_mod_cast hstep4
    have h4' := mul_le_mul_of_nonneg_right h4 hKpos.le
    have h3' := mul_le_mul_of_nonneg_left hstep3 hKpos.le
    calc (K:ℝ) * ((1 - Real.exp (-1) + ε) * R) ≤ ∑ r, ((Fr r).card : ℝ) := hcov'
      _ ≤ _ := hsum2
      _ ≤ _ := add_le_add h4' h3'
      _ = _ := by ring
  have hfin := le_of_mul_le_mul_left hmain hKpos
  have hR0 : (0:ℝ) ≤ R := Nat.cast_nonneg _
  have h6' : (R:ℝ) * (1 - a ^ k) ≤ R * (1 - Real.exp (-1) + ε / 3) :=
    mul_le_mul_of_nonneg_left hstep6 hR0
  linarith

end PartB

section PartC

open CookPvsNP

/-- A default canonical answer on one coordinate. -/
def aux_gcD_dflt (φ : Formula5) : (x : Fin φ.M ⊕ ℕ) → CoordAnswer φ x
  | Sum.inl c => (⟨fun p => (φ.clause c p).1, ⟨0, rfl⟩⟩ : {b : Fin 3 → Bool // φ.LocalSat c b})
  | Sum.inr _ => (false : Bool)

/-- The strategy induced by a choice of answers to the possible questions. -/
noncomputable def aux_gcD_strat (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (θ : (p : Σ i : Fin k, possibleQuestions φ code i) → Answer φ p.2.1) :
    Fin k → Strategy φ ℓ :=
  fun i q => if h : q ∈ possibleQuestions φ code i then θ ⟨i, ⟨q, h⟩⟩
    else fun j => aux_gcD_dflt φ (q j)

theorem aux_gcD_induced (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (θ : (p : Σ i : Fin k, possibleQuestions φ code i) → Answer φ p.2.1)
    (r : RandString φ ℓ) (p : Σ i : Fin k, possibleQuestions φ code i)
    (hp : p.2.1 = question φ code r p.1) :
    induced φ code (aux_gcD_strat φ code θ) r p.1 = answerBits (fun j => (r j).2) (θ p) := by
  obtain ⟨i, q, hq⟩ := p
  simp only at hp
  subst hp
  unfold induced aux_gcD_strat
  rw [dif_pos hq]

theorem aux_gcD_pi_two {ι : Type} [Fintype ι] [DecidableEq ι] {δ : ι → Type}
    [∀ i, DecidableEq (δ i)] (A : ∀ i, Finset (δ i)) (p p' : ι) (hpp : p ≠ p')
    (a : δ p) (a' : δ p') (ha : a ∈ A p) (ha' : a' ∈ A p') :
    ((Fintype.piFinset A).filter (fun θ => θ p = a ∧ θ p' = a')).card *
        ((A p).card * (A p').card) = (Fintype.piFinset A).card := by
  set B : ∀ i, Finset (δ i) := Function.update (Function.update A p {a}) p' {a'} with hB
  have hBp' : B p' = {a'} := by simp [hB]
  have hBp : B p = {a} := by simp [hB, Function.update_of_ne hpp]
  have hBx : ∀ x, x ≠ p → x ≠ p' → B x = A x := by
    intro x h1 h2; simp [hB, Function.update_of_ne h1, Function.update_of_ne h2]
  have hfil : (Fintype.piFinset A).filter (fun θ => θ p = a ∧ θ p' = a') =
      Fintype.piFinset B := by
    ext θ
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hA, h1, h2⟩ x
      by_cases hx : x = p
      · subst hx; rw [hBp, h1]; exact Finset.mem_singleton_self _
      · by_cases hx' : x = p'
        · subst hx'; rw [hBp', h2]; exact Finset.mem_singleton_self _
        · rw [hBx x hx hx']; exact hA x
    · intro h
      have h1 : θ p = a := by
        have := h p; rw [hBp] at this; exact Finset.mem_singleton.mp this
      have h2 : θ p' = a' := by
        have := h p'; rw [hBp'] at this; exact Finset.mem_singleton.mp this
      refine ⟨fun x => ?_, h1, h2⟩
      by_cases hx : x = p
      · subst hx; rw [h1]; exact ha
      · by_cases hx' : x = p'
        · subst hx'; rw [h2]; exact ha'
        · have := h x; rwa [hBx x hx hx'] at this
  rw [hfil, Fintype.card_piFinset, Fintype.card_piFinset]
  have hp_mem : p ∈ (Finset.univ : Finset ι).erase p' :=
    Finset.mem_erase.mpr ⟨hpp, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun x => (B x).card) (Finset.mem_univ p'),
    ← Finset.mul_prod_erase _ (fun x => (B x).card) hp_mem,
    ← Finset.mul_prod_erase Finset.univ (fun x => (A x).card) (Finset.mem_univ p'),
    ← Finset.mul_prod_erase _ (fun x => (A x).card) hp_mem]
  simp only [hBp, hBp', Finset.card_singleton]
  have : ∏ x ∈ ((Finset.univ : Finset ι).erase p').erase p, (B x).card =
      ∏ x ∈ ((Finset.univ : Finset ι).erase p').erase p, (A x).card := by
    apply Finset.prod_congr rfl
    intro x hx
    simp only [Finset.mem_erase] at hx
    rw [hBx x hx.1 hx.2.1]
  rw [this]; ring

open Classical in
theorem aux_gcD_decode (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) (ε : ℝ)
    (hε : 0 < ε) (hk : 1 ≤ k) (C : Finset (SetIdx φ code)) :
    ∃ strat : Fin k → Strategy φ ℓ,
      (goodCount φ code ε C : ℝ) * (ε / (3 * k)) ^ 2 ≤ weakAcceptCount φ code strat := by
  let A : (p : Σ i : Fin k, possibleQuestions φ code i) → Finset (Answer φ p.2.1) := fun p =>
    Finset.univ.filter (fun a => (⟨p.1, p.2, a⟩ : SetIdx φ code) ∈ C)
  let A' : (p : Σ i : Fin k, possibleQuestions φ code i) → Finset (Answer φ p.2.1) := fun p =>
    if (A p).Nonempty then A p else {fun j => aux_gcD_dflt φ (p.2.1 j)}
  set T := Fintype.piFinset A' with hT
  have hA'ne : ∀ p, (A' p).Nonempty := by
    intro p
    by_cases h : (A p).Nonempty
    · simp only [A', if_pos h]; exact h
    · simp only [A', if_neg h]; exact Finset.singleton_nonempty _
  have hTne : T.Nonempty := Fintype.piFinset_nonempty.mpr hA'ne
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hgood : ∀ r, IsGood φ code ε C r →
      (T.card : ℝ) * (ε / (3 * k)) ^ 2 ≤
        (T.filter (fun θ => WeakAccept φ code (aux_gcD_strat φ code θ) r)).card := by
    intro r hr
    obtain ⟨hw, s, hs, s', hs', hne, hq, hq', hlab⟩ := hr
    set p : Σ i : Fin k, possibleQuestions φ code i := ⟨s.1, s.2.1⟩ with hpdef
    set p' : Σ i : Fin k, possibleQuestions φ code i := ⟨s'.1, s'.2.1⟩ with hp'def
    have hpp : p ≠ p' := by
      intro h; apply hne; have h' := congrArg Sigma.fst h; exact h'
    have hsA : s.2.2 ∈ A p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    have hsA' : s'.2.2 ∈ A p' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs'⟩
    have hA'p : A' p = A p := if_pos ⟨_, hsA⟩
    have hA'p' : A' p' = A p' := if_pos ⟨_, hsA'⟩
    -- the answer sets are bounded by the weight
    have hcardA : ∀ (q : Σ i : Fin k, possibleQuestions φ code i),
        q.2.1 = question φ code r q.1 → ((A q).card : ℝ) ≤ 3 * k / ε := by
      intro q hq0
      refine le_trans ?_ hw
      apply Nat.cast_le.mpr
      apply Finset.card_le_card_of_injOn (fun a => (⟨q.1, q.2, a⟩ : SetIdx φ code))
      · intro a ha
        have ha' := (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨ha', hq0⟩
      · intro a _ b _ hab
        have h1 := sigma_mk_injective hab
        exact eq_of_heq (Sigma.mk.inj_iff.mp h1).2
    have hcp := hcardA p hq
    have hcp' := hcardA p' hq'
    have hkey := aux_gcD_pi_two A' p p' hpp s.2.2 s'.2.2 (by rw [hA'p]; exact hsA)
      (by rw [hA'p']; exact hsA')
    rw [hA'p, hA'p'] at hkey
    have hsub : T.filter (fun θ => θ p = s.2.2 ∧ θ p' = s'.2.2) ⊆
        T.filter (fun θ => WeakAccept φ code (aux_gcD_strat φ code θ) r) := by
      intro θ hθ
      rw [Finset.mem_filter] at hθ ⊢
      refine ⟨hθ.1, s.1, s'.1, hne, ?_⟩
      have e1 := aux_gcD_induced φ code θ r p hq
      have e2 := aux_gcD_induced φ code θ r p' hq'
      have e1' : induced φ code (aux_gcD_strat φ code θ) r s.1 =
          answerBits (fun j => (r j).2) s.2.2 := by rw [← hθ.2.1]; exact e1
      have e2' : induced φ code (aux_gcD_strat φ code θ) r s'.1 =
          answerBits (fun j => (r j).2) s'.2.2 := by rw [← hθ.2.2]; exact e2
      rw [e1', e2', hlab]
    have hF := Finset.card_le_card hsub
    have hkeyR : (T.card : ℝ) = ((T.filter (fun θ => θ p = s.2.2 ∧ θ p' = s'.2.2)).card : ℝ) *
        (((A p).card : ℝ) * ((A p').card : ℝ)) := by
      rw [hT]; exact_mod_cast hkey.symm
    have hprod : ((A p).card : ℝ) * ((A p').card : ℝ) ≤ (3 * k / ε) ^ 2 := by
      rw [sq]; exact mul_le_mul hcp hcp' (Nat.cast_nonneg _) (by positivity)
    have hFR : ((T.filter (fun θ => θ p = s.2.2 ∧ θ p' = s'.2.2)).card : ℝ) ≤
        (T.filter (fun θ => WeakAccept φ code (aux_gcD_strat φ code θ) r)).card := by
      exact_mod_cast hF
    have hone : (3 * k / ε) ^ 2 * (ε / (3 * k)) ^ 2 = (1:ℝ) := by
      field_simp
    calc (T.card : ℝ) * (ε / (3 * k)) ^ 2
        ≤ ((T.filter (fun θ => θ p = s.2.2 ∧ θ p' = s'.2.2)).card : ℝ) *
            (3 * k / ε) ^ 2 * (ε / (3 * k)) ^ 2 := by
          rw [hkeyR]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
      _ = ((T.filter (fun θ => θ p = s.2.2 ∧ θ p' = s'.2.2)).card : ℝ) := by
          rw [mul_assoc, hone, mul_one]
      _ ≤ _ := hFR
  -- double counting
  have hswap : ∑ θ ∈ T, (weakAcceptCount φ code (aux_gcD_strat φ code θ) : ℝ) =
      ∑ r : RandString φ ℓ,
        ((T.filter (fun θ => WeakAccept φ code (aux_gcD_strat φ code θ) r)).card : ℝ) := by
    unfold weakAcceptCount
    simp only [Finset.card_filter]
    push_cast
    exact Finset.sum_comm
  have hlow : (T.card : ℝ) * ((goodCount φ code ε C : ℝ) * (ε / (3 * k)) ^ 2) ≤
      ∑ θ ∈ T, (weakAcceptCount φ code (aux_gcD_strat φ code θ) : ℝ) := by
    rw [hswap]
    calc (T.card : ℝ) * ((goodCount φ code ε C : ℝ) * (ε / (3 * k)) ^ 2)
        = ∑ r ∈ Finset.univ.filter (IsGood φ code ε C), (T.card : ℝ) * (ε / (3 * k)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, goodCount]; ring
      _ ≤ ∑ r ∈ Finset.univ.filter (IsGood φ code ε C),
            ((T.filter (fun θ => WeakAccept φ code (aux_gcD_strat φ code θ) r)).card : ℝ) :=
          Finset.sum_le_sum (fun r hr => hgood r (Finset.mem_filter.mp hr).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.cast_nonneg _)
  have hlow' : ∑ θ ∈ T, ((goodCount φ code ε C : ℝ) * (ε / (3 * k)) ^ 2) ≤
      ∑ θ ∈ T, (weakAcceptCount φ code (aux_gcD_strat φ code θ) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]; exact hlow
  obtain ⟨θ, _, hθ⟩ := Finset.exists_le_of_sum_le hTne hlow'
  exact ⟨aux_gcD_strat φ code θ, hθ⟩

theorem aux_gcC_complete (k ℓ : ℕ) (code : Fin k → Fin ℓ → Bool) (φ : Formula5)
    (hsat : φ.toCNF.Satisfiable) :
    ∃ C : Finset (SetIdx φ code), C.card ≤ coverBudget φ code ∧
      coveredMaxCover φ code C = Finset.univ := by
  classical
  obtain ⟨τ, hτ⟩ := hsat
  have hloc := aux_gcA_loc φ τ hτ
  let f : (Σ i : Fin k, possibleQuestions φ code i) → SetIdx φ code :=
    fun p => ⟨p.1, p.2, fun j => aux_gcA_cb φ τ hloc (p.2.1 j)⟩
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · refine le_trans Finset.card_image_le ?_
    rw [Finset.card_univ, Fintype.card_sigma, coverBudget]
    apply le_of_eq; apply Finset.sum_congr rfl; intro i _; exact Fintype.card_coe _
  · apply Finset.eq_univ_of_forall
    rintro ⟨r, b⟩
    have hq : question φ code r (b (fun j => τ (φ.var (r j).1 (r j).2))) ∈
        possibleQuestions φ code (b (fun j => τ (φ.var (r j).1 (r j).2))) := by
      simp [possibleQuestions]
    simp only [coveredMaxCover, Finset.mem_biUnion]
    refine ⟨f ⟨_, ⟨_, hq⟩⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    simp only [reductionSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨rfl, ?_⟩
    have := aux_gcA_ind φ τ hloc code r (b (fun j => τ (φ.var (r j).1 (r j).2)))
    unfold induced at this
    simp only [f, cubeSystem]
    rw [this]

end PartC

end SetCoverThreshold.MaxCover

open SetCoverThreshold.MaxCover
open CookPvsNP

theorem solution (hRaz : RazRepetition) :
    (∀ (k ℓ : ℕ) (code : Fin k → Fin ℓ → Bool) (φ : Formula5), φ.toCNF.Satisfiable →
        ∃ C : Finset (SetIdx φ code), C.card ≤ coverBudget φ code ∧
          coveredMaxCover φ code C = Finset.univ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
        ∀ code : Fin k → Fin ℓ → Bool, IsCode code →
          ∀ φ : Formula5, AtMostFracSat (1 - ε') φ.toCNF →
            ∀ C : Finset (SetIdx φ code), C.card ≤ coverBudget φ code →
              ((coveredMaxCover φ code C).card : ℝ) ≤
                (1 - Real.exp (-1) + ε) *
                  (Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) : ℝ)) := by
  classical
  refine ⟨fun k ℓ code φ hsat => aux_gcC_complete k ℓ code φ hsat, ?_⟩
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := aux_gcB_main ε hε
  refine ⟨max K₀ 1, ?_⟩
  intro k hk ε' hε'
  have hkK : K₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨c, hc, hL⟩ := aux_gcA_main hRaz ε' hε'
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk1
  set δ : ℝ := ε / 3 * (ε / (3 * k)) ^ 2 / (k:ℝ) ^ 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hlim : Filter.Tendsto (fun n : ℕ => ((2:ℝ) ^ (-c)) ^ n) Filter.atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · positivity
    · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨ℓ₀, hℓ₀⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδpos))
  refine ⟨ℓ₀, ?_⟩
  intro ℓ hℓ code hcode φ hφ C hC
  have h2 : (2:ℝ) ^ (-(c * ℓ)) < δ := by
    have := hℓ₀ ℓ hℓ
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), neg_mul] at this
  by_contra hcon
  rw [not_le] at hcon
  rcases Nat.eq_zero_or_pos (Fintype.card (RandString φ ℓ)) with hR0 | hRpos
  · have hle : (coveredMaxCover φ code C).card ≤
        Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) := Finset.card_le_univ _
    rw [Fintype.card_prod, hR0, zero_mul] at hle hcon
    have : (coveredMaxCover φ code C).card = 0 := by omega
    rw [this] at hcon
    simp at hcon
  have hgood := hK₀ k hkK ℓ code hcode φ C hC hcon.le
  obtain ⟨strat, hstrat⟩ := aux_gcD_decode φ code ε hε hk1 C
  have hwa := (hL φ ℓ k code hcode).2 hφ strat
  have hRr : (0:ℝ) < Fintype.card (RandString φ ℓ) := by exact_mod_cast hRpos
  unfold weakAcceptFrac at hwa
  rw [div_le_iff₀ hRr] at hwa
  have e1 : ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) * (ε / (3 * k)) ^ 2 ≤
      weakAcceptCount φ code strat := by
    calc _ ≤ (goodCount φ code ε C : ℝ) * (ε / (3 * k)) ^ 2 :=
          mul_le_mul_of_nonneg_right hgood (by positivity)
      _ ≤ _ := hstrat
  have e2 : (k:ℝ) ^ 2 * δ * (Fintype.card (RandString φ ℓ) : ℝ) =
      ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) * (ε / (3 * k)) ^ 2 := by
    rw [hδ]; field_simp
  have e3 : (k:ℝ) ^ 2 * (2:ℝ) ^ (-(c * ℓ)) * (Fintype.card (RandString φ ℓ) : ℝ) <
      (k:ℝ) ^ 2 * δ * (Fintype.card (RandString φ ℓ) : ℝ) := by
    apply mul_lt_mul_of_pos_right _ hRr
    exact mul_lt_mul_of_pos_left h2 (by positivity)
  linarith
