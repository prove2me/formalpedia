-- Prove2me | solution 1 for PCSPBLPAff.Characterization.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T10:35:54.51449+00:00
-- url     : https://prove2.me/submissions/d89e0846-b204-4586-ab58-1a19057cc90b

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting
import Theorems.Thm_PCSPBLPAff_Characterization_lemma_7
import Theorems.Thm_PCSPBLPAff_Characterization_lemma_9

open PCSPBLPAff.Symmetric PCSPBLPAff.Characterization

namespace PCSPBLPAff.Characterization.T4aux

/-- block labelling of `[2L+1]`: the first `L` coordinates form block `0`, the rest block `1`. -/
def blk (L : ℕ) : Fin (2 * L + 1) → Fin 2 := fun l => if (l : ℕ) < L then 0 else 1

theorem blk_eq_zero_iff (L : ℕ) (l : Fin (2 * L + 1)) : blk L l = 0 ↔ (l : ℕ) < L := by
  unfold blk; split_ifs with h <;> simp [h]

theorem blk_eq_one_iff (L : ℕ) (l : Fin (2 * L + 1)) : blk L l = 1 ↔ ¬ (l : ℕ) < L := by
  unfold blk; split_ifs with h <;> simp [h]

theorem card_lt (L : ℕ) : (Finset.univ.filter (fun l : Fin (2 * L + 1) => (l : ℕ) < L)).card = L := by
  rw [Fin.card_filter_val_lt]; omega

theorem card_not_lt (L : ℕ) :
    (Finset.univ.filter (fun l : Fin (2 * L + 1) => ¬ (l : ℕ) < L)).card = L + 1 := by
  rw [Finset.filter_not, Finset.card_univ_diff, card_lt, Fintype.card_fin]
  omega

theorem card_blk0 (L : ℕ) : (Finset.univ.filter (fun l => blk L l = 0)).card = L := by
  rw [Finset.filter_congr (fun l _ => blk_eq_zero_iff L l), card_lt]

theorem card_blk1 (L : ℕ) : (Finset.univ.filter (fun l => blk L l = 1)).card = L + 1 := by
  rw [Finset.filter_congr (fun l _ => blk_eq_one_iff L l), card_not_lt]

theorem card_blk_ne0 (L : ℕ) : (Finset.univ.filter (fun l => ¬ blk L l = 0)).card = L + 1 := by
  rw [Finset.filter_congr (fun l _ => not_congr (blk_eq_zero_iff L l)), card_not_lt]

theorem xobj_prop (L : ℕ) : IsBLPAffObj (fun _ : Fin (2 * L + 1) => 1 / (2 * L + 1 : ℚ))
    (fun l => if blk L l = 0 then -1 else 1) := by
  refine ⟨fun _ => by positivity, ?_, ?_, fun i h => ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, card_blk0, card_blk_ne0]
    simp
  · exfalso
    have h' : (1 : ℚ) / (2 * L + 1) = 0 := h
    have : (0 : ℚ) < 1 / (2 * L + 1) := by positivity
    linarith

/-- the object `(w, r)` with uniform weights and `r = -1` on block `0`, `+1` on block `1`. -/
def xobj (L : ℕ) : BLPAffObj (Fin (2 * L + 1)) :=
  ⟨(fun _ => 1 / (2 * L + 1 : ℚ), fun l => if blk L l = 0 then -1 else 1), xobj_prop L⟩

theorem minorQ_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (w : Fin n → ℚ) (i : Fin n) :
    minorQ π w i = w (π.symm i) := by
  have : Finset.univ.filter (fun j => π j = i) = {π.symm i} := by
    ext j; simp [Equiv.apply_eq_iff_eq_symm_apply]
  unfold minorQ; rw [this, Finset.sum_singleton]

theorem minorZ_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (r : Fin n → ℤ) (i : Fin n) :
    minorZ π r i = r (π.symm i) := by
  have : Finset.univ.filter (fun j => π j = i) = {π.symm i} := by
    ext j; simp [Equiv.apply_eq_iff_eq_symm_apply]
  unfold minorZ; rw [this, Finset.sum_singleton]

end PCSPBLPAff.Characterization.T4aux

open PCSPBLPAff.Characterization.T4aux in
theorem PCSPBLPAff.Characterization.theorem_4_main {τ : Type} {ar : τ → ℕ} {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (hT : IsPromiseTemplate 𝔸 𝔹) :
    List.TFAE
      [ CorrectlySolves 𝔸 𝔹,
        ∀ N : ℕ, ∃ (L : ℕ) (f : (Fin L → A) → B), IsPolymorphism 𝔸 𝔹 f ∧ HasWidthAtLeast f N,
        ∀ L : ℕ, ∃ f : (Fin (2 * L + 1) → A) → B, IsPolymorphism 𝔸 𝔹 f ∧
          ∃ β : Fin (2 * L + 1) → Fin 2,
            (Finset.univ.filter (fun l => β l = 0)).card = L ∧
            (Finset.univ.filter (fun l => β l = 1)).card = L + 1 ∧
            IsBlockSymmetricFor β f ] := by
  tfae_have 2 → 1 := fun h => (lemma_7 𝔸 𝔹 hT).2 (lemma_9 𝔸 𝔹 h)
  tfae_have 3 → 2 := by
    intro h N
    obtain ⟨f, hf, β, h0, h1, hbs⟩ := h N
    refine ⟨2 * N + 1, f, hf, 2, β, by norm_num, fun b => ?_, hbs⟩
    fin_cases b <;> simp [h0, h1]
  tfae_have 1 → 3 := by
    intro h L
    obtain ⟨ξ, hξ⟩ := (lemma_7 𝔸 𝔹 hT).1 h
    refine ⟨ξ _ (xobj L), (hξ _ _).1, blk L, card_blk0 L, card_blk1 L, fun π hπ y => ?_⟩
    have e1 : minorQ π (xobj L).1.1 = (xobj L).1.1 := funext fun i => by
      rw [minorQ_perm]; rfl
    have e2 : minorZ π (xobj L).1.2 = (xobj L).1.2 := funext fun i => by
      rw [minorZ_perm]
      have := hπ (π.symm i)
      rw [Equiv.apply_symm_apply] at this
      show (if blk L (π.symm i) = 0 then -1 else 1) = (if blk L i = 0 then -1 else 1)
      rw [this]
    have hobj : IsBLPAffObj (minorQ π (xobj L).1.1) (minorZ π (xobj L).1.2) := by
      rw [e1, e2]; exact (xobj L).2
    have key := (hξ _ (xobj L)).2 _ π hobj
    have hx : (⟨(minorQ π (xobj L).1.1, minorZ π (xobj L).1.2), hobj⟩ :
        BLPAffObj (Fin (2 * L + 1))) = xobj L := Subtype.ext (Prod.ext e1 e2)
    rw [hx] at key
    exact (congrFun key y).symm
  tfae_finish

theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (hT : PCSPBLPAff.Symmetric.IsPromiseTemplate 𝔸 𝔹) :
    List.TFAE
      [ PCSPBLPAff.Symmetric.CorrectlySolves 𝔸 𝔹,
        ∀ N : ℕ, ∃ (L : ℕ) (f : (Fin L → A) → B), PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f ∧ PCSPBLPAff.Symmetric.HasWidthAtLeast f N,
        ∀ L : ℕ, ∃ f : (Fin (2 * L + 1) → A) → B, PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f ∧
          ∃ β : Fin (2 * L + 1) → Fin 2,
            (Finset.univ.filter (fun l => β l = 0)).card = L ∧
            (Finset.univ.filter (fun l => β l = 1)).card = L + 1 ∧
            PCSPBLPAff.Symmetric.IsBlockSymmetricFor β f ] :=
  PCSPBLPAff.Characterization.theorem_4_main 𝔸 𝔹 hT
