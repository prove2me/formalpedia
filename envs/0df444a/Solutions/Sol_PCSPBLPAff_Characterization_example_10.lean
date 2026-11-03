-- Prove2me | solution 1 for PCSPBLPAff.Characterization.example_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:26:02.262989+00:00
-- url     : https://prove2.me/submissions/8e1c5ee2-762a-4ffe-b5ad-fe7c411739e7

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

open PCSPBLPAff.Symmetric
open PCSPBLPAff.Characterization

namespace Example10Proof

private abbrev V := Fin 2 ⊕ Fin 3

private def α : V → V
  | .inl i => .inl (i + 1)
  | .inr j => .inr (j + 1)

private lemma arc_self_α (v : V) : example10Arc v (α v) := by
  rcases v with i | j <;> rfl

private lemma not_arc_self (v : V) : ¬ example10Arc v v := by
  rcases v with i | j
  · unfold example10Arc; fin_cases i <;> decide
  · unfold example10Arc; fin_cases j <;> decide

private def gEven (m : ℕ) (j : Fin m) : V :=
  if j.val % 2 = 0 then .inl 0 else .inl 1

private def σEvenFun (m : ℕ) (hm : m % 2 = 0) (j : Fin m) : Fin m :=
  if _h : j.val % 2 = 0 then
    ⟨j.val + 1, by have := j.isLt; omega⟩
  else
    ⟨j.val - 1, by have := j.isLt; omega⟩

private lemma σEvenFun_inv (m : ℕ) (hm : m % 2 = 0) (j : Fin m) :
    σEvenFun m hm (σEvenFun m hm j) = j := by
  ext
  unfold σEvenFun
  by_cases h : j.val % 2 = 0
  · have h2 : ¬ (j.val + 1) % 2 = 0 := by omega
    simp [h, h2]
  · have h2 : (j.val - 1) % 2 = 0 := by omega
    simp [h, h2]
    omega

private def σEven (m : ℕ) (hm : m % 2 = 0) : Equiv.Perm (Fin m) where
  toFun := σEvenFun m hm
  invFun := σEvenFun m hm
  left_inv := σEvenFun_inv m hm
  right_inv := σEvenFun_inv m hm

private lemma α_gEven (m : ℕ) (hm : m % 2 = 0) (j : Fin m) :
    α (gEven m j) = gEven m (σEven m hm j) := by
  change α (gEven m j) = gEven m (σEvenFun m hm j)
  unfold gEven σEvenFun
  by_cases h : j.val % 2 = 0
  · have h2 : ¬ (j.val + 1) % 2 = 0 := by omega
    simp [h, h2]
    rfl
  · have h2 : (j.val - 1) % 2 = 0 := by omega
    simp [h, h2]
    rfl

private def gOdd (m : ℕ) (j : Fin m) : V :=
  if j.val = 0 then .inr 0
  else if j.val = 1 then .inr 1
  else if j.val = 2 then .inr 2
  else if j.val % 2 = 1 then .inl 0
  else .inl 1

private def σOddFun (m : ℕ) (hm2 : 2 ≤ m) (hm : m % 2 = 1) (j : Fin m) : Fin m :=
  if _h0 : j.val = 0 then ⟨1, by omega⟩
  else if _h1 : j.val = 1 then ⟨2, by omega⟩
  else if _h2 : j.val = 2 then ⟨0, by omega⟩
  else if _hodd : j.val % 2 = 1 then ⟨j.val + 1, by have := j.isLt; omega⟩
  else ⟨j.val - 1, by have := j.isLt; omega⟩

private def σOddInv (m : ℕ) (hm2 : 2 ≤ m) (hm : m % 2 = 1) (j : Fin m) : Fin m :=
  if _h0 : j.val = 0 then ⟨2, by omega⟩
  else if _h1 : j.val = 1 then ⟨0, by omega⟩
  else if _h2 : j.val = 2 then ⟨1, by omega⟩
  else if _hodd : j.val % 2 = 1 then ⟨j.val + 1, by have := j.isLt; omega⟩
  else ⟨j.val - 1, by have := j.isLt; omega⟩

private lemma σOdd_left_inv (m : ℕ) (hm2 : 2 ≤ m) (hm : m % 2 = 1) (j : Fin m) :
    σOddInv m hm2 hm (σOddFun m hm2 hm j) = j := by
  ext
  unfold σOddInv σOddFun
  by_cases h0 : j.val = 0
  · simp [h0]
  · by_cases h1 : j.val = 1
    · simp [h1]
    · by_cases h2 : j.val = 2
      · simp [h2]
      · by_cases hodd : j.val % 2 = 1
        · have h_add_ne2 : j.val + 1 ≠ 2 := by omega
          have h_add_mod : ¬ (j.val + 1) % 2 = 1 := by omega
          simp [h0, h1, h2, hodd, h_add_ne2, h_add_mod]
        · have hge4 : 4 ≤ j.val := by omega
          have h_sub_ne0 : j.val - 1 ≠ 0 := by omega
          have h_sub_ne1 : j.val - 1 ≠ 1 := by omega
          have h_sub_ne2 : j.val - 1 ≠ 2 := by omega
          have h_sub_mod : (j.val - 1) % 2 = 1 := by omega
          simp [h0, h1, h2, hodd, h_sub_ne0, h_sub_ne1, h_sub_ne2, h_sub_mod]
          omega

private lemma σOdd_right_inv (m : ℕ) (hm2 : 2 ≤ m) (hm : m % 2 = 1) (j : Fin m) :
    σOddFun m hm2 hm (σOddInv m hm2 hm j) = j := by
  ext
  unfold σOddFun σOddInv
  by_cases h0 : j.val = 0
  · simp [h0]
  · by_cases h1 : j.val = 1
    · simp [h1]
    · by_cases h2 : j.val = 2
      · simp [h2]
      · by_cases hodd : j.val % 2 = 1
        · have h_add_ne2 : j.val + 1 ≠ 2 := by omega
          have h_add_mod : ¬ (j.val + 1) % 2 = 1 := by omega
          simp [h0, h1, h2, hodd, h_add_ne2, h_add_mod]
        · have hge4 : 4 ≤ j.val := by omega
          have h_sub_ne0 : j.val - 1 ≠ 0 := by omega
          have h_sub_ne1 : j.val - 1 ≠ 1 := by omega
          have h_sub_ne2 : j.val - 1 ≠ 2 := by omega
          have h_sub_mod : (j.val - 1) % 2 = 1 := by omega
          simp [h0, h1, h2, hodd, h_sub_ne0, h_sub_ne1, h_sub_ne2, h_sub_mod]
          omega

private def σOdd (m : ℕ) (hm2 : 2 ≤ m) (hm : m % 2 = 1) : Equiv.Perm (Fin m) where
  toFun := σOddFun m hm2 hm
  invFun := σOddInv m hm2 hm
  left_inv := σOdd_left_inv m hm2 hm
  right_inv := σOdd_right_inv m hm2 hm

private lemma α_gOdd (m : ℕ) (hm2 : 2 ≤ m) (hm : m % 2 = 1) (j : Fin m) :
    α (gOdd m j) = gOdd m (σOdd m hm2 hm j) := by
  change α (gOdd m j) = gOdd m (σOddFun m hm2 hm j)
  unfold gOdd σOddFun
  by_cases h0 : j.val = 0
  · simp [h0]; rfl
  · by_cases h1 : j.val = 1
    · simp [h1]; rfl
    · by_cases h2 : j.val = 2
      · simp [h2]; rfl
      · by_cases hodd : j.val % 2 = 1
        · have h_add_ne2 : j.val + 1 ≠ 2 := by omega
          have h_add_mod : ¬ (j.val + 1) % 2 = 1 := by omega
          simp [h0, h1, h2, hodd, h_add_ne2, h_add_mod]
          rfl
        · have hge4 : 4 ≤ j.val := by omega
          have h_sub_ne0 : j.val - 1 ≠ 0 := by omega
          have h_sub_ne1 : j.val - 1 ≠ 1 := by omega
          have h_sub_ne2 : j.val - 1 ≠ 2 := by omega
          have h_sub_mod : (j.val - 1) % 2 = 1 := by omega
          simp [h0, h1, h2, hodd, h_sub_ne0, h_sub_ne1, h_sub_ne2, h_sub_mod]
          rfl

private lemma exists_perm_shift_fin (m : ℕ) (hm2 : 2 ≤ m) :
    ∃ (g : Fin m → V) (σ : Equiv.Perm (Fin m)), ∀ j, α (g j) = g (σ j) := by
  by_cases hm : m % 2 = 0
  · exact ⟨gEven m, σEven m hm, α_gEven m hm⟩
  · have hm_odd : m % 2 = 1 := by omega
    exact ⟨gOdd m, σOdd m hm2 hm_odd, α_gOdd m hm2 hm_odd⟩

private lemma exists_perm_shift_type (T : Type*) [Fintype T] (hT : 2 ≤ Fintype.card T) :
    ∃ (g : T → V) (τ : Equiv.Perm T), ∀ u, α (g u) = g (τ u) := by
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  obtain ⟨g₀, σ₀, h₀⟩ := exists_perm_shift_fin (Fintype.card T) hT
  refine ⟨g₀ ∘ e, e.trans (σ₀.trans e.symm), ?_⟩
  intro u
  simp [h₀ (e u)]

private lemma glue_symm_apply {L κ : ℕ} (β : Fin L → Fin κ)
    (τS : ∀ b : Fin κ, Equiv.Perm {l : Fin L // β l = b})
    {b1 b2 : Fin κ} (hb : b1 = b2) (l' : Fin L) (h1 : β l' = b1) (h2 : β l' = b2) :
    ((τS b1).symm ⟨l', h1⟩).1 = ((τS b2).symm ⟨l', h2⟩).1 := by
  subst hb
  rfl

private lemma glue_apply {L κ : ℕ} (β : Fin L → Fin κ)
    (τS : ∀ b : Fin κ, Equiv.Perm {l : Fin L // β l = b})
    {b1 b2 : Fin κ} (hb : b1 = b2) (l' : Fin L) (h1 : β l' = b1) (h2 : β l' = b2) :
    (τS b1 ⟨l', h1⟩).1 = (τS b2 ⟨l', h2⟩).1 := by
  subst hb
  rfl

private lemma glue_val {L κ : ℕ} (β : Fin L → Fin κ)
    (gS : ∀ b : Fin κ, {l : Fin L // β l = b} → V)
    {b1 b2 : Fin κ} (hb : b1 = b2) (l' : Fin L) (h1 : β l' = b1) (h2 : β l' = b2) :
    gS b1 ⟨l', h1⟩ = gS b2 ⟨l', h2⟩ := by
  subst hb
  rfl

end Example10Proof

open Example10Proof in
theorem solution :
    ∀ (L : ℕ) (f : (Fin L → Fin 2 ⊕ Fin 3) → Fin 2 ⊕ Fin 3),
      PCSPBLPAff.Symmetric.IsPolymorphism example10Digraph example10Digraph f →
      ¬ PCSPBLPAff.Symmetric.HasWidthAtLeast f 2 := by
  classical
  rintro L f hf ⟨κ, β, _, hcard, hsym⟩
  let S (b : Fin κ) := {l : Fin L // β l = b}
  have hS_card : ∀ b : Fin κ, 2 ≤ Fintype.card (S b) := by
    intro b
    rw [Fintype.card_subtype]
    exact hcard b
  choose gS τS hS using fun b => exists_perm_shift_type (S b) (hS_card b)
  let x : Fin L → V := fun l => gS (β l) ⟨l, rfl⟩
  let πFun : Fin L → Fin L := fun l => (τS (β l) ⟨l, rfl⟩).1
  let πInv : Fin L → Fin L := fun l => ((τS (β l)).symm ⟨l, rfl⟩).1
  have hπ_β : ∀ l : Fin L, β (πFun l) = β l := fun l => (τS (β l) ⟨l, rfl⟩).2
  have h_left : ∀ l : Fin L, πInv (πFun l) = l := by
    intro l
    dsimp [πInv, πFun]
    set u := τS (β l) ⟨l, rfl⟩
    rw [glue_symm_apply β τS u.2 u.1 rfl u.2]
    change ((τS (β l)).symm (τS (β l) ⟨l, rfl⟩)).1 = l
    rw [Equiv.symm_apply_apply]
  have h_right : ∀ l : Fin L, πFun (πInv l) = l := by
    intro l
    dsimp [πFun, πInv]
    set u := (τS (β l)).symm ⟨l, rfl⟩
    rw [glue_apply β τS u.2 u.1 rfl u.2]
    change (τS (β l) ((τS (β l)).symm ⟨l, rfl⟩)).1 = l
    rw [Equiv.apply_symm_apply]
  let π : Equiv.Perm (Fin L) := {
    toFun := πFun
    invFun := πInv
    left_inv := h_left
    right_inv := h_right
  }
  have hx_shift : α ∘ x = x ∘ π := by
    ext l
    dsimp [x, π, πFun]
    rw [hS (β l) ⟨l, rfl⟩]
    set u := τS (β l) ⟨l, rfl⟩
    exact (glue_val β gS u.2 u.1 rfl u.2).symm
  let M : Fin L → Fin 2 → V := fun l c => if c = 0 then x l else α (x l)
  have hM_rel : ∀ l : Fin L, M l ∈ example10Digraph.rel () := by
    intro l
    change example10Arc (M l 0) (M l 1)
    dsimp [M]
    exact arc_self_α (x l)
  have hf_rel := hf () M hM_rel
  change example10Arc (f (fun l => M l 0)) (f (fun l => M l 1)) at hf_rel
  have hM0 : (fun l => M l 0) = x := by ext l; rfl
  have hM1 : (fun l => M l 1) = α ∘ x := by ext l; rfl
  rw [hM0, hM1, hx_shift, hsym π hπ_β x] at hf_rel
  exact not_arc_self (f x) hf_rel
