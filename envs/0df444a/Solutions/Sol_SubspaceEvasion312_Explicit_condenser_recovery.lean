-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.condenser_recovery
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:05:32.108315+00:00
-- url     : https://prove2.me/submissions/fd5fa9dd-305c-45c9-857c-f7ce2df0692c

import Mathlib
import Definitions.Def_SubspaceEvasion312_Explicit_algebra

section
set_option autoImplicit false

namespace SubspaceEvasion312.Explicit.Dev.Cond
open SubspaceEvasion312.Explicit

theorem rec_mem {F : Type} [Field F] {s m : ℕ} (C : Code F s m)
    (U : Submodule F (Blocks F s m)) (S : Fin m → Finset (Vec F s))
    {c : Blocks F s m} (hc : c ∈ recovered C U S 0) : c ∈ C ∧ c ∈ U ∧ ∀ i, c i ∈ S i := by
  obtain ⟨h1, h2, y, hy, hh⟩ := hc
  refine ⟨h1, h2, fun i => ?_⟩
  have h0 : hamming c y = 0 := by
    have : (hamming c y : ℝ) ≤ 0 := by simpa using hh
    exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le _)
  have : c i = y i := by
    by_contra hne
    have : 0 < hamming c y := by
      unfold hamming
      classical
      exact Finset.card_pos.mpr ⟨i, by simp [hne]⟩
    omega
  rw [this]; exact hy i

open Classical in
theorem inj_bound {F : Type} [Field F] {s m : ℕ} (C : Code F s m) (r ℓ : ℕ)
    (U : Submodule F (Blocks F s m)) (hU : Module.finrank F U ≤ r)
    (S : Fin m → Finset (Vec F s)) (hS : ∀ i, (S i).card ≤ ℓ)
    (T : Finset (Blocks F s m)) (hT : (↑T : Set _) ⊆ recovered C U S 0)
    (i : Fin m) (hi : Set.InjOn (fun x : Blocks F s m => x i) ((C ⊓ U : Submodule F _) : Set _)) :
    T.card ≤ ℓ := by
  have hmem : ∀ c ∈ T, c ∈ (C ⊓ U : Submodule F _) ∧ c i ∈ S i := fun c hc => by
    have := rec_mem C U S (hT hc)
    exact ⟨⟨this.1, this.2.1⟩, this.2.2 i⟩
  have hinj : Set.InjOn (fun x : Blocks F s m => x i) (↑T : Set _) :=
    hi.mono (fun c hc => (hmem c hc).1)
  calc T.card = (T.image (fun x : Blocks F s m => x i)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (S i).card := Finset.card_le_card (by
        intro v hv
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
        exact (hmem c hc).2)
    _ ≤ ℓ := hS i

theorem condenser {F : Type} [Field F] {s m r : ℕ} (C : Code F s m)
    (hC : RankCondenser C r) (ℓ : ℕ) : ListRecoverable C r 0 ℓ ℓ := by
  intro U hU S hS T hT
  have hW : Module.finrank F (C ⊓ U : Submodule F _) ≤ r :=
    (Submodule.finrank_mono inf_le_right).trans hU
  obtain ⟨i, hi⟩ := hC _ inf_le_left hW
  exact_mod_cast inj_bound C r ℓ U hU S hS T hT i hi

end SubspaceEvasion312.Explicit.Dev.Cond

namespace SubspaceEvasion312.Explicit
open SubspaceEvasion312.Explicit.Dev.Cond in
theorem chk_condenser_recovery {F : Type} [Field F] [Fintype F]
    {s m r : ℕ} (C : Code F s m) (hC : RankCondenser C r) :
    ∀ ℓ : ℕ, ListRecoverable C r 0 ℓ ℓ := condenser C hC
end SubspaceEvasion312.Explicit
end

theorem solution : type_of% @SubspaceEvasion312.Explicit.chk_condenser_recovery := @SubspaceEvasion312.Explicit.chk_condenser_recovery
