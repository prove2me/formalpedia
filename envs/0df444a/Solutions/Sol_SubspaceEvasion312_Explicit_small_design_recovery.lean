-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.small_design_recovery
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:05:32.125113+00:00
-- url     : https://prove2.me/submissions/4b6c6675-f0aa-48af-aeec-5a9406d277d7

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
end SubspaceEvasion312.Explicit
end

section
set_option autoImplicit false

namespace SubspaceEvasion312.Explicit.Dev.Small
open SubspaceEvasion312.Explicit

theorem rankCondenser_of_design {F : Type} [Field F] {s m r : ℕ} (hm : 0 < m)
    (C : Code F s m) (τ : ℕ → ℝ) (hC : SubspaceDesign C τ)
    (hτ : r = 0 ∨ τ r < 1 / (r : ℝ)) : RankCondenser C r := by
  intro U hUC hU
  by_cases h0 : Module.finrank F U = 0
  · refine ⟨⟨0, hm⟩, ?_⟩
    have : U = ⊥ := Submodule.finrank_eq_zero.mp h0
    subst this
    intro x hx y hy _
    simp at hx hy
    rw [hx, hy]
  · have hd : 0 < Module.finrank F U := Nat.pos_of_ne_zero h0
    have hr : 0 < r := lt_of_lt_of_le hd hU
    have hτr : τ r < 1 / (r : ℝ) := by
      rcases hτ with h | h
      · omega
      · exact h
    have hdes := hC.2 r U hUC hU
    have hdr : (Module.finrank F U : ℝ) * τ r < 1 := by
      have hdpos : (0 : ℝ) < Module.finrank F U := by exact_mod_cast hd
      have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
      calc (Module.finrank F U : ℝ) * τ r < Module.finrank F U * (1 / (r : ℝ)) :=
            mul_lt_mul_of_pos_left hτr hdpos
        _ = Module.finrank F U / r := by ring
        _ ≤ 1 := by
            rw [div_le_one hrpos]; exact_mod_cast hU
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hlt : (∑ i : Fin m, (Module.finrank F (coordinateKernel U i) : ℝ)) < m := by
      have := lt_of_le_of_lt hdes hdr
      rw [div_lt_one hmpos] at this
      exact this
    by_contra hno
    push_neg at hno
    have hall : ∀ i : Fin m, (1 : ℝ) ≤ Module.finrank F (coordinateKernel U i) := by
      intro i
      have hnot := hno i
      have : 0 < Module.finrank F (coordinateKernel U i) := by
        by_contra hz
        have hz' : Module.finrank F (coordinateKernel U i) = 0 := by omega
        have hbot : coordinateKernel U i = ⊥ := Submodule.finrank_eq_zero.mp hz'
        apply hnot
        intro x hx y hy hxy
        have hmem : x - y ∈ coordinateKernel U i :=
          ⟨U.sub_mem hx hy, by simp [hxy]⟩
        rw [hbot] at hmem
        simpa [sub_eq_zero] using hmem
      exact_mod_cast this
    have : (m : ℝ) ≤ ∑ i : Fin m, (Module.finrank F (coordinateKernel U i) : ℝ) := by
      calc (m : ℝ) = ∑ _i : Fin m, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hall i)
    linarith

end SubspaceEvasion312.Explicit.Dev.Small

namespace SubspaceEvasion312.Explicit
open SubspaceEvasion312.Explicit.Dev.Small in
theorem chk_small_design_recovery {F : Type} [Field F] [Fintype F]
    {s m r : ℕ} (hm : 0 < m) (C : Code F s m) (τ : ℕ → ℝ)
    (hC : SubspaceDesign C τ) (hτ : r = 0 ∨ τ r < 1 / (r : ℝ)) :
    ∀ ℓ : ℕ, ListRecoverable C r 0 ℓ ℓ :=
  fun ℓ => SubspaceEvasion312.Explicit.Dev.Cond.condenser C (rankCondenser_of_design hm C τ hC hτ) ℓ
end SubspaceEvasion312.Explicit
end

theorem solution : type_of% @SubspaceEvasion312.Explicit.chk_small_design_recovery := @SubspaceEvasion312.Explicit.chk_small_design_recovery
