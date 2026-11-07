-- Prove2me | solution 1 for SymBoolPCSP.CFixing.image_subset_of_conservative
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:09:19.845201+00:00
-- url     : https://prove2.me/submissions/268fcba9-ff88-4159-ba63-480247448470

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_image_subset_of_conservative

theorem const_of_mem_ham0k {k : ℕ} {x : Fin k → Bool} (hx : x ∈ Ham k {0, k}) :
    (∀ c, x c = false) ∨ (∀ c, x c = true) := by
  simp only [Ham, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hw] at hx
  rcases hx with h | h
  · left; intro c
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    simpa using h (Finset.mem_univ c)
  · right; intro c
    have : Finset.univ.filter (fun i => x i = true) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h)
    have hc := Finset.mem_univ c
    rw [← this, Finset.mem_filter] at hc
    exact hc.2

end Aux_image_subset_of_conservative

open Aux_image_subset_of_conservative in
/-- A conservative function (`f(v)` is always one of the entries of `v`) maps every relation consisting of constant tuples into itself: `f(P) ⊆ P` whenever `P ⊆ Ham_k({0, k})`. -/
theorem image_subset_of_conservative {k L : ℕ} (f : (Fin L → Bool) → Bool)
    (hf : ∀ v, ∃ l, f v = v l) (P : Set (Fin k → Bool)) (hP : P ⊆ Ham k {0, k}) :
    image f P ⊆ P := by
  rintro y ⟨M, hM, rfl⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    obtain ⟨l, -⟩ := hf (fun _ => false)
    have : (fun c : Fin 0 => f (fun l => M l c)) = M l := funext (fun c => c.elim0)
    rw [this]; exact hM l
  · let c0 : Fin k := ⟨0, hk⟩
    obtain ⟨l, hl⟩ := hf (fun l => M l c0)
    have hcol : ∀ c, (fun l => M l c) = fun l => M l c0 := by
      intro c; funext l
      rcases const_of_mem_ham0k (hP (hM l)) with h | h <;> simp [h]
    have : (fun c => f (fun l => M l c)) = M l := by
      funext c
      rw [hcol c, hl]
      rcases const_of_mem_ham0k (hP (hM l)) with h | h <;> simp [h]
    rw [this]; exact hM l

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {k L : ℕ} (f : (Fin L → Bool) → Bool)
    (hf : ∀ v, ∃ l, f v = v l) (P : Set (Fin k → Bool)) (hP : P ⊆ Ham k {0, k}) :
    image f P ⊆ P :=
  SymBoolPCSP.CFixing.image_subset_of_conservative f hf P hP
