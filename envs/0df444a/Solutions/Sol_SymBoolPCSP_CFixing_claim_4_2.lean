-- Prove2me | solution 1 for SymBoolPCSP.CFixing.claim_4_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:12:06.964906+00:00
-- url     : https://prove2.me/submissions/d44de536-9dd1-4a76-b47d-a7d38033590b

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace Aux_SymBoolPCSP_CFixing_claim_4_2
open SymBoolPCSP.CFixing

theorem hw_eq_sum {n : ℕ} (x : Fin n → Bool) : hw x = ∑ i, if x i = true then 1 else 0 := by
  unfold hw
  rw [Finset.card_filter]

theorem hw_snoc {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    hw (Fin.snoc (α := fun _ => Bool) y b) = hw y + (if b = true then 1 else 0) := by
  rw [hw_eq_sum, hw_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem hw_le {n : ℕ} (y : Fin n → Bool) : hw y ≤ n := by
  unfold hw
  exact (Finset.card_filter_le _ _).trans (by simp)

end Aux_SymBoolPCSP_CFixing_claim_4_2

open SymBoolPCSP.CFixing Aux_SymBoolPCSP_CFixing_claim_4_2 in
theorem solution {k : ℕ} (hk : 1 ≤ k) (S T : Set ℕ) (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {L : ℕ} (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f)
    (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham (k - 1) (S \ {k})) (Ham (k - 1) (T \ {k})) f := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show PolOf (Ham k' (S \ {k' + 1})) (Ham k' (T \ {k' + 1})) f
  intro M hM
  have hM' : ∀ l, (Fin.snoc (α := fun _ => Bool) (M l) false) ∈ Ham (k' + 1) S := by
    intro l
    have h := hM l
    simp only [Ham, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff] at h ⊢
    rw [hw_snoc]
    simpa using h.1
  have h := hf (fun l => Fin.snoc (α := fun _ => Bool) (M l) false) hM'
  have hz : (fun c => f (fun l => Fin.snoc (α := fun _ => Bool) (M l) false c)) =
      Fin.snoc (α := fun _ => Bool) (fun c => f (fun l => M l c)) false := by
    funext c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [Fin.snoc_last]
      exact hidem.1
    · simp only [Fin.snoc_castSucc]
  rw [hz] at h
  simp only [Ham, Set.mem_setOf_eq, hw_snoc] at h
  simp only [Ham, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
  refine ⟨by simpa using h, ?_⟩
  have := hw_le (fun c => f (fun l => M l c))
  omega
