-- Prove2me | solution 1 for SymBoolPCSP.CFixing.polOf_ham_flip
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:39:53.564289+00:00
-- url     : https://prove2.me/submissions/8311076a-c6b3-491a-8bf8-d0bef766fb84

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_claim_4_3

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_polOf_ham_flip

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem flipRel_univ_ham {k : ℕ} (X : Set ℕ) :
    flipRel Finset.univ (Ham k X) = Ham k {l | l ≤ k ∧ k - l ∈ X} := by
  ext y
  have hn : (fun i => xor (y i) (indicator Finset.univ i)) = neg y := by
    funext i; simp [indicator, neg]
  have hneg : hw (neg y) = k - hw y := by
    have : hw y + hw (neg y) = k := by
      unfold hw neg
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun i _ => show (if y i = true then 1 else 0) +
        (if (!y i) = true then 1 else 0) = 1 by cases y i <;> simp)]
      simp
    omega
  show (fun i => xor (y i) (indicator Finset.univ i)) ∈ Ham k X ↔ _
  rw [hn]
  show hw (neg y) ∈ X ↔ hw y ≤ k ∧ k - hw y ∈ X
  rw [hneg]; exact ⟨fun h => ⟨hw_le' y, h⟩, fun h => h.2⟩

end Aux_polOf_ham_flip

open Aux_polOf_ham_flip in
/-- Complementing all coordinates (Claim 4.3 with the full flip set): for folded `f`, `f ∈ Pol(Ham_k(S), Ham_k(T))` implies `f ∈ Pol(Ham_k(k - S), Ham_k(k - T))`. -/
theorem polOf_ham_flip {k L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham k {l | l ≤ k ∧ k - l ∈ S}) (Ham k {l | l ≤ k ∧ k - l ∈ T}) f := by
  have := (claim_4_3 (Ham k S) (Ham k T) (fun x hx => hST hx) Finset.univ f hfold).mp hf
  rwa [flipRel_univ_ham, flipRel_univ_ham] at this

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {k L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham k {l | l ≤ k ∧ k - l ∈ S}) (Ham k {l | l ≤ k ∧ k - l ∈ T}) f :=
  SymBoolPCSP.CFixing.polOf_ham_flip hST f hfold hf
