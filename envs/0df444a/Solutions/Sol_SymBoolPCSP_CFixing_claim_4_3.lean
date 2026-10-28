-- Prove2me | solution 1 for SymBoolPCSP.CFixing.claim_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:10:02.306813+00:00
-- url     : https://prove2.me/submissions/4b59d87b-e6f8-47c1-9fca-cc6dbb39716c

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem solution {k L : ℕ} (P Q : Set (Fin k → Bool)) (hPQ : P ⊆ Q) (S : Finset (Fin k))
    (f : (Fin L → Bool) → Bool) (hfold : IsFolded f) :
    PolOf P Q f ↔ PolOf (flipRel S P) (flipRel S Q) f := by
  have key : ∀ (v : Fin L → Bool) (b : Bool), f (fun l => xor (v l) b) = xor (f v) b := by
    intro v b
    cases b
    · simp
    · have h := hfold (fun l => xor (v l) true)
      have hn : neg (fun l => xor (v l) true) = v := by
        funext l; simp [neg]
      rw [hn] at h
      rw [h]; simp
  constructor
  · intro hf M hM
    have := hf (fun l c => xor (M l c) (indicator S c)) hM
    show (fun i => xor (f (fun l => M l i)) (indicator S i)) ∈ Q
    convert this using 1
    funext c
    rw [key (fun l => M l c) (indicator S c)]
  · intro hf M hM
    have hM' : ∀ l, (fun c => xor (M l c) (indicator S c)) ∈ flipRel S P := by
      intro l
      show (fun i => xor (xor (M l i) (indicator S i)) (indicator S i)) ∈ P
      convert hM l using 1
      funext i; simp
    have := hf (fun l c => xor (M l c) (indicator S c)) hM'
    change (fun i => xor (f (fun l => xor (M l i) (indicator S i))) (indicator S i)) ∈ Q at this
    convert this using 1
    funext c
    rw [key (fun l => M l c) (indicator S c)]
    simp
