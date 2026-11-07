-- Prove2me | solution 1 for SymBoolPCSP.CFixing.isSymmetricRel_eq_ham
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:39:54.440512+00:00
-- url     : https://prove2.me/submissions/c1a3c8c4-1870-4e6e-ba9c-acd0fde88d74

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

/-- A symmetric Boolean relation is the Hamming relation of its set of weights: `P = Ham_k({|x| : x ∈ P})`. -/
theorem isSymmetricRel_eq_ham {k : ℕ} {P : Set (Fin k → Bool)} (hP : IsSymmetricRel P) :
    P = Ham k {s | ∃ x ∈ P, hw x = s} := by
  ext y; constructor
  · intro hy; exact ⟨y, hy, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    have c1 : Fintype.card {c // y c = true} = Fintype.card {c // x c = true} := by
      rw [Fintype.card_subtype, Fintype.card_subtype]; exact hxy.symm
    have c2 : Fintype.card {c // ¬ y c = true} = Fintype.card {c // ¬ x c = true} := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
    let e1 := Fintype.equivOfCardEq c1
    let e2 := Fintype.equivOfCardEq c2
    have : y = x ∘ (e1.subtypeCongr e2) := by
      funext c
      by_cases hc : y c = true
      · rw [Function.comp_apply, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.trans_apply,
          Equiv.sumCompl_symm_apply_of_pos (p := fun c => y c = true) hc]
        simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
        rw [hc, (e1 ⟨c, hc⟩).2]
      · rw [Function.comp_apply, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.trans_apply,
          Equiv.sumCompl_symm_apply_of_neg (p := fun c => y c = true) hc]
        simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
        have := (e2 ⟨c, hc⟩).2
        simp only [Bool.not_eq_true] at hc this
        rw [hc, this]
    rw [this]; exact hP x hx _

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {k : ℕ} {P : Set (Fin k → Bool)} (hP : IsSymmetricRel P) :
    P = Ham k {s | ∃ x ∈ P, hw x = s} :=
  SymBoolPCSP.CFixing.isSymmetricRel_eq_ham hP
