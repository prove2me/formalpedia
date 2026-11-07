-- Prove2me | solution 1 for SymBoolPCSP.CFixing.image_negRel_of_folded
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:09:20.812485+00:00
-- url     : https://prove2.me/submissions/4e262feb-1e86-41cd-9132-8d423da9c38d

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_image_negRel_of_folded

theorem neg_neg' {k : ℕ} (x : Fin k → Bool) : neg (neg x) = x := by
  funext i; simp [neg]

end Aux_image_negRel_of_folded

open Aux_image_negRel_of_folded in
/-- For a folded `f` (`f(x) = ¬f(x̄)`), images commute with negation: `f(¬P) = ¬f(P)`. -/
theorem image_negRel_of_folded {k L : ℕ} (f : (Fin L → Bool) → Bool) (hf : IsFolded f)
    (P : Set (Fin k → Bool)) : image f (negRel P) = negRel (image f P) := by
  have hfn : ∀ v, f (neg v) = !f v := fun v => by rw [hf (neg v), neg_neg']
  ext y; constructor
  · rintro ⟨M, hM, rfl⟩
    choose N hN hNM using hM
    refine ⟨fun c => f (fun l => N l c), ⟨N, hN, rfl⟩, ?_⟩
    funext c
    have : (fun l => M l c) = neg (fun l => N l c) := by
      funext l; rw [← hNM l]; rfl
    simp only [neg, this, hfn]
  · rintro ⟨y', ⟨N, hN, rfl⟩, rfl⟩
    refine ⟨fun l => neg (N l), fun l => ⟨N l, hN l, rfl⟩, ?_⟩
    funext c
    have : (fun l => neg (N l) c) = neg (fun l => N l c) := rfl
    rw [this, hfn]; rfl

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {k L : ℕ} (f : (Fin L → Bool) → Bool) (hf : IsFolded f)
    (P : Set (Fin k → Bool)) : image f (negRel P) = negRel (image f P) :=
  SymBoolPCSP.CFixing.image_negRel_of_folded f hf P
