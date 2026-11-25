-- Prove2me | solution 1 for SNumbers.Complexification.conj_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:35.345317+00:00
-- url     : https://prove2.me/submissions/61fb4ad5-2f07-44ae-8423-32b997f8de26

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module
public import Definitions.Def_BasicResults_Spectral_Complexification

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open RCLike Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
open SNumbers
open SNumbers.Complexification
namespace SNumbers.Complexification
theorem _root_.solution (u : Complexification H) : conj u = u ↔ ∃ x, u = ofReal x := by
  constructor
  · intro h
    have hsnd : -u.2 = u.2 := by simpa only [conj_snd] using congrArg Prod.snd h
    have hz : u.2 = 0 := by
      have h2 : (2 : ℝ) • u.2 = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr hsnd.symm
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    exact ⟨u.1, by apply Prod.ext <;> simp [hz]⟩
  · rintro ⟨x, rfl⟩; exact conj_ofReal x
end SNumbers.Complexification
