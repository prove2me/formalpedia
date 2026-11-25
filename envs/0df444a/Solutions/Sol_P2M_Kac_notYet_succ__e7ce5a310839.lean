-- Prove2me | solution 1 for P2M_Kac_notYet_succ__e7ce5a310839
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:12:16.758993+00:00
-- url     : https://prove2.me/submissions/d4a2ee20-bf0d-44d7-9e49-2c14357e3ea6

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_mem_notYet_iff
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (n : ℕ) : notYet f A (n + 1) = notYet f A n ∩ (f^[n] ⁻¹' A)ᶜ := by
  ext x
  simp only [mem_inter_iff, mem_compl_iff, mem_preimage, mem_notYet_iff]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h n (by omega)⟩
  · rintro ⟨h, hn⟩ k hk
    rcases Nat.lt_or_ge k n with hkn | hkn
    · exact h k hkn
    · obtain rfl : k = n := by omega
      exact hn
end Kac
