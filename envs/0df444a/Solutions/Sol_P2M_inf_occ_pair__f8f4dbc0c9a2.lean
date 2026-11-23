-- Prove2me | solution 1 for P2M_inf_occ_pair__f8f4dbc0c9a2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:53:40.741036+00:00
-- url     : https://prove2.me/submissions/c7be9598-8279-4d81-903b-d6a0621b62e1

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Theorems.Thm_frequently_iff_strict_mono
import Theorems.Thm_frequently_in_finite_set

set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
theorem _root_.solution {X1 : Type u} {X2 : Type v} [Finite X1] [Finite X2] (xs : Stream' (X1 × X2)) :
    fst '' (InfOcc xs) = InfOcc (fst ∘ xs) ∧
    snd '' (InfOcc xs) = InfOcc (snd ∘ xs) := by
  constructor
  · ext x1 ; simp ; constructor
    · rintro ⟨x2, h_inf⟩
      obtain ⟨φ, h_mono, h_x⟩ := frequently_iff_strict_mono.mp h_inf
      apply frequently_iff_strict_mono.mpr
      exact ⟨φ, h_mono, fun m => congrArg Prod.fst (h_x m)⟩
    · intro h_inf
      let s := { x : X1 × X2 | x.1 = x1 }
      have h_inf' : ∃ᶠ k in atTop, xs k ∈ s := by exact h_inf
      obtain ⟨x, h_x, h_inf''⟩ := frequently_in_finite_set.mp h_inf'
      aesop
  · ext x2 ; simp ; constructor
    · rintro ⟨x1, h_inf⟩
      obtain ⟨φ, h_mono, h_x⟩ := frequently_iff_strict_mono.mp h_inf
      apply frequently_iff_strict_mono.mpr
      exact ⟨φ, h_mono, fun m => congrArg Prod.snd (h_x m)⟩
    · intro h_inf
      let s := { x : X1 × X2 | x.2 = x2 }
      have h_inf' : ∃ᶠ k in atTop, xs k ∈ s := by exact h_inf
      obtain ⟨x, h_x, h_inf''⟩ := frequently_in_finite_set.mp h_inf'
      aesop
