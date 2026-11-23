-- Prove2me | solution 1 for ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:16.223462+00:00
-- url     : https://prove2.me/submissions/c3149525-b211-43fa-b136-263c5eabadd1

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace ReciprocityTheory.Aut
theorem _root_.solution {x : v.adicCompletion F} (h : Valued.v x < 1) :
    Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]
    exact zero_le'
  · obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
    rw [← ha] at h ⊢
    have h1 : a < 1 := by exact_mod_cast h
    have h2 : Multiplicative.toAdd a < 0 := by
      rw [← toAdd_one, Multiplicative.toAdd_lt]
      exact h1
    have h3 : a ≤ Multiplicative.ofAdd (-1 : ℤ) := by
      rw [← Multiplicative.toAdd_le, toAdd_ofAdd]
      omega
    show (a : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    exact WithZero.coe_le_coe.mpr h3
end ReciprocityTheory.Aut
