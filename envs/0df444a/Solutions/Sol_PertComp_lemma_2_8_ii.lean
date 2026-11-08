-- Prove2me | solution 1 for PertComp.lemma_2_8_ii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:28:29.377804+00:00
-- url     : https://prove2.me/submissions/12ab2951-1f0e-4045-8210-7643d109e25a

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_PWDB_conj

theorem solution (φ : ℝ → EReal) (hmono : Monotone φ)
    (hφ : RockafellarMaxMono.Shared.ProperConvex φ) :
    {s : ℝ | PWDB.conj φ s ≠ ⊤} ⊆ Set.Ici (0 : ℝ) := by
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [Set.mem_Ici]
  by_contra hneg
  push_neg at hneg
  obtain ⟨x0, hx0⟩ := hφ.2.1
  have hbot := hφ.1 x0
  set c := (φ x0).toReal with hcdef
  have hc : φ x0 = (c : EReal) := (EReal.coe_toReal hx0 hbot).symm
  have key : ∀ x, x ≤ x0 → ((x * s - c : ℝ) : EReal) ≤ PWDB.conj φ s := by
    intro x hx
    have h1 : φ x ≤ (c : EReal) := hc ▸ hmono hx
    calc ((x * s - c : ℝ) : EReal) = ((x * s : ℝ) : EReal) - (c : EReal) := EReal.coe_sub _ _
      _ ≤ ((x * s : ℝ) : EReal) - φ x := EReal.sub_le_sub le_rfl h1
      _ ≤ PWDB.conj φ s := by
        unfold PWDB.conj
        apply le_iSup_of_le x
        have : (inner ℝ x s : ℝ) = x * s := by simp [mul_comm]
        rw [this]
  have hnb : PWDB.conj φ s ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (key x0 le_rfl)
  set B := (PWDB.conj φ s).toReal with hBdef
  have hB : PWDB.conj φ s = (B : EReal) := (EReal.coe_toReal hs hnb).symm
  set x := min x0 ((B + c + 1) / s) with hxdef
  have hx1 : x ≤ x0 := min_le_left _ _
  have hx2 : x ≤ (B + c + 1) / s := min_le_right _ _
  have hx3 : B + c + 1 ≤ x * s := (le_div_iff_of_neg hneg).mp hx2
  have h := key x hx1
  rw [hB, EReal.coe_le_coe_iff] at h
  linarith
