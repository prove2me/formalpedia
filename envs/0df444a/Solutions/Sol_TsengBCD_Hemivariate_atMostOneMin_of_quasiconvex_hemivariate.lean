-- Prove2me | solution 1 for TsengBCD.Hemivariate.atMostOneMin_of_quasiconvex_hemivariate
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:55:25.182032+00:00
-- url     : https://prove2.me/submissions/33be20b4-6a2c-43b7-bf93-f49ff164196a

import Mathlib
import Definitions.Def_TsengBCD_Hemivariate_Setting

open TsengBCD.Hemivariate

theorem solution {V : Type*} [AddCommGroup V] [Module ℝ V]
    (h : V → EReal) (hqc : IsQuasiconvex h) (hhv : IsHemivariate h) :
    ∀ a b : V, h a ≠ ⊤ → (∀ c, h a ≤ h c) → (∀ c, h b ≤ h c) → a = b := by
  intro a b ha hamin hbmin
  by_contra hab
  have habval : h b = h a := le_antisymm (hbmin a) (hamin b)
  have constant : ∀ p ∈ segment ℝ a b, h p = h a := by
    intro p hp
    rw [segment_eq_image'] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    apply le_antisymm
    · simpa [sub_add_cancel, habval] using hqc a (b - a) t ht
    · exact hamin _
  obtain ⟨p, hp, q, hq, hpq⟩ := hhv a b hab (by
    intro p hp
    simpa [constant p hp] using ha)
  exact hpq ((constant p hp).trans (constant q hq).symm)

#print axioms solution
