-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.groupObjectsInGrp
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-31T12:16:48.863371+00:00
-- url     : https://prove2.me/submissions/ba3d49f6-d23f-4fcd-bf37-151890320e00

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
import Mathlib.Tactic.Group

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intake100.P20
universe u

theorem solution {G : Type u} [Group G] :
    (∀ D : GroupMaps G, GroupObjectInGrp D →
      (∀ a b : G, a * b = b * a) ∧
      (∀ a b, D.mul a b = a * b) ∧ D.unit = 1 ∧
      (∀ a, D.inverse a = a⁻¹)) ∧
    ((∀ a b : G, a * b = b * a) → GroupObjectInGrp (mapsOfGroup G)) := by
  constructor
  · intro D h
    rcases h with ⟨hd, hu, hmone, hm, hi, him⟩
    have hl (a : G) : D.mul 1 a = a := by simpa only [hu] using hd.unit_left a
    have hr (a : G) : D.mul a 1 = a := by simpa only [hu] using hd.unit_right a
    have hmul (a b : G) : D.mul a b = a * b := by
      simpa only [mul_one, one_mul, hl, hr] using hm a 1 1 b
    have hcomm (a b : G) : a * b = b * a := by
      simpa only [mul_one, one_mul, hl, hr, hmul] using hm 1 b a 1
    refine ⟨hcomm, hmul, hu, ?_⟩
    intro a
    have hleft : D.inverse a * a = 1 := by
      simpa only [hmul, hu] using hd.inverse_left a
    exact (eq_inv_iff_mul_eq_one).2 hleft
  · intro hc
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
    · constructor
      · exact mul_assoc
      · exact one_mul
      · exact mul_one
      · exact inv_mul_cancel
      · exact mul_inv_cancel
    · exact one_mul 1
    · intro a b c d
      change a * c * (b * d) = a * b * (c * d)
      calc
        a * c * (b * d) = a * (c * b) * d := by group
        _ = a * (b * c) * d := by rw [hc c b]
        _ = a * b * (c * d) := by group
    · exact inv_one
    · intro a b
      change (a * b)⁻¹ = a⁻¹ * b⁻¹
      rw [mul_inv_rev, hc]

#print axioms solution
