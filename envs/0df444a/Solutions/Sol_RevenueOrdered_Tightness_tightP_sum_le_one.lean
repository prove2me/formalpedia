-- Prove2me | solution 1 for RevenueOrdered.Tightness.tightP_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T12:07:38.874554+00:00
-- url     : https://prove2.me/submissions/a392e886-a26d-44f8-8dc4-5ae083f326a6

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

set_option autoImplicit false

open RevenueOrdered.Tightness in
theorem tightP60799a40_geom (ε : ℝ) (k : ℕ) :
    (1 - ε) * ∑ i ∈ Finset.Icc 1 k, ε ^ i = ε - ε ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

open RevenueOrdered.Tightness in
theorem tightP60799a40_first (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (S : Finset (TightProduct k)) :
    ∑ x ∈ S, tightP k ε x S ≤ ∑ i ∈ Finset.Icc 1 k, ε ^ i := by
  classical
  set cond : TightProduct k → Prop :=
    fun x => ∀ y ∈ S, y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val with hcond
  have h1 : ∑ x ∈ S, tightP k ε x S = ∑ x ∈ S.filter cond, ε ^ x.val.1.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    unfold tightP
    by_cases hc : cond x
    · rw [if_pos ⟨hx, hc⟩, if_pos hc]
    · rw [if_neg (fun h => hc h.2), if_neg hc]
  rw [h1]
  have hinj : Set.InjOn (fun x : TightProduct k => x.val.1.val) ↑(S.filter cond) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    simp only at hab
    have h1' : a.val.1 = b.val.1 := Fin.ext hab
    have hab2 := ha.2 b hb.1 h1'.symm
    have hba2 := hb.2 a ha.1 h1'
    apply Subtype.ext
    apply Prod.ext h1'
    exact Fin.ext (le_antisymm hab2 hba2)
  rw [← Finset.sum_image (f := fun i => ε ^ i) (g := fun x : TightProduct k => x.val.1.val)
    (fun a ha b hb h => hinj ha hb h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨x, _, rfl⟩ := hi
    rw [Finset.mem_Icc]
    have := x.property
    have := x.val.1.isLt
    constructor <;> omega
  · intro i _ _
    positivity

open RevenueOrdered.Tightness in
theorem solution (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (S : Finset (TightProduct k)) :
    ∑ x ∈ S, tightP k ε x S ≤ ∑ i ∈ Finset.Icc 1 k, ε ^ i ∧
      ∑ i ∈ Finset.Icc 1 k, ε ^ i < 1 / (1 - ε) - 1 ∧
      1 / (1 - ε) - 1 = ε / (1 - ε) ∧
      ε / (1 - ε) ≤ 1 := by
  have hpos : 0 < 1 - ε := by linarith
  have h3 : 1 / (1 - ε) - 1 = ε / (1 - ε) := by
    field_simp
    ring
  refine ⟨tightP60799a40_first k ε hε S, ?_, h3, ?_⟩
  · rw [h3, lt_div_iff₀ hpos, mul_comm, tightP60799a40_geom]
    have : 0 < ε ^ (k + 1) := pow_pos hε _
    linarith
  · rw [div_le_one hpos]
    linarith
