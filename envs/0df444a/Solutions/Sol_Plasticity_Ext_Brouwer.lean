-- Prove2me | solution 1 for Plasticity.Ext.Brouwer
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:32:59.124959+00:00
-- url     : https://prove2.me/submissions/6cb49a92-ba81-4e19-93a5-a5c82dc26ef3

import Theorems.Thm_Plasticity_Ext_Brouwer_sperner
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Use
import Mathlib.Tactic.Contrapose
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Brouwer's fixed-point theorem for the cube [-1,1]^ι

Ported from harfe, *fixed-point-theorems-lean4*,
https://github.com/harfe/fixed-point-theorems-lean4
(file `FixedPointTheorems/apply_cubical_sperner.lean`; the change of variables to `[-1,1]^ι` is new), MIT licence; the copyright and permission notice is reproduced below.
Adapted to Lean v4.33.1 / Mathlib 0df444a (tactic blocks restyled, a few proof steps repaired).

Copyright (c) 2026 harfe

Permission is hereby granted, free of charge, to any person obtaining a copy of this software
and associated documentation files (the "Software"), to deal in the Software without
restriction, including without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/

open Plasticity

namespace Sol_Plasticity_Ext_Brouwer

open Classical

/-! ## The unit cube `[0,1]ⁿ` (harfe, `apply_cubical_sperner.lean`) -/

variable {n : ℕ}

/-- The unit cube `[0,1]ⁿ` in `Fin n → ℝ` (it is `Set.Icc 0 1`). -/
def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

/-- The label of `x`: the least coordinate `i` with `f(x)ᵢ < xᵢ` or `xᵢ = 1`, and `n` if there is none. -/
noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma reduced_label_props_1 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  let minval := Finset.min s
  let rlp := match minval with
    | some k => k.1
    | none => n
  by_cases he : s = ∅
  · have h1 : @rl_point n f x = n := by
      show rlp = n
      unfold rlp minval
      rw [he]
      simp only [Finset.min_empty]
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h3
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have h1 : @rl_point n f x = m.1 := by
    show rlp = m.1
    unfold rlp minval
    rw [hm]
  rw [h1]
  simp only [Fin.is_le', Fin.val_fin_le, true_and]
  intro k1
  apply And.intro
  · intro h2
    suffices h3 : k1 ∈ s by
      unfold s at h3
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
      exact h3
    apply Finset.mem_of_min
    rw [hm]
    simp only [WithTop.coe_eq_coe]
    ext
    exact h2
  · intro h2
    have h3 : k1 ∈ s := by
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, h2, and_self]
    exact Finset.min_le_of_eq h3 hm

lemma reduced_label_props_2 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by
  have h1 := reduced_label_props_1 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  · intro h2 h3
    have h4 := (h1.2 k).1 h3
    rw [h2] at h4
    simp only [zero_ne_one, or_false] at h4
    contrapose! h4
    exact (f x).2.1 k
  · intro h2
    apply (h1.2 k).2
    exact Or.inr h2

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  · intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  · contrapose!
    intro h2
    apply h1.2
    exact Or.inl h2

/-- The grid point `v ∈ {0,…,p}ⁿ` as the point `v/p` of the unit cube. -/
noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_ofPred_eq]
    rw [Pi.le_def, Pi.le_def, ←forall_and]
    intro i
    simp only [Pi.zero_apply, Pi.one_apply]
    apply And.intro
    exact div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p)
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    exact Fin.is_le (v i)
  }⟩

/-- The labelling of the grid `{0,…,p}ⁿ` induced by `f` satisfies the Sperner conditions. -/
lemma rl_proper_discrete (f : @unit_cube n → @unit_cube n) (p : ℕ) (ppos : 0 < p)
    (v : Fin n → Fin (p+1)) :
    @rl_point n f (discrete_map p v) ≤ n ∧ ∀ k : Fin n,
      (v k = 0 → @rl_point n f (discrete_map p v) ≠ k.1) ∧
      (v k = Fin.last p → @rl_point n f (discrete_map p v) ≤ k.1) := by
  let x := discrete_map p v
  have h1 := reduced_label_props_2 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  · intro h2
    apply (h1.2 k).1
    unfold x discrete_map
    simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
    exact Or.inl h2
  · intro h2
    apply (h1.2 k).2
    unfold x discrete_map
    simp only [h2, Fin.val_last]
    refine (div_eq_one_iff_eq ?_).mpr rfl
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by {rfl}
  have hx2 : x2 k = (v2 k).1 / p := by {rfl}
  rw [hx1, hx2]
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    have ppos2 : 0 < (p : ℝ) := Nat.cast_pos'.mpr ppos
    rwa [div_le_div_iff_of_pos_right ppos2, ←Nat.cast_add_one, Nat.cast_le]
  }

/-- Approximate fixed points from a fully labelled cell (child card
`Plasticity.Ext.Brouwer.sperner`). -/
lemma nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by
  let p := p0 + 1
  have ppos : 0 < p := by omega
  obtain ⟨I, h5, h4⟩ := Plasticity.Ext.Brouwer.sperner n p
    (fun v ↦ @rl_point n f (discrete_map p v)) (rl_proper_discrete f p ppos)
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map p (I i0)
  use x0
  intro k
  apply And.intro
  · apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by exact hi0
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  let xk := discrete_map p (I ik)
  use xk
  apply And.intro _ $ (reduced_label_props_3 f xk k).1 hik
  unfold x0 xk
  apply dist_discrete_map p ppos
  intro k
  exact ⟨h5 i0 ik k, h5 ik i0 k⟩
/-- Brouwer's theorem for the unit cube `[0,1]ⁿ` (harfe's `fixed_point_unit_cube`). -/
theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by
  obtain ⟨x0s, hx0⟩ := Classical.skolem.mp (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    let x0 : ℕ → Fin n → ℝ := fun i ↦ (x0s i).1
    have h2 : ∀ i, x0 i ∈ unit_cube := fun i ↦ (x0s i).2
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact h2
    use ⟨a, ha⟩
    use φ
    exact And.intro h3.1 $ tendsto_subtype_rng.mpr h3.2
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  let y0 := x0s ∘ φ
  let g : Fin n → @unit_cube n → ℝ := fun k x ↦ x.1 k
  have hc2 k : Continuous (g k) := by
    exact (continuous_apply k).comp continuous_subtype_val
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by
    show g k xxx ≤ g k (f xxx)
    have h6 :=  (hc2 k).seqContinuous h2.2
    have h7 := (hc2 k).seqContinuous $ f.2.seqContinuous h2.2
    apply le_of_tendsto_of_tendsto' h6 h7
    exact fun i ↦ (hx0 (φ i) k).1
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by
    show g k (f xxx) ≤ g k xxx
    have h5 n:= (hx0 (φ n) k).2
    obtain ⟨yk, h6⟩ := Classical.skolem.mp h5
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by
      apply tendsto_of_tendsto_of_dist h2.2
      have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h7 _
      · intro i
        apply le_trans (h6 i).1
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        apply inv_anti₀ (Nat.cast_add_one_pos i)
        simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply]
      exact fun _ ↦ dist_nonneg
    have h7 := (hc2 k).seqContinuous h4
    have h8 := (hc2 k).seqContinuous $ f.2.seqContinuous h4
    apply le_of_tendsto_of_tendsto' h8 h7
    exact fun i ↦ (h6 i).2
  use xxx
  ext k
  apply le_antisymm (h4 k) (h3 k)

/-! ## The cube `[-1,1]^ι`: affine change of variables and `ι ≃ Fin n` -/

/-- Brouwer's theorem for `[-1,1]^ι`, from the unit cube `[0,1]^m`, `m = |ι|`, via
`y ↦ (i ↦ 2 y (e i) - 1)` for an equivalence `e : ι ≃ Fin m`. -/
theorem brouwer_Icc {ι : Type*} [Fintype ι] (f : (ι → ℝ) → (ι → ℝ))
    (hf : ContinuousOn f (Set.Icc (-1) 1))
    (hmaps : Set.MapsTo f (Set.Icc (-1) 1) (Set.Icc (-1) 1)) :
    ∃ x ∈ Set.Icc (-1 : ι → ℝ) 1, f x = x := by
  let m := Fintype.card ι
  let e : ι ≃ Fin m := Fintype.equivFin ι
  let A : (Fin m → ℝ) → (ι → ℝ) := fun y i => 2 * y (e i) - 1
  let B : (ι → ℝ) → (Fin m → ℝ) := fun x k => (x (e.symm k) + 1) / 2
  have hA : Continuous A :=
    continuous_pi fun i => ((continuous_apply (e i)).const_mul 2).sub continuous_const
  have hB : Continuous B :=
    continuous_pi fun k => ((continuous_apply (e.symm k)).add continuous_const).div_const 2
  have hAB : ∀ x, A (B x) = x := by
    intro x
    funext i
    simp only [A, B, Equiv.symm_apply_apply]
    ring
  have hAm : ∀ y ∈ @unit_cube m, A y ∈ Set.Icc (-1 : ι → ℝ) 1 := by
    intro y hy
    obtain ⟨h0, h1⟩ := hy
    constructor
    · intro i
      have := h0 (e i)
      simp only [Pi.neg_apply, Pi.one_apply, Pi.zero_apply, A] at this ⊢
      linarith
    · intro i
      have := h1 (e i)
      simp only [Pi.one_apply, A] at this ⊢
      linarith
  have hBm : ∀ x ∈ Set.Icc (-1 : ι → ℝ) 1, B x ∈ @unit_cube m := by
    intro x hx
    obtain ⟨h0, h1⟩ := hx
    constructor
    · intro k
      have := h0 (e.symm k)
      simp only [Pi.neg_apply, Pi.one_apply, Pi.zero_apply, B] at this ⊢
      linarith
    · intro k
      have := h1 (e.symm k)
      simp only [Pi.one_apply, B] at this ⊢
      linarith
  let g : C(@unit_cube m, @unit_cube m) :=
    ⟨fun y => ⟨B (f (A y.1)), hBm _ (hmaps (hAm y.1 y.2))⟩, by
      apply Continuous.subtype_mk
      exact hB.comp (hf.comp_continuous (hA.comp continuous_subtype_val) (fun y => hAm y.1 y.2))⟩
  obtain ⟨y, hy⟩ := fixed_point_unit_cube g
  refine ⟨A y.1, hAm y.1 y.2, ?_⟩
  have h1 : B (f (A y.1)) = y.1 := congrArg Subtype.val hy
  calc f (A y.1) = A (B (f (A y.1))) := (hAB _).symm
    _ = A y.1 := by rw [h1]

end Sol_Plasticity_Ext_Brouwer

theorem solution {ι : Type*} [Fintype ι] (f : (ι → ℝ) → (ι → ℝ))
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (hmaps : Set.MapsTo f (Set.Icc (-1) 1) (Set.Icc (-1) 1)) :
    ∃ x ∈ Set.Icc (-1 : ι → ℝ) 1, f x = x :=
  Sol_Plasticity_Ext_Brouwer.brouwer_Icc f hf hmaps
