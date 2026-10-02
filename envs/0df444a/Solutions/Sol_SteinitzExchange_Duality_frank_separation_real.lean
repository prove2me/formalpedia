-- Prove2me | solution 1 for SteinitzExchange.Duality.frank_separation_real
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T20:01:38.107159+00:00
-- url     : https://prove2.me/submissions/2739e272-ddef-487e-a71a-6a2e839e7176

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


set_option autoImplicit false

namespace SteinitzSeparationReal

open Finset

variable {V α : Type*} [DecidableEq V]
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

def SubmodOn (S : Finset V) (f : Finset V → α) : Prop :=
  ∀ X ⊆ S, ∀ Y ⊆ S, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y

def SupermodOn (S : Finset V) (g : Finset V → α) : Prop :=
  ∀ X ⊆ S, ∀ Y ⊆ S, g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y)

def projectUpper (f : Finset V → α) (u : V) (t : α) (X : Finset V) : α :=
  min (f X) (f (insert u X) - t)

def projectLower (g : Finset V → α) (u : V) (t : α) (X : Finset V) : α :=
  max (g X) (g (insert u X) - t)

lemma min_pair_bound (aU aI aX aY bU bI bX bY t : α)
    (h00 : aU + aI ≤ aX + aY) (h11 : bU + bI ≤ bX + bY)
    (h01 : bU + aI ≤ aX + bY) (h10 : bU + aI ≤ bX + aY) :
    min aU (bU - t) + min aI (bI - t) ≤
      min aX (bX - t) + min aY (bY - t) := by
  rcases le_total aX (bX - t) with hx | hx <;>
    rcases le_total aY (bY - t) with hy | hy
  · rw [min_eq_left hx, min_eq_left hy]
    exact (add_le_add (min_le_left _ _) (min_le_left _ _)).trans h00
  · rw [min_eq_left hx, min_eq_right hy]
    calc
      min aU (bU - t) + min aI (bI - t) ≤ (bU - t) + aI :=
        add_le_add (min_le_right _ _) (min_le_left _ _)
      _ = (bU + aI) - t := by abel
      _ ≤ (aX + bY) - t := sub_le_sub_right h01 t
      _ = aX + (bY - t) := by abel
  · rw [min_eq_right hx, min_eq_left hy]
    calc
      min aU (bU - t) + min aI (bI - t) ≤ (bU - t) + aI :=
        add_le_add (min_le_right _ _) (min_le_left _ _)
      _ = (bU + aI) - t := by abel
      _ ≤ (bX + aY) - t := sub_le_sub_right h10 t
      _ = (bX - t) + aY := by abel
  · rw [min_eq_right hx, min_eq_right hy]
    calc
      min aU (bU - t) + min aI (bI - t) ≤ (bU - t) + (bI - t) :=
        add_le_add (min_le_right _ _) (min_le_right _ _)
      _ = (bU + bI) - (t + t) := by abel
      _ ≤ (bX + bY) - (t + t) := sub_le_sub_right h11 (t + t)
      _ = (bX - t) + (bY - t) := by abel

/-- Fixing the deleted coordinate preserves submodularity on the reduced
    ground set. The mixed cases use the deleted coordinate outside both sets. -/
theorem projectUpper_submodular (S : Finset V) (u : V) (hu : u ∉ S)
    (f : Finset V → α) (t : α) (hf : SubmodOn (insert u S) f) :
    SubmodOn S (projectUpper f u t) := by
  intro X hX Y hY
  have huX : u ∉ X := fun hx => hu (hX hx)
  have huY : u ∉ Y := fun hy => hu (hY hy)
  have hXS : X ⊆ insert u S := hX.trans (subset_insert _ _)
  have hYS : Y ⊆ insert u S := hY.trans (subset_insert _ _)
  have hXu : insert u X ⊆ insert u S := insert_subset_insert u hX
  have hYu : insert u Y ⊆ insert u S := insert_subset_insert u hY
  have hUU : insert u X ∪ insert u Y = insert u (X ∪ Y) := by
    ext v
    simp [or_assoc, or_left_comm, or_comm]
  have hII : insert u X ∩ insert u Y = insert u (X ∩ Y) := by
    ext v
    by_cases hv : v = u <;> simp [hv]
  have hUX : insert u X ∪ Y = insert u (X ∪ Y) := by
    ext v
    simp [or_assoc]
  have hUY : X ∪ insert u Y = insert u (X ∪ Y) := by
    ext v
    simp [or_assoc, or_left_comm, or_comm]
  have hIX : insert u X ∩ Y = X ∩ Y := by
    ext v
    by_cases hv : v = u <;> simp [hv, huY]
  have hIY : X ∩ insert u Y = X ∩ Y := by
    ext v
    by_cases hv : v = u <;> simp [hv, huX]
  apply min_pair_bound
  · exact hf X hXS Y hYS
  · simpa only [hUU, hII] using hf (insert u X) hXu (insert u Y) hYu
  · simpa only [hUY, hIY] using hf X hXS (insert u Y) hYu
  · simpa only [hUX, hIX] using hf (insert u X) hXu Y hYS

theorem projectLower_supermodular (S : Finset V) (u : V) (hu : u ∉ S)
    (g : Finset V → α) (t : α) (hg : SupermodOn (insert u S) g) :
    SupermodOn S (projectLower g u t) := by
  exact projectUpper_submodular (α := OrderDual α) S u hu g t hg

lemma cross_bounds (S : Finset V) (u : V) (hu : u ∈ S) (f g : Finset V → α)
    (hf : SubmodOn S f) (hg : SupermodOn S g) (hgf : ∀ X ⊆ S, g X ≤ f X)
    (X Y : Finset V) (hX : X ⊆ S) (hY : Y ⊆ S) (huX : u ∉ X) (huY : u ∉ Y) :
    g (insert u X) - f X ≤ f (insert u Y) - g Y := by
  have hXu : insert u X ⊆ S := insert_subset_iff.mpr ⟨hu, hX⟩
  have hYu : insert u Y ⊆ S := insert_subset_iff.mpr ⟨hu, hY⟩
  have hU : insert u (X ∪ Y) ⊆ S := insert_subset_iff.mpr ⟨hu, union_subset hX hY⟩
  have hI : X ∩ Y ⊆ S := inter_subset_left.trans hX
  have hUX : insert u X ∪ Y = insert u (X ∪ Y) := by
    ext v
    simp [or_assoc]
  have hUY : X ∪ insert u Y = insert u (X ∪ Y) := by
    ext v
    simp [or_assoc, or_left_comm, or_comm]
  have hIX : insert u X ∩ Y = X ∩ Y := by
    ext v
    by_cases hv : v = u <;> simp [hv, huY]
  have hIY : X ∩ insert u Y = X ∩ Y := by
    ext v
    by_cases hv : v = u <;> simp [hv, huX]
  have hsum : g (insert u X) + g Y ≤ f X + f (insert u Y) := by
    calc
      g (insert u X) + g Y ≤ g (insert u (X ∪ Y)) + g (X ∩ Y) := by
        simpa only [hUX, hIX] using hg (insert u X) hXu Y hY
      _ ≤ f (insert u (X ∪ Y)) + f (X ∩ Y) := add_le_add (hgf _ hU) (hgf _ hI)
      _ ≤ f X + f (insert u Y) := by
        simpa only [hUY, hIY] using hf X hX (insert u Y) hYu
  exact sub_le_sub_iff.mpr (by simpa only [add_comm] using hsum)

/-- All lower bounds for the deleted coordinate lie below all upper bounds;
    their finite maximum is a feasible value in the same ordered group. -/
theorem exists_coordinate_value (S : Finset V) (u : V) (hu : u ∈ S)
    (f g : Finset V → α) (hf : SubmodOn S f) (hg : SupermodOn S g)
    (hgf : ∀ X ⊆ S, g X ≤ f X) :
    ∃ t : α, ∀ X ⊆ S.erase u,
      g (insert u X) - f X ≤ t ∧ t ≤ f (insert u X) - g X := by
  classical
  let P : Finset (Finset V) := (S.erase u).powerset
  have hP : P.Nonempty := ⟨∅, mem_powerset.mpr (empty_subset _)⟩
  let t : α := P.sup' hP (fun X => g (insert u X) - f X)
  refine ⟨t, fun X hX => ⟨?_, ?_⟩⟩
  · exact le_sup' (fun X => g (insert u X) - f X) (show X ∈ P from mem_powerset.mpr hX)
  · apply Finset.sup'_le hP (fun X => g (insert u X) - f X)
    intro Y hY
    have hYs : Y ⊆ S.erase u := mem_powerset.mp hY
    exact cross_bounds S u hu f g hf hg hgf Y X
      (hYs.trans (erase_subset _ _)) (hX.trans (erase_subset _ _))
      (fun hy => notMem_erase u S (hYs hy)) (fun hx => notMem_erase u S (hX hx))

lemma projected_interval_sandwich (f g fu gu t : α)
    (hgf : g ≤ f) (hgfu : gu ≤ fu) (hlo : gu - f ≤ t) (hhi : t ≤ fu - g) :
    max g (gu - t) ≤ min f (fu - t) := by
  refine max_le (le_min hgf ?_) (le_min ?_ (sub_le_sub_right hgfu t))
  · apply le_sub_iff_add_le.mpr
    simpa only [add_comm] using le_sub_iff_add_le.mp hhi
  · apply sub_le_iff_le_add.mpr
    simpa only [add_comm] using sub_le_iff_le_add.mp hlo

theorem projection_normalized_and_ordered (S : Finset V) (u : V) (hu : u ∈ S)
    (f g : Finset V → α) (hf0 : f ∅ = 0) (hg0 : g ∅ = 0)
    (hgf : ∀ X ⊆ S, g X ≤ f X) (t : α)
    (ht : ∀ X ⊆ S.erase u, g (insert u X) - f X ≤ t ∧ t ≤ f (insert u X) - g X) :
    projectUpper f u t ∅ = 0 ∧ projectLower g u t ∅ = 0 ∧
      ∀ X ⊆ S.erase u, projectLower g u t X ≤ projectUpper f u t X := by
  have ht0 := ht ∅ (empty_subset _)
  have hlo : g {u} ≤ t := by simpa [hf0] using ht0.1
  have hhi : t ≤ f {u} := by simpa [hg0] using ht0.2
  refine ⟨?_, ?_, fun X hX => ?_⟩
  · simp only [projectUpper, hf0, insert_empty]
    exact min_eq_left (sub_nonneg.mpr hhi)
  · simp only [projectLower, hg0, insert_empty]
    exact max_eq_left (sub_nonpos.mpr hlo)
  · exact projected_interval_sandwich _ _ _ _ _
      (hgf X (hX.trans (erase_subset _ _)))
      (hgf (insert u X) (insert_subset_iff.mpr ⟨hu, hX.trans (erase_subset _ _)⟩))
      (ht X hX).1 (ht X hX).2

#print axioms projection_normalized_and_ordered

end SteinitzSeparationReal


set_option autoImplicit false

namespace SteinitzSeparationReal

open Finset

variable {V α : Type*} [DecidableEq V]
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- Coordinate elimination constructs a separator in the original ordered
    additive group, so the same proof yields both real and integer separation. -/
theorem separator_on_ground (S : Finset V) (f g : Finset V → α)
    (hf0 : f ∅ = 0) (hg0 : g ∅ = 0) (hf : SubmodOn S f) (hg : SupermodOn S g)
    (hgf : ∀ X ⊆ S, g X ≤ f X) :
    ∃ x : V → α, ∀ X ⊆ S, g X ≤ ∑ v ∈ X, x v ∧ (∑ v ∈ X, x v) ≤ f X := by
  classical
  induction S using Finset.induction_on generalizing f g with
  | empty =>
    refine ⟨fun _ => 0, fun X hX => ?_⟩
    obtain rfl := subset_empty.mp hX
    simp [hf0, hg0]
  | @insert u S hu ih =>
    obtain ⟨t, ht⟩ := exists_coordinate_value (insert u S) u (mem_insert_self _ _)
      f g hf hg hgf
    have htS : ∀ X ⊆ S, g (insert u X) - f X ≤ t ∧ t ≤ f (insert u X) - g X := by
      simpa only [erase_insert hu] using ht
    obtain ⟨hf'0, hg'0, hgf'⟩ :=
      projection_normalized_and_ordered (insert u S) u (mem_insert_self _ _)
        f g hf0 hg0 hgf t ht
    have hgfS : ∀ X ⊆ S, projectLower g u t X ≤ projectUpper f u t X := by
      simpa only [erase_insert hu] using hgf'
    obtain ⟨x, hx⟩ := ih (projectUpper f u t) (projectLower g u t) hf'0 hg'0
      (projectUpper_submodular S u hu f t hf)
      (projectLower_supermodular S u hu g t hg) hgfS
    let x' : V → α := Function.update x u t
    refine ⟨x', fun X hX => ?_⟩
    by_cases huX : u ∈ X
    · have hY : X.erase u ⊆ S := by
        simpa only [erase_insert hu] using Finset.erase_subset_erase u hX
      have hxY := hx (X.erase u) hY
      have hsumY : (∑ v ∈ X.erase u, x' v) = ∑ v ∈ X.erase u, x v := by
        apply sum_congr rfl
        intro v hv
        have hvu : v ≠ u := (mem_erase.mp hv).1
        simp [x', Function.update, hvu, Ne.symm hvu]
      have hsumX : (∑ v ∈ X, x' v) = (∑ v ∈ X.erase u, x v) + t := by
        calc
          (∑ v ∈ X, x' v) = ∑ v ∈ insert u (X.erase u), x' v :=
            congrArg (fun T : Finset V => ∑ v ∈ T, x' v) (insert_erase huX).symm
          _ = x' u + ∑ v ∈ X.erase u, x' v := sum_insert (notMem_erase u X)
          _ = (∑ v ∈ X.erase u, x v) + t := by simp [x', hsumY, add_comm]
      have hlo : g X - t ≤ ∑ v ∈ X.erase u, x v := by
        have h := (le_max_right (g (X.erase u)) (g (insert u (X.erase u)) - t)).trans hxY.1
        simpa only [insert_erase huX] using h
      have hhi : (∑ v ∈ X.erase u, x v) ≤ f X - t := by
        have h := hxY.2.trans (min_le_right (f (X.erase u)) (f (insert u (X.erase u)) - t))
        simpa only [insert_erase huX] using h
      rw [hsumX]
      exact ⟨sub_le_iff_le_add.mp hlo, le_sub_iff_add_le.mp hhi⟩
    · have hXS : X ⊆ S := by
        intro v hv
        rcases mem_insert.mp (hX hv) with hvu | hvs
        · subst v
          exact (huX hv).elim
        · exact hvs
      have hxX := hx X hXS
      have hsumX : (∑ v ∈ X, x' v) = ∑ v ∈ X, x v := by
        apply sum_congr rfl
        intro v hv
        have hvu : v ≠ u := fun h => huX (h ▸ hv)
        simp [x', Function.update, hvu, Ne.symm hvu]
      rw [hsumX]
      exact ⟨(le_max_left _ _).trans hxX.1, hxX.2.trans (min_le_left _ _)⟩

theorem exists_separator [Fintype V] (f g : Finset V → α)
    (hf : ∀ X Y, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y)
    (hg : ∀ X Y, g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y))
    (hf0 : f ∅ = 0) (hg0 : g ∅ = 0) (hgf : ∀ X, g X ≤ f X) :
    ∃ x : V → α, ∀ X : Finset V,
      g X ≤ ∑ v ∈ X, x v ∧ (∑ v ∈ X, x v) ≤ f X := by
  obtain ⟨x, hx⟩ := separator_on_ground univ f g hf0 hg0
    (fun X _ Y _ => hf X Y) (fun X _ Y _ => hg X Y) (fun X _ => hgf X)
  exact ⟨x, fun X => hx X (subset_univ X)⟩

#print axioms exists_separator

end SteinitzSeparationReal

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (f g : Finset V → ℝ)
    (hf : ∀ X Y : Finset V, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y)
    (hg : ∀ X Y : Finset V, g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y))
    (hf0 : f ∅ = 0) (hg0 : g ∅ = 0) (hgf : ∀ X : Finset V, g X ≤ f X) :
    ∃ xs : V → ℝ, ∀ X : Finset V,
      g X ≤ Finset.sum X (fun v => xs v) ∧ Finset.sum X (fun v => xs v) ≤ f X := by
  exact SteinitzSeparationReal.exists_separator f g hf hg hf0 hg0 hgf

#print axioms solution
