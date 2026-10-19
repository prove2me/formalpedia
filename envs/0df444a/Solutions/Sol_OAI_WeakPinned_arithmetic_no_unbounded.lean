-- Prove2me | solution 1 for OAI.WeakPinned.arithmetic_no_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:06:22.264056+00:00
-- url     : https://prove2.me/submissions/fc0d4657-6f7e-49a5-8f34-ac6e78f1535a

import Mathlib
import Definitions.Def_PinnedDistances
import Definitions.Def_OAIQWWP000
import Theorems.Thm_OAI_WeakPinned_arithmetic_balanced_length
import Theorems.Thm_OAI_WeakPinned_sampling_variance_rates

section
-- module Solutions.OAIQW_WeakPinned.ProductFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section

/- The finite-place absolute values are norm-normalized. Dividing their logarithms
   by [K:ℚ] gives the weighted contribution of locally normalized absolute values. -/

noncomputable section
open NumberField
open scoped BigOperators

namespace WeakPinned.Arithmetic

variable {K : Type u1} [Field K]

variable [NumberField K]

lemma log_product_formula (z : K) (hz : z ≠ 0) :
    (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v z)) +
      ∑ᶠ v : FinitePlace K, Real.log (v z) = 0 := by
  have hi : ∀ v : InfinitePlace K, 0 < v z := fun _ => InfinitePlace.pos_iff.mpr hz
  have hf : ∀ v : FinitePlace K, 0 < v z := fun _ => FinitePlace.pos_iff.mpr hz
  have h := congrArg Real.log (NumberField.prod_abs_eq_one hz)
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hi v).ne')
    (finprod_ne_zero fun v => (hf v).ne'), Real.log_prod (fun v _ => pow_ne_zero _ (hi v).ne'),
    Real.log_finprod hf, Real.log_one] at h
  simpa only [Real.log_pow] using h

lemma sum_archWeight : ∑ v : InfinitePlace K, archWeight v = 1 := by
  classical
  unfold archWeight
  rw [← Finset.sum_div, ← Nat.cast_sum, InfinitePlace.sum_mult_eq, div_self]
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'

lemma archWeight_nonneg (v : InfinitePlace K) : 0 ≤ archWeight v := by
  unfold archWeight
  positivity

omit [NumberField K] in
/-- Multiplicativity gives the constant depth sum on each nonzero fiber at
    every absolute value; neither the embeddings nor the field are fixed. -/
lemma raw_fiber_identity (v : AbsoluteValue K ℝ) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    -Real.log (v a) + -Real.log (v b) = -Real.log (v (a * b)) := by
  rw [map_mul, Real.log_mul (v.pos ha).ne' (v.pos hb).ne']
  ring

/-- The algebraic inversion identity used both by the unbounded tree argument
    and the bounded Mobius argument. This is valid in any field. -/
lemma paired_coordinate {F : Type u3} [Field F] (a b c d t : F)
    (ha : c ≠ a) (h : (c-a)*(d-b)=t) : d = b + t/(c-a) := by
  have h' : d-b = t/(c-a) := (eq_div_iff (sub_ne_zero.mpr ha)).mpr
    (by simpa [mul_comm] using h)
  rw [← h']
  ring

lemma paired_difference {F : Type u4} [Field F] (a b c d z w t : F)
    (hc : c ≠ a) (hz : z ≠ a)
    (hcd : (c-a)*(d-b)=t) (hzw : (z-a)*(w-b)=t) :
    w-d = t * (c-z) / ((z-a)*(c-a)) := by
  rw [paired_coordinate a b c d t hc hcd, paired_coordinate a b z w t hz hzw]
  field_simp
  ring

lemma normalized_log_product_formula (z : K) (hz : z ≠ 0) :
    (∑ v : InfinitePlace K, archWeight v * (-Real.log (v z))) +
      (Module.finrank ℚ K : ℝ)⁻¹ * ∑ᶠ v : FinitePlace K, -Real.log (v z) = 0 := by
  have hh := log_product_formula z hz
  simp only [archWeight, div_eq_mul_inv]
  rw [finsum_neg_distrib]
  have he : (∑ v : InfinitePlace K, (v.mult:ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ * (-Real.log (v z))) =
      -(Module.finrank ℚ K : ℝ)⁻¹ * ∑ v : InfinitePlace K, (v.mult:ℝ) * Real.log (v z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he]
  linear_combination -(Module.finrank ℚ K : ℝ)⁻¹ * hh

end WeakPinned.Arithmetic

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.Hierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators

/- Deterministic giant-removal identity. -/

noncomputable section
open MeasureTheory
open scoped Topology

namespace WeakPinned.Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]

namespace Depth

variable (d : Depth P)

omit [Fintype P] [DecidableEq P] in
lemma share_refl (r : ℝ) (x : P) : d.share r x x := Or.inl rfl
omit [Fintype P] [DecidableEq P] in
lemma share_symm {r : ℝ} {x y : P} (h : d.share r x y) : d.share r y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by simpa only [d.symm y x] using h)
omit [Fintype P] in
lemma share_trans {r : ℝ} {x y z : P} (hxy : d.share r x y) (hyz : d.share r y z) :
    d.share r x z := by
  by_cases h₁ : x = y
  · subst y; exact hyz
  by_cases h₂ : y = z
  · subst z; exact hxy
  by_cases h₃ : x = z
  · exact Or.inl h₃
  exact Or.inr ((le_min (hxy.resolve_left h₁) (hyz.resolve_left h₂)).trans
    (d.ultra x y z h₁ h₂ h₃))
omit [Fintype P] [DecidableEq P] in
lemma share_mono {r t : ℝ} (htr : t ≤ r) {x y : P} (h : d.share r x y) :
    d.share t x y := h.imp_right (htr.trans ·)

omit [DecidableEq P] in
@[simp] lemma self_mem_cell (r : ℝ) (x : P) : x ∈ d.cell r x := by
  simp [share_refl]

lemma cell_eq_of_share {r : ℝ} {x y : P} (h : d.share r x y) : d.cell r x = d.cell r y := by
  ext z
  simp only [mem_cell]
  exact ⟨fun hz => d.share_trans (d.share_symm h) hz, fun hz => d.share_trans h hz⟩

omit [DecidableEq P] in
lemma cell_mono {r t : ℝ} (htr : t ≤ r) (x : P) : d.cell r x ⊆ d.cell t x := by
  intro z hz
  exact (d.mem_cell t x z).mpr (d.share_mono htr ((d.mem_cell r x z).mp hz))

lemma cell_mem_cells (r : ℝ) (x : P) : d.cell r x ∈ d.cells r := by simp

lemma cell_of_mem {r : ℝ} {C : Finset P} (hC : C ∈ d.cells r) {x : P} (hx : x ∈ C) :
    C = d.cell r x := by
  obtain ⟨z, rfl⟩ := (d.mem_cells r C).mp hC
  exact d.cell_eq_of_share ((d.mem_cell r z x).mp hx)

lemma cells_disjoint {r : ℝ} {C D : Finset P} (hC : C ∈ d.cells r)
    (hD : D ∈ d.cells r) (hne : C ≠ D) : Disjoint C D := by
  apply Finset.disjoint_left.mpr
  intro x hx hd
  exact hne ((d.cell_of_mem hC hx).trans (d.cell_of_mem hD hd).symm)

lemma cells_pair_sum (r : ℝ) (x y : P) :
    (∑ C ∈ d.cells r, (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) =
      if d.share r x y then 1 else 0 := by
  have h : ∀ C ∈ d.cells r, (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0) =
      if C = d.cell r x then (if d.share r x y then 1 else 0) else 0 := by
    intro C hC
    by_cases hx : x ∈ C
    · rw [d.cell_of_mem hC hx]
      simp [d.share_refl]
    · have hne : C ≠ d.cell r x := by intro he; apply hx; simpa [he] using d.self_mem_cell r x
      simp [hx, hne]
  rw [Finset.sum_congr rfl h]
  simp [d.cell_mem_cells r x]

lemma giants_unique {r : ℝ} {C D : Finset P} (hC : C ∈ d.giants r)
    (hD : D ∈ d.giants r) : C = D := by
  rw [d.mem_giants] at hC hD
  by_contra hne
  have hd := d.cells_disjoint hC.1 hD.1 hne
  have hc := Finset.card_le_univ (C ∪ D)
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

lemma giant_eq {r : ℝ} {C : Finset P} (hC : C ∈ d.giants r) : d.giant r = C := by
  have he : d.giants r = {C} := Finset.ext fun D => by
    simp only [Finset.mem_singleton]
    exact ⟨fun hd => d.giants_unique hd hC, fun hd => hd ▸ hC⟩
  simp [giant, he]

lemma sumCells_formula (f : Finset P → ℝ) (r : ℝ) :
    d.sumCells f r = (∑ C ∈ d.cells r, f C) +
      ∑ C ∈ d.giants r, (f Cᶜ - f C) := by
  classical
  simp only [sumCells, transformed, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Finset.sum, Function.comp_def]
  change (∑ C ∈ (d.cells r).filter (fun C => ¬Fintype.card P < 2*C.card), f C) +
    (∑ C ∈ d.giants r, f Cᶜ) = (∑ C ∈ d.cells r, f C) +
      ∑ C ∈ d.giants r, (f Cᶜ - f C)
  rw [Finset.sum_sub_distrib]
  have hh := Finset.sum_filter_add_sum_filter_not (d.cells r)
    (fun C => Fintype.card P < 2*C.card) f
  change (∑ C ∈ d.giants r, f C) + _ = _ at hh
  linarith

lemma pairOverlap_formula (r : ℝ) (x y : P) :
    d.pairOverlap r x y = (if d.share r x y then 1 else 0) -
      d.giantIndicator r + d.outsideIndicator r x + d.outsideIndicator r y := by
  unfold pairOverlap
  rw [d.sumCells_formula, d.cells_pair_sum]
  unfold giantIndicator outsideIndicator
  by_cases hg : (d.giants r).Nonempty
  · obtain ⟨G,hG⟩ := hg
    have he : d.giants r = {G} := Finset.ext fun C => by
      simp only [Finset.mem_singleton]
      exact ⟨fun hc => d.giants_unique hc hG, fun hc => hc ▸ hG⟩
    rw [d.giant_eq hG]
    have hg : (d.giants r).Nonempty := ⟨G,hG⟩
    simp only [he, Finset.sum_singleton, Finset.mem_compl]
    by_cases hx : x ∈ G <;> by_cases hy : y ∈ G <;> simp [hx,hy]
    ring
  · have he : d.giants r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hg
    simp [he]

lemma giants_nonempty_iff (r : ℝ) : (d.giants r).Nonempty ↔
    ∃ x : P, ∃ C : Finset P, Fintype.card P < 2*C.card ∧ ∀ y ∈ C, d.share r x y := by
  constructor
  · rintro ⟨C,hC⟩
    obtain ⟨hC,hc⟩ := (d.mem_giants r C).mp hC
    obtain ⟨x,rfl⟩ := (d.mem_cells r C).mp hC
    exact ⟨x,d.cell r x,hc,fun y hy => (d.mem_cell r x y).mp hy⟩
  · rintro ⟨x,C,hc,hC⟩
    have hsub : C ⊆ d.cell r x := fun y hy => (d.mem_cell r x y).mpr (hC y hy)
    refine ⟨d.cell r x, (d.mem_giants r _).mpr ⟨d.cell_mem_cells r x, ?_⟩⟩
    have := Finset.card_le_card hsub
    omega

lemma giants_mono {r t : ℝ} (htr : t ≤ r) (hr : (d.giants r).Nonempty) :
    (d.giants t).Nonempty := by
  rw [d.giants_nonempty_iff] at hr ⊢
  obtain ⟨x,C,hc,hC⟩ := hr
  exact ⟨x,C,hc,fun y hy => d.share_mono htr (hC y hy)⟩

lemma isClosed_giants : IsClosed {r : ℝ | (d.giants r).Nonempty} := by
  simp_rw [d.giants_nonempty_iff, Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro x
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h : Fintype.card P < 2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy : x = y
    · simp [share, hxy]
    · simp only [share, hxy, false_or]
      exact isClosed_le continuous_id continuous_const

omit [DecidableEq P] in
lemma radius_nonneg : 0 ≤ d.radius := by unfold radius; positivity

omit [DecidableEq P] in
lemma abs_value_le_radius (x y : P) : |d.value x y| ≤ d.radius := by
  have hx : (∑ y, |d.value x y|) ≤ d.radius :=
    Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun w _ => abs_nonneg (d.value z w)))
      (Finset.mem_univ x)
  exact (Finset.single_le_sum (fun z _ => abs_nonneg (d.value x z)) (Finset.mem_univ y)).trans hx

omit [DecidableEq P] in
lemma cell_of_low {r : ℝ} (hr : r ≤ -d.radius) (x : P) : d.cell r x = Finset.univ := by
  ext y
  simp only [mem_cell, Finset.mem_univ, iff_true]
  exact Or.inr (hr.trans (abs_le.mp (d.abs_value_le_radius x y)).1)

omit [DecidableEq P] in
lemma cell_of_high {r : ℝ} (hr : d.radius < r) (x : P) : d.cell r x = {x} := by
  ext y
  simp only [mem_cell, share, Finset.mem_singleton]
  have hh : ¬r ≤ d.value x y := not_le.mpr ((abs_le.mp (d.abs_value_le_radius x y)).2.trans_lt hr)
  simp [hh, eq_comm]

lemma giants_of_low (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : r ≤ -d.radius) :
    (d.giants r).Nonempty := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x⟩ := ‹Nonempty P›
  refine ⟨Finset.univ, (d.mem_giants r _).mpr ⟨?_, ?_⟩⟩
  · exact (d.mem_cells r _).mpr ⟨x, d.cell_of_low hr x⟩
  · simp only [Finset.card_univ]
    omega

lemma giants_le_radius (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : (d.giants r).Nonempty) :
    r ≤ d.radius := by
  by_contra! h
  obtain ⟨C,hC⟩ := hr
  obtain ⟨hC,hc⟩ := (d.mem_giants r C).mp hC
  obtain ⟨x,rfl⟩ := (d.mem_cells r C).mp hC
  rw [d.cell_of_high h x, Finset.card_singleton] at hc
  omega

lemma giants_cutoff (hn : 2 ≤ Fintype.card P) (r : ℝ) :
    (d.giants r).Nonempty ↔ r ≤ d.M := by
  have hne : Set.Nonempty {t : ℝ | (d.giants t).Nonempty} := ⟨-d.radius,d.giants_of_low hn le_rfl⟩
  have hbd : BddAbove {t : ℝ | (d.giants t).Nonempty} := ⟨d.radius,fun t ht => d.giants_le_radius hn ht⟩
  exact ⟨fun hr => le_csSup hbd hr, fun hr =>
    d.giants_mono hr (d.isClosed_giants.csSup_mem hne hbd)⟩

lemma M_bounds (hn : 2 ≤ Fintype.card P) : -d.radius ≤ d.M ∧ d.M ≤ d.radius := by
  constructor
  · exact (d.giants_cutoff hn _).mp (d.giants_of_low hn le_rfl)
  · exact d.giants_le_radius hn ((d.giants_cutoff hn _).mpr le_rfl)

omit [DecidableEq P] in
lemma measurable_cell (x : P) : Measurable (fun r : ℝ => d.cell r x) := by
  apply measurable_finset_iff.mpr
  intro y
  simp only [mem_cell, share]
  exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const))

lemma measurable_cells : Measurable d.cells := by
  have hm : Measurable (fun r : ℝ => fun x : P => d.cell r x) :=
    measurable_pi_iff.mpr (d.measurable_cell)
  exact (measurable_of_finite (fun f : P → Finset P => Finset.univ.image f)).comp hm

lemma measurable_giants : Measurable d.giants :=
  (measurable_of_finite (fun s : Finset (Finset P) =>
    s.filter (fun C : Finset P => Fintype.card P < 2*C.card))).comp d.measurable_cells

lemma measurable_giant : Measurable d.giant :=
  (measurable_of_finite (fun s : Finset (Finset P) => s.biUnion id)).comp d.measurable_giants

lemma measurable_giantIndicator : Measurable d.giantIndicator :=
  (measurable_of_finite (fun s : Finset (Finset P) => if s.Nonempty then (1 : ℝ) else 0)).comp
    d.measurable_giants

lemma measurable_outsideIndicator (x : P) : Measurable (fun r => d.outsideIndicator r x) := by
  have hm : Measurable (fun r : ℝ => (d.giants r, d.giant r)) :=
    d.measurable_giants.prodMk d.measurable_giant
  exact (measurable_of_finite
    (fun st : Finset (Finset P) × Finset P => if st.1.Nonempty ∧ x ∉ st.2 then (1 : ℝ) else 0)).comp hm

lemma measurable_pairOverlap (x y : P) : Measurable (fun r => d.pairOverlap r x y) := by
  have hm : Measurable (fun r : ℝ => if d.share r x y then (1 : ℝ) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_setOfPred.mpr
    exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const))
  have ht : Measurable (fun r =>
      (if d.share r x y then (1 : ℝ) else 0) - d.giantIndicator r +
        d.outsideIndicator r x + d.outsideIndicator r y) :=
    ((hm.sub d.measurable_giantIndicator).add (d.measurable_outsideIndicator x)).add
      (d.measurable_outsideIndicator y)
  simpa only [pairOverlap_formula] using ht

lemma outsideIndicator_bounds (r : ℝ) (x : P) :
    0 ≤ d.outsideIndicator r x ∧ d.outsideIndicator r x ≤ 1 := by
  unfold outsideIndicator
  split_ifs <;> norm_num

lemma pairOverlap_bounds (r : ℝ) (x y : P) :
    0 ≤ d.pairOverlap r x y ∧ d.pairOverlap r x y ≤ 2 := by
  have lo : 0 ≤ d.pairOverlap r x y := by
    unfold pairOverlap sumCells
    apply Multiset.sum_nonneg
    intro t ht
    obtain ⟨C,hC,rfl⟩ := Multiset.mem_map.mp ht
    split_ifs <;> norm_num
  refine ⟨lo, ?_⟩
  rw [pairOverlap_formula]
  have hx := (d.outsideIndicator_bounds r x).2
  have hy := (d.outsideIndicator_bounds r y).2
  by_cases hg : (d.giants r).Nonempty
  · simp only [giantIndicator, hg, reduceIte]
    split_ifs <;> linarith
  · simp [giantIndicator, outsideIndicator, hg]
    split_ifs <;> norm_num

lemma outsideIndicator_zero_low (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : r ≤ -d.radius)
    (x : P) : d.outsideIndicator r x = 0 := by
  have hg : Finset.univ ∈ d.giants r := (d.mem_giants r _).mpr ⟨
    (d.mem_cells r _).mpr ⟨x,d.cell_of_low hr x⟩, by simp only [Finset.card_univ]; omega⟩
  simp [outsideIndicator, d.giant_eq hg]

lemma outsideIndicator_zero_high (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : d.radius < r)
    (x : P) : d.outsideIndicator r x = 0 := by
  have hg : ¬(d.giants r).Nonempty := fun hg => not_le.mpr hr (d.giants_le_radius hn hg)
  simp [outsideIndicator, hg]

lemma pairOverlap_zero_low (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : r ≤ -d.radius)
    (x y : P) : d.pairOverlap r x y = 0 := by
  have hxy : d.share r x y := Or.inr (hr.trans (abs_le.mp (d.abs_value_le_radius x y)).1)
  simp [pairOverlap_formula, giantIndicator, d.giants_of_low hn hr,
    d.outsideIndicator_zero_low hn hr, hxy]

lemma pairOverlap_zero_high (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : d.radius < r)
    (x y : P) (hxy : x ≠ y) : d.pairOverlap r x y = 0 := by
  have hg : ¬(d.giants r).Nonempty := fun hg => not_le.mpr hr (d.giants_le_radius hn hg)
  have hs : ¬d.share r x y := by
    simp only [share, hxy, false_or]
    exact not_le.mpr ((abs_le.mp (d.abs_value_le_radius x y)).2.trans_lt hr)
  simp [pairOverlap_formula, giantIndicator, hg, hs, d.outsideIndicator_zero_high hn hr]

/- The diagonal is deliberately absent from overlapLength's domain: the
   transformed singleton tails have infinite diagonal overlap. -/

lemma integrable_supported_Icc {f : ℝ → ℝ} {a b C : ℝ}
    (hm : Measurable f) (hb : ∀ r, ‖f r‖ ≤ C)
    (hz : ∀ r ∉ Set.Icc a b, f r = 0) : Integrable f := by
  have hi : IntegrableOn f (Set.Icc a b) :=
    IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall hb)
  have he : (Set.Icc a b).indicator f = f := by
    apply Set.indicator_eq_self.mpr
    intro r hr
    by_contra hn
    exact hr (hz r hn)
  simpa only [he] using hi.integrable_indicator measurableSet_Icc

lemma outsideIndicator_zero_compl (hn : 2 ≤ Fintype.card P) (x : P) :
    ∀ r ∉ Set.Icc (-d.radius) d.radius, d.outsideIndicator r x = 0 := by
  intro r hr
  by_cases hlo : r ≤ -d.radius
  · exact d.outsideIndicator_zero_low hn hlo x
  · exact d.outsideIndicator_zero_high hn
      (lt_of_not_ge (fun hhi => hr ⟨le_of_not_ge hlo, hhi⟩)) x

lemma pairOverlap_zero_compl (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    ∀ r ∉ Set.Icc (-d.radius) d.radius, d.pairOverlap r x y = 0 := by
  intro r hr
  by_cases hlo : r ≤ -d.radius
  · exact d.pairOverlap_zero_low hn hlo x y
  · exact d.pairOverlap_zero_high hn
      (lt_of_not_ge (fun hhi => hr ⟨le_of_not_ge hlo, hhi⟩)) x y hxy

lemma integrable_outsideIndicator (hn : 2 ≤ Fintype.card P) (x : P) :
    Integrable (fun r => d.outsideIndicator r x) := by
  apply integrable_supported_Icc (d.measurable_outsideIndicator x) (C := 1)
  · intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (d.outsideIndicator_bounds r x).1]
    exact (d.outsideIndicator_bounds r x).2
  · exact d.outsideIndicator_zero_compl hn x

lemma integrable_pairOverlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    Integrable (fun r => d.pairOverlap r x y) := by
  apply integrable_supported_Icc (d.measurable_pairOverlap x y) (C := 2)
  · intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (d.pairOverlap_bounds r x y).1]
    exact (d.pairOverlap_bounds r x y).2
  · exact d.pairOverlap_zero_compl hn x y hxy

lemma integral_cutoff {R a : ℝ} (hR : 0 ≤ R) (ha : a ∈ Set.Icc (-R) R) :
    (∫ r : ℝ in Set.Icc (-R) R, if r ≤ a then (1 : ℝ) else 0) = a + R := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  change (∫ r : ℝ in (-R)..R, {r : ℝ | r ≤ a}.indicator (fun _ => (1 : ℝ)) r) = a + R
  rw [intervalIntegral.integral_indicator ha, intervalIntegral.integral_const]
  simp

lemma depth_identity (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    d.value x y = d.M + d.overlapLength x y hxy - d.potential x - d.potential y := by
  let I := Set.Icc (-d.radius) d.radius
  have hoc : IntegrableOn (fun r : ℝ => if r ≤ d.value x y then (1 : ℝ) else 0) I := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun r => by split_ifs <;> norm_num)
  have hgc : IntegrableOn (fun r : ℝ => if r ≤ d.M then (1 : ℝ) else 0) I := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun r => by split_ifs <;> norm_num)
  have hs : IntegrableOn (fun r : ℝ => (if r ≤ d.value x y then (1 : ℝ) else 0) -
      (if r ≤ d.M then (1 : ℝ) else 0)) I := hoc.sub hgc
  have hx := (d.integrable_outsideIndicator hn x).integrableOn (s := I)
  have hy := (d.integrable_outsideIndicator hn y).integrableOn (s := I)
  have ha : IntegrableOn (fun r : ℝ => (if r ≤ d.value x y then (1 : ℝ) else 0) -
      (if r ≤ d.M then (1 : ℝ) else 0) + d.outsideIndicator r x) I := hs.add hx
  have he : (∫ r in I, d.pairOverlap r x y) =
      (∫ r in I, if r ≤ d.value x y then (1 : ℝ) else 0) -
      (∫ r in I, if r ≤ d.M then (1 : ℝ) else 0) +
      (∫ r in I, d.outsideIndicator r x) + (∫ r in I, d.outsideIndicator r y) := by
    calc
      _ = ∫ r in I, ((if r ≤ d.value x y then (1 : ℝ) else 0) -
          (if r ≤ d.M then 1 else 0) + d.outsideIndicator r x + d.outsideIndicator r y) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro r _
        simp only [pairOverlap_formula, share, hxy, false_or, giantIndicator,
          d.giants_cutoff hn]
      _ = _ := by rw [integral_add ha hy, integral_add hs hx, integral_sub hoc hgc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (d.pairOverlap_zero_compl hn x y hxy)] at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (d.outsideIndicator_zero_compl hn x),
    setIntegral_eq_integral_of_forall_compl_eq_zero (d.outsideIndicator_zero_compl hn y)] at he
  change d.overlapLength x y hxy = _ at he
  dsimp only [I] at he
  rw [integral_cutoff d.radius_nonneg (abs_le.mp (d.abs_value_le_radius x y)),
    integral_cutoff d.radius_nonneg (d.M_bounds hn)] at he
  change d.overlapLength x y hxy = _ - _ + d.potential x + d.potential y at he
  linarith

lemma potential_nonneg (x : P) : 0 ≤ d.potential x :=
  integral_nonneg (fun r => (d.outsideIndicator_bounds r x).1)

lemma overlapLength_nonneg (x y : P) (hxy : x ≠ y) : 0 ≤ d.overlapLength x y hxy :=
  integral_nonneg (fun r => (d.pairOverlap_bounds r x y).1)

lemma integral_bound_supported {f : ℝ → ℝ} {R C : ℝ} (hR : 0 ≤ R)
    (hi : Integrable f) (hb : ∀ r, f r ≤ C)
    (hz : ∀ r ∉ Set.Icc (-R) R, f r = 0) : (∫ r, f r) ≤ 2*R*C := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hh := integral_mono (hi.integrableOn (s := Set.Icc (-R) R))
    (integrableOn_const (s := Set.Icc (-R) R) (μ := volume)
      (C := C) (measure_Icc_lt_top.ne)) (fun r => hb r)
  rw [setIntegral_const] at hh
  simp only [Measure.real, Real.volume_Icc, sub_neg_eq_add,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ R+R), smul_eq_mul] at hh
  nlinarith

lemma potential_le (hn : 2 ≤ Fintype.card P) (x : P) : d.potential x ≤ 2*d.radius := by
  have hh := integral_bound_supported d.radius_nonneg (d.integrable_outsideIndicator hn x)
    (fun r => (d.outsideIndicator_bounds r x).2) (d.outsideIndicator_zero_compl hn x)
  change d.potential x ≤ _ at hh
  simpa only [mul_one] using hh

lemma overlapLength_le (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    d.overlapLength x y hxy ≤ 4*d.radius := by
  have hh := integral_bound_supported d.radius_nonneg (d.integrable_pairOverlap hn x y hxy)
    (fun r => (d.pairOverlap_bounds r x y).2) (d.pairOverlap_zero_compl hn x y hxy)
  change d.overlapLength x y hxy ≤ _ at hh
  linarith

lemma zero_values (hn : 2 ≤ Fintype.card P) (hzero : ∀ x y, d.value x y = 0) :
    d.M = 0 ∧ (∀ x, d.potential x = 0) ∧
      (∀ x y (hxy : x ≠ y), d.overlapLength x y hxy = 0) := by
  have hr : d.radius = 0 := by simp [radius, hzero]
  refine ⟨?_, ?_, ?_⟩
  · have := d.M_bounds hn
    rw [hr] at this
    linarith [this.1, this.2]
  · intro x
    have := d.potential_le hn x
    rw [hr] at this
    linarith [d.potential_nonneg x]
  · intro x y hxy
    have := d.overlapLength_le hn x y hxy
    rw [hr] at this
    linarith [d.overlapLength_nonneg x y hxy]

/- Joint measurability and averaging over a family of realized hierarchies. -/
section Param
variable {Ω : Type u3} [MeasurableSpace Ω] (D : Ω → Depth P)
  (hD : ∀ x y, Measurable (fun ω => (D ω).value x y))
  (R : Ω → ℝ) (hR : Measurable R)
include hD hR

omit [DecidableEq P] in
lemma measurable_cell_param (x : P) : Measurable (fun ω => (D ω).cell (R ω) x) := by
  apply measurable_finset_iff.mpr
  intro y
  simp only [mem_cell, share]
  exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le hR (hD x y)))

lemma measurable_cells_param : Measurable (fun ω => (D ω).cells (R ω)) := by
  have hm : Measurable (fun ω => fun x : P => (D ω).cell (R ω) x) :=
    measurable_pi_iff.mpr (measurable_cell_param D hD R hR)
  exact (measurable_of_finite (fun f : P → Finset P => Finset.univ.image f)).comp hm

lemma measurable_giants_param : Measurable (fun ω => (D ω).giants (R ω)) :=
  (measurable_of_finite (fun s : Finset (Finset P) =>
    s.filter (fun C : Finset P => Fintype.card P < 2*C.card))).comp
      (measurable_cells_param D hD R hR)

lemma measurable_giant_param : Measurable (fun ω => (D ω).giant (R ω)) :=
  (measurable_of_finite (fun s : Finset (Finset P) => s.biUnion id)).comp
    (measurable_giants_param D hD R hR)

lemma measurable_giantIndicator_param : Measurable (fun ω => (D ω).giantIndicator (R ω)) :=
  (measurable_of_finite (fun s : Finset (Finset P) => if s.Nonempty then (1 : ℝ) else 0)).comp
    (measurable_giants_param D hD R hR)

lemma measurable_outsideIndicator_param (x : P) : Measurable (fun ω => (D ω).outsideIndicator (R ω) x) := by
  have hm := (measurable_giants_param D hD R hR).prodMk (measurable_giant_param D hD R hR)
  exact (measurable_of_finite
    (fun st : Finset (Finset P) × Finset P => if st.1.Nonempty ∧ x ∉ st.2 then (1 : ℝ) else 0)).comp hm

lemma measurable_pairOverlap_param (x y : P) : Measurable (fun ω => (D ω).pairOverlap (R ω) x y) := by
  have hm : Measurable (fun ω => if (D ω).share (R ω) x y then (1:ℝ) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_setOfPred.mpr
    exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le hR (hD x y)))
  have hh : Measurable (fun ω => (if (D ω).share (R ω) x y then (1:ℝ) else 0) -
      (D ω).giantIndicator (R ω) + (D ω).outsideIndicator (R ω) x + (D ω).outsideIndicator (R ω) y) :=
    ((hm.sub (measurable_giantIndicator_param D hD R hR)).add
    (measurable_outsideIndicator_param D hD R hR x)).add
    (measurable_outsideIndicator_param D hD R hR y)
  simpa only [pairOverlap_formula, Pi.add_apply, Pi.sub_apply] using hh

omit hR
lemma measurable_potential_param (x : P) : Measurable (fun ω => (D ω).potential x) := by
  have hm : Measurable (fun p : Ω × ℝ => (D p.1).outsideIndicator p.2 x) :=
    measurable_outsideIndicator_param (P := P) (Ω := Ω × ℝ) (fun p : Ω × ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd x
  simpa only [potential] using hm.stronglyMeasurable.integral_prod_right.measurable

lemma measurable_overlapLength_param (x y : P) (hxy : x ≠ y) :
    Measurable (fun ω => (D ω).overlapLength x y hxy) := by
  have hm : Measurable (fun p : Ω × ℝ => (D p.1).pairOverlap p.2 x y) :=
    measurable_pairOverlap_param (P := P) (Ω := Ω × ℝ) (fun p : Ω × ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd x y
  simpa only [overlapLength] using hm.stronglyMeasurable.integral_prod_right.measurable

lemma measurable_M_param (hn : 2 ≤ Fintype.card P) : Measurable (fun ω => (D ω).M) := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ : Finset P).card by simpa using (show 1 < Fintype.card P by omega))
  have hh := (((hD x y).sub (measurable_overlapLength_param D hD x y hxy)).add
    (measurable_potential_param D hD x)).add (measurable_potential_param D hD y)
  have he : (fun ω => (D ω).value x y - (D ω).overlapLength x y hxy +
      (D ω).potential x + (D ω).potential y) = (fun ω => (D ω).M) := by
    funext ω
    have := (D ω).depth_identity hn x y hxy
    linarith
  change Measurable (fun ω => (D ω).value x y - (D ω).overlapLength x y hxy +
      (D ω).potential x + (D ω).potential y) at hh
  rwa [he] at hh

variable {μ : Measure Ω} (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
include hi

omit [DecidableEq P] in
omit hD in
lemma integrable_radius_param : Integrable (fun ω => (D ω).radius) μ := by
  unfold radius
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => (hi x y).abs))

lemma integrable_potential_param (hn : 2 ≤ Fintype.card P) (x : P) :
    Integrable (fun ω => (D ω).potential x) μ := by
  apply Integrable.mono' ((integrable_radius_param D hi).const_mul 2)
    (measurable_potential_param D hD x).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg ((D ω).potential_nonneg x)]
  exact (D ω).potential_le hn x

lemma integrable_overlapLength_param (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    Integrable (fun ω => (D ω).overlapLength x y hxy) μ := by
  apply Integrable.mono' ((integrable_radius_param D hi).const_mul 4)
    (measurable_overlapLength_param D hD x y hxy).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg ((D ω).overlapLength_nonneg x y hxy)]
  exact (D ω).overlapLength_le hn x y hxy

lemma integrable_M_param (hn : 2 ≤ Fintype.card P) : Integrable (fun ω => (D ω).M) μ := by
  apply Integrable.mono' (integrable_radius_param D hi) (measurable_M_param D hD hn).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ((D ω).M_bounds hn)

lemma integral_depth_identity (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∫ ω, (D ω).value x y ∂μ) =
      (∫ ω, (D ω).M ∂μ) + (∫ ω, (D ω).overlapLength x y hxy ∂μ) -
      (∫ ω, (D ω).potential x ∂μ) - (∫ ω, (D ω).potential y ∂μ) := by
  have hiM := integrable_M_param D hD hi hn
  have hiL := integrable_overlapLength_param D hD hi hn x y hxy
  have hix := integrable_potential_param D hD hi hn x
  have hiy := integrable_potential_param D hD hi hn y
  calc
    _ = ∫ ω, (D ω).M + (D ω).overlapLength x y hxy - (D ω).potential x - (D ω).potential y ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => (D ω).depth_identity hn x y hxy)
    _ = _ := by
      have h₁ : Integrable (fun ω => (D ω).M + (D ω).overlapLength x y hxy) μ := hiM.add hiL
      have h₂ : Integrable (fun ω => (D ω).M + (D ω).overlapLength x y hxy - (D ω).potential x) μ := h₁.sub hix
      rw [integral_sub h₂ hiy, integral_sub h₁ hix, integral_add hiM hiL]
end Param

end Depth
end WeakPinned.Hierarchy

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.RandomGrids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology

/- Square-grid construction and the finite-shift sharing law. -/

noncomputable section
open MeasureTheory
open scoped Topology ENNReal
namespace WeakPinned.Grid

lemma bin_period {l : ℝ} (hl : 0 < l) (s x : ℝ) :
    bin l (s+l) x = bin l s x - 1 := by
  unfold bin
  rw [show (x-(s+l))/l = (x-s)/l - 1 by field_simp; ring]
  exact Int.floor_sub_one _

lemma shares_period {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    Function.Periodic (fun s => shares l s x y) l := by
  intro s
  simp [shares, bin_period hl]

lemma shares_symm (l s x y : ℝ) : shares l s x y = shares l s y x := by
  simp only [shares, eq_comm]

lemma measurable_shares (l x y : ℝ) : Measurable (fun s => shares l s x y) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun
    (((measurable_const.sub measurable_id).div_const l).floor)
    (((measurable_const.sub measurable_id).div_const l).floor)

lemma bin_small_shift {l x s : ℝ} (hl : 0 < l) (hs : s ∈ Set.Ioc x (x+l)) :
    bin l s x = -1 := by
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hl).mpr
    norm_num
    linarith [hs.2]
  · apply (div_lt_iff₀ hl).mpr
    norm_num
    linarith [hs.1]

lemma shares_small_shift {l x y s : ℝ} (hl : 0 < l) (hxy : x ≤ y)
    (hs : s ∈ Set.Ioc x (x+l)) : shares l s x y = if y < s then 1 else 0 := by
  have he : bin l s y = -1 ↔ y < s := by
    simp only [bin, Int.floor_eq_iff]
    constructor
    · intro h
      have := (div_lt_iff₀ hl).mp h.2
      norm_num at this
      linarith
    · intro h
      constructor
      · apply (le_div_iff₀ hl).mpr
        norm_num
        linarith [hs.2]
      · apply (div_lt_iff₀ hl).mpr
        norm_num
        linarith
  simp only [shares, bin_small_shift hl hs, eq_comm (a := (-1 : ℤ))]
  simp only [he]

lemma shares_integral {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    (∫ s : ℝ in Set.Ioc 0 l, shares l s x y) = max 0 (l-|x-y|) := by
  wlog hxy : x ≤ y
  · simpa only [shares_symm l _ x y, abs_sub_comm x y] using this hl y x (le_of_not_ge hxy)
  have hp := (shares_period hl x y).intervalIntegral_add_eq 0 x
  simp only [zero_add] at hp
  rw [intervalIntegral.integral_of_le hl.le,
    intervalIntegral.integral_of_le (by linarith : x ≤ x+l)] at hp
  rw [hp]
  have he : (∫ s : ℝ in Set.Ioc x (x+l), shares l s x y) =
      ∫ s : ℝ in Set.Ioc x (x+l), if y < s then (1 : ℝ) else 0 := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact shares_small_shift hl hxy hs
  rw [he]
  change (∫ s : ℝ in Set.Ioc x (x+l), (Set.Ioi y).indicator (fun _ => (1 : ℝ)) s) = _
  rw [setIntegral_indicator measurableSet_Ioi]
  rw [show Set.Ioc x (x+l) ∩ Set.Ioi y = Set.Ioc y (x+l) by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]; constructor
    · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₃,h₂⟩
    · intro h; exact ⟨⟨hxy.trans_lt h.1,h.2⟩,h.1⟩]
  rw [setIntegral_const]
  simp only [Measure.real, Real.volume_Ioc, smul_eq_mul, mul_one, ENNReal.toReal_ofReal']
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  rw [max_comm]
  congr 1
  ring

lemma shares_integrableOn (l x y a b : ℝ) :
    IntegrableOn (fun s => shares l s x y) (Set.Ioc a b) := by
  apply IntegrableOn.of_bound measure_Ioc_lt_top (measurable_shares l x y).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun s => by unfold shares; split_ifs <;> norm_num)

lemma shares_gap {l : ℝ} (hl : 0 < l) {s x y : ℝ}
    (h : bin l s x = bin l s y) : |x-y| < l := by
  have hx := Int.floor_le ((x-s)/l)
  have hy := Int.lt_floor_add_one ((y-s)/l)
  have hx' := Int.floor_le ((y-s)/l)
  have hy' := Int.lt_floor_add_one ((x-s)/l)
  change (bin l s x : ℝ) ≤ (x-s)/l at hx
  change (y-s)/l < (bin l s y : ℝ) + 1 at hy
  change (bin l s y : ℝ) ≤ (y-s)/l at hx'
  change (x-s)/l < (bin l s x : ℝ) + 1 at hy'
  rw [h] at hx hy'
  rw [abs_lt]
  constructor
  · have : (y-s)/l < (x-s)/l+1 := by linarith
    have hh := (div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith
  · have : (x-s)/l < (y-s)/l+1 := by linarith
    have hh := (div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith

lemma bin_double {l : ℝ} (hl : 0 < l) (s x : ℝ) (b : ℤ) :
    bin (2*l) (s+b*l) x = (bin l s x-b)/2 := by
  unfold bin
  rw [show (x-(s+b*l))/(2*l) = ((x-s)/l-b)/2 by field_simp; ring]
  have hh := Int.floor_div_natCast (((x-s)/l)-(b:ℝ)) 2
  norm_num only [Nat.cast_ofNat, Int.floor_sub_intCast] at hh
  exact hh

lemma nested_bins {l : ℝ} (hl : 0 < l) (s x y : ℝ) (b : ℤ)
    (h : bin l s x = bin l s y) : bin (2*l) (s+b*l) x = bin (2*l) (s+b*l) y := by
  rw [bin_double hl, bin_double hl, h]

lemma uniformInterval_probability {l : ℝ} (hl : 0 < l) :
    IsProbabilityMeasure (uniformInterval l) := by
  constructor
  simp only [uniformInterval, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hl)) ENNReal.ofReal_ne_top

instance uniformInterval_finite (l : ℝ) : IsFiniteMeasure (uniformInterval l) := by
  by_cases hl : 0 < l
  · let := uniformInterval_probability hl
    infer_instance
  · have hz : uniformInterval l = 0 := by
      simp [uniformInterval, Set.Ioc_eq_empty_of_le (not_lt.mp hl)]
    rw [hz]
    infer_instance

lemma translate_restrict_Ioc (l : ℝ) :
    (volume.restrict (Set.Ioc 0 l)).map (fun x => x+l) =
      volume.restrict (Set.Ioc l (l+l)) := by
  have hh := (measurePreserving_add_right volume l).restrict_preimage
    (measurableSet_Ioc (a := l) (b := l+l))
  have he : (fun x : ℝ => x+l) ⁻¹' Set.Ioc l (l+l) = Set.Ioc 0 l := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he] at hh
  exact hh.map_eq

lemma binaryStep_eq (l : ℝ) :
    binaryStep l = (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac l := by
  simp only [binaryStep, ProbabilityTheory.bernoulliMeasure_def]
  rw [← Measure.coe_nnreal_smul, ← Measure.coe_nnreal_smul]
  congr 2
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ((1:ℝ)/2) = _
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (1-(1:ℝ)/2) = _
    norm_num only [show (1-(1:ℝ)/2) = 1/2 by norm_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num

lemma uniform_double {l : ℝ} (hl : 0 < l) :
    (uniformInterval l).conv (binaryStep l) = uniformInterval (2*l) := by
  rw [binaryStep_eq, Measure.conv_add, Measure.conv_smul_right,
    Measure.conv_smul_right, Measure.conv_dirac_zero, Measure.conv_dirac]
  rw [uniformInterval, Measure.map_smul, translate_restrict_Ioc]
  have hu : Set.Ioc 0 l ∪ Set.Ioc l (l+l) = Set.Ioc 0 (2*l) := by
    rw [Set.Ioc_union_Ioc_eq_Ioc hl.le (by linarith)]
    congr 1; linarith
  have hd : Disjoint (Set.Ioc 0 l) (Set.Ioc l (l+l)) :=
    Set.disjoint_left.mpr (by intro x h₁ h₂; exact (not_lt_of_ge h₁.2) h₂.1)
  rw [smul_smul, smul_smul, ← smul_add, ← Measure.restrict_union hd measurableSet_Ioc, hu]
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num [ENNReal.mul_inv]

instance incrementLaw_probability (n : ℕ) : IsProbabilityMeasure (incrementLaw n) := by
  cases n with
  | zero => exact uniformInterval_probability zero_lt_one
  | succ n => exact binaryStep_probability _

instance axisLaw_probability : IsProbabilityMeasure axisLaw := by
  unfold axisLaw
  infer_instance

lemma measurable_shift (n : ℕ) : Measurable (shift n) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

lemma shift_zero (ω : ℕ → ℝ) : shift 0 ω = ω 0 := by simp [shift]
lemma shift_succ (n : ℕ) (ω : ℕ → ℝ) :
    shift (n+1) ω = shift n ω + ω (n+1) := by simp [shift, Finset.sum_range_succ]

lemma map_shift (n : ℕ) : axisLaw.map (shift n) = uniformInterval (2^n) := by
  induction n with
  | zero =>
      simp only [pow_zero]
      rw [show shift 0 = (fun ω => ω 0) by funext ω; exact shift_zero ω]
      exact Measure.infinitePi_map_eval incrementLaw 0
  | succ n ih =>
      have hind := ProbabilityTheory.iIndepFun_infinitePi
        (P := incrementLaw) (X := fun _ => id) (fun _ => measurable_id)
      have hi := hind.indepFun_finsetSum_of_notMem
        (fun i => measurable_pi_apply i) (s := Finset.range (n+1)) (i := n+1) (by simp)
      have he : (∑ j ∈ Finset.range (n+1), (fun ω : ℕ → ℝ => id (ω j))) = shift n := by
        funext ω
        simp [shift]
      rw [he] at hi
      have hm := hi.map_add_eq_map_conv_map₀ (measurable_shift n).aemeasurable
        (measurable_pi_apply (n+1)).aemeasurable
      change axisLaw.map (fun ω => shift n ω + ω (n+1)) = _ at hm
      simp only [← shift_succ] at hm
      change axisLaw.map (shift (n+1)) = (axisLaw.map (shift n)).conv ((Measure.infinitePi incrementLaw).map (fun f => f (n+1))) at hm
      rw [ih, Measure.infinitePi_map_eval incrementLaw (n+1)] at hm
      rw [incrementLaw, uniform_double (by positivity)] at hm
      simpa only [pow_succ, mul_comm (2^n) (2:ℝ)] using hm

lemma integral_uniform_shares {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    (∫ s, shares l s x y ∂uniformInterval l) = max 0 (1-|x-y|/l) := by
  rw [uniformInterval, integral_smul_measure, shares_integral hl]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hl.le, smul_eq_mul]
  rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hl.le), mul_zero]
  congr 1
  field_simp

lemma integral_shift_shares (n : ℕ) (x y : ℝ) :
    (∫ ω, shares (2^n) (shift n ω) x y ∂axisLaw) =
      max 0 (1-|x-y|/(2^n)) := by
  rw [← integral_map (measurable_shift n).aemeasurable
    (measurable_shares (2^n) x y).aestronglyMeasurable, map_shift]
  exact integral_uniform_shares (by positivity) x y

lemma integral_shares_nat_periods {l : ℝ} (hl : 0 < l) (k : ℕ) (x y : ℝ) :
    (∫ s in Set.Ioc 0 (k*l), shares l s x y) = (k:ℝ)*max 0 (l-|x-y|) := by
  have hh := (shares_period hl x y).intervalIntegral_add_zsmul_eq (k:ℤ) 0
    (fun a b => ⟨shares_integrableOn l x y a b, shares_integrableOn l x y b a⟩)
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ k*l),
    intervalIntegral.integral_of_le hl.le, shares_integral hl] at hh
  exact hh

/-- The fine-scale shift is the original unit shift. Its sharing law is still
    the correct uniform-modulo-side law, not a fresh independent grid. -/
lemma integral_fine_shares (n : ℕ) (x y : ℝ) :
    (∫ ω, shares ((2:ℝ)^(- (n:ℤ))) (shift 0 ω) x y ∂axisLaw) =
      max 0 (1-|x-y|/((2:ℝ)^(- (n:ℤ)))) := by
  rw [← integral_map (measurable_shift 0).aemeasurable
    (measurable_shares _ x y).aestronglyMeasurable, map_shift]
  simp only [pow_zero, uniformInterval, ENNReal.ofReal_one, inv_one, one_smul]
  have hl : 0 < (2:ℝ)^(-(n:ℤ)) := by positivity
  have he : ((2^n:ℕ):ℝ)*(2:ℝ)^(-(n:ℤ)) = 1 := by
    simp [zpow_neg, zpow_natCast]
  have hh := integral_shares_nat_periods hl (2^n) x y
  rw [he] at hh
  rw [hh, mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ ((2^n:ℕ):ℝ)), mul_zero]
  congr 1
  simp only [Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast, div_inv_eq_mul]
  field_simp

lemma binaryStep_ae (l : ℝ) : ∀ᵐ x ∂binaryStep l, x = 0 ∨ x = l := by
  rw [binaryStep_eq]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inl rfl)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inr rfl)

lemma axis_increment_ae (n : ℕ) :
    ∀ᵐ ω ∂axisLaw, ω (n+1) = 0 ∨ ω (n+1) = (2:ℝ)^n := by
  have hh : ∀ᵐ x ∂incrementLaw (n+1), x = 0 ∨ x = (2:ℝ)^n := binaryStep_ae _
  apply ae_of_ae_map (μ := axisLaw) (f := fun ω : ℕ → ℝ => ω (n+1))
    (p := fun x : ℝ => x = 0 ∨ x = (2:ℝ)^n) (measurable_pi_apply (n+1)).aemeasurable
  simpa only [axisLaw, Measure.infinitePi_map_eval] using hh

lemma bins_nested_ae (n : ℕ) (x y : ℝ) :
    ∀ᵐ ω ∂axisLaw, bin (2^n) (shift n ω) x = bin (2^n) (shift n ω) y →
      bin (2^(n+1)) (shift (n+1) ω) x = bin (2^(n+1)) (shift (n+1) ω) y := by
  filter_upwards [axis_increment_ae n] with ω hω
  intro h
  rcases hω with hω | hω
  · simpa only [shift_succ, hω, pow_succ, mul_comm (2^n) (2:ℝ),
      Int.cast_zero, zero_mul, add_zero] using nested_bins (by positivity) (shift n ω) x y 0 h
  · simpa only [shift_succ, hω, pow_succ, mul_comm (2^n) (2:ℝ),
      Int.cast_one, one_mul] using nested_bins (by positivity) (shift n ω) x y 1 h

instance squareLaw_probability : IsProbabilityMeasure squareLaw := by
  unfold squareLaw
  infer_instance

lemma measurableSet_shareAt (m : ℤ) (x y : ℝ × ℝ) :
    MeasurableSet {ω | shareAt m ω x y} := by
  unfold shareAt bin shiftZ
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((measurable_shift _).comp measurable_fst)).div_const _).floor)
      (((measurable_const.sub ((measurable_shift _).comp measurable_fst)).div_const _).floor)
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((measurable_shift _).comp measurable_snd)).div_const _).floor)
      (((measurable_const.sub ((measurable_shift _).comp measurable_snd)).div_const _).floor)

lemma integral_shiftZ_shares (m : ℤ) (x y : ℝ) :
    (∫ ω, shares ((2:ℝ)^m) (shiftZ m ω) x y ∂axisLaw) =
      max 0 (1-|x-y|/((2:ℝ)^m)) := by
  cases m with
  | ofNat n =>
      change (∫ ω, shares ((2:ℝ)^(n:ℤ)) (shift n ω) x y ∂axisLaw) =
        max 0 (1-|x-y|/((2:ℝ)^(n:ℤ)))
      simpa only [zpow_natCast] using integral_shift_shares n x y
  | negSucc n =>
      simpa [shiftZ, Int.negSucc_eq, Int.toNat_of_nonpos] using
        integral_fine_shares (n+1) x y

lemma sharing_probability (m : ℤ) (x y : ℝ × ℝ) :
    squareLaw.real {ω | shareAt m ω x y} =
      max 0 (1-|x.1-y.1|/((2:ℝ)^m)) * max 0 (1-|x.2-y.2|/((2:ℝ)^m)) := by
  rw [← integral_indicator_one (measurableSet_shareAt m x y)]
  have he : (fun ω : GridSample => Set.indicator {ω | shareAt m ω x y} 1 ω) =
      (fun ω => shares ((2:ℝ)^m) (shiftZ m ω.1) x.1 y.1 *
        shares ((2:ℝ)^m) (shiftZ m ω.2) x.2 y.2) := by
    funext ω
    simp only [Set.indicator, Set.mem_ofPred_eq, shareAt, shares, Pi.one_apply]
    by_cases h₁ : bin ((2:ℝ)^m) (shiftZ m ω.1) x.1 = bin ((2:ℝ)^m) (shiftZ m ω.1) y.1 <;>
      by_cases h₂ : bin ((2:ℝ)^m) (shiftZ m ω.2) x.2 = bin ((2:ℝ)^m) (shiftZ m ω.2) y.2 <;>
      simp [h₁,h₂]
  rw [he, squareLaw, integral_prod_mul (fun ω : ℕ → ℝ => shares ((2:ℝ)^m) (shiftZ m ω) x.1 y.1)
    (fun ω : ℕ → ℝ => shares ((2:ℝ)^m) (shiftZ m ω) x.2 y.2),
    integral_shiftZ_shares, integral_shiftZ_shares]

lemma max_sharing_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - max 0 (1-a) * max 0 (1-b) ≤ a+b := by
  by_cases ha' : a ≤ 1
  · by_cases hb' : b ≤ 1
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      nlinarith [mul_nonneg ha hb]
    · rw [max_eq_left (show 1-b ≤ 0 by linarith)]
      nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith

lemma separation_probability_le (m : ℤ) (x y : ℝ × ℝ) :
    squareLaw.real {ω | ¬ shareAt m ω x y} ≤
      (|x.1-y.1|+|x.2-y.2|)/((2:ℝ)^m) := by
  change squareLaw.real {ω | shareAt m ω x y}ᶜ ≤ _
  rw [measureReal_compl (measurableSet_shareAt m x y), probReal_univ,
    sharing_probability, add_div]
  exact max_sharing_bound (by positivity) (by positivity)

lemma share_eventually_exists (x y : ℝ × ℝ) :
    ∀ᵐ ω ∂squareLaw, ∃ n : ℕ, shareAt n ω x y := by
  rw [ae_iff]
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ (measureReal_nonneg)
  have hb (n : ℕ) : squareLaw.real {ω | ¬ ∃ n : ℕ, shareAt n ω x y} ≤
      (|x.1-y.1|+|x.2-y.2|)/((2:ℝ)^n) := by
    refine (measureReal_mono (s₂ := {ω | ¬ shareAt (n:ℤ) ω x y})
      (by intro ω h hn; exact h ⟨n, hn⟩)).trans ?_
    simpa only [zpow_natCast] using separation_probability_le (n:ℤ) x y
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))) hb

lemma axis_nestedZ_ae (m : ℤ) (x y : ℝ) :
    ∀ᵐ ω ∂axisLaw, bin ((2:ℝ)^m) (shiftZ m ω) x = bin ((2:ℝ)^m) (shiftZ m ω) y →
      bin ((2:ℝ)^(m+1)) (shiftZ (m+1) ω) x = bin ((2:ℝ)^(m+1)) (shiftZ (m+1) ω) y := by
  by_cases hm : 0 ≤ m
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [show (n:ℤ)+1 = ((n+1:ℕ):ℤ) by omega]
    simpa only [shiftZ, Int.toNat_natCast, zpow_natCast] using bins_nested_ae n x y
  · have hm' : m+1 ≤ 0 := by omega
    filter_upwards with ω
    intro h
    simp only [shiftZ, Int.toNat_of_nonpos (by omega : m ≤ 0)] at h
    have hh := nested_bins (by positivity : 0 < (2:ℝ)^m) (shift 0 ω) x y 0
    simpa only [shiftZ, Int.toNat_of_nonpos (by omega : m ≤ 0),
      Int.toNat_of_nonpos hm', zpow_add₀ (by norm_num : (2:ℝ)≠0), zpow_one,
      mul_comm ((2:ℝ)^m) (2:ℝ), Int.cast_zero, zero_mul, add_zero] using hh h

lemma shareAt_nested_ae (m : ℤ) (x y : ℝ × ℝ) :
    ∀ᵐ ω ∂squareLaw, shareAt m ω x y → shareAt (m+1) ω x y := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (axis_nestedZ_ae m x.1 y.1),
    Measure.quasiMeasurePreserving_snd.ae (axis_nestedZ_ae m x.2 y.2)] with ω hx hy
  exact fun h => ⟨hx h.1, hy h.2⟩

lemma shareAt_trans (m : ℤ) (ω : GridSample) (x y z : ℝ × ℝ)
    (hxy : shareAt m ω x y) (hyz : shareAt m ω y z) : shareAt m ω x z :=
  ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

lemma shareAt_bddBelow (ω : GridSample) {x y : ℝ × ℝ} (hxy : x ≠ y) :
    BddBelow {m : ℤ | shareAt m ω x y} := by
  have bound {a b : ℝ} (h : a ≠ b) (f : ℤ → ℝ) :
      BddBelow {m : ℤ | bin ((2:ℝ)^m) (f m) a = bin ((2:ℝ)^m) (f m) b} := by
    obtain ⟨k,hk⟩ := exists_mem_Ico_zpow (abs_pos.mpr (sub_ne_zero.mpr h)) (by norm_num : (1:ℝ)<2)
    refine ⟨k, fun m hm => ?_⟩
    have hh := shares_gap (by positivity : 0 < (2:ℝ)^m) hm
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp (hk.1.trans hh.le)
  by_cases h₁ : x.1 = y.1
  · have h₂ : x.2 ≠ y.2 := fun h₂ => hxy (Prod.ext h₁ h₂)
    exact (bound h₂ (fun m => shiftZ m ω.2)).mono (fun _ h => h.2)
  · exact (bound h₁ (fun m => shiftZ m ω.1)).mono (fun _ h => h.1)

lemma minScale_mem {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (he : ∃ m, shareAt m ω x y) : shareAt (minScale ω x y) ω x y :=
  Int.csInf_mem he (shareAt_bddBelow ω hxy)

lemma minScale_le {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    {m : ℤ} (hm : shareAt m ω x y) : minScale ω x y ≤ m :=
  csInf_le (shareAt_bddBelow ω hxy) hm

lemma shareAt_iff_minScale_le {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (he : ∃ m, shareAt m ω x y)
    (hn : ∀ m, shareAt m ω x y → shareAt (m+1) ω x y) (m : ℤ) :
    shareAt m ω x y ↔ minScale ω x y ≤ m := by
  constructor
  · exact minScale_le hxy
  · intro hm
    have hmono : Monotone (fun k => shareAt k ω x y) := monotone_int_of_le_succ hn
    exact hmono hm (minScale_mem hxy he)

lemma minScale_eq_iff {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y) (m : ℤ) :
    minScale ω x y = m ↔
      (shareAt m ω x y ∧ ∀ k : ℤ, k < m → ¬ shareAt k ω x y) ∨
      (m = 0 ∧ ¬ ∃ k : ℤ, shareAt k ω x y) := by
  by_cases he : ∃ k, shareAt k ω x y
  · have hs := minScale_mem hxy he
    constructor
    · intro h
      left
      rw [h] at hs
      refine ⟨hs, fun k hk hks => ?_⟩
      have hh := minScale_le hxy hks
      omega
    · rintro (⟨hm,hmin⟩ | ⟨_,hn⟩)
      · apply le_antisymm (minScale_le hxy hm)
        by_contra h
        exact hmin _ (by omega) hs
      · exact False.elim (hn he)
  · have hz : minScale ω x y = 0 := by
      unfold minScale
      rw [show {m | shareAt m ω x y} = ∅ by ext m; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]; exact iff_false_intro (fun h => he ⟨m,h⟩)]
      exact Int.csInf_empty
    simp only [hz]
    constructor
    · intro hm
      exact Or.inr ⟨hm.symm,he⟩
    · rintro (⟨hm,_⟩ | ⟨rfl,_⟩)
      · exact False.elim (he ⟨m,hm⟩)
      · rfl

lemma measurable_minScale {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measurable (fun ω => minScale ω x y) := by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {ω | minScale ω x y = m}
  have he : {ω : GridSample | minScale ω x y = m} =
      ({ω | shareAt m ω x y} ∩ {ω | ∀ k < m, ¬shareAt k ω x y}) ∪
      ({ω | m = 0} ∩ {ω | ¬∃ k, shareAt k ω x y}) := by
    ext ω
    exact minScale_eq_iff hxy m
  rw [he]
  apply MeasurableSet.union
  · apply (measurableSet_shareAt m x y).inter
    have he : {ω : GridSample | ∀ k < m, ¬shareAt k ω x y} =
        ⋂ k : ℤ, ⋂ (_ : k < m), {ω : GridSample | shareAt k ω x y}ᶜ := by
      ext ω
      simp
    rw [he]
    exact MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun (_ : k < m) => (measurableSet_shareAt k x y).compl
  · apply (MeasurableSet.const (m = 0)).inter
    have he : {ω : GridSample | ¬∃ k, shareAt k ω x y} =
        (⋃ k : ℤ, {ω : GridSample | shareAt k ω x y})ᶜ := by
      ext ω
      simp
    rw [he]
    exact (MeasurableSet.iUnion fun k => measurableSet_shareAt k x y).compl

lemma measurable_gridDepth {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measurable (fun ω => gridDepth ω x y) := by
  exact (((measurable_of_countable (fun n : ℤ => (n:ℝ))).comp (measurable_minScale hxy)).neg).mul_const _

lemma gridDepth_ultra_ae {x y z : ℝ × ℝ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∀ᵐ ω ∂squareLaw, min (gridDepth ω x y) (gridDepth ω y z) ≤ gridDepth ω x z := by
  have hn : ∀ᵐ ω ∂squareLaw, ∀ m : ℤ,
      (shareAt m ω x y → shareAt (m+1) ω x y) ∧
      (shareAt m ω y z → shareAt (m+1) ω y z) := by
    rw [ae_all_iff]
    intro m
    filter_upwards [shareAt_nested_ae m x y, shareAt_nested_ae m y z] with ω h₁ h₂ using ⟨h₁,h₂⟩
  filter_upwards [share_eventually_exists x y, share_eventually_exists y z, hn] with ω h₁ h₂ hn
  have e₁ : ∃ m : ℤ, shareAt m ω x y := by obtain ⟨n,hn⟩ := h₁; exact ⟨n,hn⟩
  have e₂ : ∃ m : ℤ, shareAt m ω y z := by obtain ⟨n,hn⟩ := h₂; exact ⟨n,hn⟩
  have hm : minScale ω x z ≤ max (minScale ω x y) (minScale ω y z) := by
    apply minScale_le hxz
    apply shareAt_trans _ ω x y z
    · exact (shareAt_iff_minScale_le hxy e₁ (fun m => (hn m).1) _).mpr (le_max_left _ _)
    · exact (shareAt_iff_minScale_le hyz e₂ (fun m => (hn m).2) _).mpr (le_max_right _ _)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold gridDepth
  have hm' : (minScale ω x z : ℝ) ≤ max (minScale ω x y : ℝ) (minScale ω y z : ℝ) := by exact_mod_cast hm
  by_cases hl : (minScale ω x y : ℝ) ≤ minScale ω y z
  · rw [max_eq_right hl] at hm'
    apply (min_le_right _ _).trans
    nlinarith
  · rw [max_eq_left (le_of_not_ge hl)] at hm'
    apply (min_le_left _ _).trans
    nlinarith

/-- Euclidean norm can subsequently be used for `R`: only its elementary
    comparison with the two coordinate gaps is needed for the tail bound. -/
lemma error_upper_ae {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap : R ≤ |x.1-y.1|+|x.2-y.2|) :
    ∀ᵐ ω ∂squareLaw, gridDepth ω x y + Real.log R ≤ Real.log 2 := by
  filter_upwards [share_eventually_exists x y] with ω he
  obtain ⟨n,hn⟩ := he
  have hs := minScale_mem hxy ⟨n,hn⟩
  have h₁ := shares_gap (by positivity : 0 < (2:ℝ)^(minScale ω x y)) hs.1
  have h₂ := shares_gap (by positivity : 0 < (2:ℝ)^(minScale ω x y)) hs.2
  have hr : R ≤ 2*(2:ℝ)^(minScale ω x y) := by linarith
  have hh := Real.log_le_log hR hr
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity), Real.log_zpow] at hh
  unfold gridDepth
  linarith

lemma error_lower_tail {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap : |x.1-y.1|+|x.2-y.2| ≤ 2*R) (u : ℝ) :
    squareLaw.real {ω | gridDepth ω x y + Real.log R < -u} ≤ 4*Real.exp (-u) := by
  obtain ⟨m,hm⟩ := exists_mem_Ico_zpow (mul_pos hR (Real.exp_pos u))
    (by norm_num : (1:ℝ)<2)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm₁ : (m:ℝ)*Real.log 2 ≤ Real.log R + u := by
    have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^m) hm.1
    rw [Real.log_zpow, Real.log_mul hR.ne' (Real.exp_ne_zero _), Real.log_exp] at hh
    exact hh
  have hsub : {ω | gridDepth ω x y + Real.log R < -u} ⊆
      {ω | ¬shareAt m ω x y} := by
    intro ω hω hs
    have hk : (minScale ω x y : ℝ) ≤ (m:ℝ) := by exact_mod_cast minScale_le hxy hs
    have := mul_le_mul_of_nonneg_right hk hl.le
    change gridDepth ω x y + Real.log R < -u at hω
    unfold gridDepth at hω
    linarith
  refine (measureReal_mono hsub).trans ((separation_probability_le m x y).trans ?_)
  have hpow : 0 < (2:ℝ)^m := by positivity
  have hm₂ : R*Real.exp u < 2*(2:ℝ)^m := by
    simpa only [zpow_add₀ (by norm_num : (2:ℝ)≠0), zpow_one, mul_comm] using hm.2
  apply (div_le_iff₀ hpow).mpr
  have hex : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hh := mul_le_mul_of_nonneg_right hm₂.le (Real.exp_nonneg (-u))
  nlinarith

lemma error_abs_tail {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) {u : ℝ} (_hu : 0 ≤ u) :
    squareLaw.real {ω | u < |gridDepth ω x y + Real.log R|} ≤ 4*Real.exp (-u) := by
  by_cases hsmall : u ≤ Real.log 2
  · have hp : squareLaw.real {ω | u < |gridDepth ω x y + Real.log R|} ≤ 1 :=
      measureReal_le_one
    have hex : (1:ℝ)/2 ≤ Real.exp (-u) := by
      have := Real.exp_le_exp.mpr (neg_le_neg hsmall)
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)] at this
      simpa only [one_div] using this
    linarith
  · have hle : squareLaw.real {ω | u < |gridDepth ω x y + Real.log R|} ≤
        squareLaw.real {ω | gridDepth ω x y + Real.log R < -u} := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [error_upper_ae hxy hR hgap₁] with ω hω
      intro hh
      rcases lt_abs.mp hh with hh | hh
      · exact False.elim (hsmall (hh.le.trans hω))
      · show gridDepth ω x y + Real.log R < -u
        linarith
    exact hle.trans (error_lower_tail hxy hR hgap₂ u)

lemma error_abs_lintegral_le {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    (∫⁻ ω, ENNReal.ofReal |gridDepth ω x y + Real.log R| ∂squareLaw) ≤ ENNReal.ofReal 4 := by
  rw [lintegral_eq_lintegral_meas_lt squareLaw
    (by filter_upwards with ω; exact abs_nonneg _)
    (((measurable_gridDepth hxy).add_const _).abs.aemeasurable)]
  have he : IntegrableOn (fun u : ℝ => 4 * Real.exp (-u)) (Set.Ioi 0) volume := by
    change Integrable (fun u : ℝ => 4 * Real.exp (-u)) (volume.restrict (Set.Ioi 0))
    simpa only [neg_one_mul] using (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul 4
  calc
    _ ≤ ∫⁻ u : ℝ in Set.Ioi 0, ENNReal.ofReal (4*Real.exp (-u)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [← ENNReal.ofReal_toReal (measure_ne_top squareLaw _)]
      exact ENNReal.ofReal_le_ofReal (error_abs_tail hxy hR hgap₁ hgap₂ hu.le)
    _ = ENNReal.ofReal 4 := by
      rw [← ofReal_integral_eq_lintegral_ofReal he (by filter_upwards with u; positivity)]
      congr 1
      rw [integral_const_mul]
      have hi := integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) (0:ℝ)
      simp only [neg_one_mul, mul_zero, Real.exp_zero, neg_div_neg_eq, div_one] at hi
      rw [hi]
      norm_num

lemma error_integrable {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    Integrable (fun ω => gridDepth ω x y + Real.log R) squareLaw := by
  have hm : AEStronglyMeasurable (fun ω => gridDepth ω x y + Real.log R) squareLaw :=
    ((measurable_gridDepth hxy).add_const (Real.log R)).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  refine ⟨hm.norm, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (by filter_upwards with ω; exact norm_nonneg _)).mpr
  simpa only [Real.norm_eq_abs] using
    (error_abs_lintegral_le hxy hR hgap₁ hgap₂).trans_lt ENNReal.ofReal_lt_top

lemma mean_abs_error_le {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    (∫ ω, |gridDepth ω x y + Real.log R| ∂squareLaw) ≤ 4 := by
  have hi := (error_integrable hxy hR hgap₁ hgap₂).abs
  have hh := error_abs_lintegral_le hxy hR hgap₁ hgap₂
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with ω; exact abs_nonneg _)] at hh
  have hh' := ENNReal.toReal_mono (by simp : ENNReal.ofReal (4:ℝ) ≠ ⊤) hh
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun ω => abs_nonneg _),
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤4)] using hh'

lemma minScale_cdf {x y : ℝ × ℝ} (hxy : x ≠ y) (m : ℤ) :
    squareLaw.real {ω | minScale ω x y ≤ m} =
      max 0 (1-|x.1-y.1|/((2:ℝ)^m)) * max 0 (1-|x.2-y.2|/((2:ℝ)^m)) := by
  have hn : ∀ᵐ ω ∂squareLaw, ∀ k : ℤ, shareAt k ω x y → shareAt (k+1) ω x y := by
    rw [ae_all_iff]
    exact fun k => shareAt_nested_ae k x y
  have he : {ω | minScale ω x y ≤ m} =ᵐ[squareLaw] {ω | shareAt m ω x y} := by
    filter_upwards [share_eventually_exists x y, hn] with ω he hn
    apply propext
    obtain ⟨n,hn'⟩ := he
    exact (shareAt_iff_minScale_le hxy ⟨n,hn'⟩ hn m).symm
  rw [measureReal_def, measure_congr he]
  exact sharing_probability m x y

lemma minScale_law_same_gaps {x y x' y' : ℝ × ℝ} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (h₁ : |x.1-y.1| = |x'.1-y'.1|) (h₂ : |x.2-y.2| = |x'.2-y'.2|) :
    Measure.map (fun ω => minScale ω x y) squareLaw =
      Measure.map (fun ω => minScale ω x' y') squareLaw := by
  apply Measure.ext_of_Iic
  intro m
  rw [Measure.map_apply (measurable_minScale hxy) measurableSet_Iic,
    Measure.map_apply (measurable_minScale hxy') measurableSet_Iic]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change squareLaw.real {ω | minScale ω x y ≤ m} = squareLaw.real {ω | minScale ω x' y' ≤ m}
  rw [minScale_cdf hxy, minScale_cdf hxy', h₁, h₂]

lemma mean_depth_same_gaps {x y x' y' : ℝ × ℝ} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (h₁ : |x.1-y.1| = |x'.1-y'.1|) (h₂ : |x.2-y.2| = |x'.2-y'.2|) :
    (∫ ω, gridDepth ω x y ∂squareLaw) = ∫ ω, gridDepth ω x' y' ∂squareLaw := by
  have hf : Measurable (fun n : ℤ => -(n:ℝ)*Real.log 2) := measurable_of_countable _
  unfold gridDepth
  rw [← integral_map (measurable_minScale hxy).aemeasurable hf.aestronglyMeasurable,
      ← integral_map (measurable_minScale hxy').aemeasurable hf.aestronglyMeasurable,
      minScale_law_same_gaps hxy hxy' h₁ h₂]

lemma minScale_law_double {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measure.map (fun ω => minScale ω (2*x.1,2*x.2) (2*y.1,2*y.2)) squareLaw =
      Measure.map (fun ω => minScale ω x y + 1) squareLaw := by
  have hd : (2*x.1,2*x.2) ≠ (2*y.1,2*y.2) := by
    intro h
    apply hxy
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> linarith
  apply Measure.ext_of_Iic
  intro m
  rw [Measure.map_apply (measurable_minScale hd) measurableSet_Iic,
    Measure.map_apply ((measurable_minScale hxy).add_const 1) measurableSet_Iic]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change squareLaw.real {ω | minScale ω (2*x.1,2*x.2) (2*y.1,2*y.2) ≤ m} =
    squareLaw.real {ω | minScale ω x y + 1 ≤ m}
  rw [show {ω | minScale ω x y + 1 ≤ m} = {ω | minScale ω x y ≤ m-1} by ext ω; simp only [Set.mem_ofPred_eq]; omega,
    minScale_cdf hd, minScale_cdf hxy]
  have hpow : (2:ℝ)^(m-1) = (2:ℝ)^m / 2 := by rw [zpow_sub₀ (by norm_num), zpow_one]
  have hq (a b : ℝ) : |2*a-2*b| / (2:ℝ)^m = |a-b| / ((2:ℝ)^m/2) := by
    rw [← mul_sub, abs_mul]
    norm_num
    ring
  rw [hpow, hq x.1 y.1, hq x.2 y.2]

lemma gridDepth_integrable {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Integrable (fun ω => gridDepth ω x y) squareLaw := by
  let R := |x.1-y.1|+|x.2-y.2|
  have hR : 0 < R := by
    by_cases h₁ : x.1 = y.1
    · have h₂ : x.2 ≠ y.2 := fun h₂ => hxy (Prod.ext h₁ h₂)
      exact add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr (sub_ne_zero.mpr h₂))
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr (sub_ne_zero.mpr h₁)) (abs_nonneg _)
  have hi := error_integrable hxy hR (le_refl R) (by linarith : R ≤ 2*R)
  have hh := hi.sub (integrable_const (Real.log R))
  change Integrable (fun ω => (gridDepth ω x y + Real.log R) - Real.log R) squareLaw at hh
  simpa only [add_sub_cancel_right] using hh

lemma mean_depth_double {x y : ℝ × ℝ} (hxy : x ≠ y) :
    (∫ ω, gridDepth ω (2*x.1,2*x.2) (2*y.1,2*y.2) ∂squareLaw) =
      (∫ ω, gridDepth ω x y ∂squareLaw) - Real.log 2 := by
  have hd : (2*x.1,2*x.2) ≠ (2*y.1,2*y.2) := by
    intro h
    apply hxy
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> linarith
  have hid : ProbabilityTheory.IdentDistrib
      (fun ω => minScale ω (2*x.1,2*x.2) (2*y.1,2*y.2))
      (fun ω => minScale ω x y + 1) squareLaw squareLaw :=
    ⟨(measurable_minScale hd).aemeasurable,
      ((measurable_minScale hxy).add_const 1).aemeasurable, minScale_law_double hxy⟩
  have hh := (hid.comp (measurable_of_countable (fun n : ℤ => -(n:ℝ)*Real.log 2))).integral_eq
  change (∫ ω, gridDepth ω (2*x.1,2*x.2) (2*y.1,2*y.2) ∂squareLaw) = _ at hh
  rw [hh]
  calc
    _ = ∫ ω, gridDepth ω x y - Real.log 2 ∂squareLaw := by
      apply integral_congr_ae
      filter_upwards with ω
      simp [gridDepth]
      ring
    _ = _ := by rw [integral_sub (gridDepth_integrable hxy) (integrable_const _)]; simp

/-- Parameter measurability, needed before integrating orientation and phase. -/
lemma measurableSet_shareAt_param {T : Type u1} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (m : ℤ) :
    MeasurableSet {t | shareAt m (W t) (X t) (Y t)} := by
  unfold shareAt bin shiftZ
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      ((hX.fst.sub ((measurable_shift _).comp hW.fst)).div_const _).floor
      ((hY.fst.sub ((measurable_shift _).comp hW.fst)).div_const _).floor
  · exact measurableSet_eq_fun
      ((hX.snd.sub ((measurable_shift _).comp hW.snd)).div_const _).floor
      ((hY.snd.sub ((measurable_shift _).comp hW.snd)).div_const _).floor

lemma measurable_minScale_param {T : Type u2} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (hne : ∀ t, X t ≠ Y t) :
    Measurable (fun t => minScale (W t) (X t) (Y t)) := by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {t | minScale (W t) (X t) (Y t) = m}
  have he : {t | minScale (W t) (X t) (Y t) = m} =
      ({t | shareAt m (W t) (X t) (Y t)} ∩
        ⋂ k : ℤ, ⋂ (_ : k < m), {t | shareAt k (W t) (X t) (Y t)}ᶜ) ∪
      ({t | m = 0} ∩ (⋃ k : ℤ, {t | shareAt k (W t) (X t) (Y t)})ᶜ) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, Set.mem_iUnion]
    exact minScale_eq_iff (hne t) m
  rw [he]
  exact ((measurableSet_shareAt_param hW hX hY m).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun (_ : k < m) =>
      (measurableSet_shareAt_param hW hX hY k).compl)).union
    ((MeasurableSet.const (m = 0)).inter (MeasurableSet.iUnion fun k =>
      measurableSet_shareAt_param hW hX hY k).compl)

lemma measurable_gridDepth_param {T : Type u3} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (hne : ∀ t, X t ≠ Y t) :
    Measurable (fun t => gridDepth (W t) (X t) (Y t)) := by
  exact (((measurable_of_countable (fun n : ℤ => (n:ℝ))).comp
    (measurable_minScale_param hW hX hY hne)).neg).mul_const _

lemma zero_ne_polarPair (t θ : ℝ) : (0,0) ≠ polarPair t θ := by
  intro h
  have he : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have h₁ : Real.cos θ = 0 := (mul_eq_zero.mp (congrArg Prod.fst h).symm).resolve_left he
  have h₂ : Real.sin θ = 0 := (mul_eq_zero.mp (congrArg Prod.snd h).symm).resolve_left he
  have hh := Real.sin_sq_add_cos_sq θ
  rw [h₁,h₂] at hh
  norm_num at hh

lemma polarPair_gaps (t θ : ℝ) :
    Real.exp t ≤ |(polarPair t θ).1|+|(polarPair t θ).2| ∧
    |(polarPair t θ).1|+|(polarPair t θ).2| ≤ 2*Real.exp t := by
  have hsum : 1 ≤ |Real.cos θ|+|Real.sin θ| := by
    have hsq := Real.sin_sq_add_cos_sq θ
    have hpos := mul_nonneg (abs_nonneg (Real.cos θ)) (abs_nonneg (Real.sin θ))
    have hc := abs_nonneg (Real.cos θ)
    have hs := abs_nonneg (Real.sin θ)
    nlinarith [sq_abs (Real.cos θ), sq_abs (Real.sin θ)]
  have hsum' : |Real.cos θ|+|Real.sin θ| ≤ 2 := by
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  simp only [polarPair, abs_mul, abs_of_pos (Real.exp_pos t)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg t)]
  · nlinarith [mul_le_mul_of_nonneg_left hsum' (Real.exp_nonneg t)]

lemma polarMean_integral (t θ : ℝ) :
    polarMean t θ = ∫ ω, gridDepth ω (0,0) (polarPair t θ) + t ∂squareLaw := by
  rw [integral_add (gridDepth_integrable (zero_ne_polarPair t θ)) (integrable_const _)]
  simp [polarMean]

lemma polarMean_bound (t θ : ℝ) : |polarMean t θ| ≤ 4 := by
  rw [polarMean_integral]
  have hg := polarPair_gaps t θ
  have hh := mean_abs_error_le (zero_ne_polarPair t θ) (Real.exp_pos t)
    (by simpa only [zero_sub, abs_neg] using hg.1)
    (by simpa only [zero_sub, abs_neg] using hg.2)
  rw [Real.log_exp] at hh
  have hb : |∫ ω, gridDepth ω (0,0) (polarPair t θ) + t ∂squareLaw| ≤
      ∫ ω, |gridDepth ω (0,0) (polarPair t θ) + t| ∂squareLaw := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (f := fun ω => gridDepth ω (0,0) (polarPair t θ) + t) (μ := squareLaw))
  exact hb.trans hh

lemma measurable_polarPair : Measurable (fun p : ℝ × ℝ => polarPair p.1 p.2) := by
  exact (measurable_fst.exp.mul measurable_snd.cos).prodMk
    (measurable_fst.exp.mul measurable_snd.sin)

lemma measurable_polarMean : Measurable (fun p : ℝ × ℝ => polarMean p.1 p.2) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × GridSample =>
      gridDepth p.2 (0,0) (polarPair p.1.1 p.1.2)) :=
    measurable_gridDepth_param measurable_snd measurable_const
      (measurable_polarPair.comp measurable_fst) (fun p => zero_ne_polarPair _ _)
  have hi : StronglyMeasurable (fun p : ℝ × ℝ => ∫ ω,
      gridDepth ω (0,0) (polarPair p.1 p.2) ∂squareLaw) :=
    hm.stronglyMeasurable.integral_prod_right
  exact hi.measurable.add measurable_fst

lemma polarPair_double (t θ : ℝ) : polarPair (t+Real.log 2) θ =
    (2*(polarPair t θ).1,2*(polarPair t θ).2) := by
  simp only [polarPair,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  congr 1 <;> ring

lemma polarMean_period_phase (θ : ℝ) : Function.Periodic (fun t => polarMean t θ) (Real.log 2) := by
  intro t
  have hm := mean_depth_double (zero_ne_polarPair t θ)
  simp only [mul_zero] at hm
  simp only [polarMean,polarPair_double,hm]
  ring

lemma polarMean_period_angle (t : ℝ) : Function.Periodic (polarMean t) (2*Real.pi) := by
  intro θ
  simp only [polarMean,polarPair,Real.cos_periodic θ,Real.sin_periodic θ]

lemma uniformInterval_integral {l : ℝ} (hl : 0 < l) (f : ℝ → ℝ) :
    (∫ x, f x ∂uniformInterval l) = l⁻¹ * ∫ x in (0:ℝ)..l, f x := by
  rw [uniformInterval, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hl.le, smul_eq_mul, intervalIntegral.integral_of_le hl.le]

lemma uniformInterval_period_shift {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ}
    (hf : Function.Periodic f l) (a : ℝ) :
    (∫ x, f (x+a) ∂uniformInterval l) = ∫ x, f x ∂uniformInterval l := by
  rw [uniformInterval_integral hl, uniformInterval_integral hl,
    intervalIntegral.integral_comp_add_right]
  congr 1
  simpa only [zero_add, add_comm l a] using hf.intervalIntegral_add_eq a 0

lemma uniformInterval_period_sub {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ}
    (hf : Function.Periodic f l) (a : ℝ) :
    (∫ x, f (a-x) ∂uniformInterval l) = ∫ x, f (-x) ∂uniformInterval l := by
  have hp : Function.Periodic (fun x => f (-x)) l := by
    intro x
    simpa only [neg_add, sub_eq_add_neg] using hf.sub_eq (-x)
  have hh := uniformInterval_period_shift hl hp (-a)
  simpa only [neg_add, neg_neg, sub_eq_add_neg, add_comm] using hh

lemma polar_average_constant (t φ : ℝ) :
    (∫ ξ, ∫ θ, polarMean (t-ξ) (θ+φ)
      ∂uniformInterval (2*Real.pi) ∂uniformInterval (Real.log 2)) = kappa := by
  simp_rw [uniformInterval_period_shift (by positivity : 0 < 2*Real.pi)
    (polarMean_period_angle _) φ]
  have hp : Function.Periodic
      (fun t => ∫ θ, polarMean t θ ∂uniformInterval (2*Real.pi)) (Real.log 2) := by
    intro x
    apply integral_congr_ae
    filter_upwards with θ
    exact polarMean_period_phase θ x
  exact uniformInterval_period_sub (Real.log_pos (by norm_num)) hp t

lemma rotateC_sub (ξ θ : ℝ) (z w : ℂ) :
    rotateC ξ θ (z-w) = rotateC ξ θ z - rotateC ξ θ w := by
  exact mul_sub _ _ _

lemma norm_rotateC (ξ θ : ℝ) (z : ℂ) :
    ‖rotateC ξ θ z‖ = Real.exp (-ξ) * ‖z‖ := by
  simp only [rotateC, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one]

lemma rotatePair_ne (ξ θ : ℝ) {z w : ℂ} (hne : z ≠ w) :
    rotatePair ξ θ z ≠ rotatePair ξ θ w := by
  intro he
  have h : rotateC ξ θ z = rotateC ξ θ w := Complex.ext
    (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hn := norm_rotateC ξ θ (z-w)
  rw [rotateC_sub, h, sub_self, norm_zero] at hn
  have hz : ‖z-w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  exact (mul_ne_zero (Real.exp_ne_zero _) hz) hn.symm

lemma rotatePair_gaps (ξ θ : ℝ) (z w : ℂ) :
    Real.exp (-ξ)*‖z-w‖ ≤
      |(rotatePair ξ θ z).1-(rotatePair ξ θ w).1| +
      |(rotatePair ξ θ z).2-(rotatePair ξ θ w).2| ∧
    |(rotatePair ξ θ z).1-(rotatePair ξ θ w).1| +
      |(rotatePair ξ θ z).2-(rotatePair ξ θ w).2| ≤ 2*(Real.exp (-ξ)*‖z-w‖) := by
  have hh := Complex.norm_le_abs_re_add_abs_im (rotateC ξ θ (z-w))
  have hr := Complex.abs_re_le_norm (rotateC ξ θ (z-w))
  have hi := Complex.abs_im_le_norm (rotateC ξ θ (z-w))
  rw [norm_rotateC, rotateC_sub] at hh hr hi
  simp only [Complex.sub_re, Complex.sub_im] at hh hr hi
  exact ⟨hh, by dsimp only [rotatePair]; linarith⟩

lemma rotateC_polar (ξ θ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    rotateC ξ θ z = (Real.exp (Real.log ‖z‖-ξ) : ℂ) *
      Complex.exp (((θ+z.arg : ℝ) : ℂ)*Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add,
    Real.exp_sub, Real.exp_log (norm_pos_iff.mpr hz),
    div_eq_mul_inv, ← Real.exp_neg, Complex.ofReal_mul]
  calc
    _ = (Real.exp (-ξ) : ℂ) * Complex.exp ((θ:ℂ)*Complex.I) *
        ((‖z‖:ℂ) * Complex.exp ((z.arg:ℂ)*Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
      rfl
    _ = _ := by ring

lemma exp_polarPair (t θ : ℝ) :
    ((Real.exp t : ℂ) * Complex.exp ((θ:ℂ)*Complex.I)).re = (polarPair t θ).1 ∧
    ((Real.exp t : ℂ) * Complex.exp ((θ:ℂ)*Complex.I)).im = (polarPair t θ).2 := by
  simp [polarPair, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]

lemma rotated_mean (ξ θ : ℝ) {z w : ℂ} (hne : z ≠ w) :
    (∫ ω, gridDepth ω (rotatePair ξ θ z) (rotatePair ξ θ w) ∂squareLaw)
      - ξ + Real.log ‖z-w‖ = polarMean (Real.log ‖z-w‖-ξ) (θ+(z-w).arg) := by
  have hp := exp_polarPair (Real.log ‖z-w‖-ξ) (θ+(z-w).arg)
  rw [← rotateC_polar ξ θ (sub_ne_zero.mpr hne), rotateC_sub] at hp
  have hm := mean_depth_same_gaps (rotatePair_ne ξ θ hne)
    (zero_ne_polarPair (Real.log ‖z-w‖-ξ) (θ+(z-w).arg))
    (by dsimp only [rotatePair]; simp only [zero_sub, abs_neg, ← hp.1]; rfl)
    (by dsimp only [rotatePair]; simp only [zero_sub, abs_neg, ← hp.2]; rfl)
  rw [hm, polarMean]
  ring

instance phaseLaw_probability : IsProbabilityMeasure phaseLaw := by
  let := uniformInterval_probability (Real.log_pos (by norm_num : (1:ℝ) < 2))
  let := uniformInterval_probability (by positivity : 0 < 2*Real.pi)
  exact Measure.prod.instIsProbabilityMeasure _ _

instance fullLaw_probability : IsProbabilityMeasure fullLaw := by
  exact Measure.prod.instIsProbabilityMeasure _ _

lemma measurable_rotatePair (z : ℂ) : Measurable (fun p : ℝ × ℝ => rotatePair p.1 p.2 z) := by
  unfold rotatePair rotateC
  fun_prop

lemma measurable_depth {z w : ℂ} (hne : z ≠ w) : Measurable (fun ω => depth ω z w) := by
  unfold depth
  exact (measurable_gridDepth_param measurable_snd
    ((measurable_rotatePair z).comp measurable_fst)
    ((measurable_rotatePair w).comp measurable_fst)
    (fun p => rotatePair_ne _ _ hne)).sub measurable_fst.fst

lemma measurable_error {z w : ℂ} (hne : z ≠ w) : Measurable (fun ω => error ω z w) :=
  (measurable_depth hne).add_const _

lemma error_fixed_phase {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) (ω : GridSample) :
    error (p,ω) z w = gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) +
      Real.log (Real.exp (-p.1)*‖z-w‖) := by
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)), Real.log_exp]
  simp only [error, depth]
  ring

lemma error_integrable_fixed {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) :
    Integrable (fun ω => error (p,ω) z w) squareLaw := by
  simp_rw [error_fixed_phase hne p]
  exact error_integrable (rotatePair_ne _ _ hne)
    (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
    (rotatePair_gaps _ _ _ _).1 (rotatePair_gaps _ _ _ _).2

lemma mean_abs_error_fixed {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) :
    (∫ ω, |error (p,ω) z w| ∂squareLaw) ≤ 4 := by
  simp_rw [error_fixed_phase hne p]
  exact mean_abs_error_le (rotatePair_ne _ _ hne)
    (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
    (rotatePair_gaps _ _ _ _).1 (rotatePair_gaps _ _ _ _).2

lemma error_integrable_full {z w : ℂ} (hne : z ≠ w) :
    Integrable (fun ω => error ω z w) fullLaw := by
  apply (integrable_prod_iff (measurable_error hne).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (error_integrable_fixed hne)
  · apply Integrable.of_bound ((measurable_error hne).norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable) 4
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using mean_abs_error_fixed hne p

lemma mean_error_fixed {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) :
    (∫ ω, error (p,ω) z w ∂squareLaw) =
      polarMean (Real.log ‖z-w‖-p.1) (p.2+(z-w).arg) := by
  have hi : Integrable (fun ω => gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w)) squareLaw :=
    gridDepth_integrable (rotatePair_ne _ _ hne)
  have his : Integrable (fun ω => gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) - p.1) squareLaw :=
    hi.sub (integrable_const p.1)
  simp only [error, depth]
  rw [integral_add his (integrable_const (Real.log ‖z-w‖)), integral_sub hi (integrable_const p.1)]
  simp only [integral_const, probReal_univ, one_smul]
  exact rotated_mean _ _ hne

lemma measurable_shifted_polarMean (t φ : ℝ) :
    Measurable (fun p : ℝ × ℝ => polarMean (t-p.1) (p.2+φ)) := by
  have h₁ : Measurable (fun p : ℝ × ℝ => t-p.1) := measurable_const.sub measurable_fst
  have h₂ : Measurable (fun p : ℝ × ℝ => p.2+φ) := measurable_snd.add_const φ
  change Measurable ((fun p : ℝ × ℝ => polarMean p.1 p.2) ∘
    (fun p : ℝ × ℝ => (t-p.1,p.2+φ)))
  apply Measurable.comp measurable_polarMean
  exact h₁.prodMk h₂

lemma mean_error_full {z w : ℂ} (hne : z ≠ w) :
    (∫ ω, error ω z w ∂fullLaw) = kappa := by
  rw [fullLaw, integral_prod _ (error_integrable_full hne)]
  simp_rw [mean_error_fixed hne]
  have hm := measurable_shifted_polarMean (Real.log ‖z-w‖) (z-w).arg
  have hi := Integrable.of_bound (μ := phaseLaw) hm.aestronglyMeasurable 4
    (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using polarMean_bound _ _))
  rw [phaseLaw, integral_prod _ hi]
  exact polar_average_constant _ _

lemma abs_error_tail_full {z w : ℂ} (hne : z ≠ w) {u : ℝ} (hu : 0 ≤ u) :
    fullLaw.real {ω | u < |error ω z w|} ≤ 4*Real.exp (-u) := by
  have hs : MeasurableSet {ω : FullSample | u < |error ω z w|} :=
    measurableSet_lt measurable_const (measurable_error hne).abs
  have hb : fullLaw {ω | u < |error ω z w|} ≤ ENNReal.ofReal (4*Real.exp (-u)) := by
    rw [fullLaw, Measure.prod_apply hs]
    calc
      _ ≤ ∫⁻ _p, ENNReal.ofReal (4*Real.exp (-u)) ∂phaseLaw := by
        apply lintegral_mono
        intro p
        have he : squareLaw.real {ω | u < |error (p,ω) z w|} ≤ 4*Real.exp (-u) := by
          simp_rw [error_fixed_phase hne p]
          exact error_abs_tail (rotatePair_ne _ _ hne)
            (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
            (rotatePair_gaps _ _ _ _).1 (rotatePair_gaps _ _ _ _).2 hu
        have hh := ENNReal.ofReal_le_ofReal he
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hh
        exact hh
      _ = _ := by simp
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [measureReal_def]
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*Real.exp (-u))] using hh

lemma mean_abs_error_full {z w : ℂ} (hne : z ≠ w) :
    (∫ ω, |error ω z w| ∂fullLaw) ≤ 4 := by
  rw [fullLaw, integral_prod _ (error_integrable_full hne).abs]
  calc
    _ ≤ ∫ _p, (4:ℝ) ∂phaseLaw := integral_mono
      (error_integrable_full hne).abs.integral_prod_left (integrable_const _)
      (mean_abs_error_fixed hne)
    _ = _ := by simp

lemma depth_ultra_ae {x y z : ℂ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∀ᵐ ω ∂fullLaw, min (depth ω x y) (depth ω y z) ≤ depth ω x z := by
  have hs : MeasurableSet {ω : FullSample | min (depth ω x y) (depth ω y z) ≤ depth ω x z} :=
    measurableSet_le ((measurable_depth hxy).min (measurable_depth hyz)) (measurable_depth hxz)
  apply (Measure.ae_prod_iff_ae_ae hs).mpr
  filter_upwards with p
  filter_upwards [gridDepth_ultra_ae (rotatePair_ne p.1 p.2 hxy)
    (rotatePair_ne p.1 p.2 hyz) (rotatePair_ne p.1 p.2 hxz)] with ω hh
  simpa only [depth,min_sub_sub_right,sub_le_sub_iff_right] using hh

end WeakPinned.Grid

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal

noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
namespace WeakPinned.Global
open Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z : P → K) (hZ : Function.Injective Z)
include hZ

omit [Fintype P] [DecidableEq P] [NumberField K] in
lemma embedding_ne (v : InfinitePlace K) {x y : P} (hne : x ≠ y) :
    v.embedding (Z x) ≠ v.embedding (Z y) :=
  fun hh => hne (hZ (v.embedding.injective hh))

omit [DecidableEq P] [NumberField K] in
lemma measurableSet_good (v : InfinitePlace K) : MeasurableSet {ω | good Z v ω} := by
  simp only [good, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  apply MeasurableSet.iInter
  intro z
  apply MeasurableSet.iInter
  intro hxy
  apply MeasurableSet.iInter
  intro hyz
  apply MeasurableSet.iInter
  intro hxz
  exact measurableSet_le
    ((Grid.measurable_depth (embedding_ne Z hZ v hxy)).min
      (Grid.measurable_depth (embedding_ne Z hZ v hyz)))
    (Grid.measurable_depth (embedding_ne Z hZ v hxz))

omit [DecidableEq P] [NumberField K] in
lemma good_ae (v : InfinitePlace K) : ∀ᵐ ω ∂Grid.fullLaw, good Z v ω := by
  simp only [good, Filter.eventually_all]
  intro x y z hxy hyz hxz
  exact Grid.depth_ultra_ae (embedding_ne Z hZ v hxy)
    (embedding_ne Z hZ v hyz) (embedding_ne Z hZ v hxz)

omit [NumberField K] in
lemma arch_value_ae (v : InfinitePlace K) {x y : P} (hxy : x ≠ y) :
    (fun ω => (arch Z v ω).value x y) =ᵐ[Grid.fullLaw]
      (fun ω => Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y))) := by
  filter_upwards [good_ae Z hZ v] with ω h
  simp [arch,h,hxy]

omit [NumberField K] in
lemma arch_measurable (v : InfinitePlace K) (x y : P) :
    Measurable (fun ω => (arch Z v ω).value x y) := by
  by_cases hxy : x = y
  · subst y
    simpa only [arch,ne_eq,not_true_eq_false,and_false,reduceIte] using
      (measurable_const : Measurable (fun _ : Grid.FullSample => (0:ℝ)))
  · simpa [arch,hxy] using (Grid.measurable_depth (embedding_ne Z hZ v hxy)).ite
      (measurableSet_good Z hZ v) (measurable_const : Measurable (fun _ : Grid.FullSample => (0:ℝ)))

omit [NumberField K] in
lemma arch_integrable (v : InfinitePlace K) (x y : P) :
    Integrable (fun ω => (arch Z v ω).value x y) Grid.fullLaw := by
  by_cases hxy : x = y
  · subst y
    simpa only [arch,ne_eq,not_true_eq_false,and_false,reduceIte] using
      (integrable_const (0:ℝ) : Integrable (fun _ : Grid.FullSample => (0:ℝ)) Grid.fullLaw)
  · have hi := (Grid.error_integrable_full (embedding_ne Z hZ v hxy)).sub
      (integrable_const (Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖))
    have he : (fun ω => Grid.error ω (v.embedding (Z x)) (v.embedding (Z y)) -
        Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖) =
        (fun ω => Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y))) := by
      funext ω; simp only [Grid.error,add_sub_cancel_right]
    change Integrable (fun ω => Grid.error ω (v.embedding (Z x)) (v.embedding (Z y)) -
        Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖) Grid.fullLaw at hi
    rw [he] at hi
    exact hi.congr (arch_value_ae Z hZ v hxy).symm

lemma arch_mean (v : InfinitePlace K) (x y : P) (hxy : x ≠ y) :
    (∫ ω, (arch Z v ω).value x y ∂Grid.fullLaw) = -Real.log (v (Z x-Z y)) + Grid.kappa := by
  rw [integral_congr_ae (arch_value_ae Z hZ v hxy)]
  have hh := Grid.mean_error_full (embedding_ne Z hZ v hxy)
  have hi := (arch_integrable Z hZ v x y).congr (arch_value_ae Z hZ v hxy)
  simp only [Grid.error] at hh
  rw [integral_add hi (integrable_const _)] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  rw [← map_sub, InfinitePlace.norm_embedding_eq] at hh
  linarith

omit [DecidableEq P] in
lemma badPlaces_mem (v : FinitePlace K) : v ∈ badPlaces Z hZ ↔ ∃ x y, x ≠ y ∧ v (Z x-Z y) ≠ 1 := by
  simp only [badPlaces, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨⟨x,y⟩,hne⟩,hh⟩
    exact ⟨x,y,hne,hh⟩
  · rintro ⟨x,y,hne,hh⟩
    exact ⟨⟨(x,y),hne⟩,hh⟩

lemma finite_value_sum (x y : P) (hxy : x ≠ y) :
    (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).value x y) =
      ∑ᶠ v : FinitePlace K, -Real.log (v (Z x-Z y)) := by
  simp only [finite,hxy,reduceIte]
  symm
  apply finsum_eq_sum_of_support_subset
  intro v hv
  apply (badPlaces_mem Z hZ v).mpr
  refine ⟨x,y,hxy,?_⟩
  intro hh
  exact hv (by simp [hh])

lemma coordinate_overlap_identity (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    L Z hZ x y hxy = Grid.kappa - M Z hZ + S Z hZ x + S Z hZ y := by
  have harch : (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).M ∂Grid.fullLaw)) +
      (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).overlapLength x y hxy ∂Grid.fullLaw)) -
      (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).potential x ∂Grid.fullLaw)) -
      (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).potential y ∂Grid.fullLaw)) =
      (∑ v : InfinitePlace K, Arithmetic.archWeight v * (-Real.log (v (Z x-Z y)))) + Grid.kappa := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    have he : ∀ v : InfinitePlace K,
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).M ∂Grid.fullLaw) +
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).overlapLength x y hxy ∂Grid.fullLaw) -
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).potential x ∂Grid.fullLaw) -
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).potential y ∂Grid.fullLaw) =
        Arithmetic.archWeight v * (-Real.log (v (Z x-Z y))) + Arithmetic.archWeight v * Grid.kappa := by
      intro v
      have hh := Depth.integral_depth_identity (arch Z v) (arch_measurable Z hZ v)
        (arch_integrable Z hZ v) hn x y hxy
      rw [arch_mean Z hZ v x y hxy] at hh
      linear_combination -Arithmetic.archWeight v * hh
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Arithmetic.sum_archWeight,one_mul]
  have hfin : (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).M) +
      (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).overlapLength x y hxy) -
      (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential x) -
      (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential y) =
      ∑ᶠ v : FinitePlace K, -Real.log (v (Z x-Z y)) := by
    rw [← finite_value_sum Z hZ x y hxy, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact ((finite Z hZ v).depth_identity hn x y hxy).symm
  have hprod := Arithmetic.normalized_log_product_formula (Z x-Z y) (sub_ne_zero.mpr (hZ.ne hxy))
  dsimp only [L,M,S]
  linear_combination harch + (Module.finrank ℚ K : ℝ)⁻¹ * hfin + hprod

lemma S_nonneg (x : P) : 0 ≤ S Z hZ x := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun v _ => mul_nonneg (Arithmetic.archWeight_nonneg v)
      (integral_nonneg (fun ω => (arch Z v ω).potential_nonneg x)))
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => (finite Z hZ v).potential_nonneg x))

end WeakPinned.Global

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma sum_map_count (m : Multiset (Finset P)) (f : Finset P → ℝ) :
    (m.map f).sum = ∑ C, (m.count C : ℝ) * f C := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
      simp_rw [Nat.cast_add, add_mul]
      rw [Finset.sum_add_distrib]
      simp [add_comm]

lemma sumCells_count (f : Finset P → ℝ) (r : ℝ) :
    d.sumCells f r = ∑ C, d.count r C * f C := sum_map_count _ _

lemma count_nonneg (r : ℝ) (C : Finset P) : 0 ≤ d.count r C := Nat.cast_nonneg _

lemma count_le_overlap (r : ℝ) (C : Finset P) (x y : P) (hx : x ∈ C) (hy : y ∈ C) :
    d.count r C ≤ d.pairOverlap r x y := by
  rw [pairOverlap, d.sumCells_count]
  calc
    d.count r C = d.count r C * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0) := by simp [hx,hy]
    _ ≤ _ := Finset.single_le_sum (f := fun D => d.count r D * (if x ∈ D ∧ y ∈ D then (1 : ℝ) else 0)) (fun D _ => mul_nonneg (d.count_nonneg r D) (by positivity)) (Finset.mem_univ C)

lemma measurable_count (C : Finset P) : Measurable (fun r => d.count r C) := by
  let F : Finset (Finset P) × Finset (Finset P) → ℝ := fun st =>
    (((st.1.filter (fun D => ¬Fintype.card P < 2*D.card)).val +
       st.2.val.map (fun D => Dᶜ)).count C : ℝ)
  have hh : Measurable (fun r => F (d.cells r, d.giants r)) :=
    (measurable_of_finite F).comp (d.measurable_cells.prodMk d.measurable_giants)
  change Measurable (fun r => F (d.cells r, d.giants r))
  exact hh

lemma integrable_count (hn : 2 ≤ Fintype.card P) (C : Finset P) (hC : 2 ≤ C.card) :
    Integrable (fun r => d.count r C) := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hC
  apply (d.integrable_pairOverlap hn x y hxy).mono' (d.measurable_count C).aestronglyMeasurable
  filter_upwards with r
  simpa only [Real.norm_eq_abs, abs_of_nonneg (d.count_nonneg r C)] using d.count_le_overlap r C x y hx hy

lemma mass_nonneg (C : Finset P) : 0 ≤ d.mass C := by
  unfold mass
  split_ifs
  · exact integral_nonneg (fun r => d.count_nonneg r C)
  · rfl

lemma mass_singleton (C : Finset P) (hC : C.card ≤ 1) : d.mass C = 0 := by
  simp [mass, show ¬2 ≤ C.card by omega]

lemma mass_le_overlap (hn : 2 ≤ Fintype.card P) (C : Finset P) (x y : P)
    (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C) :
    d.mass C ≤ d.overlapLength x y hxy := by
  have hC : 2 ≤ C.card := Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
  rw [mass, ite_eq_left hC, overlapLength]
  exact integral_mono (d.integrable_count hn C hC) (d.integrable_pairOverlap hn x y hxy)
    (fun r => d.count_le_overlap r C x y hx hy)

lemma integral_sumCells (hn : 2 ≤ Fintype.card P) (f : Finset P → ℝ)
    (hf : ∀ C, C.card ≤ 1 → f C = 0) :
    (∫ r, d.sumCells f r) = ∑ C, d.mass C * f C := by
  have hi (C : Finset P) : Integrable (fun r => d.count r C * f C) := by
    by_cases hC : 2 ≤ C.card
    · exact (d.integrable_count hn C hC).mul_const _
    · simp [hf C (by omega)]
  simp_rw [d.sumCells_count]
  rw [integral_finsetSum _ (fun C _ => hi C)]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : 2 ≤ C.card
  · simp [mass,hC,integral_mul_const]
  · simp [mass,hC,hf C (by omega)]

lemma mass_overlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∑ C, d.mass C * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) =
      d.overlapLength x y hxy := by
  symm
  apply d.integral_sumCells hn
  intro C hC
  have hh : ¬(x ∈ C ∧ y ∈ C) := by
    rintro ⟨hx,hy⟩
    have := Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
    omega
  simp [hh]

section Param
variable {Ω : Type u4} [MeasurableSpace Ω] (D : Ω → Depth P)
    (hD : ∀ x y, Measurable (fun ω => (D ω).value x y))
include hD
lemma measurable_count_param (C : Finset P) :
    Measurable (fun p : Ω × ℝ => (D p.1).count p.2 C) := by
  let F : Finset (Finset P) × Finset (Finset P) → ℝ := fun st =>
    (((st.1.filter (fun E => ¬Fintype.card P < 2*E.card)).val +
       st.2.val.map (fun E => Eᶜ)).count C : ℝ)
  have hm : Measurable (fun p : Ω×ℝ => ((D p.1).cells p.2, (D p.1).giants p.2)) :=
    (measurable_cells_param (P:=P) (Ω:=Ω×ℝ) (fun p : Ω×ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd).prodMk
    (measurable_giants_param (P:=P) (Ω:=Ω×ℝ) (fun p : Ω×ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd)
  have hh : Measurable (fun p : Ω×ℝ => F ((D p.1).cells p.2, (D p.1).giants p.2)) :=
    (measurable_of_finite F).comp hm
  change Measurable (fun p : Ω×ℝ => F ((D p.1).cells p.2, (D p.1).giants p.2))
  exact hh

lemma measurable_mass_param (C : Finset P) : Measurable (fun ω => (D ω).mass C) := by
  unfold mass
  split_ifs with hC
  · exact (measurable_count_param D hD C).stronglyMeasurable.integral_prod_right.measurable
  · exact measurable_const

lemma integrable_mass_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (hn : 2 ≤ Fintype.card P) (C : Finset P) :
    Integrable (fun ω => (D ω).mass C) μ := by
  by_cases hC : 2 ≤ C.card
  · obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hC
    apply (integrable_overlapLength_param D hD hi hn x y hxy).mono'
      (measurable_mass_param D hD C).aestronglyMeasurable
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg ((D ω).mass_nonneg C)] using
      (D ω).mass_le_overlap hn C x y hxy hx hy
  · simp only [mass, hC, reduceIte]
    exact integrable_zero _ _ _

lemma averaged_mass_overlap {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∑ C, (∫ ω, (D ω).mass C ∂μ) * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) =
      ∫ ω, (D ω).overlapLength x y hxy ∂μ := by
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun C _ => (integrable_mass_param D hD hi hn C).mul_const _)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => (D ω).mass_overlap hn x y hxy))
end Param
end WeakPinned.Hierarchy.Depth

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.Variance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators

/- Finite off-diagonal variance. All diagonal terms are identically zero,
   not O(1/n): singleton cells may persist forever. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace WeakPinned.Variance

variable {P : Type u1} [Fintype P] [DecidableEq P]

lemma sum_pairProb (B : Finset P) (hB : 2 ≤ B.card) (x : P) :
    ∑ y, pairProb B x y = prob B x := by
  classical
  by_cases hx : x ∈ B
  · have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
    have hk1 : (B.card : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
      linarith
    have he : ∀ y, pairProb B x y = if y ∈ B.erase x then
        1 / ((B.card : ℝ) * (B.card - 1)) else 0 := by
      intro y
      simp only [pairProb, hx, true_and, Finset.mem_erase, ne_comm (a := y)]
      simp only [and_comm]
    simp_rw [he]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, Finset.card_erase_of_mem hx]
    rw [Nat.cast_sub (by omega)]
    simp only [Nat.cast_one, prob, hx, reduceIte]
    field_simp
  · simp [pairProb, prob, hx]

omit [Fintype P] in
lemma pairProb_symm (B : Finset P) (x y : P) : pairProb B x y = pairProb B y x := by
  simp only [pairProb, and_left_comm, ne_comm]

omit [Fintype P] in
lemma pairProb_diag (B : Finset P) (x : P) : pairProb B x x = 0 := by
  simp [pairProb]

omit [Fintype P] in
lemma sum_prob_cell (B C : Finset P) : ∑ x ∈ C, prob B x = cellProb B C := by
  simp only [prob, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one_div,
    cellProb, Finset.inter_comm]

omit [Fintype P] in
lemma pairCell_formula (B C : Finset P) :
    pairCell B C = ((B ∩ C).card : ℝ) * ((B ∩ C).card - 1) /
      ((B.card : ℝ) * (B.card - 1)) := by
  classical
  unfold pairCell pairProb
  rw [← Finset.sum_product C C (fun xy : P × P =>
    if xy.1 ∈ B ∧ xy.2 ∈ B ∧ xy.1 ≠ xy.2 then
      1 / ((B.card : ℝ) * (B.card - 1)) else 0), ← Finset.sum_filter]
  have hf : (C ×ˢ C).filter (fun xy => xy.1 ∈ B ∧ xy.2 ∈ B ∧ xy.1 ≠ xy.2) =
      (B ∩ C).offDiag := by
    ext ⟨x,y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag, Finset.mem_inter]
    tauto
  rw [hf, Finset.sum_const, nsmul_eq_mul, Finset.offDiag_card, ← Nat.mul_sub_one]
  by_cases hb : (B ∩ C).card = 0
  · simp [hb]
  · rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
    ring

omit [Fintype P] in
lemma cellProb_nonneg (B C : Finset P) : 0 ≤ cellProb B C := by
  unfold cellProb
  positivity

omit [Fintype P] in
lemma cellProb_le_one (B C : Finset P) : cellProb B C ≤ 1 := by
  unfold cellProb
  apply div_le_one_of_le₀
  · exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₂ := C))
  · positivity

omit [Fintype P] in
lemma pairCell_nonneg (B C : Finset P) : 0 ≤ pairCell B C := by
  unfold pairCell pairProb
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs with h
  · have : 2 ≤ B.card := Finset.one_lt_card.mpr ⟨x,h.1,y,h.2.1,h.2.2⟩
    have : (2 : ℝ) ≤ B.card := by exact_mod_cast this
    have : 0 ≤ (B.card : ℝ) - 1 := by linarith
    positivity
  · rfl

private lemma pair_fraction_bounds (n m : ℝ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    (1/2) * (m/n)^2 ≤ m*(m-1)/(n*(n-1)) ∧
      m*(m-1)/(n*(n-1)) ≤ (m/n)^2 := by
  have hn : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hmn0 : 0 ≤ m/n := div_nonneg (by linarith) hn.le
  have hlow : m/(2*n) ≤ (m-1)/(n-1) := by
    apply (div_le_div_iff₀ (by positivity) hn1).mpr
    nlinarith [mul_nonneg hn.le (show 0 ≤ m-2 by linarith)]
  have hupp : (m-1)/(n-1) ≤ m/n := by
    apply (div_le_div_iff₀ hn1 hn).mpr
    nlinarith
  have he : m*(m-1)/(n*(n-1)) = (m/n)*((m-1)/(n-1)) := by
    field_simp
  rw [he]
  constructor
  · calc
      (1/2) * (m/n)^2 = (m/n)*(m/(2*n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow hmn0
  · simpa only [sq] using mul_le_mul_of_nonneg_left hupp hmn0

lemma uniform_pair_comparison (C : Finset P) (hC : 2 ≤ C.card) :
    (1/2) * (cellProb Finset.univ C)^2 ≤ pairCell Finset.univ C ∧
      pairCell Finset.univ C ≤ (cellProb Finset.univ C)^2 := by
  rw [pairCell_formula]
  simp only [cellProb, Finset.univ_inter, Finset.card_univ]
  apply pair_fraction_bounds
  · exact_mod_cast hC
  · exact_mod_cast Finset.card_le_univ C

omit [Fintype P] in
lemma singleton_pairCell (B C : Finset P) (hC : C.card ≤ 1) : pairCell B C = 0 := by
  unfold pairCell
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have : x = y := Finset.card_le_one.mp hC x hx y hy
  subst y
  exact pairProb_diag B x

omit [Fintype P] in
lemma singleton_fiber_term (B C : Finset P) (hB : 2 ≤ B.card) (hC : C.card ≤ 1) :
    (if 2 / (B.card : ℝ) ≤ cellProb B C then (cellProb B C)^2 else 0) = 0 := by
  have hk : 0 < (B.card : ℝ) := by exact_mod_cast (by omega : 0 < B.card)
  have hi : (B ∩ C).card ≤ 1 := (Finset.card_le_card Finset.inter_subset_right).trans hC
  have hiR : ((B ∩ C).card : ℝ) < 2 := by exact_mod_cast (by omega : (B ∩ C).card < 2)
  have hp : cellProb B C < 2 / (B.card : ℝ) :=
    (div_lt_div_iff_of_pos_right hk).mpr hiR
  simp only [not_le.mpr hp, reduceIte]

section Family
variable {I : Type u2} [Fintype I]
variable (w : I → ℝ) (B : I → Finset P)

lemma mean_cell_bound (C : Finset P) (M : ℝ)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M * prob Finset.univ x) :
    (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C := by
  simp_rw [← sum_prob_cell, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun x _ => hdom x

end Family

section CellIntegral
variable {Ω : Type u3} [MeasurableSpace Ω]

section Quantitative
local instance instMeasurableSpaceFinset_solutions_r12b633_1 : MeasurableSpace (Finset P) := ⊤
local instance instDiscreteMeasurableSpaceFinset_solutions_r12b633_1 : DiscreteMeasurableSpace (Finset P) := ⟨fun _ => trivial⟩
variable {I : Type u5} [Fintype I]

lemma varianceCell_singleton (w : I → ℝ) (B : I → Finset P) (T : ℝ)
    (hT : 1 ≤ T) (hB : ∀ i, 2 ≤ (B i).card) (D : Finset P) (hD : D.card ≤ 1) :
    varianceCell w B T D = 0 := by
  have hd : (D.card : ℝ) ≤ T := (by exact_mod_cast hD : (D.card : ℝ) ≤ 1).trans hT
  simp [varianceCell, not_lt.mpr hd, singleton_fiber_term _ _ (hB _) hD]

end Quantitative

end CellIntegral

end WeakPinned.Variance

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Global
open Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z : P → K) (hZ : Function.Injective Z)

lemma cellMass_nonneg (C : Finset P) : 0 ≤ cellMass Z hZ C := by
  exact add_nonneg
    (Finset.sum_nonneg (fun v _ => mul_nonneg (Arithmetic.archWeight_nonneg v)
      (integral_nonneg (fun ω => (arch Z v ω).mass_nonneg C))))
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => (finite Z hZ v).mass_nonneg C)))

lemma cellMass_overlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∑ C, cellMass Z hZ C * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) = L Z hZ x y hxy := by
  simp only [cellMass, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
    mul_assoc, L]
  rw [← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.mul_sum, Depth.averaged_mass_overlap (arch Z v) (arch_measurable Z hZ v)
      (arch_integrable Z hZ v) hn x y hxy]
  · congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    exact (finite Z hZ v).mass_overlap hn x y hxy

end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy Variance
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable {K : Type u6} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

lemma totalMass_nonneg (C : Finset P) : 0 ≤ totalMass Z₁ Z₂ h₁ h₂ C :=
  add_nonneg (cellMass_nonneg Z₁ h₁ C) (cellMass_nonneg Z₂ h₂ C)

lemma totalPotential_nonneg (x : P) : 0 ≤ totalPotential Z₁ Z₂ h₁ h₂ x :=
  add_nonneg (S_nonneg Z₁ h₁ x) (S_nonneg Z₂ h₂ x)

lemma totalMass_overlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    weightedOverlap (totalMass Z₁ Z₂ h₁ h₂) x y =
      baseConstant Z₁ Z₂ h₁ h₂ + totalPotential Z₁ Z₂ h₁ h₂ x + totalPotential Z₁ Z₂ h₁ h₂ y := by
  simp only [weightedOverlap,weightedIntegral,totalMass,add_mul,Finset.sum_add_distrib]
  rw [cellMass_overlap Z₁ h₁ hn x y hxy,cellMass_overlap Z₂ h₂ hn x y hxy,
    coordinate_overlap_identity Z₁ h₁ hn x y hxy,coordinate_overlap_identity Z₂ h₂ hn x y hxy]
  simp only [baseConstant,totalPotential]
  ring

end WeakPinned.Global

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.SmallCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.SmallFiber
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
lemma mass_nonneg {p : P → ℝ} (hp : ∀ y, 0 ≤ p y) (C : Finset P) : 0 ≤ mass p C :=
  Finset.sum_nonneg (fun y _ => hp y)

end WeakPinned.SmallFiber

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiberOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Hierarchy.Depth
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma sumCells_split (f : Finset P → ℝ) (r : ℝ) :
    d.sumCells f r =
      (∑ C ∈ d.cells r, if ¬Fintype.card P < 2*C.card then f C else 0) +
      ∑ C ∈ d.giants r, f Cᶜ := by
  classical
  simp only [sumCells,transformed,Multiset.map_add,Multiset.sum_add,
    Multiset.map_map,Function.comp_def]
  change (∑ C ∈ (d.cells r).filter (fun C => ¬Fintype.card P < 2*C.card), f C) + _ = _
  rw [Finset.sum_filter]
  rfl

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u6} [Fintype P] [DecidableEq P]
variable (d : Depth P)
lemma integrable_sumCells (hn : 2 ≤ Fintype.card P) (f : Finset P → ℝ)
    (hf : ∀ C, C.card ≤ 1 → f C = 0) : Integrable (d.sumCells f) := by
  change Integrable (fun r => d.sumCells f r)
  simp_rw [d.sumCells_count]
  apply integrable_finsetSum
  intro C _
  by_cases hC : 2 ≤ C.card
  · exact (d.integrable_count hn C hC).mul_const _
  · simp only [hf C (by omega),mul_zero]
    exact integrable_zero _ _ _
end WeakPinned.Hierarchy.Depth

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.GlobalOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Grid
open MeasureTheory

lemma truncated_error_integrable {z w : ℂ} (hne : z ≠ w) (t : ℝ) :
    Integrable (fun ω => max (|error ω z w|-t) 0) fullLaw :=
  (((error_integrable_full hne).abs.sub (integrable_const t)).sup (integrable_zero _ _ _))

lemma truncated_error_mean {z w : ℂ} (hne : z ≠ w) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, max (|error ω z w|-t) 0 ∂fullLaw) ≤ 4*Real.exp (-t) := by
  have hm : Measurable (fun ω => max (|error ω z w|-t) 0) :=
    ((measurable_error hne).abs.sub_const t).max measurable_const
  have hn (ω : FullSample) : 0 ≤ max (|error ω z w|-t) 0 := le_max_right _ _
  have hi := truncated_error_integrable hne t
  have he : IntegrableOn (fun u : ℝ => (4*Real.exp (-t))*Real.exp (-u)) (Set.Ioi 0) volume := by
    simpa only [neg_one_mul, IntegrableOn] using
      (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul (4*Real.exp (-t))
  have hb : (∫⁻ ω, ENNReal.ofReal (max (|error ω z w|-t) 0) ∂fullLaw) ≤
      ENNReal.ofReal (4*Real.exp (-t)) := by
    rw [lintegral_eq_lintegral_meas_lt fullLaw
      (Filter.Eventually.of_forall hn) hm.aemeasurable]
    calc
      _ ≤ ∫⁻ u : ℝ in Set.Ioi 0, ENNReal.ofReal ((4*Real.exp (-t))*Real.exp (-u)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := hu
        have hs : {ω : FullSample | u < max (|error ω z w|-t) 0} =
            {ω : FullSample | u+t < |error ω z w|} := by
          ext ω
          simp only [Set.mem_ofPred_eq,lt_max_iff]
          constructor
          · rintro (h | h) <;> linarith
          · intro h; exact Or.inl (by linarith)
        rw [hs, ← ENNReal.ofReal_toReal (measure_ne_top fullLaw _)]
        have hh := abs_error_tail_full hne (add_nonneg hu.le ht)
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ 4*Real.exp (-(u+t)) := hh
          _ = _ := by rw [neg_add,Real.exp_add]; ring
      _ = ENNReal.ofReal (4*Real.exp (-t)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal he (by filter_upwards with u; positivity)]
        congr 1
        rw [integral_const_mul]
        have hz := integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) (0:ℝ)
        simp only [neg_one_mul,mul_zero,Real.exp_zero,neg_div_neg_eq,div_one] at hz
        rw [hz,mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

lemma truncated_sum_bound (a b H : ℝ) :
    max (|a+b|-H) 0 ≤ 2*max (|a|-H/2) 0 + 2*max (|b|-H/2) 0 := by
  apply max_le
  · have ht := abs_add_le a b
    have h₁ := le_max_left (|a|-H/2) 0
    have h₂ := le_max_left (|b|-H/2) 0
    have h₃ := le_max_right (|a|-H/2) 0
    have h₄ := le_max_right (|b|-H/2) 0
    linarith
  · positivity

lemma paired_error_mean {z₁ w₁ z₂ w₂ : ℂ} (h₁ : z₁ ≠ w₁) (h₂ : z₂ ≠ w₂)
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ ω, max (|error ω z₁ w₁ + error ω z₂ w₂|-H) 0 ∂fullLaw) ≤
      16*Real.exp (-H/2) := by
  have hi : Integrable (fun ω => max (|error ω z₁ w₁ + error ω z₂ w₂|-H) 0) fullLaw := by
    exact Integrable.sup (((error_integrable_full h₁).add (error_integrable_full h₂)).abs.sub
      (integrable_const H)) (integrable_zero _ _ _)
  have hia := truncated_error_integrable h₁ (H/2)
  have hib := truncated_error_integrable h₂ (H/2)
  have hh := integral_mono hi ((hia.const_mul 2).add (hib.const_mul 2))
    (fun ω => truncated_sum_bound (error ω z₁ w₁) (error ω z₂ w₂) H)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hia.const_mul 2) (hib.const_mul 2)] at hh
  simp only [integral_const_mul] at hh
  have hta := truncated_error_mean h₁ (div_nonneg hH (by norm_num : (0:ℝ)≤2))
  have htb := truncated_error_mean h₂ (div_nonneg hH (by norm_num : (0:ℝ)≤2))
  rw [neg_div'] at hta htb
  linarith

end WeakPinned.Grid

namespace WeakPinned.Global
open Hierarchy Variance SmallFiber
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]
variable {K : Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

lemma arch_fiber_defect (v : InfinitePlace K) (a b : P) (hab : a ≠ b) (t : K)
    (ht : (Z₁ a-Z₁ b)*(Z₂ a-Z₂ b)=t) :
    (fun ω => (arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)) =ᵐ[Grid.fullLaw]
      (fun ω => Grid.error ω (v.embedding (Z₁ a)) (v.embedding (Z₁ b))+
        Grid.error ω (v.embedding (Z₂ a)) (v.embedding (Z₂ b))) := by
  have he := Arithmetic.raw_fiber_identity v.val (Z₁ a-Z₁ b) (Z₂ a-Z₂ b)
    (sub_ne_zero.mpr (h₁.ne hab)) (sub_ne_zero.mpr (h₂.ne hab))
  rw [ht] at he
  change -Real.log (v (Z₁ a-Z₁ b)) + -Real.log (v (Z₂ a-Z₂ b)) = -Real.log (v t) at he
  filter_upwards [arch_value_ae Z₁ h₁ v hab,arch_value_ae Z₂ h₂ v hab] with ω hA hB
  rw [hA,hB]
  simp only [Grid.error,← map_sub,InfinitePlace.norm_embedding_eq]
  linarith

lemma arch_defect_mean (v : InfinitePlace K) (a b : P) (hab : a ≠ b) (t : K)
    (ht : (Z₁ a-Z₁ b)*(Z₂ a-Z₂ b)=t) (H : ℝ) (hH : 0 ≤ H) :
    (∫ ω, max (|(arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)|-H) 0 ∂Grid.fullLaw) ≤
      16*Real.exp (-H/2) := by
  have he := arch_fiber_defect Z₁ Z₂ h₁ h₂ v a b hab t ht
  have he' : (fun ω => max (|(arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)|-H) 0) =ᵐ[Grid.fullLaw]
      (fun ω => max (|Grid.error ω (v.embedding (Z₁ a)) (v.embedding (Z₁ b))+
        Grid.error ω (v.embedding (Z₂ a)) (v.embedding (Z₂ b))|-H) 0) := by
    filter_upwards [he] with ω hh
    rw [hh]
  rw [integral_congr_ae he']
  exact Grid.paired_error_mean (embedding_ne Z₁ h₁ v hab) (embedding_ne Z₂ h₂ v hab) hH

lemma arch_weighted_defect (v : InfinitePlace K) (w : I → ℝ) (p : I → P → ℝ)
    (x : I → P) (t : I → K) (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1)
    (hp : ∀ i y, 0 ≤ p i y) (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (H : ℝ) (hH : 0 ≤ H) :
    (∫ ω, ∑ i, w i*∑ y, p i y*max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0 ∂Grid.fullLaw) ≤ 16*Real.exp (-H/2) := by
  have hi (i : I) (y : P) : Integrable (fun ω => max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0) Grid.fullLaw :=
    ((((arch_integrable Z₁ h₁ v _ _).add (arch_integrable Z₂ h₂ v _ _)).add (integrable_const _)).abs.sub
      (integrable_const H)).sup (integrable_zero _ _ _)
  rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum (s:=Finset.univ)
    (fun y _ => (hi i y).const_mul _)).const_mul _)]
  simp_rw [integral_const_mul,integral_finsetSum _ (fun y _ => (hi _ y).const_mul _),integral_const_mul]
  calc
    _ ≤ ∑ i, w i * ∑ y, p i y*(16*Real.exp (-H/2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : p i y=0
      · simp [hy]
      · have hxy : x i ≠ y := by intro he; rw [← he,hx i] at hy; exact hy rfl
        exact mul_le_mul_of_nonneg_left (arch_defect_mean Z₁ Z₂ h₁ h₂ v _ _ hxy _ (ht i y hy) H hH) (hp i y)
    _ = _ := by simp only [← Finset.sum_mul,hp1,one_mul,hW]

omit h₁ h₂ in
lemma finite_zero_outside {Z : P → K} (hZ : Function.Injective Z) (v : FinitePlace K)
    (hv : v ∉ badPlaces Z hZ) : ∀ a b, (finite Z hZ v).value a b=0 := by
  intro a b
  by_cases hab : a=b
  · simp [finite,hab]
  · have hunit : v (Z a-Z b)=1 := by
      by_contra h
      exact hv ((badPlaces_mem Z hZ v).mpr ⟨a,b,hab,h⟩)
    simp [finite,hab,hunit]

omit h₁ h₂ in
lemma finite_mass_zero {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (v : FinitePlace K) (hv : v ∉ badPlaces Z hZ) (C : Finset P) : (finite Z hZ v).mass C=0 := by
  have hz := (finite Z hZ v).zero_values hn (finite_zero_outside hZ v hv)
  by_cases hC : C.card ≤ 1
  · exact (finite Z hZ v).mass_singleton C hC
  · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1<C.card)
    have hl := (finite Z hZ v).mass_le_overlap hn C a b hab ha hb
    rw [hz.2.2 a b hab] at hl
    exact le_antisymm hl ((finite Z hZ v).mass_nonneg C)

omit h₁ h₂ in
lemma sum_finite_mass {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (C : Finset P) :
    (∑ v ∈ V, (finite Z hZ v).mass C) = ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).mass C := by
  symm
  exact Finset.sum_subset hV (fun v _ hv => finite_mass_zero hZ hn v hv C)

omit h₁ h₂ in
lemma sum_finite_potential {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (a : P) :
    (∑ v ∈ V, (finite Z hZ v).potential a) = ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential a := by
  symm
  exact Finset.sum_subset hV (fun v _ hv =>
    ((finite Z hZ v).zero_values hn (finite_zero_outside hZ v hv)).2.1 a)

omit h₁ h₂ in
lemma placeAverage_mono (V : Finset (FinitePlace K)) {A A' : InfinitePlace K → ℝ} {F F' : FinitePlace K → ℝ}
    (hA : ∀ v, A v ≤ A' v) (hF : ∀ v ∈ V, F v ≤ F' v) : placeAverage V A F ≤ placeAverage V A' F' := by
  apply add_le_add
  · exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hA v) (Arithmetic.archWeight_nonneg v))
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (by positivity)

omit h₁ h₂ in
lemma placeAverage_arch_const (V : Finset (FinitePlace K)) (a : ℝ) :
    placeAverage V (fun _ => a) (fun _ => 0) = a := by
  simp only [placeAverage,Finset.sum_const_zero,mul_zero,add_zero,← Finset.sum_mul,Arithmetic.sum_archWeight,one_mul]

end WeakPinned.Global

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ExtremalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology

/- Finite extremal core construction. The truncated-fiber score gives the same
   core as pruning while avoiding an arbitrary pruning order. It uses the
   original fibers without a generic-position hypothesis. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Core
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]

namespace Fibers
variable (G : Fibers V I)

omit [Fintype V] [Fintype I] in
lemma edge_no_loop (K : ℝ) (C : Finset V) (v : V) : ¬G.edge K C v v := by
  rintro ⟨e,_,he,hv⟩
  exact G.no_loop e (he ▸ (Finset.mem_inter.mp hv).1)

end Fibers
end WeakPinned.Core

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.IncomingFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype I] in
lemma edgeLaw_diag (x : V) : G.edgeLaw x x=0 := by
  have hh : (x,x) ∉ G.edges := by
    intro h
    exact G.edge_no_loop (-1) Finset.univ x (Finset.mem_filter.mp h).2
  simp [edgeLaw,hh]

omit [Fintype I] in
lemma fiberWeight_prob (e : I) (y : V) :
    G.fiberWeight e*prob (G.targets e) y = if y ∈ G.targets e then 1/G.edgeCount else 0 := by
  by_cases hy : y ∈ G.targets e
  · have hk : ((G.targets e).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr ⟨y,hy⟩)
    simp only [fiberWeight,prob,ite_eq_left hy]
    field_simp
  · simp [prob,hy]

lemma sampling_fiber (x y : V) :
    (∑ e, if G.source e=x then G.fiberWeight e * prob (G.targets e) y else 0) =
      G.edgeLaw x y := by
  have he := G.edge_indicator (-1) Finset.univ x y
  simp only [G.active_univ_neg_one,true_and,Finset.mem_inter,Finset.mem_univ,and_true] at he
  have hh : (∑ e, if G.source e=x then G.fiberWeight e * prob (G.targets e) y else 0) =
      (∑ e, if G.source e=x ∧ y ∈ G.targets e then (1:ℝ) else 0)/G.edgeCount := by
    simp only [Finset.sum_div,G.fiberWeight_prob]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.source e=x <;> by_cases hy : y ∈ G.targets e <;> simp [hs,hy]
  rw [hh,he]
  by_cases he : G.edge (-1) Finset.univ x y <;> simp [edgeLaw,edges,edgeSet,he]

lemma fiber_marginal (y : V) :
    (∑ e, G.fiberWeight e * prob (G.targets e) y) = ∑ x, G.edgeLaw x y := by
  simp_rw [← G.sampling_fiber]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

omit [Fintype I] in
lemma incoming_marginal (y : V) : ∑ x, G.edgeLaw x y=G.incomingWeight y := by
  simp only [edgeLaw,incomingWeight,incoming,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  simp only [mul_one_div]

omit [Fintype I] in
lemma sampling_incoming (x y : V) :
    G.incomingWeight y*prob (G.incoming y) x=G.edgeLaw x y := by
  by_cases he : (x,y) ∈ G.edges
  · have hm : x ∈ G.incoming y := by simp [incoming,he]
    have hk : ((G.incoming y).card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr ⟨x,hm⟩)
    simp only [incomingWeight,prob,ite_eq_left hm,edgeLaw,ite_eq_left he]
    field_simp
  · have hm : x ∉ G.incoming y := by simp [incoming,he]
    simp [prob,hm,edgeLaw,he]

omit [Fintype I] in
lemma sum_edgeLaw (hG : 0 < G.edgeCount) : (∑ x, ∑ y, G.edgeLaw x y)=1 := by
  rw [← Fintype.sum_prod_type (f:=fun xy : V × V => G.edgeLaw xy.1 xy.2)]
  simp only [edgeLaw,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have he : Finset.univ.filter (fun xy : V × V => xy ∈ G.edges)=G.edges := by simp
  rw [he]
  change G.edgeCount*(1/G.edgeCount)=1
  field_simp

omit [Fintype I] in
lemma sum_incomingWeight (hG : 0 < G.edgeCount) : ∑ y, G.incomingWeight y=1 := by
  simp_rw [← G.incoming_marginal]
  rw [Finset.sum_comm,G.sum_edgeLaw hG]

lemma fiber_domination (B : ℝ) (hdom : ∀ x y, G.edgeLaw x y ≤ B*pairProb Finset.univ x y)
    (hn : 2 ≤ Fintype.card V) (y : V) :
    (∑ e, G.fiberWeight e*prob (G.targets e) y) ≤ B*prob Finset.univ y := by
  rw [G.fiber_marginal]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => hdom x y)
  simpa only [← Finset.mul_sum,pairProb_symm _ _ y,sum_pairProb Finset.univ (by simpa using hn)] using hh

omit [Fintype I] in
/-- The exact bound on omitted small incoming degrees, not just a formal
    little-o assertion. -/
lemma small_incoming_mass (T : ℝ) (hT : 0 ≤ T) :
    (∑ y, if ((G.incoming y).card : ℝ)<T then G.incomingWeight y else 0) ≤
      (Fintype.card V : ℝ)*T/G.edgeCount := by
  have hn : 0 ≤ G.edgeCount := by unfold edgeCount; positivity
  have hh : ∀ y, (if ((G.incoming y).card : ℝ)<T then G.incomingWeight y else 0) ≤ T/G.edgeCount := by
    intro y
    split_ifs with hy
    · exact div_le_div_of_nonneg_right hy.le hn
    · exact div_nonneg hT hn
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hh y)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_div_assoc] using hs

end WeakPinned.Core.Fibers

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned
open scoped BigOperators
open Variance
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable {G : Core.Fibers V I} {θ γ c η : ℝ}

lemma PreparedGraph.edgeCount_pos (h : PreparedGraph V I G θ γ c η) (hη : η<θ) : 0<G.edgeCount := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hp : 0<(θ-η)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) :=
    mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)
  exact hp.trans_le h.lower

lemma PreparedGraph.edge_domination (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (x y : V) :
    G.edgeLaw x y ≤ (1/(θ-η))*pairProb Finset.univ x y := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hden : 0<(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) := mul_pos (by linarith) (by linarith)
  by_cases hxy : x=y
  · subst y; simp [G.edgeLaw_diag,pairProb]
  · have he : pairProb Finset.univ x y=1/((Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) := by simp [pairProb,hxy]
    rw [he]
    unfold Core.Fibers.edgeLaw
    split_ifs
    · have hh := one_div_le_one_div_of_le (mul_pos (sub_pos.mpr hη) hden) (by simpa only [mul_assoc] using h.lower)
      calc
        1 / G.edgeCount ≤ 1 / ((θ-η)*((Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1))) := hh
        _ = _ := by rw [one_div_mul_one_div]
    · positivity

end WeakPinned

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance SmallFiber
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

lemma qCell_eq (C : Finset V) : G.qCell C = SmallFiber.edgeCell G.fiberWeight (fun e => prob (G.targets e)) G.source C := by
  unfold qCell SmallFiber.edgeCell SmallFiber.edgeLaw
  simp_rw [G.sampling_fiber]

omit [Fintype I] in
lemma qCell_bound {B : ℝ} (hdom : ∀ x y, G.edgeLaw x y ≤ B*pairProb Finset.univ x y) (C : Finset V) :
    G.qCell C ≤ B*pairCell Finset.univ C := by
  unfold qCell pairCell
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hdom x y))

end WeakPinned.Core.Fibers

namespace WeakPinned.Variance
open scoped BigOperators
variable {V : Type u5} [Fintype V] [DecidableEq V]

lemma weighted_pair (m : Finset V → ℝ) (q : V → V → ℝ) :
    weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, q x y)=
      ∑ x, ∑ y, q x y*weightedOverlap m x y := by
  have hc (C : Finset V) : (∑ x ∈ C, ∑ y ∈ C, q x y)=
      ∑ x, ∑ y, q x y*(if x∈C ∧ y∈C then (1:ℝ) else 0) := by
    simp only [mul_ite,mul_one,mul_zero,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp
  simp only [weightedIntegral,hc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [weightedOverlap,weightedIntegral,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  ring

lemma weighted_additive (m : Finset V → ℝ) (b : ℝ) (S : V → ℝ)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y)
    (q : V → V → ℝ) (hdiag : ∀ x, q x x=0) (h1 : (∑ x, ∑ y, q x y)=1) :
    weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, q x y)=
      b+∑ x, ((∑ y, q x y)+(∑ y, q y x))*S x := by
  rw [weighted_pair]
  have hp (x y : V) : q x y*weightedOverlap m x y=q x y*(b+S x+S y) := by
    by_cases hxy : x=y
    · subst y; simp [hdiag]
    · rw [hL x y hxy]
  simp_rw [hp,mul_add,Finset.sum_add_distrib]
  have hb : (∑ x, ∑ y, q x y*b)=b := by
    simp only [← Finset.sum_mul,h1,one_mul]
  rw [hb]
  simp only [← Finset.sum_mul,add_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun x y => q x y*S y)]
  simp only [← Finset.sum_mul]
  ring

lemma uniform_additive (m : Finset V → ℝ) (b : ℝ) (S : V → ℝ)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y) (hn : 2≤Fintype.card V) :
    weightedIntegral m (pairCell Finset.univ)=b+2*(∑ x, prob Finset.univ x*S x) := by
  have hsum : (∑ x : V, ∑ y : V, pairProb Finset.univ x y)=1 := by
    simp_rw [sum_pairProb Finset.univ (by simpa using hn)]
    exact sum_prob Finset.univ (Finset.card_pos.mp (by simpa using (show 0<Fintype.card V by omega)))
  have hh := weighted_additive m b S hL (pairProb Finset.univ) (by intro x; simp [pairProb]) hsum
  change weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, pairProb Finset.univ x y) = _
  rw [hh]
  simp_rw [pairProb_symm Finset.univ _ _,sum_pairProb Finset.univ (by simpa using hn)]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

end WeakPinned.Variance

namespace WeakPinned
open scoped BigOperators
open Variance SmallFiber Global
variable {V : Type u8} {I : Type u9} [Fintype V] [Fintype I] [DecidableEq V]
variable {G : Core.Fibers V I} {θ γ c η : ℝ}
variable {K : Type u10} [Field K] [NumberField K]
variable (Z₁ Z₂ : V → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

lemma overlapScale_nonneg : 0 ≤ overlapScale Z₁ Z₂ h₁ h₂ := by
  exact Finset.sum_nonneg (fun C _ => mul_nonneg (totalMass_nonneg Z₁ Z₂ h₁ h₂ C) (pairCell_nonneg _ _))

lemma potentialScale_nonneg : 0 ≤ potentialScale Z₁ Z₂ h₁ h₂ := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (totalPotential_nonneg Z₁ Z₂ h₁ h₂ x)
  simp only [prob,Finset.mem_univ,ite_true]
  positivity

end WeakPinned

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u11} {I : Type u12} [Fintype P] [DecidableEq P] [Fintype I]
lemma varianceCell_nonneg (w : I → ℝ) (B : I → Finset P) (T : ℝ)
    (hw : ∀ i, 0≤w i) (C : Finset P) : 0≤varianceCell w B T C := by
  unfold varianceCell
  split_ifs
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hw i)
    split_ifs <;> positivity

end WeakPinned.Variance

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.OverlapRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance
variable {V : Type u4} {I : Type u5} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype I] in
lemma retainedWeight_nonneg (T : ℝ) (y : V) : 0≤G.retainedWeight T y := by
  unfold retainedWeight incomingWeight edgeCount
  split_ifs <;> positivity

omit [Fintype I] in
lemma retainedWeight_le (T : ℝ) (y : V) : G.retainedWeight T y≤G.incomingWeight y := by
  unfold retainedWeight
  split_ifs
  · exact le_rfl
  · unfold incomingWeight edgeCount; positivity

omit [Fintype I] in
lemma sum_retainedWeight (T : ℝ) (hG : 0<G.edgeCount) : (∑ y, G.retainedWeight T y)≤1 := by
  rw [← G.sum_incomingWeight hG]
  exact Finset.sum_le_sum (fun y _ => G.retainedWeight_le T y)

omit [Fintype I] in
lemma retainedSet_size (T : ℝ) (hT : T≤Fintype.card V) (y : V) : T≤((G.retainedSet T y).card:ℝ) := by
  unfold retainedSet
  split_ifs with h
  · exact h
  · simpa using hT

end WeakPinned.Core.Fibers

namespace WeakPinned
open Filter Variance Global
open scoped Topology BigOperators
variable {V : ℕ → Type u6} {I : ℕ → Type u7} {K : ℕ → Type u8} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

lemma PreparedGraph.uniform_domination {V : Type u9} {I : Type u10} [Fintype V] [Fintype I] [DecidableEq V]
    {G : Core.Fibers V I} {θ γ c η : ℝ} (h : PreparedGraph V I G θ γ c η) (hθ : 0<θ)
    (hη : η≤θ/2) (x y : V) : G.edgeLaw x y≤(2/θ)*pairProb Finset.univ x y := by
  have hh : η<θ := by linarith
  refine (h.edge_domination hh x y).trans (mul_le_mul_of_nonneg_right ?_ (by
    unfold pairProb
    split_ifs
    · have hn : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
      simp only [Finset.card_univ]
      exact div_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))
    · exact le_rfl))
  apply (div_le_div_iff₀ (by linarith : 0<θ-η) hθ).mpr
  linarith

end WeakPinned

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.MinPotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

/-- The giant-complement second moment estimate needed to compare W and W₂.
The linear error, unlike an absolute singleton error, can be integrated. -/
lemma cell_second_moment (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) (C : Finset P) :
    (∑ i, w i*(cellProb (B i) C)^2) ≤
      2*varianceCell w B T C + 4*pairCell Finset.univ C + κ*M*cellProb Finset.univ C := by
  have hmean := mean_cell_bound w B C M hdom
  have hm : 0≤M*cellProb Finset.univ C := (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (cellProb_nonneg _ _))).trans hmean
  unfold varianceCell
  split_ifs with hlarge
  · have hmC : 2≤C.card := by have : (1:ℝ)<C.card := hT.trans_lt hlarge; exact_mod_cast this
    have hcomp := (uniform_pair_comparison C hmC).1
    have hb : (∑ i, w i*(cellProb Finset.univ C)^2) ≤ (cellProb Finset.univ C)^2 := by
      rw [← Finset.sum_mul]
      nlinarith [sq_nonneg (cellProb Finset.univ C)]
    have hh : (∑ i, w i*(cellProb (B i) C)^2) ≤
        2*(∑ i, w i*(cellProb (B i) C-cellProb Finset.univ C)^2) +
        2*(∑ i, w i*(cellProb Finset.univ C)^2) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (show (cellProb (B i) C)^2 ≤
        2*(cellProb (B i) C-cellProb Finset.univ C)^2+2*(cellProb Finset.univ C)^2 by
          nlinarith [sq_nonneg (cellProb (B i) C-2*cellProb Finset.univ C)]) (hw i)
      nlinarith
    nlinarith [mul_nonneg hκ hm]
  · have hh : (∑ i, w i*(cellProb (B i) C)^2) ≤
        (∑ i, w i*(if 2/((B i).card:ℝ)≤cellProb (B i) C then (cellProb (B i) C)^2 else 0)) +
        κ*(∑ i, w i*cellProb (B i) C) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · nlinarith [mul_nonneg hκ (mul_nonneg (hw i) (cellProb_nonneg (B i) C))]
      · have hp : cellProb (B i) C≤κ := (le_of_lt (lt_of_not_ge hi)).trans (hk i)
        have h := mul_le_mul_of_nonneg_left hp (mul_nonneg (hw i) (cellProb_nonneg (B i) C))
        nlinarith
    have hκmean := mul_le_mul_of_nonneg_left hmean hκ
    nlinarith [pairCell_nonneg Finset.univ C]

end WeakPinned.Variance

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
open scoped BigOperators
variable {P : Type u3} [Fintype P] [DecidableEq P] (d : Depth P)

lemma mem_giant_iff_cell (r : ℝ) (x : P) :
    x ∈ d.giant r ↔ Fintype.card P < 2*(d.cell r x).card := by
  constructor
  · intro hx
    obtain ⟨C,hC,hx⟩ := Finset.mem_biUnion.mp hx
    have hc := (d.mem_giants r C).mp hC
    simpa only [d.cell_of_mem hc.1 hx] using hc.2
  · intro hx
    have hc : d.cell r x ∈ d.giants r := (d.mem_giants r _).mpr ⟨d.cell_mem_cells _ _,hx⟩
    rw [d.giant_eq hc]
    exact d.self_mem_cell r x

lemma mem_giant_exists (r : ℝ) (x : P) :
    x ∈ d.giant r ↔ ∃ C : Finset P, Fintype.card P < 2*C.card ∧ ∀ y ∈ C, d.share r x y := by
  rw [d.mem_giant_iff_cell]
  constructor
  · intro hc
    exact ⟨d.cell r x,hc,fun y hy => (d.mem_cell r x y).mp hy⟩
  · rintro ⟨C,hc,hs⟩
    have hsub : C ⊆ d.cell r x := fun y hy => (d.mem_cell r x y).mpr (hs y hy)
    have := Finset.card_le_card hsub
    omega

lemma mem_giant_mono {r t : ℝ} (htr : t ≤ r) {x : P} (hx : x ∈ d.giant r) : x ∈ d.giant t := by
  rw [d.mem_giant_iff_cell] at hx ⊢
  have := Finset.card_le_card (d.cell_mono htr x)
  omega

lemma isClosed_mem_giant (x : P) : IsClosed {r : ℝ | x ∈ d.giant r} := by
  simp_rw [d.mem_giant_exists,Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h : Fintype.card P < 2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy : x=y
    · simp [share,hxy]
    · simp only [share,hxy,false_or]
      exact isClosed_le continuous_id continuous_const

lemma mem_giant_low (hn : 2 ≤ Fintype.card P) (x : P) : x ∈ d.giant (-d.radius) := by
  rw [d.mem_giant_iff_cell,d.cell_of_low le_rfl,Finset.card_univ]
  omega

lemma mem_giant_le_M (hn : 2 ≤ Fintype.card P) {r : ℝ} {x : P} (hx : x ∈ d.giant r) : r ≤ d.M := by
  obtain ⟨C,hC,_⟩ := Finset.mem_biUnion.mp hx
  exact (d.giants_cutoff hn r).mp ⟨C,hC⟩

lemma departure_cutoff (hn : 2 ≤ Fintype.card P) (x : P) (r : ℝ) :
    x ∈ d.giant r ↔ r ≤ d.departure x := by
  have hne : Set.Nonempty {t : ℝ | x ∈ d.giant t} := ⟨-d.radius,d.mem_giant_low hn x⟩
  have hbd : BddAbove {t : ℝ | x ∈ d.giant t} := ⟨d.M,fun t ht => d.mem_giant_le_M hn ht⟩
  exact ⟨fun hx => le_csSup hbd hx,fun hr => d.mem_giant_mono hr ((d.isClosed_mem_giant x).csSup_mem hne hbd)⟩

lemma departure_le_M (hn : 2 ≤ Fintype.card P) (x : P) : d.departure x ≤ d.M :=
  d.mem_giant_le_M hn ((d.departure_cutoff hn x _).mpr le_rfl)

lemma outside_departure (hn : 2 ≤ Fintype.card P) (x : P) :
    (fun r => d.outsideIndicator r x) = (Set.Ioc (d.departure x) d.M).indicator (fun _ => (1:ℝ)) := by
  funext r
  simp only [outsideIndicator,d.giants_cutoff hn,d.departure_cutoff hn,not_le,Set.indicator,Set.mem_Ioc]
  congr 1
  exact propext and_comm

lemma integral_one_Ioc {a b : ℝ} (hab : a ≤ b) :
    (∫ r : ℝ, (Set.Ioc a b).indicator (fun _ => (1:ℝ)) r)=b-a := by
  rw [integral_indicator measurableSet_Ioc,integral_const]
  simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma potential_departure (hn : 2 ≤ Fintype.card P) (x : P) : d.potential x = d.M-d.departure x := by
  unfold potential
  rw [d.outside_departure hn x,integral_one_Ioc (d.departure_le_M hn x)]

lemma outside_product (hn : 2 ≤ Fintype.card P) (x y : P) :
    (fun r => d.outsideIndicator r x*d.outsideIndicator r y) =
      (Set.Ioc (max (d.departure x) (d.departure y)) d.M).indicator (fun _ => (1:ℝ)) := by
  funext r
  rw [congrFun (d.outside_departure hn x) r,congrFun (d.outside_departure hn y) r]
  simp only [Set.indicator,Set.mem_Ioc,max_lt_iff]
  split_ifs <;> simp_all

/-- Exact layer-cake identity, including the finite set of threshold ties. -/
lemma min_potential (hn : 2 ≤ Fintype.card P) (x y : P) :
    min (d.potential x) (d.potential y) = ∫ r, d.outsideIndicator r x*d.outsideIndicator r y := by
  rw [d.outside_product hn x y,integral_one_Ioc (max_le (d.departure_le_M hn x) (d.departure_le_M hn y)),
    d.potential_departure hn x,d.potential_departure hn y]
  exact min_sub_sub_left d.M (d.departure x) (d.departure y)

end WeakPinned.Hierarchy.Depth

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace WeakPinned.MinKernel
variable {P : Type u4} [Fintype P]

lemma integrable_step (a : ℝ) : Integrable (step a) := by
  rw [step,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma step_mul (a b : ℝ) : (fun r => step a r*step b r)=step (min a b) := by
  funext r
  simp only [step,Set.indicator,Set.mem_Ioc,le_min_iff]
  split_ifs <;> simp_all

lemma integral_step (a : ℝ) (ha : 0≤a) : (∫ r, step a r)=a := by
  rw [step,integral_indicator measurableSet_Ioc]
  simp [integral_const,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal ha]

lemma tail_product (p a b : P → ℝ) :
    (fun r => tail p a r*tail p b r) = fun r => ∑ x, ∑ y, (p x*p y)*step (min (a x) (b y)) r := by
  funext r
  simp only [tail]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [← congrFun (step_mul (a x) (b y)) r]
  ring

lemma integrable_tail_product (p a b : P → ℝ) : Integrable (fun r => tail p a r*tail p b r) := by
  rw [tail_product]
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (integrable_step _).const_mul _

lemma energy_integral (p a b : P → ℝ) (ha : ∀ x, 0≤a x) (hb : ∀ x, 0≤b x) :
    energy p a b = ∫ r, tail p a r*tail p b r := by
  rw [tail_product,integral_finsetSum _ (fun x _ => integrable_finsetSum _ fun y _ => (integrable_step _).const_mul _)]
  simp_rw [integral_finsetSum _ (fun y _ => (integrable_step _).const_mul _),integral_const_mul]
  simp only [integral_step _ (le_min (ha _) (hb _)),energy]

lemma energy_cross (p a b : P → ℝ) (ha : ∀ x, 0≤a x) (hb : ∀ x, 0≤b x) :
    2*energy p a b ≤ energy p a a+energy p b b := by
  rw [energy_integral p a b ha hb,energy_integral p a a ha ha,energy_integral p b b hb hb]
  rw [← integral_const_mul,← integral_add (integrable_tail_product p a a) (integrable_tail_product p b b)]
  apply integral_mono ((integrable_tail_product p a b).const_mul 2)
    ((integrable_tail_product p a a).add (integrable_tail_product p b b))
  intro r
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (tail p a r-tail p b r)]

lemma min_add_four (a b c d : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
    min (a+b) (c+d) ≤ min a c+min a d+min b c+min b d := by
  simp only [min_def]
  split_ifs <;> linarith

lemma energy_sum (p a b : P → ℝ) (hp : ∀ x, 0≤p x) (ha : ∀ x, 0≤a x) (hb : ∀ x, 0≤b x) :
    energy p (a+b) (a+b) ≤ 2*(energy p a a+energy p b b) := by
  have hh : energy p (a+b) (a+b) ≤ energy p a a+energy p a b+energy p b a+energy p b b := by
    unfold energy
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    have h := mul_le_mul_of_nonneg_left (min_add_four (a x) (b x) (a y) (b y) (ha x) (hb x) (ha y) (hb y))
      (mul_nonneg (hp x) (hp y))
    simpa only [Pi.add_apply,mul_add] using h
  nlinarith [energy_cross p a b ha hb,energy_cross p b a hb ha]
end WeakPinned.MinKernel

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
open scoped BigOperators
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma integrable_outside_product (hn : 2 ≤ Fintype.card P) (x y : P) :
    Integrable (fun r => d.outsideIndicator r x*d.outsideIndicator r y) := by
  rw [d.outside_product hn x y,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma outsideMass_square (p : P → ℝ) (r : ℝ) :
    (d.outsideMass p r)^2 = ∑ x, ∑ y, p x*p y*(d.outsideIndicator r x*d.outsideIndicator r y) := by
  unfold outsideMass
  rw [pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma iid_min_potential (hn : 2 ≤ Fintype.card P) (p : P → ℝ) :
    MinKernel.energy p d.potential d.potential = ∫ r, (d.outsideMass p r)^2 := by
  simp only [d.outsideMass_square]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ fun y _ => (d.integrable_outside_product hn x y).const_mul _)]
  simp_rw [integral_finsetSum _ (fun y _ => (d.integrable_outside_product hn _ y).const_mul _),integral_const_mul]
  simp only [MinKernel.energy,d.min_potential hn]

/-- The source min-potential upper bound before averaging places and grids. -/

theorem iid_min_two_potentials (d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ x, 0≤p x) :
    (∑ x, ∑ y, p x*p y*min (d.potential x+d'.potential x) (d.potential y+d'.potential y)) ≤
      2*((∫ r, (d.outsideMass p r)^2)+(∫ r, (d'.outsideMass p r)^2)) := by
  rw [← d.iid_min_potential hn p,← d'.iid_min_potential hn p]
  exact MinKernel.energy_sum p d.potential d'.potential hp d.potential_nonneg d'.potential_nonneg
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory Variance
open scoped BigOperators
variable {P : Type u6} {I : Type u7} [Fintype P] [DecidableEq P] [Fintype I]
variable (d : Depth P)

lemma outsideMass_prob (B : Finset P) {r : ℝ} {G : Finset P} (hG : G∈d.giants r) :
    d.outsideMass (prob B) r=cellProb B Gᶜ := by
  have hne : (d.giants r).Nonempty := ⟨G,hG⟩
  have he (x) : prob B x*d.outsideIndicator r x=if x∈Gᶜ then prob B x else 0 := by
    simp only [outsideIndicator,hne,d.giant_eq hG,true_and]
    by_cases hx : x∈G <;> simp [hx]
  simp only [outsideMass,he,Finset.sum_ite_mem,Finset.univ_inter,sum_prob_cell]

lemma outsideMass_zero (p : P → ℝ) {r : ℝ} (hG : ¬(d.giants r).Nonempty) : d.outsideMass p r=0 := by
  simp [outsideMass,outsideIndicator,hG]

lemma sumCells_nonneg (f : Finset P → ℝ) (hf : ∀ C, 0≤f C) (r : ℝ) : 0≤d.sumCells f r := by
  rw [d.sumCells_count]
  exact Finset.sum_nonneg (fun C _ => mul_nonneg (by unfold count; positivity) (hf C))

lemma complement_le_sumCells (f : Finset P → ℝ) (hf : ∀ C, 0≤f C) {r : ℝ} {G : Finset P}
    (hG : G∈d.giants r) : f Gᶜ≤d.sumCells f r := by
  have hs : d.giants r={G} := Finset.ext fun C => by
    simp only [Finset.mem_singleton]
    exact ⟨fun hC => d.giants_unique hC hG,fun h => h ▸ hG⟩
  rw [d.sumCells_split,hs,Finset.sum_singleton]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun C _ => by split_ifs <;> simp_all only [le_refl]))

lemma outside_square_bound (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) (r : ℝ) :
    (∑ i, w i*(d.outsideMass (prob (B i)) r)^2) ≤
      d.sumCells (fun C => 2*varianceCell w B T C+4*pairCell Finset.univ C) r +
      κ*M*d.outsideMass (prob Finset.univ) r := by
  have hf (C : Finset P) : 0≤2*varianceCell w B T C+4*pairCell Finset.univ C :=
    add_nonneg (mul_nonneg (by norm_num) (varianceCell_nonneg w B T hw C))
      (mul_nonneg (by norm_num) (pairCell_nonneg _ _))
  by_cases hg : (d.giants r).Nonempty
  · obtain ⟨G,hG⟩ := hg
    simp_rw [d.outsideMass_prob _ hG]
    exact (cell_second_moment w B T M κ hw hW hT hκ hk hdom Gᶜ).trans
      (add_le_add (d.complement_le_sumCells _ hf hG) le_rfl)
  · simp only [d.outsideMass_zero _ hg,zero_pow (by norm_num : 2≠0),mul_zero,Finset.sum_const_zero,add_zero]
    exact d.sumCells_nonneg _ hf r

lemma integrable_outsideMass_square (hn : 2≤Fintype.card P) (p : P → ℝ) :
    Integrable (fun r => (d.outsideMass p r)^2) := by
  simp only [d.outsideMass_square]
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (d.integrable_outside_product hn x y).const_mul _

lemma integral_outsideMass (hn : 2≤Fintype.card P) (p : P → ℝ) :
    (∫ r, d.outsideMass p r)=∑ x, p x*d.potential x := by
  simp only [outsideMass]
  rw [integral_finsetSum _ (fun x _ => (d.integrable_outsideIndicator hn x).const_mul _)]
  simp only [integral_const_mul,potential]

/-- The integrable complement second moment estimate. All singleton terms
are charged to the finite potential, not integrated as constant errors. -/
theorem integrated_outside_square (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) :
    (∑ i, w i*(∫ r, (d.outsideMass (prob (B i)) r)^2)) ≤
      2*weightedIntegral d.mass (varianceCell w B T) +
      4*weightedIntegral d.mass (pairCell Finset.univ) +
      κ*M*(∑ x, prob Finset.univ x*d.potential x) := by
  let f := fun C => 2*varianceCell w B T C+4*pairCell Finset.univ C
  have hf : ∀ C, C.card≤1 → f C=0 := by
    intro C hC
    simp [f,varianceCell_singleton w B T hT hB C hC,singleton_pairCell Finset.univ C hC]
  have hi₁ : Integrable (fun r => ∑ i, w i*(d.outsideMass (prob (B i)) r)^2) :=
    integrable_finsetSum _ (fun i _ => (d.integrable_outsideMass_square hn _).const_mul _)
  have hi₂ : Integrable (fun r => d.sumCells f r) := d.integrable_sumCells hn f hf
  have hi₃ : Integrable (fun r => κ*M*d.outsideMass (prob Finset.univ) r) :=
    (integrable_finsetSum _ (fun x _ => (d.integrable_outsideIndicator hn x).const_mul _)).const_mul _
  have hh := integral_mono hi₁ (hi₂.add hi₃) (d.outside_square_bound w B T M κ hw hW hT hκ hk hdom)
  simp only [Pi.add_apply] at hh
  rw [integral_finsetSum _ (fun i _ => (d.integrable_outsideMass_square hn _).const_mul _),
    integral_add hi₂ hi₃,integral_const_mul,d.integral_outsideMass hn _,d.integral_sumCells hn f hf] at hh
  try simp only [integral_const_mul] at hh
  have he : (∑ C, d.mass C*f C)=
      2*weightedIntegral d.mass (varianceCell w B T)+4*weightedIntegral d.mass (pairCell Finset.univ) := by
    simp only [weightedIntegral,f,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl; intro C _; ring
    · apply Finset.sum_congr rfl; intro C _; ring
  rwa [he] at hh

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.MinKernel
open scoped BigOperators
variable {P : Type u8} [Fintype P]

/-- A fiber whose potential is a constant plus nonnegative overlap and a
small signed grid error has a large iid minimum. This preserves self-pairs
in the sampling, exactly as in the unbounded-scale argument. -/
lemma energy_lower (p S L E : P → ℝ) (c : ℝ)
    (hp : ∀ x, 0≤p x) (hsum : (∑ x, p x)=1)
    (hL : ∀ x, 0≤L x)
    (hS : ∀ x, p x≠0 → S x=c+L x-E x) :
    (∑ x, p x*S x)-(∑ x, p x*L x)-(∑ x, p x*|E x|)≤energy p S S := by
  have hpair (x y : P) :
      p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2) ≤
        p x*p y*min (S x) (S y) := by
    by_cases hx : p x=0
    · simp [hx]
    by_cases hy : p y=0
    · simp [hy]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hp x) (hp y))
    have hxS := hS x hx
    have hyS := hS y hy
    apply le_min <;> linarith [hL x,hL y,le_abs_self (E x),le_abs_self (E y),neg_abs_le (E x),neg_abs_le (E y)]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hpair x y))
  change _≤energy p S S at hh
  have he : (∑ x, ∑ y, p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2))=
      (∑ x, p x*S x)-(∑ x, p x*L x)-(∑ x, p x*|E x|) := by
    have hform (x y : P) : p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2)=
        (p x*S x)*p y/2+p x*(p y*S y)/2-
        ((p x*L x)*p y/2+p x*(p y*L y)/2+(p x*|E x|)*p y/2+p x*(p y*|E y|)/2) := by ring
    simp_rw [hform,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_div,
      ← Finset.mul_sum,← Finset.sum_mul,hsum,mul_one,one_mul]
    ring
  rwa [he] at hh
end WeakPinned.MinKernel

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory Variance
open scoped BigOperators
variable {P : Type u9} {I : Type u10} [Fintype P] [DecidableEq P] [Fintype I]

lemma min_upper_family (d d' : Depth P) (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) :
    (∑ i, w i*MinKernel.energy (prob (B i)) (d.potential+d'.potential) (d.potential+d'.potential)) ≤
      4*(weightedIntegral d.mass (varianceCell w B T)+weightedIntegral d'.mass (varianceCell w B T))+
      8*(weightedIntegral d.mass (pairCell Finset.univ)+weightedIntegral d'.mass (pairCell Finset.univ))+
      2*κ*M*(∑ x, prob Finset.univ x*(d.potential x+d'.potential x)) := by
  have hm (i) := d.iid_min_two_potentials d' hn (prob (B i))
    (fun x => by unfold prob; split_ifs <;> positivity)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (hm i) (hw i))
  change (∑ i, w i*MinKernel.energy (prob (B i)) (d.potential+d'.potential) (d.potential+d'.potential))≤_ at hsum
  have h₁ := d.integrated_outside_square hn w B T M κ hw hW hT hκ hB hk hdom
  have h₂ := d'.integrated_outside_square hn w B T M κ hw hW hT hκ hB hk hdom
  have hr : (∑ i, w i*(2*((∫ r, (d.outsideMass (prob (B i)) r)^2)+
      (∫ r, (d'.outsideMass (prob (B i)) r)^2))))=
      2*((∑ i, w i*(∫ r, (d.outsideMass (prob (B i)) r)^2))+
      (∑ i, w i*(∫ r, (d'.outsideMass (prob (B i)) r)^2))) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hr] at hsum
  simp only [mul_add,Finset.sum_add_distrib]
  linarith

lemma local_potential_fiber_bound (d d' : Depth P) (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (src : I → P) (t : I → ℝ) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hsrc : ∀ i, src i∉B i)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) :
    (∑ i, w i*∑ y, prob (B i) y*(d.potential y+d'.potential y)) ≤
      4*(weightedIntegral d.mass (varianceCell w B T)+weightedIntegral d'.mass (varianceCell w B T))+
      8*(weightedIntegral d.mass (pairCell Finset.univ)+weightedIntegral d'.mass (pairCell Finset.univ))+
      2*κ*M*(∑ x, prob Finset.univ x*(d.potential x+d'.potential x))+
      (∑ i, w i*∑ y, prob (B i) y*(weightedOverlap d.mass (src i) y+weightedOverlap d'.mass (src i) y))+
      (∑ i, w i*∑ y, prob (B i) y*|d.value (src i) y+d'.value (src i) y-t i|) := by
  have hp (i : I) (y : P) : 0≤prob (B i) y := by unfold prob; split_ifs <;> positivity
  have hL (dd : Depth P) (x y : P) : 0≤weightedOverlap dd.mass x y := by
    apply Finset.sum_nonneg; intro C _
    exact mul_nonneg (dd.mass_nonneg C) (by dsimp; split_ifs <;> norm_num)
  have hs (i : I) (y : P) (hy : prob (B i) y≠0) : y∈B i := by
    by_contra hh; exact hy (by simp [prob,hh])
  have hv (dd : Depth P) (i : I) (y : P) (hy : prob (B i) y≠0) :
      weightedOverlap dd.mass (src i) y=dd.overlapLength (src i) y (fun he => hsrc i (he ▸ hs i y hy)) :=
    dd.mass_overlap hn _ _ _
  have he (i : I) := MinKernel.energy_lower (prob (B i))
    (d.potential+d'.potential)
    (fun y => weightedOverlap d.mass (src i) y+weightedOverlap d'.mass (src i) y)
    (fun y => d.value (src i) y+d'.value (src i) y-t i)
    (d.M+d'.M-d.potential (src i)-d'.potential (src i)-t i)
    (hp i) (sum_prob (B i) (Finset.card_pos.mp (by have := hB i; omega)))
    (fun y => add_nonneg (hL d _ _) (hL d' _ _)) (by
      intro y hy
      have hxy : src i≠y := fun h => hsrc i (h ▸ hs i y hy)
      have hx := d.depth_identity hn (src i) y hxy
      have hx' := d'.depth_identity hn (src i) y hxy
      rw [hv d i y hy,hv d' i y hy]
      simp only [Pi.add_apply]
      linarith)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (he i) (hw i))
  have hu := min_upper_family d d' hn w B T M κ hw hW hT hκ hB hk hdom
  simp only [Pi.add_apply,mul_sub,Finset.sum_sub_distrib] at hh
  linarith

end WeakPinned.Hierarchy.Depth
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.GlobalPotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

lemma average_mono {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g)
    (hfg : ∀ d d', f d d'≤g d d') :
    average Z₁ Z₂ h₁ h₂ f≤average Z₁ Z₂ h₁ h₂ g  := by
  classical
  apply add_le_add
  · apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (integral_mono (hi v) (hj v) (fun ω => hfg _ _))
      (Arithmetic.archWeight_nonneg v)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun v _ => hfg _ _)

lemma average_add {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => f d d'+g d d')=
      average Z₁ Z₂ h₁ h₂ f+average Z₁ Z₂ h₁ h₂ g  := by
  classical
  unfold average
  simp only [integral_add (hi _) (hj _),mul_add,Finset.sum_add_distrib]
  ring

lemma average_mul (f : Depth P → Depth P → ℝ) (c : ℝ) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => c*f d d')=c*average Z₁ Z₂ h₁ h₂ f  := by
  classical
  unfold average
  simp only [integral_const_mul,Finset.mul_sum,mul_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro v _ <;> ring

lemma average_sum {J : Type u3} [Fintype J] (f : J → Depth P → Depth P → ℝ)
    (hi : ∀ j, AverageIntegrable Z₁ Z₂ (f j)) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => ∑ j, f j d d')=
      ∑ j, average Z₁ Z₂ h₁ h₂ (f j)  := by
  classical
  unfold average
  simp_rw [integral_finsetSum _ (fun j _ => hi j _),Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_comm (s:=placeUnion Z₁ Z₂ h₁ h₂)]
  simp only [Finset.sum_add_distrib]

lemma average_potential_left (hn : 2≤Fintype.card P) (x : P) :
    average Z₁ Z₂ h₁ h₂ (fun d _ => d.potential x)=S Z₁ h₁ x  := by
  classical
  unfold average S
  congr 2
  exact sum_finite_potential h₁ hn _ Finset.subset_union_left x

lemma average_potential_right (hn : 2≤Fintype.card P) (x : P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d' => d'.potential x)=S Z₂ h₂ x  := by
  classical
  unfold average S
  congr 2
  exact sum_finite_potential h₂ hn _ Finset.subset_union_right x

lemma average_mass_left (hn : 2≤Fintype.card P) (C : Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun d _ => d.mass C)=cellMass Z₁ h₁ C  := by
  classical
  unfold average cellMass
  congr 2
  exact sum_finite_mass h₁ hn _ Finset.subset_union_left C

lemma average_mass_right (hn : 2≤Fintype.card P) (C : Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d' => d'.mass C)=cellMass Z₂ h₂ C  := by
  classical
  unfold average cellMass
  congr 2
  exact sum_finite_mass h₂ hn _ Finset.subset_union_right C

omit [NumberField K] in
include h₁ in
lemma integrable_potential_left (hn : 2≤Fintype.card P) (x : P) :
    AverageIntegrable Z₁ Z₂ (fun d _ => d.potential x) :=
  fun v => Depth.integrable_potential_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn x

omit [NumberField K] in
include h₂ in
lemma integrable_potential_right (hn : 2≤Fintype.card P) (x : P) :
    AverageIntegrable Z₁ Z₂ (fun _ d' => d'.potential x) :=
  fun v => Depth.integrable_potential_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn x

omit [NumberField K] in
include h₁ in
lemma integrable_mass_left (hn : 2≤Fintype.card P) (C : Finset P) :
    AverageIntegrable Z₁ Z₂ (fun d _ => d.mass C) :=
  fun v => Depth.integrable_mass_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn C

omit [NumberField K] in
include h₂ in
lemma integrable_mass_right (hn : 2≤Fintype.card P) (C : Finset P) :
    AverageIntegrable Z₁ Z₂ (fun _ d' => d'.mass C) :=
  fun v => Depth.integrable_mass_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn C

end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable {K : Type u5} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit [NumberField K] in
include h₁ h₂ in
lemma integrable_potentialEval (hn : 2≤Fintype.card P) (p : P → ℝ) :
    AverageIntegrable Z₁ Z₂ (potentialEval p) := by
  intro v
  exact integrable_finsetSum (s:=Finset.univ) (fun y _ =>
    ((integrable_potential_left Z₁ Z₂ h₁ hn y v).add
      (integrable_potential_right Z₁ Z₂ h₂ hn y v)).const_mul (p y))

omit [NumberField K] in
include h₁ h₂ in
lemma integrable_massEval (hn : 2≤Fintype.card P) (q : Finset P → ℝ) :
    AverageIntegrable Z₁ Z₂ (massEval q) := by
  intro v
  exact (integrable_finsetSum (s:=Finset.univ) (fun C _ =>
      (integrable_mass_left Z₁ Z₂ h₁ hn C v).mul_const (q C))).add
    (integrable_finsetSum (s:=Finset.univ) (fun C _ =>
      (integrable_mass_right Z₁ Z₂ h₂ hn C v).mul_const (q C)))

lemma average_potentialEval (hn : 2≤Fintype.card P) (p : P → ℝ) :
    average Z₁ Z₂ h₁ h₂ (potentialEval p)=∑ y, p y*totalPotential Z₁ Z₂ h₁ h₂ y := by
  unfold potentialEval
  rw [average_sum Z₁ Z₂ h₁ h₂ _ (fun y v =>
    ((integrable_potential_left Z₁ Z₂ h₁ hn y v).add
      (integrable_potential_right Z₁ Z₂ h₂ hn y v)).const_mul (p y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [average_mul,average_add Z₁ Z₂ h₁ h₂
    (integrable_potential_left Z₁ Z₂ h₁ hn y) (integrable_potential_right Z₁ Z₂ h₂ hn y),
    average_potential_left Z₁ Z₂ h₁ h₂ hn,average_potential_right Z₁ Z₂ h₁ h₂ hn]
  rfl

lemma average_massEval (hn : 2≤Fintype.card P) (q : Finset P → ℝ) :
    average Z₁ Z₂ h₁ h₂ (massEval q)=weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) q := by
  have he : massEval q=(fun d d' => ∑ C, q C*(d.mass C+d'.mass C)) := by
    funext d d'
    simp only [massEval,weightedIntegral,mul_add,Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> ring
  rw [he,average_sum Z₁ Z₂ h₁ h₂ _ (fun C v =>
    ((integrable_mass_left Z₁ Z₂ h₁ hn C v).add
      (integrable_mass_right Z₁ Z₂ h₂ hn C v)).const_mul (q C))]
  apply Finset.sum_congr rfl
  intro C _
  rw [average_mul,average_add Z₁ Z₂ h₁ h₂
    (integrable_mass_left Z₁ Z₂ h₁ hn C) (integrable_mass_right Z₁ Z₂ h₂ hn C),
    average_mass_left Z₁ Z₂ h₁ h₂ hn,average_mass_right Z₁ Z₂ h₁ h₂ hn]
  simp only [totalMass]; ring

omit Z₁ Z₂ h₁ h₂ in
lemma massEval_edge {I : Type u6} [Fintype I] (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (d d' : Depth P) :
    massEval (SmallFiber.edgeCell w p x) d d'=
      ∑ i, w i*∑ y, p i y*(weightedOverlap d.mass (x i) y+weightedOverlap d'.mass (x i) y) := by
  have he (m : Finset P → ℝ) : weightedIntegral m (SmallFiber.edgeCell w p x)=
      ∑ i, w i*∑ y, p i y*weightedOverlap m (x i) y := by
    unfold SmallFiber.edgeCell
    rw [weighted_pair]
    unfold SmallFiber.edgeLaw
    simp only [Finset.sum_mul]
    calc
      _ = ∑ a, ∑ i, ∑ y, (if x i=a then w i*p i y else 0)*weightedOverlap m a y := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ y, (if x i=a then w i*p i y else 0)*weightedOverlap m a y := Finset.sum_comm
      _ = _ := by
        simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
        simp [Finset.mul_sum,mul_assoc]
  -- commute the source sum after inserting the indicator
  simp only [massEval,he,mul_add,Finset.sum_add_distrib]
end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u7} {I : Type u8} [Fintype P] [DecidableEq P] [Fintype I]
variable {K : Type u9} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
lemma potentialEval_mixture (w : I → ℝ) (p : I → P → ℝ) (d d' : Depth P) :
    potentialEval (fun y => ∑ i, w i*p i y) d d'=∑ i, w i*∑ y, p i y*(d.potential y+d'.potential y) := by
  simp only [potentialEval,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

lemma average_sub {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => f d d'-g d d')=
      average Z₁ Z₂ h₁ h₂ f-average Z₁ Z₂ h₁ h₂ g := by
  classical
  unfold average
  simp only [integral_sub (hi _) (hj _),mul_sub,Finset.sum_sub_distrib]
  ring

/-- The first-moment raw-depth error is archimedean only. Its global constant
is independent of the degree and all coordinates. -/
lemma arithmetic_potential_fiber_bound (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (src : I → P) (t : I → K) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)=1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hsrc : ∀ i, src i∉B i)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x)
    (ht : ∀ i y, y∈B i → (Z₁ (src i)-Z₁ y)*(Z₂ (src i)-Z₂ y)=t i) :
    (∑ y, (∑ i, w i*prob (B i) y)*totalPotential Z₁ Z₂ h₁ h₂ y) ≤
      4*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (varianceCell w B T)+
      8*overlapScale Z₁ Z₂ h₁ h₂+
      2*κ*M*potentialScale Z₁ Z₂ h₁ h₂+
      weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (SmallFiber.edgeCell w (fun i => prob (B i)) src)+16 := by
  classical
  let p : I → P → ℝ := fun i => prob (B i)
  let r : P → ℝ := fun y => ∑ i, w i*p i y
  let q := SmallFiber.edgeCell w p src
  let vcell := varianceCell w B T
  let pc := pairCell (Finset.univ : Finset P)
  let unif := prob (Finset.univ : Finset P)
  let R : Depth P → Depth P → ℝ := fun d d' =>
    4*massEval vcell d d'+8*massEval pc d d'+2*κ*M*potentialEval unif d d'+massEval q d d'
  let f : Depth P → Depth P → ℝ := fun d d' => potentialEval r d d'-R d d'
  have hp (i y) : 0≤p i y := by dsimp [p,prob]; split_ifs <;> positivity
  have hp1 (i) : ∑ y, p i y=1 := sum_prob (B i) (Finset.card_pos.mp (by have := hB i; omega))
  have hx (i) : p i (src i)=0 := by simp [p,prob,hsrc i]
  have ht' (i y) (hy : p i y≠0) : (Z₁ (src i)-Z₁ y)*(Z₂ (src i)-Z₂ y)=t i := by
    apply ht i y
    by_contra hn'; exact hy (by simp [p,prob,hn'])
  have hL := integrable_potentialEval Z₁ Z₂ h₁ h₂ hn r
  have hV := integrable_massEval Z₁ Z₂ h₁ h₂ hn vcell
  have hP := integrable_massEval Z₁ Z₂ h₁ h₂ hn pc
  have hA := integrable_potentialEval Z₁ Z₂ h₁ h₂ hn unif
  have hQ := integrable_massEval Z₁ Z₂ h₁ h₂ hn q
  have hR : AverageIntegrable Z₁ Z₂ R := fun v =>
    ((((hV v).const_mul 4).add ((hP v).const_mul 8)).add ((hA v).const_mul (2*κ*M))).add (hQ v)
  have hf : AverageIntegrable Z₁ Z₂ f := fun v => (hL v).sub (hR v)
  have hb (d d' : Depth P) (a : I → ℝ) :
      f d d'≤∑ i, w i*∑ y, p i y*|d.value (src i) y+d'.value (src i) y-a i| := by
    have hh := d.local_potential_fiber_bound d' hn w B src a T M κ hw hW.le hT hκ hB hk hsrc hdom
    rw [← potentialEval_mixture,← massEval_edge] at hh
    change potentialEval r d d'≤R d d'+_ at hh
    exact sub_le_iff_le_add'.mpr hh
  have ha (v : NumberField.InfinitePlace K) :
      (∫ ω, f (arch Z₁ v ω) (arch Z₂ v ω) ∂Grid.fullLaw)≤16 := by
    let E : Grid.FullSample → ℝ := fun ω => ∑ i, w i*∑ y, p i y*
      |(arch Z₁ v ω).value (src i) y+(arch Z₂ v ω).value (src i) y+Real.log (v (t i))|
    have hi : Integrable E Grid.fullLaw := integrable_finsetSum (s:=Finset.univ) (fun i _ =>
      (integrable_finsetSum (s:=Finset.univ) (fun y _ =>
        ((((arch_integrable Z₁ h₁ v _ _).add (arch_integrable Z₂ h₂ v _ _)).add
          (integrable_const _)).abs.const_mul (p i y)))).const_mul (w i))
    have hu : (∫ ω, E ω ∂Grid.fullLaw)≤16 := by
      simpa only [E,sub_zero,max_eq_left (abs_nonneg (_ : ℝ)),neg_zero,zero_div,Real.exp_zero,mul_one]
        using arch_weighted_defect Z₁ Z₂ h₁ h₂ v w p src t hw hW hp hp1 hx ht' 0 (by norm_num)
    exact (integral_mono (hf v) hi (fun ω => by
      simpa only [sub_neg_eq_add] using hb (arch Z₁ v ω) (arch Z₂ v ω) (fun i => -Real.log (v (t i))))).trans hu
  have hv (v : NumberField.FinitePlace K) : f (finite Z₁ h₁ v) (finite Z₂ h₂ v)≤0 := by
    have he (i y) : p i y*|(finite Z₁ h₁ v).value (src i) y+
        (finite Z₂ h₂ v).value (src i) y-(-Real.log (v (t i)))|=0 := by
      by_cases hy : p i y=0
      · simp [hy]
      · have hxy : src i≠y := by intro hh; exact hsrc i (hh ▸ (by
          by_contra hm; exact hy (by simp [p,prob,hm])))
        have hh := Arithmetic.raw_fiber_identity v.val (Z₁ (src i)-Z₁ y) (Z₂ (src i)-Z₂ y)
          (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
        rw [ht' i y hy] at hh
        change -Real.log (v (Z₁ (src i)-Z₁ y)) + -Real.log (v (Z₂ (src i)-Z₂ y)) = -Real.log (v (t i)) at hh
        simp only [finite,ite_eq_right hxy,hh,sub_self,abs_zero,mul_zero]
    simpa only [he,Finset.sum_const_zero,mul_zero] using
      hb (finite Z₁ h₁ v) (finite Z₂ h₂ v) (fun i => -Real.log (v (t i)))
  have hg : average Z₁ Z₂ h₁ h₂ f≤16 := by
    change placeAverage (placeUnion Z₁ Z₂ h₁ h₂) _ _≤16
    have hh := placeAverage_mono (placeUnion Z₁ Z₂ h₁ h₂) ha (fun v _ => hv v)
    rwa [placeAverage_arch_const] at hh
  have hRe : average Z₁ Z₂ h₁ h₂ R =
      4*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) vcell+
      8*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) pc+
      2*κ*M*(∑ y, unif y*totalPotential Z₁ Z₂ h₁ h₂ y)+
      weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) q := by
    unfold R
    rw [average_add Z₁ Z₂ h₁ h₂ (fun v => (((hV v).const_mul 4).add ((hP v).const_mul 8)).add ((hA v).const_mul (2*κ*M))) hQ,
      average_add Z₁ Z₂ h₁ h₂ (fun v => ((hV v).const_mul 4).add ((hP v).const_mul 8)) (fun v => (hA v).const_mul (2*κ*M)),
      average_add Z₁ Z₂ h₁ h₂ (fun v => (hV v).const_mul 4) (fun v => (hP v).const_mul 8)]
    simp only [average_mul,average_massEval Z₁ Z₂ h₁ h₂ hn,average_potentialEval Z₁ Z₂ h₁ h₂ hn]
  change average Z₁ Z₂ h₁ h₂ (fun d d' => potentialEval r d d'-R d d')≤16 at hg
  rw [average_sub Z₁ Z₂ h₁ h₂ hL hR,average_potentialEval Z₁ Z₂ h₁ h₂ hn,hRe] at hg
  exact sub_le_iff_le_add'.mp hg
end WeakPinned.Global

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u10} [Fintype P] [DecidableEq P]

/-- Nonnegative additive off-diagonal overlap controls the potential at every
vertex, not merely at vertices typical for the edge marginal. -/
lemma point_potential_lower (m : Finset P → ℝ) (b : ℝ) (S : P → ℝ)
    (hm : ∀ C : Finset P, (0 : ℝ) ≤ m C) (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y)
    (hn : 3≤Fintype.card P) (x : P) :
    (∑ y, prob Finset.univ y*S y)-2*weightedIntegral m (pairCell Finset.univ)≤S x := by
  let n : ℝ := Fintype.card P
  have hn3 : 3≤n := by dsimp [n]; exact_mod_cast hn
  have hn0 : n≠0 := by linarith
  let A : ℝ := (∑ y, prob Finset.univ y*S y)
  let W : ℝ := weightedIntegral m (pairCell Finset.univ)
  have hW : 0≤W := Finset.sum_nonneg (fun C _ => mul_nonneg (hm C) (pairCell_nonneg _ _))
  have hu : W=b+2*A := uniform_additive m b S hL (by omega)
  have hs : (∑ y, S y)=n*A := by
    dsimp [A,prob,n]
    simp only [Finset.mem_univ,ite_true]
    rw [← Finset.mul_sum]
    have hn0' : (Fintype.card P : ℝ) ≠ 0 := hn0
    field_simp
  have hnn : 0 ≤ ∑ y ∈ Finset.univ.erase x, (b+S x+S y) := by
    apply Finset.sum_nonneg
    intro y hy
    rw [← hL x y (Finset.ne_of_mem_erase hy).symm]
    exact Finset.sum_nonneg (fun C _ => mul_nonneg (hm C) (by dsimp; split_ifs <;> norm_num))
  have hsx : (∑ y ∈ Finset.univ.erase x, S y)=(∑ y, S y)-S x := by
    exact eq_sub_of_add_eq (Finset.sum_erase_add Finset.univ S (Finset.mem_univ x))
  have hcount : ((Finset.univ.erase x).card:ℝ)=n-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,Nat.cast_sub (by omega),Nat.cast_one]
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hcount,hsx,hs] at hnn
  change A-2*W≤S x
  nlinarith [mul_nonneg (by linarith : 0≤n-3) hW]

end WeakPinned.Variance

namespace WeakPinned
open Global Variance
open scoped BigOperators
variable {P : Type u11} {I : Type u12} [Fintype P] [Fintype I] [DecidableEq P]
variable {K : Type u13} [Field K] [NumberField K]

/-- Quantitative scale balance for arithmetic fibers, without an unboundedness assumption. -/

theorem arithmetic_scale_balance (G : Core.Fibers P I)
    (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
    (hn : 3≤Fintype.card P) (hG : 0<G.edgeCount)
    (T M κ : ℝ) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(G.targets i).card) (hk : ∀ i, 2/((G.targets i).card:ℝ)≤κ)
    (hdom : ∀ x y, G.edgeLaw x y≤M*pairProb Finset.univ x y)
    (t : I → K) (ht : ∀ i y, y∈G.targets i →
      (Z₁ (G.source i)-Z₁ y)*(Z₂ (G.source i)-Z₂ y)=t i) :
    (1-2*κ*M)*potentialScale Z₁ Z₂ h₁ h₂ ≤
      4*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (varianceCell G.fiberWeight G.targets T)+
      (10+M)*overlapScale Z₁ Z₂ h₁ h₂+16 := by
  have hn2 : 2≤Fintype.card P := by omega
  have hh := arithmetic_potential_fiber_bound Z₁ Z₂ h₁ h₂ hn2 G.fiberWeight G.targets G.source t T M κ
    G.fiberWeight_nonneg (G.sum_fiberWeight hG) hT hκ hB hk G.no_loop
    (G.fiber_domination M hdom hn2) ht
  let m := totalMass Z₁ Z₂ h₁ h₂
  let S := totalPotential Z₁ Z₂ h₁ h₂
  let r : P → ℝ := fun y => ∑ i, G.fiberWeight i*prob (G.targets i) y
  have hr0 (y) : 0≤r y := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (G.fiberWeight_nonneg i)
    unfold prob; split_ifs <;> positivity
  have hr1 : ∑ y, r y=1 := by
    dsimp [r]
    rw [Finset.sum_comm]
    have hp1 (i : I) : ∑ y, prob (G.targets i) y=1 :=
      sum_prob (G.targets i) (Finset.card_pos.mp (by have := hB i; omega))
    simp_rw [← Finset.mul_sum,hp1,mul_one]
    exact G.sum_fiberWeight hG
  have hl : potentialScale Z₁ Z₂ h₁ h₂-2*overlapScale Z₁ Z₂ h₁ h₂≤∑ y, r y*S y := by
    have hlo (y) := point_potential_lower m (baseConstant Z₁ Z₂ h₁ h₂) S
      (totalMass_nonneg Z₁ Z₂ h₁ h₂) (totalMass_overlap Z₁ Z₂ h₁ h₂ hn2) hn y
    have hu := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => mul_le_mul_of_nonneg_left (hlo y) (hr0 y))
    simpa only [← Finset.sum_mul,hr1,one_mul,potentialScale,overlapScale,m,S] using hu
  have he : SmallFiber.edgeCell G.fiberWeight (fun i => prob (G.targets i)) G.source=G.qCell := by
    funext C; exact (G.qCell_eq C).symm
  have hq : weightedIntegral m G.qCell≤M*overlapScale Z₁ Z₂ h₁ h₂ := by
    simp only [weightedIntegral,Finset.mul_sum,overlapScale]
    calc
      _ ≤ ∑ C, m C*(M*pairCell Finset.univ C) := Finset.sum_le_sum (fun C _ =>
        mul_le_mul_of_nonneg_left (G.qCell_bound hdom C) (totalMass_nonneg Z₁ Z₂ h₁ h₂ C))
      _ = _ := by apply Finset.sum_congr rfl; intro C _; dsimp [m]; ring
  rw [he] at hh
  change (∑ y, r y*S y)≤_ at hh
  change weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) G.qCell≤_ at hq
  nlinarith
end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

/-- Elementary absorption of the two asymptotically small errors. -/
lemma scale_balance_rate (W A V δ : ℕ → ℝ) (B : ℝ) (hB : 0≤B)
    (hW : ∀ j, 0≤W j) (hA : ∀ j, 0≤A j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hV : Tendsto (fun j => V j/(W j+A j+1)) atTop (𝓝 0))
    (hbal : ∀ᶠ j in atTop, (1-δ j)*A j≤4*V j+(10+B)*W j+16) :
    ∀ᶠ j in atTop, A j≤(64+4*B)*(W j+1) := by
  filter_upwards [hbal,hδ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4)),
    hV.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/16))] with j hb hd hv
  have hden : 0<W j+A j+1 := by linarith [hW j,hA j]
  have hv' := (div_lt_iff₀ hden).mp hv
  nlinarith [hW j,hA j,mul_nonneg (hW j) hB]
end WeakPinned

namespace WeakPinned
open Global Variance Filter
open scoped Topology BigOperators
variable {V : ℕ → Type u14} {I : ℕ → Type u15} {K : ℕ → Type u16} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

theorem arithmetic_scale_comparison (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y ∈ (G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    ∀ᶠ j in atTop, potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) ≤
      (64+8/θ)*(overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1) := by
  let n : ℕ → ℝ := fun j => Fintype.card (V j)
  let κ : ℕ → ℝ := fun j => 2/(n j)^γ
  have hnγ : Tendsto (fun j => (n j)^γ) atTop atTop := (tendsto_rpow_atTop hγ).comp hn
  have hκ : Tendsto κ atTop (𝓝 0) := by
    simpa only [κ,div_eq_mul_inv,mul_zero,Function.comp_def] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnγ)
  have hv := (sampling_variance_rates G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht).1
  have hs := scale_balance_rate
    (fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
    (fun j => potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
    (fiberVariance G c Z₁ Z₂ h₁ h₂) (fun j => 2*κ j*(2/θ)) (2/θ) (by positivity)
    (fun j => overlapScale_nonneg _ _ _ _) (fun j => potentialScale_nonneg _ _ _ _)
    (by simpa using (tendsto_const_nhds.mul hκ).mul_const (2/θ)) hv
  have hb : ∀ᶠ j in atTop,
      (1-2*κ j*(2/θ))*potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) ≤
      4*fiberVariance G c Z₁ Z₂ h₁ h₂ j+(10+2/θ)*overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+16 := by
    filter_upwards [hn.eventually (eventually_ge_atTop (3:ℝ)),hnγ.eventually (eventually_ge_atTop (2:ℝ))] with j hj hjγ
    have hn3 : 3≤Fintype.card (V j) := by exact_mod_cast hj
    have hne : 0<(G j).edgeCount := (hG j).edgeCount_pos (by linarith [hηb j])
    have hn0 : 0<n j := by change (0:ℝ)<Fintype.card (V j); linarith
    have hBk (i) : (n j)^γ≤((G j).targets i).card := (hG j).fiber i |>.le
    have hBk2 (i) : 2≤((G j).targets i).card := by exact_mod_cast hjγ.trans (hBk i)
    have hk (i) : 2/(((G j).targets i).card:ℝ)≤κ j :=
      div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hn0 _) (hBk i)
    have hT : 1≤(n j)^(1-c) := Real.one_le_rpow (by linarith) (by linarith)
    exact arithmetic_scale_balance (G j) (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) hn3 hne
      ((n j)^(1-c)) (2/θ) (κ j) hT (by dsimp [κ]; positivity) hBk2 hk
      ((hG j).uniform_domination hθ (hηb j)) (t j) (ht j)
  have hh := hs hb
  convert hh using 1; ring_nf
end WeakPinned

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.CutApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section

namespace WeakPinned.Cuts
open scoped BigOperators

lemma tent_nonneg (δ u : ℝ) : 0≤tent δ u := le_max_left _ _
lemma tent_symm (δ u : ℝ) : tent δ (1-u)=tent δ u := by
  unfold tent
  rw [show 1-u-δ=1-δ-u by ring,show 1-δ-(1-u)=u-δ by ring,min_comm]
lemma tent_zero_left {δ u : ℝ} (hu : u≤δ) : tent δ u=0 := by
  unfold tent
  exact max_eq_left ((min_le_left _ _).trans (sub_nonpos.mpr hu))
lemma tent_zero_right {δ u : ℝ} (hu : 1-δ≤u) : tent δ u=0 := by
  rw [← tent_symm]
  exact tent_zero_left (by linarith)
lemma tent_le_one {δ u : ℝ} (hδ : 0≤δ) (hu : u≤1) : tent δ u≤1 := by
  exact max_le (by norm_num) ((min_le_left _ _).trans (by linarith))
lemma tent_lipschitz (δ u v : ℝ) : |tent δ u-tent δ v|≤|u-v| := by
  have hm := abs_max_sub_max_le_max (0:ℝ) (min (u-δ) (1-δ-u)) 0 (min (v-δ) (1-δ-v))
  have hn := abs_min_sub_min_le_max (u-δ) (1-δ-u) (v-δ) (1-δ-v)
  have he : 1-δ-u-(1-δ-v)=-(u-v) := by ring
  have hf : u-δ-(v-δ)=u-v := by ring
  simp only [he,hf,abs_neg,max_self] at hn
  exact hm.trans (max_le (by simp [abs_nonneg]) hn)
lemma tent_positive {δ u : ℝ} (hu : 0<tent δ u) : δ<u ∧ u<1-δ := by
  have h : 0 < min (u-δ) (1-δ-u) := (lt_max_iff.mp hu).resolve_left (lt_irrefl _)
  have := lt_min_iff.mp h
  constructor <;> linarith
lemma cutError_nonneg (δ p a : ℝ) : 0≤cutError δ p a :=
  add_nonneg (abs_nonneg _) (mul_nonneg (tent_nonneg _ _) (abs_nonneg _))
lemma cutError_symm (δ p a : ℝ) : cutError δ (1-p) (1-a)=cutError δ p a := by
  simp only [cutError,tent_symm,show 1-p-(1-a)=-(p-a) by ring,abs_neg]
lemma cutError_le {δ p a : ℝ} (hδ : 0≤δ) (ha : a≤1) : cutError δ p a≤2*|p-a| := by
  have := tent_lipschitz δ p a
  have := mul_le_mul_of_nonneg_right (tent_le_one hδ ha) (abs_nonneg (p-a))
  unfold cutError
  linarith
lemma cutError_young {δ p a ε : ℝ} (hδ : 0≤δ) (ha : a≤1) (hε : 0<ε) :
    cutError δ p a≤ε+(p-a)^2/ε := by
  apply (cutError_le hδ ha).trans
  apply (mul_le_mul_iff_left₀ hε).mp
  have he : (ε+(p-a)^2/ε)*ε=ε^2+(p-a)^2 := by field_simp
  rw [he]
  nlinarith [sq_nonneg (|p-a|-ε),sq_abs (p-a)]

/-- Tiny uniform cells have nonzero balanced-cut weight only if their sampled
mass is separated from zero. The variance quadratic then pays the cut error. -/
lemma cutError_tiny {δ p a : ℝ} (hδ : 0<δ) (ha : a<δ/2) (hp : p≤1) :
    cutError δ p a≤(4/δ^2)*(p-a)^2 ∧ cutError δ p a≤(4/δ^2)*(p^2/2) := by
  have hz : tent δ a=0 := tent_zero_left (by linarith)
  rw [cutError,hz,sub_zero,abs_of_nonneg (tent_nonneg _ _),zero_mul,add_zero]
  by_cases hh : tent δ p=0
  · rw [hh]; constructor <;> positivity
  · have ht : 0<tent δ p := lt_of_le_of_ne (tent_nonneg _ _) (Ne.symm hh)
    have hpd := (tent_positive ht).1
    have ht1 := tent_le_one hδ.le hp
    have hd2 : 0<δ^2 := sq_pos_of_pos hδ
    constructor
    · apply ht1.trans
      apply (mul_le_mul_iff_left₀ hd2).mp
      have he : ((4/δ^2)*(p-a)^2)*δ^2=4*(p-a)^2 := by field_simp
      rw [he]
      nlinarith [sq_nonneg (p-a-δ/2),mul_nonneg (by linarith : 0≤p-a-δ/2) hδ.le]
    · apply ht1.trans
      apply (mul_le_mul_iff_left₀ hd2).mp
      have he : ((4/δ^2)*(p^2/2))*δ^2=2*p^2 := by field_simp; ring
      rw [he]
      nlinarith [sq_nonneg (p-δ),mul_nonneg (by linarith : 0≤p-δ) hδ.le]
end WeakPinned.Cuts

namespace WeakPinned.Variance
open scoped BigOperators
open Cuts
variable {P : Type u1} {I : Type u2} [Fintype P] [Fintype I] [DecidableEq P]

lemma familyCutError_bound (w : I → ℝ) (B : I → Finset P) (T δ ε : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hδ : 0<δ) (hε : 0<ε)
    (hk : ∀ i, 2/((B i).card:ℝ)≤δ) (C : Finset P)
    (hlarge : δ/2≤cellProb Finset.univ C → T<C.card)
    (hpair : δ/2≤cellProb Finset.univ C → 1≤(8/δ^2)*pairCell Finset.univ C) :
    familyCutError w B δ C≤(8*ε/δ^2)*pairCell Finset.univ C+
      (1/ε+4/δ^2)*varianceCell w B T C := by
  have hv : 0≤varianceCell w B T C := varianceCell_nonneg w B T hw C
  by_cases ha : δ/2≤cellProb Finset.univ C
  · have he := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (cutError_young (p:=cellProb (B i) C) hδ.le (cellProb_le_one (Finset.univ : Finset P) C) hε) (hw i))
    change familyCutError w B δ C≤_ at he
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,← mul_div_assoc,← Finset.sum_div] at he
    have hvf : varianceCell w B T C=∑ i, w i*(cellProb (B i) C-cellProb Finset.univ C)^2 := by
      simp only [varianceCell,ite_eq_left (hlarge ha)]
    rw [← hvf] at he
    have he2 : (∑ i, w i)*ε≤ε := by nlinarith
    have he3 : ε≤(8*ε/δ^2)*pairCell Finset.univ C := by
      have hh := mul_le_mul_of_nonneg_left (hpair ha) hε.le
      calc
        ε = ε*1 := by ring
        _ ≤ ε*((8/δ^2)*pairCell Finset.univ C) := hh
        _ = _ := by ring
    have hx : 0≤(4/δ^2)*varianceCell w B T C := mul_nonneg (by positivity) hv
    have hh : varianceCell w B T C/ε=(1/ε)*varianceCell w B T C := by ring
    rw [hh] at he
    nlinarith
  · have hat : cellProb Finset.univ C<δ/2 := lt_of_not_ge ha
    have hb : familyCutError w B δ C≤(4/δ^2)*varianceCell w B T C := by
      unfold familyCutError varianceCell
      split_ifs with hl
      · rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hh := (cutError_tiny hδ hat (cellProb_le_one (B i) C)).1
        have hm := mul_le_mul_of_nonneg_left hh (hw i)
        convert hm using 1; ring
      · simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        by_cases hpk : 2/((B i).card:ℝ)≤cellProb (B i) C
        · rw [ite_eq_left hpk]
          have hh := (cutError_tiny hδ hat (cellProb_le_one (B i) C)).2
          have hm := mul_le_mul_of_nonneg_left hh (hw i)
          convert hm using 1; ring
        · rw [ite_eq_right hpk]
          have hp : cellProb (B i) C≤δ := (le_of_lt (lt_of_not_ge hpk)).trans (hk i)
          simp only [cutError,tent_zero_left hp,tent_zero_left (show cellProb Finset.univ C≤δ by linarith),
            sub_self,abs_zero,zero_mul,add_zero,mul_zero]
          norm_num
    have hx : 0≤(8*ε/δ^2)*pairCell Finset.univ C := mul_nonneg (by positivity) (pairCell_nonneg _ _)
    have hy : 0≤(1/ε)*varianceCell w B T C := mul_nonneg (by positivity) hv
    nlinarith
end WeakPinned.Variance

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u3} {I : Type u4} [Fintype P] [Fintype I] [DecidableEq P]

lemma balanced_cell_size (δ : ℝ) (hδ : 0<δ) (hn : 4≤δ*(Fintype.card P:ℝ))
    (C : Finset P) (ha : δ/2≤cellProb Finset.univ C) : 2≤C.card := by
  have hn0 : (0:ℝ)<Fintype.card P := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hδ.le h
    linarith
  simp only [cellProb,Finset.univ_inter,Finset.card_univ] at ha
  have hh := (le_div_iff₀ hn0).mp ha
  exact_mod_cast (show (2:ℝ)≤C.card by nlinarith)

lemma balanced_cell_pair (δ : ℝ) (hδ : 0<δ) (hn : 4≤δ*(Fintype.card P:ℝ))
    (C : Finset P) (ha : δ/2≤cellProb Finset.univ C) :
    1≤(8/δ^2)*pairCell Finset.univ C := by
  have hpair := (uniform_pair_comparison C (balanced_cell_size δ hδ hn C ha)).1
  have han := cellProb_nonneg (Finset.univ : Finset P) C
  have hh : δ^2≤8*pairCell Finset.univ C := by nlinarith
  have he : (8/δ^2)*pairCell Finset.univ C=(8*pairCell Finset.univ C)/δ^2 := by ring
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by simpa using hh)

/-- Integrated approximation to balanced tree cuts, quantitatively, with no
selection of a realizing grid and no hidden count of occurrence multiplicities. -/
lemma weighted_cut_approximation (m : Finset P → ℝ) (hm : ∀ C, 0 ≤ m C)
    (w : I → ℝ) (B : I → Finset P) (T δ ε : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hδ : 0<δ) (hε : 0<ε)
    (hn : 4≤δ*(Fintype.card P:ℝ)) (hT : T<δ*(Fintype.card P:ℝ)/2)
    (hk : ∀ i, 2/((B i).card:ℝ)≤δ) :
    weightedIntegral m (familyCutError w B δ)≤
      (8*ε/δ^2)*weightedIntegral m (pairCell Finset.univ)+
      (1/ε+4/δ^2)*weightedIntegral m (varianceCell w B T) := by
  have hn0 : (0:ℝ)<Fintype.card P := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hδ.le h
    linarith
  have hpoint (C : Finset P) := familyCutError_bound w B T δ ε hw hW hδ hε hk C
    (fun ha => by
      simp only [cellProb,Finset.univ_inter,Finset.card_univ] at ha
      have hh := (le_div_iff₀ hn0).mp ha
      linarith) (balanced_cell_pair δ hδ hn C)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun C _ =>
    mul_le_mul_of_nonneg_left (hpoint C) (hm C))
  change weightedIntegral m (familyCutError w B δ)≤_ at hh
  convert hh using 1
  simp only [weightedIntegral,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> ring

end WeakPinned.Variance

namespace WeakPinned
open Filter
open scoped Topology

/-- A Young estimate for every fixed positive ε implies the required little-o
cut approximation. D is the actual (positive) overlap normalization. -/
lemma cut_approximation_rate (E V W D : ℕ → ℝ) (δ K : ℝ) (hδ : 0<δ) (hK : 0<K)
    (hE : ∀ j, 0≤E j) (hD : ∀ j, 0<D j)
    (hW : ∀ᶠ j in atTop, W j≤K*D j)
    (hV : Tendsto (fun j => V j/D j) atTop (𝓝 0))
    (hb : ∀ ε : ℝ, 0<ε → ∀ᶠ j in atTop,
      E j≤(8*ε/δ^2)*W j+(1/ε+4/δ^2)*V j) :
    Tendsto (fun j => E j/D j) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ζ hζ
  let ε : ℝ := ζ*δ^2/(32*K)
  have hε : 0<ε := by dsimp [ε]; positivity
  have heq : (8*ε/δ^2)*K=ζ/4 := by dsimp [ε]; field_simp; ring
  have hc : 0<1/ε+4/δ^2 := by positivity
  have hh : ∀ᶠ j in atTop, |(1/ε+4/δ^2)*(V j/D j)|<ζ/2 := by
    have hh0 : Tendsto (fun j => (1/ε+4/δ^2)*(V j/D j)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hV.const_mul (1/ε+4/δ^2)
    exact (hh0.eventually (Metric.ball_mem_nhds (0:ℝ) (half_pos hζ))).mono
      (fun j hj => by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hj)
  have hh' : ∀ᶠ j in atTop, |E j/D j-0|<ζ := by
    filter_upwards [hb ε hε,hW,hh] with j hj hjw hjv
    have hn := div_nonneg (hE j) (hD j).le
    rw [sub_zero,abs_of_nonneg hn]
    have hp := mul_le_mul_of_nonneg_left hjw (show 0≤8*ε/δ^2 by positivity)
    have hle : E j/D j≤(8*ε/δ^2)*K+(1/ε+4/δ^2)*(V j/D j) := by
      apply (div_le_iff₀ (hD j)).mpr
      have he : ((8*ε/δ^2)*K+(1/ε+4/δ^2)*(V j/D j))*D j =
        (8*ε/δ^2)*(K*D j)+(1/ε+4/δ^2)*V j := by field_simp [ne_of_gt (hD j)]
      rw [he]
      linarith
    rw [heq] at hle
    have := (le_abs_self _).trans_lt hjv
    linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh'
  exact ⟨N,fun j hj => by simpa only [Real.dist_eq] using hN j hj⟩
end WeakPinned

namespace WeakPinned
open Filter Variance Global
open scoped Topology BigOperators
variable {P : ℕ → Type u5} {I : ℕ → Type u6} [∀ j, Fintype (P j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (P j)]

lemma variance_to_cut_rate (m : ∀ j, Finset (P j) → ℝ) (hm : ∀ j C, 0 ≤ m j C)
    (w : ∀ j, I j → ℝ) (B : ∀ j, I j → Finset (P j)) (D : ℕ → ℝ) (γ c δ : ℝ)
    (hD : ∀ j, 0<D j) (hδ : 0<δ) (hγ : 0<γ) (hc : 0<c)
    (hn : Tendsto (fun j => (Fintype.card (P j):ℝ)) atTop atTop)
    (hw : ∀ j i, 0≤w j i) (hW : ∀ j, (∑ i, w j i)≤1)
    (hsize : ∀ j i, (Fintype.card (P j):ℝ)^γ≤((B j i).card:ℝ))
    (hWD : ∀ j, weightedIntegral (m j) (pairCell Finset.univ)≤D j)
    (hV : Tendsto (fun j => weightedIntegral (m j)
      (varianceCell (w j) (B j) ((Fintype.card (P j):ℝ)^(1-c)))/D j) atTop (𝓝 0)) :
    Tendsto (fun j => weightedIntegral (m j) (familyCutError (w j) (B j) δ)/D j) atTop (𝓝 0) := by
  let n := fun j => (Fintype.card (P j):ℝ)
  have hnγ : Tendsto (fun j => n j^γ) atTop atTop := (tendsto_rpow_atTop hγ).comp hn
  have hnc : Tendsto (fun j => n j^(-c)) atTop (𝓝 0) := (tendsto_rpow_neg_atTop hc).comp hn
  apply cut_approximation_rate _ _ (fun j => weightedIntegral (m j) (pairCell Finset.univ)) D δ 1 hδ (by norm_num)
    (fun j => Finset.sum_nonneg (fun C _ => mul_nonneg (hm j C)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hw j i) (Cuts.cutError_nonneg _ _ _))))) hD
    (Eventually.of_forall (fun j => by simpa using hWD j)) hV
  intro ε hε
  filter_upwards [hn.eventually (eventually_gt_atTop (4/δ)),
    hnγ.eventually (eventually_ge_atTop (2/δ)), hnc.eventually (gt_mem_nhds (half_pos hδ))] with j hj hjγ hjc
  have hn0 : 0<n j := (by positivity : 0<4/δ).trans hj
  have hnj : 4≤δ*n j := by
    have hh := (div_lt_iff₀ hδ).mp hj
    nlinarith
  have hT : n j^(1-c)<δ*n j/2 := by
    rw [sub_eq_add_neg,Real.rpow_add hn0,Real.rpow_one]
    nlinarith
  have hk (i) : 2/((B j i).card:ℝ)≤δ := by
    have hbs : 0<((B j i).card:ℝ) := (Real.rpow_pos_of_pos hn0 γ).trans_le (hsize j i)
    apply (div_le_iff₀ hbs).mpr
    have hh := (div_le_iff₀ hδ).mp (hjγ.trans (hsize j i))
    nlinarith
  exact weighted_cut_approximation (m j) (hm j) (w j) (B j) (n j^(1-c)) δ ε
    (hw j) (hW j) hδ hε hnj hT hk

end WeakPinned

namespace WeakPinned
open Filter Variance Global
open scoped Topology BigOperators
variable {V : ℕ → Type u7} {I : ℕ → Type u8} {K : ℕ → Type u9} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

/-- Cut approximation for both sampling families, normalized by W₂+A+1
    and hence by W in the unbounded regime. -/
theorem sampling_cut_approximation_rates (δ : ℝ) (hδ : 0<δ) (hθ : 0<θ)
    (hγ : 0<γ) (hγ1 : γ<1) (hc : 0<c) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y ∈ (G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    Tendsto (fun j => weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
        (familyCutError (G j).fiberWeight (G j).targets δ)/
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) ∧
    Tendsto (fun j => weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
        (familyCutError ((G j).retainedWeight ((Fintype.card (V j):ℝ)^γ))
          ((G j).retainedSet ((Fintype.card (V j):ℝ)^γ)) δ)/
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) := by
  have hv := sampling_variance_rates G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  let m := fun j => totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let D := fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1
  have hD (j) : 0<D j := by dsimp [D]; linarith [overlapScale_nonneg (Z₁ j) (Z₂ j) (h₁ j) (h₂ j),potentialScale_nonneg (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)]
  have hWD (j) : weightedIntegral (m j) (pairCell Finset.univ)≤D j := by
    change overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)≤_
    dsimp [D]
    linarith [potentialScale_nonneg (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)]
  have hpos (j) : 0<(G j).edgeCount := (hG j).edgeCount_pos (by linarith [hηb j])
  constructor
  · exact variance_to_cut_rate m (fun j => totalMass_nonneg _ _ _ _)
      (fun j => (G j).fiberWeight) (fun j => (G j).targets) D γ c δ hD hδ hγ hc hn
      (fun j => (G j).fiberWeight_nonneg) (fun j => ((G j).sum_fiberWeight (hpos j)).le)
      (fun j i => ((hG j).fiber i).le) hWD hv.1
  · apply variance_to_cut_rate m (fun j => totalMass_nonneg _ _ _ _)
      (fun j => (G j).retainedWeight ((Fintype.card (V j):ℝ)^γ))
      (fun j => (G j).retainedSet ((Fintype.card (V j):ℝ)^γ)) D γ c δ hD hδ hγ hc hn
      (fun j => (G j).retainedWeight_nonneg _) (fun j => (G j).sum_retainedWeight _ (hpos j)) _ hWD hv.2
    intro j y
    apply (G j).retainedSet_size
    have hn1 : (1:ℝ)≤Fintype.card (V j) := by exact_mod_cast (by have := (hG j).card_ge; omega : 1≤Fintype.card (V j))
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hγ1.le
end WeakPinned

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.TreeTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section

/- Finite tree transport by laminar-cut telescoping, without optimal-coupling selection. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Cuts
variable {P : Type u1} [Fintype P] [DecidableEq P]

omit [Fintype P] in
lemma laminar_erase {s : Finset (Finset P)} (hs : Laminar s) (C : Finset P) : Laminar (s.erase C) :=
  fun _ hA _ hB => hs _ (Finset.mem_of_mem_erase hA) _ (Finset.mem_of_mem_erase hB)

omit [Fintype P] in
lemma minimal_constant {s : Finset (Finset P)} (hs : Laminar s)
    (C : Finset P) (hC : C ∈ s) (hmin : ∀ D ∈ s, C.card ≤ D.card)
    (d : Finset P → ℝ) (a : ℝ) :
    ∀ x ∈ C, value (s.erase C) d a x = a+∑ D ∈ s.erase C, if C ⊆ D then d D else 0 := by
  intro x hx
  unfold value
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  have hDs := Finset.mem_of_mem_erase hD
  have hDC : D ≠ C := (Finset.mem_erase.mp hD).1
  have hnot : ¬D ⊆ C := by
    intro hh
    exact hDC (Finset.eq_of_subset_of_card_le hh (hmin D hDs))
  by_cases hCD : C ⊆ D
  · simp [hCD,hCD hx]
  · have hd : Disjoint C D := (hs C hC D hDs).resolve_left hCD |>.resolve_left hnot
    have hxD : x ∉ D := fun hxD => Finset.disjoint_left.mp hd hx hxD
    simp [hCD,hxD]

omit [Fintype P] in
lemma value_erase {s : Finset (Finset P)} (C : Finset P) (hC : C ∈ s)
    (d : Finset P → ℝ) (a : ℝ) (x : P) :
    value s d a x = value (s.erase C) d a x + (if x ∈ C then d C else 0) := by
  unfold value
  rw [← Finset.add_sum_erase _ _ hC]
  ring

/-- Dual tree transport with completely explicit cut cost. The signed measure
    b has total mass zero. Neither nonnegativity nor coupling existence is needed. -/
lemma signed_lipschitz_bound (s : Finset (Finset P)) (hs : Laminar s)
    (b : P → ℝ) (hb : ∑ x, b x=0) (d : Finset P → ℝ) (a : ℝ)
    (g : ℝ → ℝ) (hg : ∀ u v, |g u-g v| ≤ |u-v|) :
    |∑ x, b x*g (value s d a x)| ≤ ∑ C ∈ s, |d C| * |mass b C| := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hsn : s.Nonempty
    · obtain ⟨C,hC,hmin⟩ := Finset.exists_min_image s Finset.card hsn
      let q := a+∑ D ∈ s.erase C, if C ⊆ D then d D else 0
      let Δ := g (q+d C)-g q
      have hΔ : |Δ| ≤ |d C| := by
        simpa only [Δ,add_sub_cancel_left] using hg (q+d C) q
      have he (x : P) : g (value s d a x) =
          g (value (s.erase C) d a x)+(if x ∈ C then Δ else 0) := by
        rw [value_erase C hC]
        by_cases hx : x ∈ C
        · rw [ite_eq_left hx,ite_eq_left hx,minimal_constant hs C hC hmin d a x hx]
          dsimp only [Δ,q]
          ring
        · simp [hx]
      have hi := ih (s.erase C) (Finset.erase_ssubset hC) (laminar_erase hs C)
      have he' : (∑ x, b x*g (value s d a x)) =
          (∑ x, b x*g (value (s.erase C) d a x))+Δ*mass b C := by
        simp_rw [he,mul_add,Finset.sum_add_distrib]
        congr 1
        simp only [mul_ite,mul_zero,mass,Finset.mul_sum]
        simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      rw [he',← Finset.add_sum_erase _ _ hC]
      calc
        _ ≤ |∑ x, b x*g (value (s.erase C) d a x)|+|Δ*mass b C| := abs_add_le _ _
        _ ≤ (∑ D ∈ s.erase C, |d D| * |mass b D|)+|d C| * |mass b C| := by
          apply add_le_add hi
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)
        _ = _ := by ring
    · have hs0 := Finset.not_nonempty_iff_eq_empty.mp hsn
      simp only [hs0,value,Finset.sum_empty,add_zero,← Finset.sum_mul,hb,zero_mul,abs_zero,le_refl]

omit [Fintype P] in
lemma distance_symm (s : Finset (Finset P)) (l : Finset P → ℝ) (x y : P) :
    distance s l x y=distance s l y x := by
  simp only [distance,abs_sub_comm]

omit [Fintype P] in
lemma distance_nonneg (s : Finset (Finset P)) (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C)
    (x y : P) : 0 ≤ distance s l x y :=
  Finset.sum_nonneg (fun C hC => mul_nonneg (hl C hC) (abs_nonneg _))

omit [Fintype P] in
lemma distance_as_value (s : Finset (Finset P)) (l : Finset P → ℝ) (x y : P) :
    distance s l x y=value s (coeff l y) (rootDistance s l y) x := by
  simp only [distance,value,rootDistance,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> simp [ind,coeff,hx,hy]

omit [Fintype P] in
lemma abs_coeff (l : Finset P → ℝ) (y : P) (C : Finset P) (hC : 0 ≤ l C) :
    |coeff l y C|=l C := by
  unfold coeff
  split_ifs <;> simp [abs_of_nonneg hC]

lemma function_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p q : P → ℝ)
    (hpq : ∑ x, p x=∑ x, q x) (y : P) (g : ℝ → ℝ)
    (hg : ∀ u v, |g u-g v| ≤ |u-v|) :
    |(∑ x, p x*g (distance s l x y))-(∑ x, q x*g (distance s l x y))| ≤ cost s l p q := by
  have hb : (∑ x, (p x-q x))=0 := by rw [Finset.sum_sub_distrib,hpq,sub_self]
  have hh := signed_lipschitz_bound s hs (fun x => p x-q x) hb (coeff l y) (rootDistance s l y) g hg
  simp only [← distance_as_value,sub_mul,Finset.sum_sub_distrib,mass] at hh
  simp only [cost,mass]
  convert hh using 1
  exact Finset.sum_congr rfl (fun C hC => by rw [abs_coeff l y C (hl C hC)])

lemma first_fluctuation_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p q : P → ℝ)
    (hpq : ∑ x, p x=∑ x, q x) (x' y : P) :
    |(∑ x, p x*|distance s l x y-distance s l x' y|)-
      (∑ x, q x*|distance s l x y-distance s l x' y|)| ≤ cost s l p q := by
  apply function_transfer s hs l hl p q hpq y (fun u => |u-distance s l x' y|)
  intro u v
  simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le_abs_sub (u-distance s l x' y) (v-distance s l x' y)

omit [Fintype P] in
lemma value_sub (s : Finset (Finset P)) (d e : Finset P → ℝ) (a b : ℝ) (x : P) :
    value s d a x-value s e b x=value s (fun C => d C-e C) (a-b) x := by
  simp only [value]
  have he : (∑ C ∈ s, if x ∈ C then d C-e C else 0) =
      (∑ C ∈ s, if x ∈ C then d C else 0)-(∑ C ∈ s, if x ∈ C then e C else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun C _ => by split_ifs <;> ring)
  rw [he]
  ring

lemma last_fluctuation_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p q : P → ℝ)
    (hpq : ∑ x, p x=∑ x, q x) (x x' : P) :
    |(∑ y, p y*|distance s l x y-distance s l x' y|)-
      (∑ y, q y*|distance s l x y-distance s l x' y|)| ≤ 2*cost s l p q := by
  have hb : (∑ y, (p y-q y))=0 := by rw [Finset.sum_sub_distrib,hpq,sub_self]
  have hh := signed_lipschitz_bound s hs (fun y => p y-q y) hb
    (fun C => coeff l x C-coeff l x' C) (rootDistance s l x-rootDistance s l x') abs abs_abs_sub_abs_le_abs_sub
  have he (y : P) : value s (fun C => coeff l x C-coeff l x' C) (rootDistance s l x-rootDistance s l x') y =
      distance s l x y-distance s l x' y := by
    rw [← value_sub,← distance_as_value,← distance_as_value,distance_symm s l y x,distance_symm s l y x']
  simp only [he,sub_mul,Finset.sum_sub_distrib,mass] at hh
  refine hh.trans ?_
  simp only [cost,mass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C hC
  have hc : |coeff l x C-coeff l x' C| ≤ 2*l C := by
    calc
      _ ≤ |coeff l x C|+|coeff l x' C| := abs_sub _ _
      _ = _ := by rw [abs_coeff l x C (hl C hC),abs_coeff l x' C (hl C hC)]; ring
  calc
    _ ≤ (2*l C)*|∑ y ∈ C, p y-∑ y ∈ C, q y| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ = _ := by ring

omit [Fintype P] [DecidableEq P] in
lemma mass_nonneg (p : P → ℝ) (hp : ∀ x, 0 ≤ p x) (C : Finset P) : 0 ≤ mass p C :=
  Finset.sum_nonneg (fun x _ => hp x)

lemma expected_cut (p : P → ℝ) (hp : ∑ x, p x=1) (C : Finset P) (y : P) :
    (∑ x, p x*|ind C x-ind C y|) = if y ∈ C then 1-mass p C else mass p C := by
  by_cases hy : y ∈ C
  · have he (x : P) : p x*|ind C x-ind C y|=p x-(if x ∈ C then p x else 0) := by
      by_cases hx : x ∈ C <;> simp [ind,hx,hy]
    simp_rw [he]
    simp only [Finset.sum_sub_distrib,hp,← Finset.sum_filter,
      Finset.filter_mem_eq_inter,Finset.univ_inter,ite_eq_left hy,mass]
  · have he (x : P) : p x*|ind C x-ind C y|=if x ∈ C then p x else 0 := by
      by_cases hx : x ∈ C <;> simp [ind,hx,hy]
    simp_rw [he]
    simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,ite_eq_right hy,mass]

lemma expected_distance_ge (s : Finset (Finset P)) (l : Finset P → ℝ)
    (hl : ∀ C ∈ s, 0 ≤ l C) (p : P → ℝ) (hp : ∑ x, p x=1) (η : ℝ)
    (hbal : ∀ C ∈ s, 0 < l C → η ≤ mass p C ∧ η ≤ 1-mass p C) (y : P) :
    η*(∑ C ∈ s, l C) ≤ ∑ x, p x*distance s l x y := by
  simp only [distance,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro C hC
  have he : (∑ x, p x*(l C*|ind C x-ind C y|)) =
      l C*(∑ x, p x*|ind C x-ind C y|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [he,expected_cut p hp]
  by_cases hpos : 0 < l C
  · rcases hbal C hC hpos with ⟨h1,h2⟩
    have hh : η ≤ if y ∈ C then 1-mass p C else mass p C := by split_ifs <;> assumption
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh (hl C hC)
  · have hz : l C=0 := le_antisymm (le_of_not_gt hpos) (hl C hC)
    simp [hz]

omit [Fintype P] in
lemma exists_zero_cell (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C)
    (hn : (s.filter (fun C => 0 < l C)).Nonempty) :
    ∃ C ∈ s, 0 < l C ∧ ∀ x ∈ C, ∀ y ∈ C, distance s l x y=0 := by
  obtain ⟨C,hC,hmin⟩ := Finset.exists_min_image (s.filter (fun C => 0 < l C)) Finset.card hn
  rcases Finset.mem_filter.mp hC with ⟨hCs,hCl⟩
  refine ⟨C,hCs,hCl,?_⟩
  intro x hx y hy
  unfold distance
  apply Finset.sum_eq_zero
  intro D hD
  by_cases hd : 0 < l D
  · have hcD : C.card ≤ D.card := hmin D (Finset.mem_filter.mpr ⟨hD,hd⟩)
    rcases hs C hCs D hD with hCD | hDC | hdis
    · simp [ind,hCD hx,hCD hy]
    · have he : C=D := (Finset.eq_of_subset_of_card_le hDC hcD).symm
      simp [ind,← he,hx,hy]
    · have hxD : x ∉ D := fun h => Finset.disjoint_left.mp hdis hx h
      have hyD : y ∉ D := fun h => Finset.disjoint_left.mp hdis hy h
      simp [ind,hxD,hyD]
  · have hz : l D=0 := le_antisymm (le_of_not_gt hd) (hl D hD)
    simp [hz]

/-- A minimal positive cut collapses a set of mass at least η to a single
    pseudometric point. This gives a direct fluctuation bound without
    constructing a tree graph. -/
lemma fluctuation_lower (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p : P → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x=1) (η : ℝ) (hη : 0 ≤ η)
    (hbal : ∀ C ∈ s, 0 < l C → η ≤ mass p C ∧ η ≤ 1-mass p C) :
    η^3*(∑ C ∈ s, l C) ≤
      ∑ y, p y*∑ x', p x'*∑ x, p x*|distance s l x y-distance s l x' y| := by
  let L := ∑ C ∈ s, l C
  have hL : 0 ≤ L := Finset.sum_nonneg hl
  have hf0 (y x' : P) : 0 ≤ ∑ x, p x*|distance s l x y-distance s l x' y| :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hp0 x) (abs_nonneg _))
  by_cases hn : (s.filter (fun C => 0 < l C)).Nonempty
  · obtain ⟨C,hC,hCl,hzero⟩ := exists_zero_cell s hs l hl hn
    have hm : η ≤ mass p C := (hbal C hC hCl).1
    have hc0 := mass_nonneg p hp0 C
    have hy (y : P) (hy : y ∈ C) : mass p C*(η*L) ≤
        ∑ x', p x'*∑ x, p x*|distance s l x y-distance s l x' y| := by
      calc
        _ = ∑ x' ∈ C, p x'*(η*L) := by simp only [mass,Finset.sum_mul]
        _ ≤ ∑ x' ∈ C, p x'*∑ x, p x*|distance s l x y-distance s l x' y| := by
          apply Finset.sum_le_sum
          intro x' hx'
          apply mul_le_mul_of_nonneg_left _ (hp0 x')
          simp only [hzero x' hx' y hy,sub_zero,abs_of_nonneg (distance_nonneg s l hl _ _)]
          exact expected_distance_ge s l hl p hp η hbal y
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
          (fun x' _ _ => mul_nonneg (hp0 x') (hf0 y x'))
    calc
      _ ≤ mass p C*(mass p C*(η*L)) := by
        have hsq : η*η ≤ mass p C*mass p C := mul_le_mul hm hm hη hc0
        have hmL := mul_le_mul_of_nonneg_right hsq (mul_nonneg hη hL)
        dsimp only [L] at hmL
        nlinarith only [hmL]
      _ = ∑ y ∈ C, p y*(mass p C*(η*L)) := by simp only [mass,Finset.sum_mul]
      _ ≤ ∑ y ∈ C, p y*∑ x', p x'*∑ x, p x*|distance s l x y-distance s l x' y| :=
        Finset.sum_le_sum (fun y hyC => mul_le_mul_of_nonneg_left (hy y hyC) (hp0 y))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        (fun y _ _ => mul_nonneg (hp0 y) (Finset.sum_nonneg (fun x' _ => mul_nonneg (hp0 x') (hf0 y x'))))
  · have hz : ∑ C ∈ s, l C=0 := by
      apply Finset.sum_eq_zero
      intro C hC
      have hnot : ¬0 < l C := fun hc => hn ⟨C,Finset.mem_filter.mpr ⟨hC,hc⟩⟩
      exact le_antisymm (le_of_not_gt hnot) (hl C hC)
    rw [hz,mul_zero]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hp0 y)
      (Finset.sum_nonneg (fun x' _ => mul_nonneg (hp0 x') (hf0 y x'))))

omit [Fintype P] [DecidableEq P] in
lemma cost_symm (s : Finset (Finset P)) (l : Finset P → ℝ) (p q : P → ℝ) :
    cost s l p q=cost s l q p := by simp only [cost,abs_sub_comm]

omit [Fintype P] in
lemma fluctuation_symm (s : Finset (Finset P)) (l : Finset P → ℝ) (x x' y : P) :
    fluctuation s l x x' y=fluctuation s l x' x y := abs_sub_comm _ _

lemma sum_le_add_of_abs {a b c : ℝ} (h : |a-b| ≤ c) : a ≤ b+c :=
  by have := (abs_le.mp h).2; linarith

lemma doubleMean_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (p q : P → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp : ∑ x, p x=1) (hq : ∑ x, q x=1) (y : P) :
    doubleMean s l p y ≤ doubleMean s l q y+2*cost s l p q := by
  have h1 (x' : P) : (∑ x, p x*fluctuation s l x x' y) ≤
      (∑ x, q x*fluctuation s l x x' y)+cost s l p q :=
    sum_le_add_of_abs (first_fluctuation_transfer s hs l hl p q (hp.trans hq.symm) x' y)
  have h2 (x : P) : (∑ x', p x'*fluctuation s l x x' y) ≤
      (∑ x', q x'*fluctuation s l x x' y)+cost s l p q := by
    simpa only [fluctuation,abs_sub_comm] using
      sum_le_add_of_abs (first_fluctuation_transfer s hs l hl p q (hp.trans hq.symm) x y)
  calc
    _ ≤ ∑ x', p x'*((∑ x, q x*fluctuation s l x x' y)+cost s l p q) :=
      Finset.sum_le_sum (fun x' _ => mul_le_mul_of_nonneg_left (h1 x') (hp0 x'))
    _ = (∑ x, q x*∑ x', p x'*fluctuation s l x x' y)+cost s l p q := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul]
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => by ring))
    _ ≤ (∑ x, q x*((∑ x', q x'*fluctuation s l x x' y)+cost s l p q))+cost s l p q := by
      exact add_le_add (Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h2 x) (hq0 x))) le_rfl
    _ = doubleMean s l q y+2*cost s l p q := by
      simp only [doubleMean,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hq,one_mul]
      rw [show (∑ x, q x*∑ x', q x'*fluctuation s l x x' y) =
          ∑ x, q x*∑ x', q x'*fluctuation s l x' x y from by simp_rw [fluctuation_symm s l _ _ y]]
      ring

lemma doubleMean_fiber (s : Finset (Finset P)) (l : Finset P → ℝ) (p : P → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x=1) (y : P) (R : ℝ) :
    doubleMean s l p y ≤ 2*∑ x, p x*|distance s l x y-R| := by
  have ht (x x' : P) : fluctuation s l x x' y ≤
      |distance s l x y-R|+|distance s l x' y-R| := by
    simpa only [fluctuation,abs_sub_comm (R : ℝ)] using abs_sub_le (distance s l x y) R (distance s l x' y)
  calc
    _ ≤ ∑ x', p x'*∑ x, p x*(|distance s l x y-R|+|distance s l x' y-R|) := by
      apply Finset.sum_le_sum
      intro x' _
      apply mul_le_mul_of_nonneg_left _ (hp0 x')
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (ht x x') (hp0 x))
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul]
      ring

lemma last_doubleMean_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (a p q : P → ℝ)
    (ha0 : ∀ x, 0 ≤ a x) (ha : ∑ x, a x=1) (hpq : ∑ x, p x=∑ x, q x) :
    (∑ y, p y*doubleMean s l a y) ≤
      (∑ y, q y*doubleMean s l a y)+2*cost s l p q := by
  have ht (x x' : P) : (∑ y, p y*fluctuation s l x x' y) ≤
      (∑ y, q y*fluctuation s l x x' y)+2*cost s l p q :=
    sum_le_add_of_abs (last_fluctuation_transfer s hs l hl p q hpq x x')
  have he (b : P → ℝ) : (∑ y, b y*doubleMean s l a y) =
      ∑ x', a x'*∑ x, a x*∑ y, b y*fluctuation s l x x' y := by
    simp only [doubleMean,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [he p,he q]
  calc
    _ ≤ ∑ x', a x'*∑ x, a x*((∑ y, q y*fluctuation s l x x' y)+2*cost s l p q) := by
      apply Finset.sum_le_sum
      intro x' _
      apply mul_le_mul_of_nonneg_left _ (ha0 x')
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (ht x x') (ha0 x))
    _ = _ := by simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,ha,one_mul]

/-- Finite transport to independent sampling with explicit cut costs. -/

lemma iid_transfer (s : Finset (Finset P)) (hs : Laminar s)
    (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0 ≤ l C) (a t : P → ℝ) (ρ : P → P → ℝ)
    (ha0 : ∀ x, 0 ≤ a x) (ht0 : ∀ y, 0 ≤ t y) (hρ0 : ∀ y x, 0 ≤ ρ y x)
    (ha : ∑ x, a x=1) (ht : ∑ y, t y=1) (hρ : ∀ y, ∑ x, ρ y x=1) (R : P → ℝ) :
    (∑ y, a y*doubleMean s l a y) ≤
      2*(∑ y, t y*∑ x, ρ y x*|distance s l x y-R y|)+
      2*(∑ y, t y*cost s l (ρ y) a)+2*cost s l t a := by
  have hlast := last_doubleMean_transfer s hs l hl a a t ha0 ha (ha.trans ht.symm)
  rw [cost_symm s l a t] at hlast
  have hy (y : P) : doubleMean s l a y ≤
      2*(∑ x, ρ y x*|distance s l x y-R y|)+2*cost s l (ρ y) a := by
    have h1 := doubleMean_transfer s hs l hl a (ρ y) ha0 (hρ0 y) ha (hρ y) y
    rw [cost_symm s l a (ρ y)] at h1
    exact h1.trans (add_le_add (doubleMean_fiber s l (ρ y) (hρ0 y) (hρ y) y (R y)) le_rfl)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ => mul_le_mul_of_nonneg_left (hy y) (ht0 y))
  have he : (∑ y, t y*(2*(∑ x, ρ y x*|distance s l x y-R y|)+2*cost s l (ρ y) a)) =
      2*(∑ y, t y*∑ x, ρ y x*|distance s l x y-R y|)+2*(∑ y, t y*cost s l (ρ y) a) := by
    simp only [mul_add,Finset.sum_add_distrib]
    rw [Finset.mul_sum,Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [he] at hsum
  linarith

end WeakPinned.Cuts

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.CutGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma mem_allCuts (C : Finset P) : C ∈ d.allCuts ↔ ∃ r : ℝ, C ∈ d.cells r := by
  classical
  simp [allCuts]

lemma cells_subset_allCuts (r : ℝ) : d.cells r ⊆ d.allCuts :=
  fun C hC => (d.mem_allCuts C).mpr ⟨r,hC⟩

lemma allCuts_laminar : Cuts.Laminar d.allCuts := by
  intro C hC B hB
  obtain ⟨r,hr⟩ := (d.mem_allCuts C).mp hC
  obtain ⟨t,ht⟩ := (d.mem_allCuts B).mp hB
  by_cases hi : Disjoint C B
  · exact Or.inr (Or.inr hi)
  · obtain ⟨x,hxC,hxB⟩ := Finset.not_disjoint_iff.mp hi
    rw [d.cell_of_mem hr hxC,d.cell_of_mem ht hxB]
    rcases le_total t r with h | h
    · exact Or.inl (d.cell_mono h x)
    · exact Or.inr (Or.inl (d.cell_mono h x))

lemma measurable_cutAt (f : Finset P → ℝ) (C : Finset P) : Measurable (d.cutAt f C) :=
  (measurable_of_finite (fun s : Finset (Finset P) => if C ∈ s then f C else 0)).comp d.measurable_cells

lemma cutAt_bound (f : Finset P → ℝ) (C : Finset P) (r : ℝ) : ‖d.cutAt f C r‖ ≤ |f C| := by
  unfold cutAt
  split_ifs <;> simp [Real.norm_eq_abs,abs_nonneg]

lemma cutAt_vanish (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (C : Finset P) (r : ℝ) (hr : r ∉ Set.Icc (-d.radius) d.radius) :
    d.cutAt f C r=0 := by
  unfold cutAt
  split_ifs with hc
  · obtain ⟨x,rfl⟩ := (d.mem_cells r C).mp hc
    rcases not_and_or.mp hr with hlo | hhi
    · rw [d.cell_of_low (le_of_lt (lt_of_not_ge hlo)),hfu]
    · rw [d.cell_of_high (lt_of_not_ge hhi),hfs]
  · rfl

lemma integrable_cutAt (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (C : Finset P) : Integrable (d.cutAt f C) := by
  exact integrable_supported_Icc (d.measurable_cutAt f C) (d.cutAt_bound f C)
    (d.cutAt_vanish f hfu hfs C)

lemma cutLength_nonneg (f : Finset P → ℝ) (hf : ∀ C, 0 ≤ f C) (C : Finset P) :
    0 ≤ d.cutLength f C := by
  apply integral_nonneg
  intro r
  unfold cutAt
  split_ifs
  · exact hf C
  · exact le_rfl

lemma cutLength_eq_zero (f : Finset P → ℝ) (C : Finset P) (hC : f C=0) :
    d.cutLength f C=0 := by simp [cutLength,cutAt,hC]

lemma cutLength_outside (f : Finset P → ℝ) (C : Finset P) (hC : C ∉ d.allCuts) :
    d.cutLength f C=0 := by
  have hh (r : ℝ) : C ∉ d.cells r := fun hc => hC ((d.mem_allCuts C).mpr ⟨r,hc⟩)
  simp [cutLength,cutAt,hh]

lemma integral_cut_sum (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (g : Finset P → ℝ) :
    (∫ r, ∑ C ∈ d.cells r, f C*g C) = ∑ C ∈ d.allCuts, d.cutLength f C*g C := by
  have he (r : ℝ) : (∑ C ∈ d.cells r, f C*g C) =
      ∑ C ∈ d.allCuts, d.cutAt f C r*g C := by
    simp only [cutAt,ite_mul,zero_mul,← Finset.sum_filter]
    congr 1
    ext C
    simp only [Finset.mem_filter]
    exact ⟨fun hc => ⟨d.cells_subset_allCuts r hc,hc⟩,fun hc => hc.2⟩
  simp only [he]
  rw [integral_finsetSum _ (fun C _ => (d.integrable_cutAt f hfu hfs C).mul_const (g C))]
  exact Finset.sum_congr rfl (fun C _ => by rw [integral_mul_const]; rfl)

lemma symmetric_integral_cut_sum (hn : 2 ≤ Fintype.card P) (f : Finset P → ℝ)
    (hfs : ∀ C, C.card ≤ 1 → f C=0) (hsym : ∀ C, f Cᶜ=f C) :
    (∑ C, d.mass C*f C) = ∑ C ∈ d.allCuts, d.cutLength f C := by
  have hu : f Finset.univ=0 := by simpa using (hsym ∅).trans (hfs ∅ (by simp))
  rw [← d.integral_sumCells hn f hfs]
  have he (r : ℝ) : d.sumCells f r=∑ C ∈ d.cells r, f C := by
    simp only [d.sumCells_formula,hsym,sub_self,Finset.sum_const_zero,add_zero]
  simp only [he]
  simpa using d.integral_cut_sum f hu (fun x => hfs {x} (by simp)) (fun _ => 1)

lemma cutLength_balanced (p : P → ℝ) (w : ℝ → ℝ) (η : ℝ)
    (hws : ∀ u, ¬(η ≤ u ∧ η ≤ 1-u) → w u=0) (C : Finset P)
    (hC : 0 < d.cutLength (fun B => w (Cuts.mass p B)) C) :
    η ≤ Cuts.mass p C ∧ η ≤ 1-Cuts.mass p C := by
  by_contra hn
  have hz := d.cutLength_eq_zero (fun B => w (Cuts.mass p B)) C (hws _ hn)
  linarith

lemma actual_cut_fluctuation (p : P → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x=1)
    (w : ℝ → ℝ) (hw : ∀ u, 0 ≤ w u) (η : ℝ) (hη : 0 ≤ η)
    (hws : ∀ u, ¬(η ≤ u ∧ η ≤ 1-u) → w u=0) :
    η^3*(∑ C ∈ d.allCuts, d.cutLength (fun B => w (Cuts.mass p B)) C) ≤
      ∑ y, p y*Cuts.doubleMean d.allCuts (d.cutLength (fun B => w (Cuts.mass p B))) p y := by
  exact Cuts.fluctuation_lower d.allCuts d.allCuts_laminar _
    (fun C _ => d.cutLength_nonneg _ (fun C => hw _) C) p hp0 hp η hη
    (fun C _ hC => d.cutLength_balanced p w η hws C hC)

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u2} [Fintype P] [DecidableEq P]
variable (d : Depth P)

omit [Fintype P] [DecidableEq P] in
lemma value_eq_of_lt (x y z : P) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hlt : d.value x y < d.value y z) : d.value x z=d.value x y := by
  have h1 := d.ultra x y z hxy hyz hxz
  rw [min_eq_left (le_of_lt hlt)] at h1
  apply le_antisymm _ h1
  by_contra! hn
  have h2 := d.ultra x z y hxz hyz.symm hxy
  rw [d.symm z y] at h2
  exact (lt_min hn hlt).not_ge h2

lemma differenceTail_pos (x y : P) (hxy : x ≠ y) (u : ℝ) (hu : 0 < u) :
    d.differenceTail x y u=d.cell (d.value x y+u) y := by
  ext z
  simp only [differenceTail,Finset.mem_filter,Finset.mem_univ,true_and,mem_cell,share]
  by_cases hzy : z=y
  · simp [hzy]
  by_cases hzx : z=x
  · subst z
    have hlt : ¬d.value x y+u ≤ d.value y x := by rw [d.symm y x]; linarith
    simp [hxy,hxy.symm,hlt]
  · simp only [hzx,ne_eq,false_or,not_false_eq_true,true_and,eq_comm (a:=y) (b:=z),hzy]
    constructor
    · intro h
      have hlt : d.value x z < d.value z y := by rw [d.symm z y]; linarith
      have he := d.value_eq_of_lt x z y (Ne.symm hzx) hzy hxy hlt
      linarith
    · intro h
      have hlt : d.value x y < d.value y z := by linarith
      rw [d.value_eq_of_lt x y z hxy (Ne.symm hzy) (Ne.symm hzx) hlt]
      linarith

lemma differenceTail_neg_compl (x y : P) (hxy : x ≠ y) (u : ℝ) (hu : u < 0)
    (hne : ∀ z, u ≠ d.value x y-d.value x z) :
    (d.differenceTail x y u)ᶜ=d.cell (d.value x y-u) x := by
  ext z
  simp only [Finset.mem_compl,differenceTail,Finset.mem_filter,Finset.mem_univ,true_and,mem_cell,share]
  by_cases hzx : z=x
  · subst z
    simp [hxy]
  by_cases hzy : z=y
  · subst z
    have hlt : ¬d.value x y-u ≤ d.value x y := by linarith
    simp [hxy,hxy.symm,hlt]
  · simp only [hzy,false_or,ne_eq,not_false_eq_true,true_and,eq_comm (a:=x) (b:=z),hzx,not_le]
    constructor
    · intro h
      have hlt : d.value y z < d.value z x := by rw [d.symm z x]; linarith
      have he := d.value_eq_of_lt y z x (Ne.symm hzy) hzx hxy.symm hlt
      rw [d.symm y x] at he
      linarith
    · intro h
      have hlt : d.value y x < d.value x z := by rw [d.symm y x]; linarith
      have he := d.value_eq_of_lt y x z hxy.symm (Ne.symm hzx) (Ne.symm hzy) hlt
      rw [d.symm y x] at he
      have hn := hne z
      rw [he]
      rcases lt_or_eq_of_le h with h | h
      · linarith
      · exfalso
        apply hn
        linarith

lemma mass_compl (p : P → ℝ) (hp : ∑ x, p x=1) (C : Finset P) :
    Cuts.mass p Cᶜ=1-Cuts.mass p C := by
  have hh := Finset.sum_add_sum_compl C p
  simp only [Cuts.mass]
  rw [hp] at hh
  linarith

lemma ae_differenceTail_formula (p : P → ℝ) (hp : ∑ x, p x=1) (w : ℝ → ℝ)
    (hw : ∀ u, w (1-u)=w u) (x y : P) (hxy : x ≠ y) :
    ∀ᵐ u : ℝ, w (Cuts.mass p (d.differenceTail x y u)) =
      (if d.value x y < d.value x y+u then w (Cuts.mass p (d.cell (d.value x y+u) y)) else 0)+
      (if d.value x y < d.value x y-u then w (Cuts.mass p (d.cell (d.value x y-u) x)) else 0) := by
  have hn : ∀ᵐ u : ℝ, ∀ z : P, u ≠ d.value x y-d.value x z :=
    ae_all_iff.mpr (fun z => volume.ae_ne _)
  filter_upwards [hn,volume.ae_ne (0 : ℝ)] with u hne hu
  rcases lt_or_gt_of_ne hu with hu | hu
  · have he := d.differenceTail_neg_compl x y hxy u hu hne
    have hm := mass_compl p hp (d.differenceTail x y u)
    rw [he] at hm
    rw [ite_eq_right (by linarith),ite_eq_left (by linarith),zero_add,hm,hw]
  · rw [d.differenceTail_pos x y hxy u hu,ite_eq_left (by linarith),ite_eq_right (by linarith),add_zero]

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)

omit [DecidableEq P] in
lemma measurable_aboveCell (f : Finset P → ℝ) (a : ℝ) (x : P) :
    Measurable (d.aboveCell f a x) := by
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · exact (measurable_of_finite f).comp (d.measurable_cell x)
  · exact measurable_const

omit [DecidableEq P] in
lemma integrable_aboveCell (f : Finset P → ℝ) (hfs : ∀ x, f {x}=0)
    (a : ℝ) (ha : -d.radius ≤ a) (x : P) : Integrable (d.aboveCell f a x) := by
  apply integrable_supported_Icc (d.measurable_aboveCell f a x)
      (C:=∑ C : Finset P, |f C|) (a:= -d.radius) (b:=d.radius)
  · intro r
    unfold aboveCell
    split_ifs
    · simpa only [Real.norm_eq_abs] using (Finset.single_le_sum (s:=Finset.univ) (f:=fun C : Finset P => |f C|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ (d.cell r x)))
    · simpa using Finset.sum_nonneg (fun C (_ : C ∈ (Finset.univ : Finset (Finset P))) => abs_nonneg (f C))
  · intro r hr
    rcases not_and_or.mp hr with hlo | hhi
    · have hh : ¬a < r := by have := lt_of_not_ge hlo; linarith
      simp [aboveCell,hh]
    · simp [aboveCell,d.cell_of_high (lt_of_not_ge hhi) x,hfs]

lemma sum_cut_separation (f : Finset P → ℝ) (r : ℝ) (x y : P) (hxy : x ≠ y) :
    (∑ C ∈ d.cells r, f C*|Cuts.ind C x-Cuts.ind C y|) =
      d.aboveCell f (d.value x y) x r+d.aboveCell f (d.value x y) y r := by
  have hmem (z : P) (C : Finset P) (hC : C ∈ d.cells r) : z ∈ C ↔ C=d.cell r z :=
    ⟨fun hz => d.cell_of_mem hC hz,fun he => by rw [he]; exact d.self_mem_cell r z⟩
  by_cases hr : r ≤ d.value x y
  · have hce : d.cell r x=d.cell r y := d.cell_eq_of_share (Or.inr hr)
    have hz : ∑ C ∈ d.cells r, f C*|Cuts.ind C x-Cuts.ind C y|=0 := by
      apply Finset.sum_eq_zero
      intro C hC
      have hm : x ∈ C ↔ y ∈ C := by rw [hmem x C hC,hmem y C hC,hce]
      simp only [Cuts.ind,hm,sub_self,abs_zero,mul_zero]
    simp [hz,aboveCell,not_lt.mpr hr]
  · have hlt : d.value x y < r := lt_of_not_ge hr
    have hns : ¬d.share r x y := by simpa [share,hxy] using hr
    have he (C : Finset P) (hC : C ∈ d.cells r) :
        f C*|Cuts.ind C x-Cuts.ind C y| =
          (if C=d.cell r x then f (d.cell r x) else 0)+
          (if C=d.cell r y then f (d.cell r y) else 0) := by
      by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
      · have hc := d.cell_of_mem hC hx
        have hh : d.share r x y := by rwa [hc,d.mem_cell] at hy
        exact (hns hh).elim
      · have hc := (hmem x C hC).mp hx
        have hn : C ≠ d.cell r y := fun h => hy ((hmem y C hC).mpr h)
        simp only [Cuts.ind,ite_eq_left hx,ite_eq_right hy,sub_zero,abs_one,mul_one,ite_eq_left hc,ite_eq_right hn,add_zero]
        rw [hc]
      · have hc := (hmem y C hC).mp hy
        have hn : C ≠ d.cell r x := fun h => hx ((hmem x C hC).mpr h)
        simp only [Cuts.ind,ite_eq_right hx,ite_eq_left hy,zero_sub,abs_neg,abs_one,mul_one,ite_eq_left hc,ite_eq_right hn,zero_add]
        rw [hc]
      · have hn1 : C ≠ d.cell r x := fun h => hx ((hmem x C hC).mpr h)
        have hn2 : C ≠ d.cell r y := fun h => hy ((hmem y C hC).mpr h)
        simp [Cuts.ind,hx,hy,hn1,hn2]
    rw [Finset.sum_congr rfl he,Finset.sum_add_distrib]
    simp [d.cell_mem_cells,aboveCell,hlt]

lemma cut_distance_two_integrals (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (x y : P) (hxy : x ≠ y) :
    Cuts.distance d.allCuts (d.cutLength f) x y =
      (∫ r, d.aboveCell f (d.value x y) x r)+(∫ r, d.aboveCell f (d.value x y) y r) := by
  rw [Cuts.distance,← d.integral_cut_sum f hfu hfs (fun C => |Cuts.ind C x-Cuts.ind C y|)]
  simp only [d.sum_cut_separation f _ x y hxy]
  exact integral_add (d.integrable_aboveCell f hfs _ (abs_le.mp (d.abs_value_le_radius x y)).1 x)
    (d.integrable_aboveCell f hfs _ (abs_le.mp (d.abs_value_le_radius x y)).1 y)

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable (d : Depth P)

/-- Exact projection identity, including the formal infinite values at the
    two endpoints, represented by their tail-set membership. -/
lemma cut_projection (p : P → ℝ) (hp : ∑ x, p x=1) (w : ℝ → ℝ)
    (hwu : w 1=0) (hws : ∀ x, w (p x)=0) (hwsym : ∀ u, w (1-u)=w u)
    (x y : P) (hxy : x ≠ y) :
    Cuts.distance d.allCuts (d.cutLength (fun C => w (Cuts.mass p C))) x y =
      ∫ u, w (Cuts.mass p (d.differenceTail x y u)) := by
  let f : Finset P → ℝ := fun C => w (Cuts.mass p C)
  have hfu : f Finset.univ=0 := by simpa [f,Cuts.mass,hp] using hwu
  have hfs : ∀ z, f {z}=0 := by intro z; simpa [f,Cuts.mass] using hws z
  have hi (z : P) := d.integrable_aboveCell f hfs (d.value x y)
    (abs_le.mp (d.abs_value_le_radius x y)).1 z
  have hiY : Integrable (fun u => d.aboveCell f (d.value x y) y (d.value x y+u)) := by
    exact ((measurePreserving_add_left volume (d.value x y)).integrable_comp (hi y).aestronglyMeasurable).mpr (hi y)
  have hiX : Integrable (fun u => d.aboveCell f (d.value x y) x (d.value x y-u)) :=
    (integrable_comp_sub_left _ _).mpr (hi x)
  rw [d.cut_distance_two_integrals f hfu hfs x y hxy]
  have he := integral_congr_ae (d.ae_differenceTail_formula p hp w hwsym x y hxy)
  change (∫ u, w (Cuts.mass p (d.differenceTail x y u))) =
    ∫ u, d.aboveCell f (d.value x y) y (d.value x y+u)+d.aboveCell f (d.value x y) x (d.value x y-u) at he
  rw [he,integral_add hiY hiX,integral_add_left_eq_self,integral_sub_left_eq_self]
  exact add_comm _ _

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Tail
open MeasureTheory
open scoped NNReal
variable {P : Type u5} [Fintype P]

lemma measurable_step (a : ℝ) : Measurable (step a) := by
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const

lemma measurable_law (b : ℝ) (p f : P → ℝ) : Measurable (law b p f) :=
  measurable_const.add (Finset.measurable_sum _ (fun _z _ => measurable_const.mul (measurable_step _)))

lemma step_difference (a b u : ℝ) : |step a u-step b u| =
    if min a b < u ∧ u ≤ max a b then 1 else 0 := by
  unfold step
  rcases le_total a b with h | h
  · rw [min_eq_left h,max_eq_right h]
    by_cases hua : u ≤ a
    · have hub : u ≤ b := hua.trans h
      simp [hua,hub,not_lt.mpr hua]
    · have hau : a < u := lt_of_not_ge hua
      by_cases hub : u ≤ b <;> simp [hua,hub,hau]
  · rw [min_eq_right h,max_eq_left h]
    by_cases hub : u ≤ b
    · have hua : u ≤ a := hub.trans h
      simp [hua,hub,not_lt.mpr hub]
    · have hbu : b < u := lt_of_not_ge hub
      by_cases hua : u ≤ a <;> simp [hua,hub,hbu]

lemma step_difference_indicator (a b : ℝ) : (fun u => |step a u-step b u|) =
    (Set.Ioc (min a b) (max a b)).indicator (fun _ : ℝ => 1) := by
  funext u
  simp [step_difference,Set.indicator_apply]

lemma integrable_step_difference (a b : ℝ) : Integrable (fun u => |step a u-step b u|) := by
  rw [step_difference_indicator,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma integral_step_difference (a b : ℝ) : (∫ u, |step a u-step b u|) = |a-b| := by
  rw [step_difference_indicator,integral_indicator measurableSet_Ioc]
  simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,measureReal_def,Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max (a:=a) (b:=b)))]
  rcases le_total a b with hh | hh
  · simp [max_eq_right hh,min_eq_left hh,abs_of_nonpos (sub_nonpos.mpr hh)]
  · simp [max_eq_left hh,min_eq_right hh,abs_of_nonneg (sub_nonneg.mpr hh)]

lemma law_difference_bound (b : ℝ) (p f g : P → ℝ) (hp : ∀ z, 0 ≤ p z) (u : ℝ) :
    |law b p f u-law b p g u| ≤ ∑ z, p z*|step (f z) u-step (g z) u| := by
  have he : law b p f u-law b p g u=∑ z, p z*(step (f z) u-step (g z) u) := by
    simp only [law,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ∑ z, |p z*(step (f z) u-step (g z) u)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul,abs_of_nonneg (hp _)]

lemma lipschitz_tail_bound (b : ℝ) (p f g : P → ℝ) (hp : ∀ z, 0 ≤ p z)
    (w : ℝ → ℝ) (Λ : ℝ≥0) (hw : LipschitzWith Λ w) :
    (∫ u, |w (law b p f u)-w (law b p g u)|) ≤ (Λ:ℝ)*∑ z, p z*|f z-g z| := by
  let h : ℝ → ℝ := fun u => (Λ:ℝ)*∑ z, p z*|step (f z) u-step (g z) u|
  have hi : Integrable h := (integrable_finsetSum (s:=Finset.univ)
    (fun z _ => (integrable_step_difference (f z) (g z)).const_mul (p z))).const_mul _
  have hb (u : ℝ) : |w (law b p f u)-w (law b p g u)| ≤ h u := by
    have hh := hw.norm_sub_le (law b p f u) (law b p g u)
    simp only [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (law_difference_bound b p f g hp u) Λ.coe_nonneg)
  have hm : Measurable (fun u => |w (law b p f u)-w (law b p g u)|) :=
    ((hw.continuous.measurable.comp (measurable_law b p f)).sub
      (hw.continuous.measurable.comp (measurable_law b p g))).abs
  have hi' := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun u => by
    simpa only [Real.norm_eq_abs,abs_abs] using hb u))
  calc
    _ ≤ ∫ u, h u := integral_mono hi' hi hb
    _ = _ := by
      simp only [h,integral_const_mul]
      rw [integral_finsetSum _ (fun z _ => (integrable_step_difference (f z) (g z)).const_mul (p z))]
      simp only [integral_const_mul,integral_step_difference]

end WeakPinned.Tail

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u6} [Fintype P] [DecidableEq P]
variable (d : Depth P)

omit [DecidableEq P] in
lemma integrable_cellWeight (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (x : P) : Integrable (fun r => f (d.cell r x)) := by
  apply integrable_supported_Icc ((measurable_of_finite f).comp (d.measurable_cell x))
    (C:=∑ C : Finset P, |f C|) (a:= -d.radius) (b:=d.radius)
  · intro r
    simpa only [Function.comp_def,Real.norm_eq_abs] using (Finset.single_le_sum (s:=Finset.univ) (f:=fun C : Finset P => |f C|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (d.cell r x)))
  · intro r hr
    change f (d.cell r x)=0
    rcases not_and_or.mp hr with hlo | hhi
    · rw [d.cell_of_low (le_of_lt (lt_of_not_ge hlo)),hfu]
    · rw [d.cell_of_high (lt_of_not_ge hhi),hfs]

lemma cut_root_projection (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (y : P) :
    Cuts.rootDistance d.allCuts (d.cutLength f) y = ∫ r, f (d.cell r y) := by
  rw [Cuts.rootDistance,← d.integral_cut_sum f hfu hfs (fun C => Cuts.ind C y)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  have he (C : Finset P) (hC : C ∈ d.cells r) : f C*Cuts.ind C y =
      if C=d.cell r y then f (d.cell r y) else 0 := by
    by_cases hy : y ∈ C
    · have hc := d.cell_of_mem hC hy
      subst C
      simp [Cuts.ind,d.self_mem_cell]
    · have hn : C ≠ d.cell r y := fun h => hy (h ▸ d.self_mem_cell r y)
      simp [Cuts.ind,hy,hn]
  change (∑ C ∈ d.cells r, f C*Cuts.ind C y)=f (d.cell r y)
  rw [Finset.sum_congr rfl he]
  simp [d.cell_mem_cells]

lemma integrable_differenceTail (p : P → ℝ) (hp : ∑ x, p x=1) (w : ℝ → ℝ)
    (hws : ∀ x, w (p x)=0) (hwsym : ∀ u, w (1-u)=w u)
    (x y : P) (hxy : x ≠ y) : Integrable (fun u => w (Cuts.mass p (d.differenceTail x y u))) := by
  let f : Finset P → ℝ := fun C => w (Cuts.mass p C)
  have hfs : ∀ z, f {z}=0 := by intro z; simpa [f,Cuts.mass] using hws z
  have hi (z : P) := d.integrable_aboveCell f hfs (d.value x y)
    (abs_le.mp (d.abs_value_le_radius x y)).1 z
  have hiY : Integrable (fun u => d.aboveCell f (d.value x y) y (d.value x y+u)) :=
    ((measurePreserving_add_left volume (d.value x y)).integrable_comp (hi y).aestronglyMeasurable).mpr (hi y)
  have hiX : Integrable (fun u => d.aboveCell f (d.value x y) x (d.value x y-u)) :=
    (integrable_comp_sub_left _ _).mpr (hi x)
  apply (hiY.add hiX).congr
  filter_upwards [d.ae_differenceTail_formula p hp w hwsym x y hxy] with u hu
  exact hu.symm

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Tail
open MeasureTheory Hierarchy
open scoped NNReal
variable {P : Type u7} [Fintype P] [DecidableEq P]

omit [Fintype P] in
lemma offTwo_nonneg (p : P → ℝ) (hp : ∀ z, 0 ≤ p z) (x y z : P) : 0 ≤ offTwo p x y z := by
  unfold offTwo
  split_ifs <;> simp [hp]

lemma mass_as_sum (p : P → ℝ) (C : Finset P) : Cuts.mass p C=∑ z, if z ∈ C then p z else 0 := by
  simp [Cuts.mass]

lemma differenceTail_law (d : Depth P) (p : P → ℝ) (x y : P) (hxy : x ≠ y) (u : ℝ) :
    Cuts.mass p (d.differenceTail x y u)=
      law (p y) (offTwo p x y) (fun z => d.value y z-d.value x z) u := by
  rw [mass_as_sum]
  have he (z : P) : (if z ∈ d.differenceTail x y u then p z else 0)=
      (if z=y then p y else 0)+offTwo p x y z*step (d.value y z-d.value x z) u := by
    by_cases hy : z=y
    · subst z; simp [Depth.differenceTail,offTwo]
    by_cases hx : z=x
    · subst z; simp [Depth.differenceTail,offTwo,hxy]
    · simp [Depth.differenceTail,offTwo,step,hx,hy,mul_ite]
  simp only [he,Finset.sum_add_distrib]
  simp [law]

lemma rootTail_law (d : Depth P) (p : P → ℝ) (x y : P) (hx : p x=0) (hxy : x ≠ y) (c u : ℝ) :
    Cuts.mass p (d.cell (u-c) y)=law (p y) (offTwo p x y) (fun z => d.value y z+c) u := by
  rw [mass_as_sum]
  have he (z : P) : (if z ∈ d.cell (u-c) y then p z else 0)=
      (if z=y then p y else 0)+offTwo p x y z*step (d.value y z+c) u := by
    by_cases hy : z=y
    · subst z; simp [offTwo,d.self_mem_cell]
    by_cases hz : z=x
    · subst z; simp [offTwo,hx,hxy]
    · have hh : u-c ≤ d.value y z ↔ u ≤ d.value y z+c := by constructor <;> intro hh <;> linarith
      simp [Depth.mem_cell,Depth.share,offTwo,step,hz,hy,Ne.symm hy,hh,mul_ite]
  simp only [he,Finset.sum_add_distrib]
  simp [law]

/-- Quantitative fiber-tree comparison, before inserting the arithmetic
    raw-depth equation. The y endpoint is included; x has zero fiber mass. -/
lemma fiber_cut_error (d d' : Depth P) (p : P → ℝ) (hp0 : ∀ z, 0 ≤ p z) (hp : ∑ z, p z=1)
    (w : ℝ → ℝ) (Λ : ℝ≥0) (hw : LipschitzWith Λ w)
    (hwu : w 1=0) (hws : ∀ z, w (p z)=0) (hwsym : ∀ u, w (1-u)=w u)
    (x y : P) (hpx : p x=0) (hxy : x ≠ y) (c : ℝ) :
    |Cuts.distance d.allCuts (d.cutLength (fun C => w (Cuts.mass p C))) x y-
      Cuts.rootDistance d'.allCuts (d'.cutLength (fun C => w (Cuts.mass p C))) y| ≤
      (Λ:ℝ)*∑ z, offTwo p x y z*|d.value y z-d.value x z-(d'.value y z+c)| := by
  let f : Finset P → ℝ := fun C => w (Cuts.mass p C)
  have hfu : f Finset.univ=0 := by simpa [f,Cuts.mass,hp] using hwu
  have hfs : ∀ z, f {z}=0 := by intro z; simpa [f,Cuts.mass] using hws z
  let a := law (p y) (offTwo p x y) (fun z => d.value y z-d.value x z)
  let b := law (p y) (offTwo p x y) (fun z => d'.value y z+c)
  have hia : Integrable (fun u => w (a u)) := by
    simpa only [differenceTail_law d p x y hxy] using
      d.integrable_differenceTail p hp w hws hwsym x y hxy
  have hib0 := d'.integrable_cellWeight f hfu hfs y
  have hib : Integrable (fun u => w (b u)) := by
    have hh := ((measurePreserving_add_right volume (-c)).integrable_comp hib0.aestronglyMeasurable).mpr hib0
    simpa only [Function.comp_def,f,← sub_eq_add_neg,rootTail_law d' p x y hpx hxy c] using hh
  have he : (∫ u, w (b u))=Cuts.rootDistance d'.allCuts (d'.cutLength f) y := by
    rw [d'.cut_root_projection f hfu hfs y]
    have hh := integral_add_right_eq_self (μ:=volume) (fun r => f (d'.cell r y)) (-c)
    simpa only [f,← sub_eq_add_neg,rootTail_law d' p x y hpx hxy c] using hh
  rw [d.cut_projection p hp w hwu hws hwsym x y hxy,← he]
  simp only [differenceTail_law d p x y hxy]
  change |(∫ u, w (a u))-(∫ u, w (b u))| ≤ _
  rw [← integral_sub hia hib]
  calc
    _ ≤ ∫ u, |w (a u)-w (b u)| := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun u => w (a u)-w (b u))
    _ ≤ _ := lipschitz_tail_bound (p y) (offTwo p x y) _ _ (offTwo_nonneg p hp0 x y) w Λ hw

end WeakPinned.Tail

namespace WeakPinned.Arithmetic
variable {K : Type u8} [Field K]

lemma paired_log (v : AbsoluteValue K ℝ) (a b c d z w t : K)
    (hc : c ≠ a) (hz : z ≠ a) (hcz : c ≠ z) (ht : t ≠ 0)
    (hcd : (c-a)*(d-b)=t) (hzw : (z-a)*(w-b)=t) :
    -Real.log (v (w-d)) = -Real.log (v (c-z))+Real.log (v (z-a))-
      Real.log (v t)+Real.log (v (c-a)) := by
  rw [paired_difference a b c d z w t hc hz hcd hzw,
    map_div₀,map_mul,map_mul,
    Real.log_div (mul_ne_zero (v.pos ht).ne' (v.pos (sub_ne_zero.mpr hcz)).ne')
      (mul_ne_zero (v.pos (sub_ne_zero.mpr hz)).ne' (v.pos (sub_ne_zero.mpr hc)).ne'),
    Real.log_mul (v.pos ht).ne' (v.pos (sub_ne_zero.mpr hcz)).ne',
    Real.log_mul (v.pos (sub_ne_zero.mpr hz)).ne' (v.pos (sub_ne_zero.mpr hc)).ne']
  ring

lemma absval_sub_symm (v : AbsoluteValue K ℝ) (a b : K) : v (a-b)=v (b-a) := by
  rw [← neg_sub b a,map_neg_eq_map]

/-- The raw cross-fiber identity at every place. The three points are distinct
    and the source is outside its fiber. -/
lemma raw_cross_fiber {P : Type u9} (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁)
    (h₂ : Function.Injective Z₂) (v : AbsoluteValue K ℝ) (x y z : P)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (t : K)
    (hy : (Z₁ x-Z₁ y)*(Z₂ x-Z₂ y)=t)
    (hz : (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t) :
    -Real.log (v (Z₂ y-Z₂ z)) = -Real.log (v (Z₁ y-Z₁ z))-
      (-Real.log (v (Z₁ x-Z₁ z)))-Real.log (v t)-(-Real.log (v (Z₁ x-Z₁ y))) := by
  have ht : t ≠ 0 := by rw [← hy]; exact mul_ne_zero (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
  have hh := paired_log v (Z₁ x) (Z₂ x) (Z₁ y) (Z₂ y) (Z₁ z) (Z₂ z) t
    (h₁.ne hxy.symm) (h₁.ne hxz.symm) (h₁.ne hyz) ht
    (by convert hy using 1; ring) (by convert hz using 1; ring)
  rw [absval_sub_symm v (Z₂ z) (Z₂ y),absval_sub_symm v (Z₁ z) (Z₁ x),
    absval_sub_symm v (Z₁ y) (Z₁ x)] at hh
  linarith
end WeakPinned.Arithmetic

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiberTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory Cuts
open scoped BigOperators
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma cutLength_bound (f : Finset P → ℝ) (hfu : f Finset.univ=0)
    (hfs : ∀ x, f {x}=0) (C : Finset P) :
    |d.cutLength f C|≤2*d.radius*|f C| := by
  rw [← Real.norm_eq_abs,cutLength]
  apply (norm_integral_le_integral_norm _).trans
  exact integral_bound_supported d.radius_nonneg (d.integrable_cutAt f hfu hfs C).norm
    (d.cutAt_bound f C) (fun r hr => by rw [d.cutAt_vanish f hfu hfs C r hr,norm_zero])

lemma sum_cutLength_univ (f : Finset P → ℝ) (g : Finset P → ℝ) :
    (∑ C ∈ d.allCuts, d.cutLength f C*g C)=∑ C, d.cutLength f C*g C := by
  exact Finset.sum_subset (Finset.subset_univ _) (fun C _ hC => by rw [d.cutLength_outside f C hC,zero_mul])

lemma cutLength_mul (f g : Finset P → ℝ) (C : Finset P) :
    d.cutLength (fun B => f B*g B) C=d.cutLength f C*g C := by
  unfold cutLength
  rw [← integral_mul_const]
  congr 1
  funext r
  simp only [cutAt,ite_mul,zero_mul]

lemma cutLength_difference_le (f g : Finset P → ℝ)
    (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0)
    (hgu : g Finset.univ=0) (hgs : ∀ x, g {x}=0) (C : Finset P) :
    |d.cutLength f C-d.cutLength g C|≤d.cutLength (fun B => |f B-g B|) C := by
  rw [cutLength,cutLength,← integral_sub (d.integrable_cutAt f hfu hfs C) (d.integrable_cutAt g hgu hgs C)]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans_eq
  congr 1
  funext r
  simp only [cutAt,Real.norm_eq_abs]
  split_ifs <;> simp

lemma distance_cut_difference (f g : Finset P → ℝ)
    (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0)
    (hgu : g Finset.univ=0) (hgs : ∀ x, g {x}=0) (x y : P) :
    |distance d.allCuts (d.cutLength f) x y-distance d.allCuts (d.cutLength g) x y|≤
      ∑ C ∈ d.allCuts, d.cutLength (fun B => |f B-g B|) C := by
  unfold distance
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro C hC
  rw [← sub_mul,abs_mul,abs_abs]
  have hi : |ind C x-ind C y|≤1 := by unfold ind; split_ifs <;> norm_num
  have h1 := mul_le_mul_of_nonneg_right (d.cutLength_difference_le f g hfu hfs hgu hgs C) (abs_nonneg (ind C x-ind C y))
  exact h1.trans (by simpa using mul_le_mul_of_nonneg_left hi (d.cutLength_nonneg _ (fun B => abs_nonneg _) C))

lemma root_cut_difference (f g : Finset P → ℝ)
    (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0)
    (hgu : g Finset.univ=0) (hgs : ∀ x, g {x}=0) (y : P) :
    |rootDistance d.allCuts (d.cutLength f) y-rootDistance d.allCuts (d.cutLength g) y|≤
      ∑ C ∈ d.allCuts, d.cutLength (fun B => |f B-g B|) C := by
  unfold rootDistance
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro C hC
  rw [← sub_mul,abs_mul]
  have hi : |ind C y|≤1 := by unfold ind; split_ifs <;> norm_num
  have h1 := mul_le_mul_of_nonneg_right (d.cutLength_difference_le f g hfu hfs hgu hgs C) (abs_nonneg (ind C y))
  exact h1.trans (by simpa using mul_le_mul_of_nonneg_left hi (d.cutLength_nonneg _ (fun B => abs_nonneg _) C))

lemma cost_cut_formula (f : Finset P → ℝ) (p a : P → ℝ) :
    cost d.allCuts (d.cutLength f) p a =
      ∑ C ∈ d.allCuts, d.cutLength (fun B => f B*|Cuts.mass p B-Cuts.mass a B|) C := by
  simp only [cost,d.cutLength_mul]

variable {Ω : Type u2} [MeasurableSpace Ω] (D : Ω → Depth P)
    (hD : ∀ x y, Measurable (fun ω => (D ω).value x y))
include hD
lemma measurable_cutLength_param (f : Finset P → ℝ) (C : Finset P) :
    Measurable (fun ω => (D ω).cutLength f C) := by
  have hm : Measurable (fun p : Ω×ℝ => (D p.1).cutAt f C p.2) :=
    (measurable_of_finite (fun s : Finset (Finset P) => if C ∈ s then f C else 0)).comp
    (measurable_cells_param (P:=P) (Ω:=Ω×ℝ) (fun p : Ω×ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma integrable_cutLength_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (f : Finset P → ℝ) (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0) (C : Finset P) :
    Integrable (fun ω => (D ω).cutLength f C) μ := by
  apply (((integrable_radius_param D hi).const_mul 2).mul_const |f C|).mono'
    (measurable_cutLength_param D hD f C).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => (D ω).cutLength_bound f hfu hfs C)

lemma integrable_cutSum_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (f g : Finset P → ℝ) (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0) :
    Integrable (fun ω => ∑ C ∈ (D ω).allCuts, (D ω).cutLength f C*g C) μ := by
  simp only [sum_cutLength_univ]
  exact integrable_finsetSum _ (fun C _ => (integrable_cutLength_param D hD hi f hfu hfs C).mul_const (g C))

lemma integrable_cutDistance_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (f : Finset P → ℝ) (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0) (x y : P) :
    Integrable (fun ω => distance (D ω).allCuts ((D ω).cutLength f) x y) μ :=
  integrable_cutSum_param D hD hi f (fun B => |ind B x-ind B y|) hfu hfs

lemma integrable_rootDistance_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (f : Finset P → ℝ) (hfu : f Finset.univ=0) (hfs : ∀ x, f {x}=0) (y : P) :
    Integrable (fun ω => rootDistance (D ω).allCuts ((D ω).cutLength f) y) μ :=
  integrable_cutSum_param D hD hi f (fun B => ind B y) hfu hfs
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Cuts
lemma tent_lipschitzWith (δ : ℝ) : LipschitzWith 1 (tent δ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using tent_lipschitz δ x y
end WeakPinned.Cuts

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance Cuts
open scoped BigOperators
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable {K : Type u4} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

lemma arch_cross_defect (v : NumberField.InfinitePlace K) (x y z : P)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (t : K)
    (hy : (Z₁ x-Z₁ y)*(Z₂ x-Z₂ y)=t) (hz : (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t) :
    (fun ω => (arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-
      ((arch Z₂ v ω).value y z+(Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))))) =ᵐ[Grid.fullLaw]
    (fun ω => Grid.error ω (v.embedding (Z₁ y)) (v.embedding (Z₁ z))-
      Grid.error ω (v.embedding (Z₁ x)) (v.embedding (Z₁ z))-
      Grid.error ω (v.embedding (Z₂ y)) (v.embedding (Z₂ z))) := by
  have he := Arithmetic.raw_cross_fiber Z₁ Z₂ h₁ h₂ v.val x y z hxy hxz hyz t hy hz
  filter_upwards [arch_value_ae Z₁ h₁ v hyz,arch_value_ae Z₁ h₁ v hxz,arch_value_ae Z₂ h₂ v hyz] with ω ha hb hc
  rw [ha,hb,hc]
  simp only [Grid.error,← map_sub,NumberField.InfinitePlace.norm_embedding_eq]
  change -Real.log (v (Z₂ y-Z₂ z)) = -Real.log (v (Z₁ y-Z₁ z)) -
    -Real.log (v (Z₁ x-Z₁ z)) - Real.log (v t) - -Real.log (v (Z₁ x-Z₁ y)) at he
  linarith

lemma arch_cross_defect_mean (v : NumberField.InfinitePlace K) (x y z : P)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (t : K)
    (hy : (Z₁ x-Z₁ y)*(Z₂ x-Z₂ y)=t) (hz : (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t) :
    (∫ ω, |(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-
      ((arch Z₂ v ω).value y z+(Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))))| ∂Grid.fullLaw)≤12 := by
  have hEq := arch_cross_defect Z₁ Z₂ h₁ h₂ v x y z hxy hxz hyz t hy hz
  have heq := integral_congr_ae (hEq.fun_comp (abs : ℝ → ℝ))
  dsimp only [Function.comp_def] at heq
  rw [heq]
  have ha := Grid.error_integrable_full (embedding_ne Z₁ h₁ v hyz)
  have hb := Grid.error_integrable_full (embedding_ne Z₁ h₁ v hxz)
  have hc := Grid.error_integrable_full (embedding_ne Z₂ h₂ v hyz)
  have hh := integral_mono ((ha.sub hb).sub hc).abs ((ha.abs.add hb.abs).add hc.abs) (fun ω =>
    (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl))
  dsimp only [Pi.sub_apply,Pi.add_apply] at hh
  have hAdd := integral_add (ha.abs.add hb.abs) hc.abs
  have hAdd2 := integral_add ha.abs hb.abs
  dsimp only [Pi.add_apply] at hAdd hAdd2
  rw [hAdd,hAdd2] at hh
  have h1 := Grid.mean_abs_error_full (embedding_ne Z₁ h₁ v hyz)
  have h2 := Grid.mean_abs_error_full (embedding_ne Z₁ h₁ v hxz)
  have h3 := Grid.mean_abs_error_full (embedding_ne Z₂ h₂ v hyz)
  linarith

/-- Actual local cut projection under an arithmetic fiber probability. The
atom at y is retained and the source has zero mass. -/
lemma arch_fiber_cut (v : NumberField.InfinitePlace K) (p : P → ℝ)
    (hp0 : ∀ z, 0≤p z) (hp : ∑ z, p z=1) (x y : P) (hpx : p x=0) (hpy : p y≠0)
    (t : K) (ht : ∀ z, p z≠0 → (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t)
    (δ : ℝ) (hδ : 0≤δ) (hps : ∀ z, p z≤δ) :
    (∫ ω, |distance (arch Z₁ v ω).allCuts ((arch Z₁ v ω).cutLength (fun C => tent δ (mass p C))) x y-
      rootDistance (arch Z₂ v ω).allCuts ((arch Z₂ v ω).cutLength (fun C => tent δ (mass p C))) y| ∂Grid.fullLaw)≤12 := by
  have hxy : x≠y := fun hh => hpy (hh ▸ hpx)
  let f : Finset P → ℝ := fun C => tent δ (mass p C)
  have hfu : f Finset.univ=0 := by simp only [f,mass,hp]; exact tent_zero_right (by linarith)
  have hfs (z) : f {z}=0 := by simp only [f,mass,Finset.sum_singleton]; exact tent_zero_left (hps z)
  have hl := Depth.integrable_cutDistance_param (arch Z₁ v) (arch_measurable Z₁ h₁ v) (arch_integrable Z₁ h₁ v) f hfu hfs x y
  have hr := Depth.integrable_rootDistance_param (arch Z₂ v) (arch_measurable Z₂ h₂ v) (arch_integrable Z₂ h₂ v) f hfu hfs y
  let c := Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))
  let E : Grid.FullSample → ℝ := fun ω => ∑ z, Tail.offTwo p x y z*
    |(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-((arch Z₂ v ω).value y z+c)|
  have hEi (z : P) : Integrable (fun ω => Tail.offTwo p x y z*
    |(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-((arch Z₂ v ω).value y z+c)|) Grid.fullLaw :=
    ((((arch_integrable Z₁ h₁ v y z).sub (arch_integrable Z₁ h₁ v x z)).sub
      ((arch_integrable Z₂ h₂ v y z).add (integrable_const c))).abs.const_mul _)
  have hi : Integrable E Grid.fullLaw := integrable_finsetSum _ (fun z _ => hEi z)
  have hh := integral_mono (hl.sub hr).abs hi (fun ω => by
    simpa only [f,E,Pi.sub_apply,NNReal.coe_one,one_mul] using Tail.fiber_cut_error
      (arch Z₁ v ω) (arch Z₂ v ω) p hp0 hp (tent δ) 1 (tent_lipschitzWith δ)
      (tent_zero_right (by linarith)) (fun z => tent_zero_left (hps z)) (tent_symm δ) x y hpx hxy c)
  apply hh.trans
  unfold E
  rw [integral_finsetSum Finset.univ (fun z _ => hEi z)]
  simp only [integral_const_mul]
  apply le_trans (Finset.sum_le_sum (fun z _ => show Tail.offTwo p x y z* _≤12*p z from ?_))
    (by rw [← Finset.mul_sum,hp,mul_one])
  by_cases hzx : z=x
  · subst z; simp [Tail.offTwo,hpx]
  by_cases hzy : z=y
  · subst z; simp only [Tail.offTwo,or_true,reduceIte,zero_mul]; exact mul_nonneg (by norm_num) (hp0 y)
  by_cases hpz : p z=0
  · simp [Tail.offTwo,hzx,hzy,hpz]
  · simp only [Tail.offTwo,hzx,hzy,or_self,reduceIte]
    have he := arch_cross_defect_mean Z₁ Z₂ h₁ h₂ v x y z hxy (Ne.symm hzx) (Ne.symm hzy) t (ht y hpy) (ht z hpz)
    dsimp [c]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left he (hp0 z)

end WeakPinned.Global
noncomputable section

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance Cuts
open scoped BigOperators
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable {K : Type u6} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

lemma finite_fiber_cut (v : NumberField.FinitePlace K) (p : P → ℝ)
    (hp0 : ∀ z, 0≤p z) (hp : ∑ z, p z=1) (x y : P) (hpx : p x=0) (hpy : p y≠0)
    (t : K) (ht : ∀ z, p z≠0 → (Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t)
    (δ : ℝ) (hδ : 0≤δ) (hps : ∀ z, p z≤δ) :
    |distance (finite Z₁ h₁ v).allCuts ((finite Z₁ h₁ v).cutLength (fun C => tent δ (mass p C))) x y-
      rootDistance (finite Z₂ h₂ v).allCuts ((finite Z₂ h₂ v).cutLength (fun C => tent δ (mass p C))) y|≤0 := by
  have hxy : x≠y := fun hh => hpy (hh ▸ hpx)
  let c := Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))
  have hh := Tail.fiber_cut_error (finite Z₁ h₁ v) (finite Z₂ h₂ v) p hp0 hp (tent δ) 1
    (tent_lipschitzWith δ) (tent_zero_right (by linarith)) (fun z => tent_zero_left (hps z))
    (tent_symm δ) x y hpx hxy c
  simp only [NNReal.coe_one,one_mul] at hh
  apply hh.trans
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro z _
  by_cases hxz : x=z
  · subst z; simp [Tail.offTwo]
  by_cases hyz : y=z
  · subst z; simp [Tail.offTwo]
  by_cases hpz : p z=0
  · simp [Tail.offTwo,hpz]
  · have he := Arithmetic.raw_cross_fiber Z₁ Z₂ h₁ h₂ v.val x y z hxy hxz hyz t (ht y hpy) (ht z hpz)
    change -Real.log (v (Z₂ y-Z₂ z)) = -Real.log (v (Z₁ y-Z₁ z)) -
      -Real.log (v (Z₁ x-Z₁ z)) - Real.log (v t) - -Real.log (v (Z₁ x-Z₁ y)) at he
    suffices (finite Z₁ h₁ v).value y z-(finite Z₁ h₁ v).value x z-
      ((finite Z₂ h₂ v).value y z+c)=0 by rw [this,abs_zero,mul_zero]
    simp only [finite,ite_eq_right hyz,ite_eq_right hxz,c]
    linarith

omit [NumberField K] in
lemma integrable_arch_cut_error (v : NumberField.InfinitePlace K) (p : P → ℝ)
    (δ : ℝ) (hpu : tent δ (mass p Finset.univ)=0) (hps : ∀ x, tent δ (mass p {x})=0)
    (x y : P) :
    Integrable (fun ω => |distance (arch Z₁ v ω).allCuts ((arch Z₁ v ω).cutLength (fun C => tent δ (mass p C))) x y-
      rootDistance (arch Z₂ v ω).allCuts ((arch Z₂ v ω).cutLength (fun C => tent δ (mass p C))) y|) Grid.fullLaw := by
  exact ((Depth.integrable_cutDistance_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) _ hpu hps x y).sub
    (Depth.integrable_rootDistance_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
      (arch_integrable Z₂ h₂ v) _ hpu hps y)).abs

variable {I : Type u7} [Fintype I]

omit [NumberField K] in
lemma fiber_cut_discrepancy_integrable (w : I → ℝ) (p : I → P → ℝ) (src : I → P)
    (hp : ∀ i, ∑ z, p i z=1) (δ : ℝ) (hδ : 0≤δ) (hps : ∀ i z, p i z≤δ) :
    AverageIntegrable Z₁ Z₂ (fiberCutDiscrepancy w p src δ) := by
  intro v
  apply integrable_finsetSum
  intro i _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro y _
  apply Integrable.const_mul
  exact integrable_arch_cut_error Z₁ Z₂ h₁ h₂ v (p i) δ
    (by simp only [mass,hp]; exact tent_zero_right (by linarith))
    (fun z => by simp only [mass,Finset.sum_singleton]; exact tent_zero_left (hps i z)) (src i) y

/-- A bounded projection estimate with exact fiber atoms and no restriction on
    degree, finite places or variation of number fields. -/
lemma arithmetic_fiber_cut (w : I → ℝ) (p : I → P → ℝ) (src : I → P) (t : I → K)
    (hw : ∀ i, 0≤w i) (hW : ∑ i, w i=1) (hp0 : ∀ i z, 0≤p i z)
    (hp : ∀ i, ∑ z, p i z=1) (hpx : ∀ i, p i (src i)=0)
    (ht : ∀ i z, p i z≠0 → (Z₁ (src i)-Z₁ z)*(Z₂ (src i)-Z₂ z)=t i)
    (δ : ℝ) (hδ : 0≤δ) (hps : ∀ i z, p i z≤δ) :
    average Z₁ Z₂ h₁ h₂ (fiberCutDiscrepancy w p src δ)≤12 := by
  classical
  have hi (v : NumberField.InfinitePlace K) (i : I) (y : P) :=
    integrable_arch_cut_error Z₁ Z₂ h₁ h₂ v (p i) δ
      (by simp only [mass,hp]; exact tent_zero_right (by linarith))
      (fun z => by simp only [mass,Finset.sum_singleton]; exact tent_zero_left (hps i z)) (src i) y
  have ha (v : NumberField.InfinitePlace K) :
      (∫ ω, fiberCutDiscrepancy w p src δ (arch Z₁ v ω) (arch Z₂ v ω) ∂Grid.fullLaw)≤12 := by
    unfold fiberCutDiscrepancy
    rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum _ (fun y _ => (hi v i y).const_mul (p i y))).const_mul (w i))]
    simp only [integral_const_mul]
    have he (i : I) : (∫ ω, ∑ y, p i y*|distance (arch Z₁ v ω).allCuts
        ((arch Z₁ v ω).cutLength (fun C => tent δ (mass (p i) C))) (src i) y-
        rootDistance (arch Z₂ v ω).allCuts ((arch Z₂ v ω).cutLength (fun C => tent δ (mass (p i) C))) y| ∂Grid.fullLaw)≤12 := by
      rw [integral_finsetSum _ (fun y _ => (hi v i y).const_mul (p i y))]
      simp only [integral_const_mul]
      calc
        _ ≤ ∑ y, p i y*12 := Finset.sum_le_sum (fun y _ => by
          by_cases hy : p i y=0
          · simp [hy]
          · exact mul_le_mul_of_nonneg_left (arch_fiber_cut Z₁ Z₂ h₁ h₂ v (p i) (hp0 i) (hp i)
              (src i) y (hpx i) hy (t i) (ht i) δ hδ (hps i)) (hp0 i y))
        _ = 12 := by rw [← Finset.sum_mul,hp,one_mul]
    exact (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (he i) (hw i))).trans_eq
      (by rw [← Finset.sum_mul,hW,one_mul])
  have hv (v : NumberField.FinitePlace K) :
      fiberCutDiscrepancy w p src δ (finite Z₁ h₁ v) (finite Z₂ h₂ v)≤0 := by
    apply Finset.sum_nonpos
    intro i _
    apply mul_nonpos_of_nonneg_of_nonpos (hw i)
    apply Finset.sum_nonpos
    intro y _
    by_cases hy : p i y=0
    · simp [hy]
    · exact mul_nonpos_of_nonneg_of_nonpos (hp0 i y) (finite_fiber_cut Z₁ Z₂ h₁ h₂ v
        (p i) (hp0 i) (hp i) (src i) y (hpx i) hy (t i) (ht i) δ hδ (hps i))
  change placeAverage (placeUnion Z₁ Z₂ h₁ h₂) _ _≤12
  have hh := placeAverage_mono (placeUnion Z₁ Z₂ h₁ h₂) ha (fun v _ => hv v)
  rwa [placeAverage_arch_const] at hh
end WeakPinned.Global
noncomputable section
namespace WeakPinned.Cuts
open MeasureTheory Hierarchy Variance
open scoped BigOperators
variable {P : Type u8} [Fintype P] [DecidableEq P]

lemma mass_complement (p : P → ℝ) (hp : ∑ x, p x=1) (C : Finset P) : mass p Cᶜ=1-mass p C := by
  have hh := Finset.sum_compl_add_sum C p
  rw [hp] at hh
  exact eq_sub_of_add_eq hh

omit [Fintype P] [DecidableEq P] in
lemma mass_small (p : P → ℝ) (δ : ℝ) (hδ : 0≤δ) (hp : ∀ x, p x≤δ)
    (C : Finset P) (hC : C.card≤1) : mass p C≤δ := by
  have hh := Finset.sum_le_sum (s:=C) (fun x _ => hp x)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  have hc : (C.card:ℝ)≤1 := by exact_mod_cast hC
  exact hh.trans (by nlinarith)

omit [Fintype P] [DecidableEq P] in
lemma cutError_small (p a : P → ℝ) (δ : ℝ) (hδ : 0≤δ)
    (hp : ∀ x, p x≤δ) (ha : ∀ x, a x≤δ) (C : Finset P) (hC : C.card≤1) :
    cutError δ (mass p C) (mass a C)=0 := by
  simp only [cutError,tent_zero_left (mass_small p δ hδ hp C hC),
    tent_zero_left (mass_small a δ hδ ha C hC),sub_self,abs_zero,zero_mul,add_zero]

lemma cutError_complement (p a : P → ℝ) (hp : ∑ x, p x=1) (ha : ∑ x, a x=1)
    (δ : ℝ) (C : Finset P) :
    cutError δ (mass p Cᶜ) (mass a Cᶜ)=cutError δ (mass p C) (mass a C) := by
  rw [mass_complement p hp,mass_complement a ha,cutError_symm]

lemma charge_occurrence (d : Depth P) (hn : 2≤Fintype.card P) (δ : ℝ) (hδ : 0≤δ)
    (p a : P → ℝ) (hp : ∑ x, p x=1) (ha : ∑ x, a x=1)
    (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) :
    charge d δ p a=weightedIntegral d.mass (fun C => cutError δ (mass p C) (mass a C)) := by
  symm
  exact d.symmetric_integral_cut_sum hn _ (cutError_small p a δ hδ hps has)
    (cutError_complement p a hp ha δ)

omit [DecidableEq P] in
lemma tent_mass_univ (p : P → ℝ) (hp : ∑ x, p x=1) (δ : ℝ) (hδ : 0≤δ) :
    tent δ (mass p Finset.univ)=0 := by
  simp only [mass,hp]
  exact tent_zero_right (by linarith)
omit [Fintype P] [DecidableEq P] in
lemma tent_mass_singleton (p : P → ℝ) (δ : ℝ) (hp : ∀ x, p x≤δ) (x : P) :
    tent δ (mass p {x})=0 := by
  simp only [mass,Finset.sum_singleton]
  exact tent_zero_left (hp x)

end WeakPinned.Cuts
namespace WeakPinned.Hierarchy.Depth
open Cuts MeasureTheory
variable {P : Type u9} [Fintype P] [DecidableEq P]
lemma cutLength_mono (d : Depth P) (f g : Finset P → ℝ)
    (hf : f Finset.univ=0) (hfs : ∀ x, f {x}=0) (hg : g Finset.univ=0) (hgs : ∀ x, g {x}=0)
    (hfg : ∀ C, f C≤g C) (C : Finset P) : d.cutLength f C≤d.cutLength g C := by
  apply integral_mono (d.integrable_cutAt f hf hfs C) (d.integrable_cutAt g hg hgs C)
  intro r
  simp only [cutAt]
  split_ifs
  · exact hfg C
  · rfl
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Cuts
open MeasureTheory Hierarchy Variance
variable {P : Type u10} [Fintype P] [DecidableEq P]
lemma distance_change_charge (d : Depth P) (δ : ℝ) (hδ : 0≤δ) (p a : P → ℝ)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) (x y : P) :
    |distance d.allCuts (d.cutLength (fun C => tent δ (mass p C))) x y-
      distance d.allCuts (d.cutLength (fun C => tent δ (mass a C))) x y|≤charge d δ p a := by
  apply (d.distance_cut_difference _ _ (tent_mass_univ p hp δ hδ) (tent_mass_singleton p δ hps)
    (tent_mass_univ a ha δ hδ) (tent_mass_singleton a δ has) x y).trans
  apply Finset.sum_le_sum
  intro C _
  apply d.cutLength_mono
  · simp only [tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero]
  · intro z; simp only [tent_mass_singleton p δ hps,tent_mass_singleton a δ has,sub_self,abs_zero]
  · simp only [cutError,tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero,zero_mul,add_zero]
  · intro z; exact cutError_small p a δ hδ hps has _ (by simp)
  · intro C; exact le_add_of_nonneg_right (mul_nonneg (tent_nonneg _ _) (abs_nonneg _))

lemma root_change_charge (d : Depth P) (δ : ℝ) (hδ : 0≤δ) (p a : P → ℝ)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) (y : P) :
    |rootDistance d.allCuts (d.cutLength (fun C => tent δ (mass p C))) y-
      rootDistance d.allCuts (d.cutLength (fun C => tent δ (mass a C))) y|≤charge d δ p a := by
  apply (d.root_cut_difference _ _ (tent_mass_univ p hp δ hδ) (tent_mass_singleton p δ hps)
    (tent_mass_univ a ha δ hδ) (tent_mass_singleton a δ has) y).trans
  apply Finset.sum_le_sum
  intro C _
  apply d.cutLength_mono
  · simp only [tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero]
  · intro z; simp only [tent_mass_singleton p δ hps,tent_mass_singleton a δ has,sub_self,abs_zero]
  · simp only [cutError,tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero,zero_mul,add_zero]
  · intro z; exact cutError_small p a δ hδ hps has _ (by simp)
  · intro C; exact le_add_of_nonneg_right (mul_nonneg (tent_nonneg _ _) (abs_nonneg _))

lemma cost_le_charge (d : Depth P) (δ : ℝ) (hδ : 0≤δ) (p a : P → ℝ)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) :
    cost d.allCuts (d.cutLength (fun C => tent δ (mass a C))) p a≤charge d δ p a := by
  rw [d.cost_cut_formula]
  apply Finset.sum_le_sum
  intro C _
  apply d.cutLength_mono
  · simp only [tent_mass_univ a ha δ hδ,zero_mul]
  · intro z; simp only [tent_mass_singleton a δ has,zero_mul]
  · simp only [cutError,tent_mass_univ p hp δ hδ,tent_mass_univ a ha δ hδ,sub_self,abs_zero,zero_mul,add_zero]
  · intro z; exact cutError_small p a δ hδ hps has _ (by simp)
  · intro C; exact le_add_of_nonneg_left (abs_nonneg _)
end WeakPinned.Cuts
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.TreeContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section

namespace WeakPinned.Cuts
open MeasureTheory Hierarchy Variance
open scoped BigOperators
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

omit [Fintype P] [DecidableEq P] in
lemma cost_mixture (s : Finset (Finset P)) (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0≤l C)
    (w : I → ℝ) (p : I → P → ℝ) (a : P → ℝ) (hw : ∀ i, 0≤w i) (hW : ∑ i, w i=1) :
    cost s l (fun y => ∑ i, w i*p i y) a≤∑ i, w i*cost s l (p i) a := by
  have hm (C : Finset P) : mass (fun y => ∑ i, w i*p i y) C-mass a C=
      ∑ i, w i*(mass (p i) C-mass a C) := by
    simp only [mass,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hW,one_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  unfold cost
  simp only [hm]
  calc
    _ ≤ ∑ C ∈ s, l C*∑ i, w i*|mass (p i) C-mass a C| := by
      apply Finset.sum_le_sum
      intro C hC
      apply mul_le_mul_of_nonneg_left _ (hl C hC)
      convert Finset.abs_sum_le_sum_abs (s:=Finset.univ) (fun i => w i*(mass (p i) C-mass a C)) using 1
      simp only [abs_mul,abs_of_nonneg (hw _)]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun C _ => by ring))

omit [DecidableEq P] in
lemma mass_upper (p : P → ℝ) (hp0 : ∀ x, 0≤p x) (hp : ∑ x, p x=1) (C : Finset P) : mass p C≤1 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hp0 x)).trans_eq hp

omit [DecidableEq P] in
lemma cost_bound (s : Finset (Finset P)) (l : Finset P → ℝ) (hl : ∀ C ∈ s, 0≤l C)
    (p a : P → ℝ) (hp0 : ∀ x, 0≤p x) (ha0 : ∀ x, 0≤a x)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) : cost s l p a≤∑ C ∈ s, l C := by
  apply Finset.sum_le_sum
  intro C hC
  have hh : |mass p C-mass a C|≤1 := abs_le.mpr ⟨by linarith [mass_nonneg p hp0 C,mass_upper a ha0 ha C],
    by linarith [mass_nonneg a ha0 C,mass_upper p hp0 hp C]⟩
  simpa using mul_le_mul_of_nonneg_left hh (hl C hC)

lemma projection_replacement (d d' : Depth P) (δ : ℝ) (hδ : 0≤δ) (p a : P → ℝ)
    (hp : ∑ x, p x=1) (ha : ∑ x, a x=1) (hps : ∀ x, p x≤δ) (has : ∀ x, a x≤δ) (x y : P) :
    |distance d.allCuts (d.cutLength (fun C => tent δ (mass a C))) x y-
        rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass a C))) y|≤
      |distance d.allCuts (d.cutLength (fun C => tent δ (mass p C))) x y-
        rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass p C))) y|+
      charge d δ p a+charge d' δ p a := by
  have h1 := distance_change_charge d δ hδ p a hp ha hps has x y
  have h2 := root_change_charge d' δ hδ p a hp ha hps has y
  let A := distance d.allCuts (d.cutLength (fun C => tent δ (mass a C))) x y
  let B := rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass a C))) y
  let C := distance d.allCuts (d.cutLength (fun C => tent δ (mass p C))) x y
  let D := rootDistance d'.allCuts (d'.cutLength (fun C => tent δ (mass p C))) y
  change |C-A|≤charge d δ p a at h1
  change |D-B|≤charge d' δ p a at h2
  change |A-B|≤|C-D|+charge d δ p a+charge d' δ p a
  have hh1 : |A-B|≤|A-C|+|C-B| := abs_sub_le A C B
  have hh2 : |C-B|≤|C-D|+|D-B| := abs_sub_le C D B
  have hh3 : |A-C|=|C-A| := abs_sub_comm A C
  rw [hh3] at hh1
  linarith only [hh1,hh2,h1,h2]

lemma family_charge_occurrence (d : Depth P) (hn : 2≤Fintype.card P) (w : I → ℝ)
    (B : I → Finset P) (hB : ∀ i, (B i).Nonempty) (δ : ℝ) (hδ : 0≤δ)
    (hp : ∀ i x, prob (B i) x≤δ) (ha : ∀ x, prob (Finset.univ : Finset P) x≤δ) :
    (∑ i, w i*charge d δ (prob (B i)) (prob Finset.univ))=
      weightedIntegral d.mass (familyCutError w B δ) := by
  have ha1 : ∑ x, prob (Finset.univ : Finset P) x=1 := sum_prob _ (by
    apply Finset.univ_nonempty_iff.mpr
    exact Fintype.card_pos_iff.mp (by omega))
  simp only [charge_occurrence d hn δ hδ _ _ (sum_prob _ (hB _)) ha1 (hp _) ha]
  simp only [weightedIntegral,Finset.mul_sum,familyCutError]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro i _
  simp only [mass,sum_prob_cell]
  ring

/-- One coordinate of the finite tree contradiction, before arithmetic
averaging. The incoming laws are arbitrary probabilities representing the
actual conditional source law, not an independence hypothesis. -/
lemma length_upper (d d' : Depth P) (δ : ℝ) (hδ : 0≤δ)
    (a t : P → ℝ) (ρ : P → P → ℝ) (w : I → ℝ) (p : I → P → ℝ) (src : I → P)
    (ha0 : ∀ x, 0≤a x) (ht0 : ∀ y, 0≤t y) (hρ0 : ∀ y x, 0≤ρ y x) (hw : ∀ i, 0≤w i)
    (ha : ∑ x, a x=1) (ht : ∑ y, t y=1) (hρ : ∀ y, ∑ x, ρ y x=1) (hW : ∑ i, w i=1)
    (hp : ∀ i, ∑ y, p i y=1) (hp0 : ∀ i y, 0≤p i y)
    (has : ∀ x, a x≤δ) (hps : ∀ i x, p i x≤δ)
    (htm : t=fun y => ∑ i, w i*p i y)
    (hedge : ∀ F : P → P → ℝ, (∑ y, t y*∑ x, ρ y x*F x y)=∑ i, w i*∑ y, p i y*F (src i) y) :
    δ^3*(∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass a B)) C)≤
      2*Global.fiberCutDiscrepancy w p src δ d d'+
      4*(∑ i, w i*charge d δ (p i) a)+2*(∑ i, w i*charge d' δ (p i) a)+
      2*(∑ y, t y*cost d.allCuts (d.cutLength (fun B => tent δ (mass a B))) (ρ y) a) := by
  let l := d.cutLength (fun B => tent δ (mass a B))
  have hl (C) (_ : C∈d.allCuts) : 0≤l C := d.cutLength_nonneg _ (fun C => tent_nonneg _ _) C
  have hlow := d.actual_cut_fluctuation a ha0 ha (tent δ) (tent_nonneg δ) δ hδ (fun u hn => by
    apply le_antisymm _ (tent_nonneg δ u)
    by_contra hh
    have hu := tent_positive (lt_of_not_ge hh)
    exact hn ⟨hu.1.le,by linarith [hu.2]⟩)
  have hupper := iid_transfer d.allCuts d.allCuts_laminar l hl a t ρ ha0 ht0 hρ0 ha ht hρ
    (rootDistance d'.allCuts (d'.cutLength (fun B => tent δ (mass a B))))
  rw [hedge] at hupper
  have hproj : (∑ i, w i*∑ y, p i y*
      |distance d.allCuts l (src i) y-rootDistance d'.allCuts (d'.cutLength (fun B => tent δ (mass a B))) y|)≤
      Global.fiberCutDiscrepancy w p src δ d d'+∑ i, w i*charge d δ (p i) a+∑ i, w i*charge d' δ (p i) a := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s:=Finset.univ) (fun y _ => mul_le_mul_of_nonneg_left
        (projection_replacement d d' δ hδ (p i) a (hp i) ha (hps i) has (src i) y) (hp0 i y))) (hw i))
    simpa only [Global.fiberCutDiscrepancy,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul,l] using hh
  have hcost : cost d.allCuts l t a≤∑ i, w i*charge d δ (p i) a := by
    rw [htm]
    exact (cost_mixture d.allCuts l hl w p a hw hW).trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (cost_le_charge d δ hδ (p i) a (hp i) ha (hps i) has) (hw i)))
  dsimp only [l] at hupper hproj hcost
  linarith
end WeakPinned.Cuts
noncomputable section
namespace WeakPinned.Core.Fibers
open MeasureTheory Hierarchy Variance Cuts
open scoped BigOperators
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype I] in
lemma conditionalSource_nonneg (y x : V) : 0≤G.conditionalSource y x := by
  unfold conditionalSource
  split_ifs <;> exact prob_nn _ _

omit [Fintype I] in
lemma conditionalSource_sum (hn : 2≤Fintype.card V) (y : V) : ∑ x, G.conditionalSource y x=1 := by
  unfold conditionalSource
  split_ifs with h
  · exact sum_prob _ h
  · exact sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))

omit [Fintype I] in
lemma incomingWeight_nonneg (y : V) : 0≤G.incomingWeight y := by unfold incomingWeight edgeCount; positivity

omit [Fintype I] in
lemma sampling_conditional (y x : V) : G.incomingWeight y*G.conditionalSource y x=G.edgeLaw x y := by
  by_cases h : (G.incoming y).Nonempty
  · simpa only [conditionalSource,ite_eq_left h] using G.sampling_incoming x y
  · have he : G.incoming y=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hh := G.sampling_incoming x y
    have hw : G.incomingWeight y=0 := by simp [incomingWeight,he]
    simp only [hw,zero_mul] at hh ⊢
    exact hh

lemma incoming_eval (F : V → V → ℝ) :
    (∑ y, G.incomingWeight y*∑ x, G.conditionalSource y x*F x y)=
      ∑ e, G.fiberWeight e*∑ y, prob (G.targets e) y*F (G.source e) y := by
  simp only [Finset.mul_sum,← mul_assoc,G.sampling_conditional,← G.sampling_fiber,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext y
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro y _
  simp only [ite_mul,zero_mul]
  simp

lemma incoming_repr : G.incomingWeight=fun y => ∑ e, G.fiberWeight e*prob (G.targets e) y := by
  funext y
  rw [G.fiber_marginal,G.incoming_marginal]

omit [Fintype I] in
lemma omittedMass_nonneg (T : ℝ) : 0≤G.omittedMass T := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact G.incomingWeight_nonneg y
  · rfl

omit [Fintype I] in
lemma retained_cost (d : Depth V) (δ T : ℝ) (hδ : 0≤δ) (hT : 0<T)
    (has : ∀ x, prob (Finset.univ : Finset V) x≤δ)
    (hrs : ∀ y x, prob (G.retainedSet T y) x≤δ)
    (hrn : ∀ y, (G.retainedSet T y).Nonempty) (hn : 2≤Fintype.card V) :
    (∑ y, G.incomingWeight y*cost d.allCuts (d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)))
      (G.conditionalSource y) (prob Finset.univ))≤
      (∑ y, G.retainedWeight T y*charge d δ (prob (G.retainedSet T y)) (prob Finset.univ))+
      G.omittedMass T*(∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)) C) := by
  have ha : ∑ x, prob (Finset.univ : Finset V) x=1 :=
    sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
  unfold omittedMass
  rw [Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  by_cases hs : T≤((G.incoming y).card:ℝ)
  · have hy : (G.incoming y).Nonempty := Finset.card_pos.mp (by exact_mod_cast hT.trans_le hs)
    have he : G.retainedSet T y=G.incoming y := by simp only [retainedSet,ite_eq_left hs]
    have hh := cost_le_charge d δ hδ (prob (G.retainedSet T y)) (prob Finset.univ)
      (sum_prob _ (hrn y)) ha (hrs y) has
    simp only [he] at hh
    simpa only [retainedWeight,ite_eq_left hs,conditionalSource,ite_eq_left hy,not_lt_of_ge hs,ite_false,zero_mul,add_zero,he]
      using mul_le_mul_of_nonneg_left hh (G.incomingWeight_nonneg y)
  · have hh := cost_bound d.allCuts (d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)))
      (fun C _ => d.cutLength_nonneg _ (fun B => tent_nonneg _ _) C)
      (G.conditionalSource y) (prob Finset.univ) (G.conditionalSource_nonneg y) (prob_nn _)
      (G.conditionalSource_sum hn y) ha
    simpa only [retainedWeight,ite_eq_right hs,lt_of_not_ge hs,ite_true,zero_mul,zero_add] using
      mul_le_mul_of_nonneg_left hh (G.incomingWeight_nonneg y)

lemma graph_length_upper (d d' : Depth V) (δ T : ℝ) (hδ : 0≤δ) (hT : 0<T)
    (hn : 2≤Fintype.card V) (hG : 0<G.edgeCount)
    (has : ∀ x, prob (Finset.univ : Finset V) x≤δ)
    (hps : ∀ e x, prob (G.targets e) x≤δ) (hpn : ∀ e, (G.targets e).Nonempty)
    (hrs : ∀ y x, prob (G.retainedSet T y) x≤δ) (hrn : ∀ y, (G.retainedSet T y).Nonempty) :
    δ^3*(∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)) C)≤
      2*Global.fiberCutDiscrepancy G.fiberWeight (fun e => prob (G.targets e)) G.source δ d d'+
      4*(∑ e, G.fiberWeight e*charge d δ (prob (G.targets e)) (prob Finset.univ))+
      2*(∑ e, G.fiberWeight e*charge d' δ (prob (G.targets e)) (prob Finset.univ))+
      2*(∑ y, G.retainedWeight T y*charge d δ (prob (G.retainedSet T y)) (prob Finset.univ))+
      2*G.omittedMass T*(∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)) C) := by
  have ha : ∑ x, prob (Finset.univ : Finset V) x=1 :=
    sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
  have hh := length_upper d d' δ hδ (prob Finset.univ) G.incomingWeight G.conditionalSource G.fiberWeight
    (fun e => prob (G.targets e)) G.source (prob_nn _) G.incomingWeight_nonneg G.conditionalSource_nonneg
    G.fiberWeight_nonneg ha (G.sum_incomingWeight hG) (G.conditionalSource_sum hn) (G.sum_fiberWeight hG)
    (fun e => sum_prob _ (hpn e)) (fun e => prob_nn _) has hps G.incoming_repr G.incoming_eval
  have hc := G.retained_cost d δ T hδ hT has hrs hrn hn
  linarith
end WeakPinned.Core.Fibers

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.UnboundedContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23

section

namespace WeakPinned
open Filter Variance Global Cuts
open scoped Topology BigOperators

lemma change_scale_rate (W A X : ℕ → ℝ) (C : ℝ) (hC : 0<C)
    (hW : ∀ j, 0≤W j) (hA : ∀ j, 0≤A j) (hX : ∀ j, 0≤X j)
    (hWtop : Tendsto W atTop atTop)
    (hcomp : ∀ᶠ j in atTop, A j≤C*(W j+1))
    (hrate : Tendsto (fun j => X j/(W j+A j+1)) atTop (𝓝 0)) :
    Tendsto (fun j => X j/W j) atTop (𝓝 0) := by
  have hb : ∀ᶠ j in atTop, X j/W j≤(2+2*C)*(X j/(W j+A j+1)) := by
    filter_upwards [hWtop.eventually (eventually_ge_atTop (1:ℝ)),hcomp] with j hj hc
    have hw : 0<W j := by linarith
    have hd : 0<W j+A j+1 := by linarith [hA j]
    apply (div_le_iff₀ hw).mpr
    have hbound : W j+A j+1≤(2+2*C)*W j := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hbound (hX j)
    convert (div_le_div_of_nonneg_right hh hd.le) using 1 <;> field_simp
  exact squeeze_zero' (Eventually.of_forall (fun j => div_nonneg (hX j) (hW j))) hb
    (by simpa using hrate.const_mul (2+2*C))

end WeakPinned

noncomputable section
namespace WeakPinned.Cuts
open Hierarchy Variance
variable {P : Type u9} [Fintype P] [DecidableEq P]
lemma tent_length_occurrence (d : Depth P) (hn : 2≤Fintype.card P) (δ : ℝ) (hδ : 0≤δ)
    (has : ∀ x, prob (Finset.univ : Finset P) x≤δ) :
    (∑ C ∈ d.allCuts, d.cutLength (fun B => tent δ (mass (prob Finset.univ) B)) C)=
      weightedIntegral d.mass (fun C => tent δ (cellProb Finset.univ C)) := by
  have ha : ∑ x, prob (Finset.univ : Finset P) x=1 :=
    sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
  symm
  simp only [← sum_prob_cell]
  change weightedIntegral d.mass (fun C => tent δ (mass (prob Finset.univ) C))=_
  exact d.symmetric_integral_cut_sum hn _ (fun C hC => tent_zero_left (mass_small _ δ hδ has C hC))
    (fun C => by rw [mass_complement _ ha,tent_symm])
end WeakPinned.Cuts

namespace WeakPinned.Global
open Hierarchy Variance Cuts MeasureTheory
open scoped BigOperators
variable {P : Type u10} [Fintype P] [DecidableEq P]
variable {K : Type u11} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

lemma average_swap (f : Depth P → Depth P → ℝ) :
    average Z₂ Z₁ h₂ h₁ f=average Z₁ Z₂ h₁ h₂ (fun d d' => f d' d) := by
  classical
  unfold average placeUnion
  rw [Finset.union_comm (badPlaces Z₂ h₂)]

omit [NumberField K] in
include h₁ in
lemma integrable_weighted_left (hn : 2≤Fintype.card P) (f : Finset P → ℝ) :
    AverageIntegrable Z₁ Z₂ (fun d _ => weightedIntegral d.mass f) := by
  intro v
  apply integrable_finsetSum
  intro C _
  exact (integrable_mass_left Z₁ Z₂ h₁ hn C v).mul_const (f C)

omit [NumberField K] in
include h₂ in
lemma integrable_weighted_right (hn : 2≤Fintype.card P) (f : Finset P → ℝ) :
    AverageIntegrable Z₁ Z₂ (fun _ d' => weightedIntegral d'.mass f) := by
  intro v
  apply integrable_finsetSum
  intro C _
  exact (integrable_mass_right Z₁ Z₂ h₂ hn C v).mul_const (f C)

lemma average_weighted_left (hn : 2≤Fintype.card P) (f : Finset P → ℝ) :
    average Z₁ Z₂ h₁ h₂ (fun d _ => weightedIntegral d.mass f)=weightedIntegral (cellMass Z₁ h₁) f := by
  simp only [weightedIntegral,mul_comm _ (f _)]
  rw [average_sum Z₁ Z₂ h₁ h₂ _ (fun C v => (integrable_mass_left Z₁ Z₂ h₁ hn C v).const_mul (f C))]
  simp_rw [average_mul,average_mass_left Z₁ Z₂ h₁ h₂ hn]

lemma average_weighted_right (hn : 2≤Fintype.card P) (f : Finset P → ℝ) :
    average Z₁ Z₂ h₁ h₂ (fun _ d' => weightedIntegral d'.mass f)=weightedIntegral (cellMass Z₂ h₂) f := by
  simp only [weightedIntegral,mul_comm _ (f _)]
  rw [average_sum Z₁ Z₂ h₁ h₂ _ (fun C v => (integrable_mass_right Z₁ Z₂ h₂ hn C v).const_mul (f C))]
  simp_rw [average_mul,average_mass_right Z₁ Z₂ h₁ h₂ hn]

omit [NumberField K] in
include h₁ h₂ in
lemma integrable_total_integral (hn : 2≤Fintype.card P) (f : Finset P → ℝ) :
    AverageIntegrable Z₁ Z₂ (localTotalIntegral f) := fun v =>
  (integrable_weighted_left Z₁ Z₂ h₁ hn f v).add (integrable_weighted_right Z₁ Z₂ h₂ hn f v)

lemma average_total_integral (hn : 2≤Fintype.card P) (f : Finset P → ℝ) :
    average Z₁ Z₂ h₁ h₂ (localTotalIntegral f)=weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) f := by
  change average Z₁ Z₂ h₁ h₂ (fun d d' => weightedIntegral d.mass f+weightedIntegral d'.mass f)=_
  rw [average_add Z₁ Z₂ h₁ h₂ (integrable_weighted_left Z₁ Z₂ h₁ hn f)
    (integrable_weighted_right Z₁ Z₂ h₂ hn f),average_weighted_left Z₁ Z₂ h₁ h₂ hn,
    average_weighted_right Z₁ Z₂ h₁ h₂ hn]
  simp only [weightedIntegral,totalMass,add_mul,Finset.sum_add_distrib]

end WeakPinned.Global

namespace WeakPinned.Core.Fibers
open Hierarchy Variance Cuts Global
variable {V : Type u12} {I : Type u13} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)
lemma two_length_upper (d d' : Depth V) (δ T : ℝ) (hδ : 0≤δ) (hT : 0<T)
    (hn : 2≤Fintype.card V) (hG : 0<G.edgeCount)
    (has : ∀ x, prob (Finset.univ : Finset V) x≤δ)
    (hps : ∀ e x, prob (G.targets e) x≤δ) (hpn : ∀ e, (G.targets e).Nonempty)
    (hrs : ∀ y x, prob (G.retainedSet T y) x≤δ) (hrn : ∀ y, (G.retainedSet T y).Nonempty) :
    δ^3*localTotalIntegral (fun C => tent δ (cellProb Finset.univ C)) d d'≤
      2*(fiberCutDiscrepancy G.fiberWeight (fun e => prob (G.targets e)) G.source δ d d'+
        fiberCutDiscrepancy G.fiberWeight (fun e => prob (G.targets e)) G.source δ d' d)+
      6*localTotalIntegral (familyCutError G.fiberWeight G.targets δ) d d'+
      2*localTotalIntegral (familyCutError (G.retainedWeight T) (G.retainedSet T) δ) d d'+
      2*G.omittedMass T*localTotalIntegral (fun C => tent δ (cellProb Finset.univ C)) d d' := by
  have h1 := G.graph_length_upper d d' δ T hδ hT hn hG has hps hpn hrs hrn
  have h2 := G.graph_length_upper d' d δ T hδ hT hn hG has hps hpn hrs hrn
  simp only [tent_length_occurrence _ hn δ hδ has,
    family_charge_occurrence _ hn G.fiberWeight G.targets hpn δ hδ hps has,
    family_charge_occurrence _ hn (G.retainedWeight T) (G.retainedSet T) hrn δ hδ hrs has] at h1 h2
  dsimp only [localTotalIntegral]
  linarith
end WeakPinned.Core.Fibers

namespace WeakPinned.Global
open Hierarchy Variance Cuts MeasureTheory
variable {V : Type u14} {I : Type u15} [Fintype V] [Fintype I] [DecidableEq V]
variable {K : Type u16} [Field K] [NumberField K]
variable (G : Core.Fibers V I) (Z₁ Z₂ : V → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

lemma arithmetic_length_upper (t : I → K) (ht : ∀ e y, y∈G.targets e →
      (Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e)
    (δ T : ℝ) (hδ : 0≤δ) (hT : 0<T) (hn : 2≤Fintype.card V) (hG : 0<G.edgeCount)
    (has : ∀ x, prob (Finset.univ : Finset V) x≤δ)
    (hps : ∀ e x, prob (G.targets e) x≤δ) (hpn : ∀ e, (G.targets e).Nonempty)
    (hrs : ∀ y x, prob (G.retainedSet T y) x≤δ) (hrn : ∀ y, (G.retainedSet T y).Nonempty) :
    δ^3*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (fun C => tent δ (cellProb Finset.univ C))≤
      48+6*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (familyCutError G.fiberWeight G.targets δ)+
      2*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (familyCutError (G.retainedWeight T) (G.retainedSet T) δ)+
      2*G.omittedMass T*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (fun C => tent δ (cellProb Finset.univ C)) := by
  have hL := integrable_total_integral Z₁ Z₂ h₁ h₂ hn (fun C => tent δ (cellProb Finset.univ C))
  have hF := integrable_total_integral Z₁ Z₂ h₁ h₂ hn (familyCutError G.fiberWeight G.targets δ)
  have hR := integrable_total_integral Z₁ Z₂ h₁ h₂ hn (familyCutError (G.retainedWeight T) (G.retainedSet T) δ)
  have hp := fun e => sum_prob (G.targets e) (hpn e)
  have hD := fiber_cut_discrepancy_integrable Z₁ Z₂ h₁ h₂ G.fiberWeight (fun e => prob (G.targets e)) G.source hp δ hδ hps
  have hD' := fiber_cut_discrepancy_integrable Z₂ Z₁ h₂ h₁ G.fiberWeight (fun e => prob (G.targets e)) G.source hp δ hδ hps
  have hh := average_mono Z₁ Z₂ h₁ h₂ (fun v => (hL v).const_mul (δ^3))
    (fun v => (((((hD v).add (hD' v)).const_mul 2).add ((hF v).const_mul 6)).add
      ((hR v).const_mul 2)).add ((hL v).const_mul (2*G.omittedMass T)))
    (fun d d' => G.two_length_upper d d' δ T hδ hT hn hG has hps hpn hrs hrn)
  rw [average_add Z₁ Z₂ h₁ h₂
    (fun v => ((((hD v).add (hD' v)).const_mul 2).add ((hF v).const_mul 6)).add ((hR v).const_mul 2))
    (fun v => (hL v).const_mul (2*G.omittedMass T))] at hh
  rw [average_add Z₁ Z₂ h₁ h₂
    (fun v => (((hD v).add (hD' v)).const_mul 2).add ((hF v).const_mul 6))
    (fun v => (hR v).const_mul 2)] at hh
  rw [average_add Z₁ Z₂ h₁ h₂
    (fun v => ((hD v).add (hD' v)).const_mul 2) (fun v => (hF v).const_mul 6)] at hh
  simp only [average_mul] at hh
  have hpx (e) : prob (G.targets e) (G.source e)=0 := by simp [prob,G.no_loop e]
  have hte (e) (z) (hz : prob (G.targets e) z≠0) :
      (Z₁ (G.source e)-Z₁ z)*(Z₂ (G.source e)-Z₂ z)=t e := by
    apply ht
    by_contra h
    exact hz (by simp [prob,h])
  have hd := arithmetic_fiber_cut Z₁ Z₂ h₁ h₂ G.fiberWeight (fun e => prob (G.targets e)) G.source t
    G.fiberWeight_nonneg (G.sum_fiberWeight hG) (fun e => Core.Fibers.prob_nn (G.targets e)) hp hpx hte δ hδ hps
  have hd' := arithmetic_fiber_cut Z₂ Z₁ h₂ h₁ G.fiberWeight (fun e => prob (G.targets e)) G.source t
    G.fiberWeight_nonneg (G.sum_fiberWeight hG) (fun e => Core.Fibers.prob_nn (G.targets e)) hp hpx
    (fun e z hz => by rw [mul_comm]; exact hte e z hz) δ hδ hps
  rw [average_swap] at hd'
  rw [average_add Z₁ Z₂ h₁ h₂ hD (fun v => hD' v)] at hh
  simp only [average_total_integral Z₁ Z₂ h₁ h₂ hn] at hh
  linarith
end WeakPinned.Global
noncomputable section
namespace WeakPinned
open Filter Variance Core.Fibers
open scoped Topology
variable {V : Type u17} {I : Type u18} [Fintype V] [Fintype I] [DecidableEq V]

omit [Fintype V] in
lemma prob_bound_of_size (B : Finset V) (δ : ℝ) (hδ : 0<δ) (hB : 1/δ≤(B.card:ℝ)) :
    B.Nonempty ∧ ∀ x, prob B x≤δ := by
  have hb : 0<(B.card:ℝ) := (one_div_pos.mpr hδ).trans_le hB
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hb),?_⟩
  intro x
  unfold prob
  split_ifs
  · exact (div_le_iff₀ hb).mpr (by have := (div_le_iff₀ hδ).mp hB; nlinarith)
  · exact hδ.le

lemma PreparedGraph.omitted_bound {G : Core.Fibers V I} {θ γ c η : ℝ}
    (hG : PreparedGraph V I G θ γ c η) (hθ : 0<θ) (hη : η≤θ/2) :
    G.omittedMass ((Fintype.card V:ℝ)^γ) ≤ (4/θ)*(Fintype.card V:ℝ)^(γ-1) := by
  let n : ℝ := Fintype.card V
  have hn : 2≤n := by dsimp only [n]; exact_mod_cast hG.card_ge
  have hn0 : 0<n := by linarith
  have hE := hG.edgeCount_pos (by linarith)
  have hEl : (θ/4)*n^2≤G.edgeCount := by
    have hp : 0≤(n-1)*n := mul_nonneg (by linarith) hn0.le
    have hh := mul_nonneg (show 0≤θ-η-θ/2 by linarith) hp
    have hh' := mul_nonneg (show 0≤θ/4 by positivity) (show 0≤n*(n-2) by positivity)
    dsimp [n] at *
    nlinarith [hG.lower]
  apply (G.small_incoming_mass _ (Real.rpow_nonneg hn0.le γ)).trans
  change n*n^γ/G.edgeCount≤(4/θ)*n^(γ-1)
  rw [Real.rpow_sub hn0,Real.rpow_one]
  apply (div_le_iff₀ hE).mpr
  have hh := mul_le_mul_of_nonneg_left hEl (show 0≤(4/θ)*(n^γ/n) by positivity)
  have he : (4/θ)*(n^γ/n)*((θ/4)*n^2)=n*n^γ := by field_simp
  rw [he] at hh
  exact hh

variable {Vn : ℕ → Type u19} {In : ℕ → Type u20} [∀ j, Fintype (Vn j)] [∀ j, Fintype (In j)] [∀ j, DecidableEq (Vn j)]
lemma omitted_rate (G : ∀ j, Core.Fibers (Vn j) (In j)) (θ γ c : ℝ) (η : ℕ → ℝ)
    (hθ : 0<θ) (hγ1 : γ<1) (hη : ∀ j, η j≤θ/2)
    (hn : Tendsto (fun j => (Fintype.card (Vn j):ℝ)) atTop atTop)
    (hG : ∀ j, PreparedGraph (Vn j) (In j) (G j) θ γ c (η j)) :
    Tendsto (fun j => (G j).omittedMass ((Fintype.card (Vn j):ℝ)^γ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => (G j).omittedMass_nonneg _) (fun j => (hG j).omitted_bound hθ (hη j))
  have hh := (tendsto_rpow_neg_atTop (show 0<1-γ by linarith)).comp hn
  have he : -(1-γ)=γ-1 := by ring
  rw [he] at hh
  simpa using hh.const_mul (4/θ)

lemma sampling_atoms_eventually (G : ∀ j, Core.Fibers (Vn j) (In j)) (θ γ c : ℝ) (η : ℕ → ℝ)
    (γ0 : 0<γ) (γ1 : γ<1) (δ : ℝ) (hδ : 0<δ)
    (hn : Tendsto (fun j => (Fintype.card (Vn j):ℝ)) atTop atTop)
    (hG : ∀ j, PreparedGraph (Vn j) (In j) (G j) θ γ c (η j)) :
    ∀ᶠ j in atTop,
      (∀ x, prob (Finset.univ : Finset (Vn j)) x≤δ) ∧
      (∀ e, ((G j).targets e).Nonempty) ∧ (∀ e x, prob ((G j).targets e) x≤δ) ∧
      (∀ y, ((G j).retainedSet ((Fintype.card (Vn j):ℝ)^γ) y).Nonempty) ∧
      (∀ y x, prob ((G j).retainedSet ((Fintype.card (Vn j):ℝ)^γ) y) x≤δ) := by
  have hpow := (tendsto_rpow_atTop γ0).comp hn
  filter_upwards [hn.eventually (eventually_ge_atTop (1/δ)),hpow.eventually (eventually_ge_atTop (1/δ))] with j hnδ hnγ
  have hn1 : (1:ℝ)≤Fintype.card (Vn j) := by exact_mod_cast (show 1≤Fintype.card (Vn j) by have := (hG j).card_ge; omega)
  have hs : (Fintype.card (Vn j):ℝ)^γ≤Fintype.card (Vn j) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 γ1.le
  have hf (e) := prob_bound_of_size ((G j).targets e) δ hδ (hnγ.trans ((hG j).fiber e).le)
  have hr (y) := prob_bound_of_size ((G j).retainedSet ((Fintype.card (Vn j):ℝ)^γ) y) δ hδ
    (hnγ.trans ((G j).retainedSet_size _ hs y))
  exact ⟨(prob_bound_of_size Finset.univ δ hδ (by simpa using hnδ)).2,
    fun e => (hf e).1,fun e => (hf e).2,fun y => (hr y).1,fun y => (hr y).2⟩
end WeakPinned
noncomputable section
namespace WeakPinned
open Filter Variance Global Cuts
open scoped Topology BigOperators

lemma length_rate_contradiction (W F R L o : ℕ → ℝ) (δ b : ℝ) (hδ : 0<δ) (hb : 0<b)
    (hW : Tendsto W atTop atTop)
    (hF : Tendsto (fun j => F j/W j) atTop (𝓝 0))
    (hR : Tendsto (fun j => R j/W j) atTop (𝓝 0))
    (ho : Tendsto o atTop (𝓝 0))
    (hlow : ∀ᶠ j in atTop, b*W j≤L j)
    (hupp : ∀ᶠ j in atTop, δ^3*L j≤48+6*F j+2*R j+2*o j*L j) : False := by
  have h48 : Tendsto (fun j => (48:ℝ)/W j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero, Function.comp_apply] using (tendsto_inv_atTop_zero.comp hW).const_mul 48
  have he : Tendsto (fun j => (48+6*F j+2*R j)/W j) atTop (𝓝 0) := by
    convert (h48.add (hF.const_mul 6)).add (hR.const_mul 2) using 1
    · ext j; ring
    · norm_num
  have hbound := ho.eventually (gt_mem_nhds (show 0<δ^3/4 by positivity))
  have hsmall := he.eventually (gt_mem_nhds (show 0<δ^3*b/2 by positivity))
  obtain ⟨j,hjW,hjo,hje,hjl,hju⟩ := (hW.eventually (eventually_gt_atTop (0:ℝ)) |>.and
    (hbound.and (hsmall.and (hlow.and hupp)))).exists
  have hl0 : 0<L j := (mul_pos hb hjW).trans_le hjl
  have hopen := mul_le_mul_of_nonneg_right hjo.le hl0.le
  have he' := (div_lt_iff₀ hjW).mp hje
  have hl' := mul_le_mul_of_nonneg_left hjl (show 0≤δ^3/2 by positivity)
  nlinarith

variable {V : ℕ → Type u21} {I : ℕ → Type u22} {K : ℕ → Type u23} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

/-- The entire unbounded regime is impossible for the actual prepared
arithmetic models, allowing arbitrary and varying number fields. -/
theorem arithmetic_no_unbounded_oai (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hc : 0<c) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e)
    (hWtop : Tendsto (fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)) atTop atTop) : False := by
  obtain ⟨δ,hδ,_,hlow⟩ := arithmetic_balanced_length G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht hWtop
  let W := fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let A := fun j => potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let m := fun j => totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let F := fun j => weightedIntegral (m j) (familyCutError (G j).fiberWeight (G j).targets δ)
  let R := fun j => weightedIntegral (m j) (familyCutError
    ((G j).retainedWeight ((Fintype.card (V j):ℝ)^γ)) ((G j).retainedSet ((Fintype.card (V j):ℝ)^γ)) δ)
  have hF0 (j) : 0≤F j := Finset.sum_nonneg (fun C _ => mul_nonneg (totalMass_nonneg _ _ _ _ C)
    (Finset.sum_nonneg (fun e _ => mul_nonneg ((G j).fiberWeight_nonneg e) (cutError_nonneg _ _ _))))
  have hR0 (j) : 0≤R j := Finset.sum_nonneg (fun C _ => mul_nonneg (totalMass_nonneg _ _ _ _ C)
    (Finset.sum_nonneg (fun y _ => mul_nonneg ((G j).retainedWeight_nonneg _ y) (cutError_nonneg _ _ _))))
  have hcomp := arithmetic_scale_comparison G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  have hcut := sampling_cut_approximation_rates G θ γ c η Z₁ Z₂ h₁ h₂ δ hδ hθ hγ hγ1 hc hcγ hn hη hη0 hηb hG t ht
  have hf := change_scale_rate W A F (64+8/θ) (by positivity)
    (fun j => overlapScale_nonneg _ _ _ _) (fun j => potentialScale_nonneg _ _ _ _) hF0 hWtop hcomp hcut.1
  have hr := change_scale_rate W A R (64+8/θ) (by positivity)
    (fun j => overlapScale_nonneg _ _ _ _) (fun j => potentialScale_nonneg _ _ _ _) hR0 hWtop hcomp hcut.2
  apply length_rate_contradiction W F R (fun j => weightedIntegral (m j) (fun C => tent δ (cellProb Finset.univ C)))
    (fun j => (G j).omittedMass ((Fintype.card (V j):ℝ)^γ)) δ (δ/4) hδ (by positivity)
    hWtop hf hr (omitted_rate G θ γ c η hθ hγ1 hηb hn hG) hlow
  filter_upwards [sampling_atoms_eventually G θ γ c η hγ hγ1 δ hδ hn hG] with j hj
  exact arithmetic_length_upper (G j) (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) (t j) (ht j) δ
    ((Fintype.card (V j):ℝ)^γ) hδ.le (Real.rpow_pos_of_pos (by exact_mod_cast (show 0<Fintype.card (V j) by have := (hG j).card_ge; omega)) γ)
    (hG j).card_ge ((hG j).edgeCount_pos (by linarith [hηb j])) hj.1 hj.2.2.1 hj.2.1 hj.2.2.2.2 hj.2.2.2.1
end WeakPinned

end
end
end
end

end OAI
end

theorem solution.{u21, u22, u23} : type_of% @OAI.WeakPinned.arithmetic_no_unbounded_oai.{u21, u22, u23} := @OAI.WeakPinned.arithmetic_no_unbounded_oai.{u21, u22, u23}
