-- Prove2me | solution 1 for OAI.WeakPinned.sampling_variance_rates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:03:08.87423+00:00
-- url     : https://prove2.me/submissions/500b0a20-dada-4947-9924-76e00ee19f8b

import Mathlib
import Definitions.Def_PinnedDistances
import Definitions.Def_OAIQWWP000

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

omit [DecidableEq P] in
lemma ambient_card_ge_two (B : Finset P) (hB : 2 ≤ B.card) :
    2 ≤ Fintype.card P := hB.trans (Finset.card_le_univ B)

lemma mixedProb_decompose (B : Finset P) (hB : 2 ≤ B.card) (x y : P) :
    mixedProb B x y = (B.card : ℝ) / Fintype.card P * pairProb B x y +
      prob B x / Fintype.card P * (if y ∈ B then 0 else 1) := by
  have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  have hn : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast (by have := ambient_card_ge_two B hB; omega : Fintype.card P ≠ 0)
  have hk1 : (B.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
    linarith
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> by_cases hxy : x = y
  all_goals simp_all [mixedProb, pairProb, prob]
  all_goals field_simp

lemma sum_mixedProb (B : Finset P) (hB : 2 ≤ B.card) (x : P) :
    ∑ y, mixedProb B x y = prob B x := by
  have hn : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast (by have := ambient_card_ge_two B hB; omega : Fintype.card P ≠ 0)
  have hout : (∑ y : P, (if y ∈ B then (0 : ℝ) else 1)) =
      Fintype.card P - (B.card : ℝ) := by
    have he : ∀ y : P, (if y ∈ B then (0 : ℝ) else 1) =
        if y ∈ Bᶜ then 1 else 0 := by intro y; simp
    simp_rw [he]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.card_compl,
      Nat.cast_sub (Finset.card_le_univ B)]
  simp_rw [mixedProb_decompose B hB, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_pairProb B hB, hout]
  field_simp
  ring

lemma sum_mixedProb_left (B : Finset P) (hB : 2 ≤ B.card) (y : P) :
    ∑ x, mixedProb B x y = 1 / Fintype.card P := by
  have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  have hne : B.Nonempty := Finset.card_pos.mp (by omega)
  simp_rw [mixedProb_decompose B hB, Finset.sum_add_distrib,
    ← Finset.mul_sum, pairProb_symm B _ y, sum_pairProb B hB,
    ← Finset.sum_mul, ← Finset.sum_div, sum_prob B hne]
  by_cases hy : y ∈ B <;> simp [prob, hy]
  field_simp

lemma mixedProb_diag (B : Finset P) (x : P) : mixedProb B x x = 0 := by
  simp [mixedProb]

lemma signedPair_diag (B : Finset P) (x : P) : signedPair B x x = 0 := by
  simp [signedPair, pairProb_diag, mixedProb_diag]

lemma signedPair_row (B : Finset P) (hB : 2 ≤ B.card) (x : P) :
    (∑ y, signedPair B x y) = 1 / Fintype.card P - prob B x := by
  have hP : 2 ≤ (Finset.univ : Finset P).card := ambient_card_ge_two B hB
  simp_rw [signedPair, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_pairProb B hB, sum_mixedProb B hB,
    sum_pairProb Finset.univ hP]
  simp only [prob, Finset.mem_univ, reduceIte, Finset.card_univ]
  ring

lemma signedPair_col (B : Finset P) (hB : 2 ≤ B.card) (y : P) :
    (∑ x, signedPair B x y) = prob B y - 1 / Fintype.card P := by
  have hP : 2 ≤ (Finset.univ : Finset P).card := ambient_card_ge_two B hB
  simp_rw [signedPair, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_mixedProb_left B hB, pairProb_symm B _ y,
    pairProb_symm Finset.univ _ y, sum_pairProb B hB,
    sum_pairProb Finset.univ hP]
  simp only [prob, Finset.mem_univ, reduceIte, Finset.card_univ]
  ring

/-- Exact cancellation against every additive off-diagonal overlap kernel.
    Only the sum of the two marginals is constrained. -/
lemma additive_cancel (H L : P → P → ℝ) (b : ℝ) (S : P → ℝ)
    (hdiag : ∀ x, H x x = 0)
    (hmass : (∑ x, ∑ y, H x y) = 0)
    (hmarg : ∀ x, (∑ y, H x y) + ∑ y, H y x = 0)
    (hL : ∀ x y, x ≠ y → L x y = b + S x + S y) :
    (∑ x, ∑ y, H x y * L x y) = 0 := by
  have hterm (x y : P) : H x y * L x y = H x y * (b + S x + S y) := by
    by_cases h : x = y
    · subst y; simp [hdiag]
    · rw [hL x y h]
  simp_rw [hterm, mul_add, Finset.sum_add_distrib]
  have hb : (∑ x, ∑ y, H x y * b) = (∑ x, ∑ y, H x y) * b := by
    simp_rw [Finset.sum_mul]
  rw [hb, hmass, zero_mul, zero_add]
  have h₁ : (∑ x, ∑ y, H x y * S x) = ∑ x, (∑ y, H x y) * S x := by
    simp_rw [Finset.sum_mul]
  have h₂ : (∑ x, ∑ y, H x y * S y) = ∑ x, (∑ y, H y x) * S x := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  rw [h₁, h₂, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _
  rw [← add_mul, hmarg, zero_mul]

lemma variance_cancel (B : Finset P) (hB : 2 ≤ B.card)
    (L : P → P → ℝ) (b : ℝ) (S : P → ℝ)
    (hL : ∀ x y, x ≠ y → L x y = b + S x + S y) :
    (∑ x, ∑ y, signedPair B x y * L x y) = 0 := by
  apply additive_cancel _ _ b S (signedPair_diag B) _ _ hL
  · simp_rw [signedPair_row B hB, Finset.sum_sub_distrib]
    have hn : (Fintype.card P : ℝ) ≠ 0 := by
      exact_mod_cast (by have := ambient_card_ge_two B hB; omega : Fintype.card P ≠ 0)
    rw [sum_prob B (Finset.card_pos.mp (by omega))]
    simp [hn]
  · intro x
    rw [signedPair_row B hB, signedPair_col B hB]
    ring

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
lemma sum_outside_cell (B C : Finset P) :
    (∑ y ∈ C, if y ∈ B then (0 : ℝ) else 1) =
      (C.card : ℝ) - (B ∩ C).card := by
  have he : ∀ y, (if y ∈ B then (0 : ℝ) else 1) =
      if y ∉ B then 1 else 0 := by intro y; split_ifs <;> rfl
  simp_rw [he]
  rw [← Finset.sum_filter]
  rw [show C.filter (fun y => y ∉ B) = C \ B by ext y; simp]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_sdiff,
    Nat.cast_sub (Finset.card_le_card Finset.inter_subset_right)]

lemma mixedCell_formula (B C : Finset P) (hB : 2 ≤ B.card) :
    mixedCell B C = (B.card : ℝ) / Fintype.card P * pairCell B C +
      cellProb B C / Fintype.card P * ((C.card : ℝ) - (B ∩ C).card) := by
  unfold mixedCell
  simp_rw [mixedProb_decompose B hB, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_outside_cell B C, ← Finset.sum_mul, ← Finset.sum_div, sum_prob_cell B C]
  rfl

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

private lemma pair_fraction (k b : ℝ) (hk : k ≠ 0) (hk1 : k - 1 ≠ 0) :
    b * (b-1) / (k*(k-1)) = (b/k)^2 - (b/k)*(1-b/k)/(k-1) := by
  field_simp
  ring

omit [Fintype P] in
lemma pairCell_centered (B C : Finset P) (hB : 2 ≤ B.card) :
    pairCell B C = (cellProb B C)^2 - cellProb B C * (1-cellProb B C) /
      ((B.card : ℝ) - 1) := by
  have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  have hk1 : (B.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
    linarith
  rw [pairCell_formula, cellProb, pair_fraction _ _ hk hk1]

lemma mixedCell_centered (B C : Finset P) (hB : 2 ≤ B.card) :
    mixedCell B C = cellProb Finset.univ C * cellProb B C -
      (B.card : ℝ) / Fintype.card P *
        (cellProb B C * (1-cellProb B C) / ((B.card : ℝ)-1)) := by
  have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  rw [mixedCell_formula B C hB, pairCell_centered B C hB]
  simp only [cellProb, Finset.univ_inter, Finset.card_univ]
  field_simp
  ring

lemma mixedCell_le_product (B C : Finset P) (hB : 2 ≤ B.card) :
    mixedCell B C ≤ cellProb Finset.univ C * cellProb B C := by
  rw [mixedCell_centered B C hB]
  have hp := cellProb_nonneg B C
  have hp1 := cellProb_le_one B C
  have hk : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
  have hk0 : 0 ≤ (B.card : ℝ) - 1 := by linarith
  have hp10 : 0 ≤ 1-cellProb B C := sub_nonneg.mpr hp1
  have hh : 0 ≤ (B.card : ℝ) / Fintype.card P *
      (cellProb B C * (1-cellProb B C) / ((B.card : ℝ)-1)) := by positivity
  linarith

lemma signedCell_formula (B C : Finset P) (hB : 2 ≤ B.card) :
    (∑ x ∈ C, ∑ y ∈ C, signedPair B x y) =
      (cellProb B C - cellProb Finset.univ C)^2 +
      (2 * (B.card : ℝ) / Fintype.card P - 1) *
        (cellProb B C * (1-cellProb B C) / ((B.card : ℝ)-1)) -
      cellProb Finset.univ C * (1-cellProb Finset.univ C) /
        ((Fintype.card P : ℝ)-1) := by
  have hP : 2 ≤ (Finset.univ : Finset P).card := ambient_card_ge_two B hB
  simp_rw [signedPair, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change pairCell B C - 2 * mixedCell B C + pairCell Finset.univ C = _
  rw [pairCell_centered B C hB, mixedCell_centered B C hB,
    pairCell_centered Finset.univ C hP]
  simp only [Finset.card_univ]
  ring

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
lemma fiber_pair_lower (B C : Finset P) (hB : 2 ≤ B.card) :
    (1/2) * (if 2 / (B.card : ℝ) ≤ cellProb B C then (cellProb B C)^2 else 0) ≤
      pairCell B C := by
  split_ifs with hp
  · have hk : 0 < (B.card : ℝ) := by exact_mod_cast (by omega : 0 < B.card)
    have hb : (2 : ℝ) ≤ (B ∩ C).card :=
      (div_le_div_iff_of_pos_right hk).mp hp
    rw [pairCell_formula, cellProb]
    exact (pair_fraction_bounds _ _ hb
      (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₂ := C)))).1
  · simpa only [mul_zero] using pairCell_nonneg B C

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

lemma singleton_mixedCell (B C : Finset P) (hC : C.card ≤ 1) : mixedCell B C = 0 := by
  unfold mixedCell
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have : x = y := Finset.card_le_one.mp hC x hx y hy
  subst y
  exact mixedProb_diag B x

omit [Fintype P] in
lemma singleton_fiber_term (B C : Finset P) (hB : 2 ≤ B.card) (hC : C.card ≤ 1) :
    (if 2 / (B.card : ℝ) ≤ cellProb B C then (cellProb B C)^2 else 0) = 0 := by
  have hk : 0 < (B.card : ℝ) := by exact_mod_cast (by omega : 0 < B.card)
  have hi : (B ∩ C).card ≤ 1 := (Finset.card_le_card Finset.inter_subset_right).trans hC
  have hiR : ((B ∩ C).card : ℝ) < 2 := by exact_mod_cast (by omega : (B ∩ C).card < 2)
  have hp : cellProb B C < 2 / (B.card : ℝ) :=
    (div_lt_div_iff_of_pos_right hk).mpr hiR
  simp only [not_le.mpr hp, reduceIte]

lemma signedCell_eq (B C : Finset P) :
    signedCell B C = ∑ x ∈ C, ∑ y ∈ C, signedPair B x y := by
  simp only [signedCell, pairCell, mixedCell, signedPair,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

lemma singleton_signedCell (B C : Finset P) (hC : C.card ≤ 1) : signedCell B C = 0 := by
  simp [signedCell, singleton_pairCell _ _ hC, singleton_mixedCell _ _ hC]

private lemma correction_bound (p k ε : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hk : 0 < k-1) (he : 1/(k-1) ≤ ε) :
    0 ≤ p*(1-p)/(k-1) ∧ p*(1-p)/(k-1) ≤ ε*p := by
  have hε : 0 ≤ ε := (by positivity : 0 ≤ 1/(k-1)).trans he
  constructor
  · exact div_nonneg (mul_nonneg hp (sub_nonneg.mpr hp1)) hk.le
  · calc
      p*(1-p)/(k-1) ≤ p/(k-1) := by
        apply div_le_div_of_nonneg_right _ hk.le
        nlinarith [sq_nonneg p]
      _ = p * (1/(k-1)) := by ring
      _ ≤ p*ε := mul_le_mul_of_nonneg_left he hp
      _ = _ := mul_comm _ _

/-- The finite large-cell estimate before converting a to pair mass. -/
lemma signedCell_lower (B C : Finset P) (hB : 2 ≤ B.card) (ε : ℝ)
    (hk : 1 / ((B.card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε) :
    (cellProb B C - cellProb Finset.univ C)^2 -
      ε * (cellProb B C + cellProb Finset.univ C) ≤ signedCell B C := by
  have hkr : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
  have hnr : (2 : ℝ) ≤ Fintype.card P := by exact_mod_cast ambient_card_ge_two B hB
  have hp := correction_bound (cellProb B C) (B.card : ℝ) ε
    (cellProb_nonneg B C) (cellProb_le_one B C) (by linarith) hk
  have ha := correction_bound (cellProb Finset.univ C) (Fintype.card P : ℝ) ε
    (cellProb_nonneg _ C) (cellProb_le_one _ C) (by linarith) hn
  rw [signedCell_eq, signedCell_formula B C hB]
  have hc : 0 ≤ 2 * (B.card : ℝ) / Fintype.card P := by positivity
  nlinarith [mul_nonneg hc hp.1]

section Family
variable {I : Type u2} [Fintype I]
variable (w : I → ℝ) (B : I → Finset P)

lemma mean_cell_bound (C : Finset P) (M : ℝ)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M * prob Finset.univ x) :
    (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C := by
  simp_rw [← sum_prob_cell, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun x _ => hdom x

lemma family_large_raw (C : Finset P) (M ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1) (hε : 0 ≤ ε)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hmean : (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C) :
    (∑ i, w i * (cellProb (B i) C - cellProb Finset.univ C)^2) -
      ε*(M+1)*cellProb Finset.univ C ≤ (∑ i, w i * signedCell (B i) C) := by
  let a := cellProb Finset.univ C
  have ha : 0 ≤ a := cellProb_nonneg _ _
  have hc : (∑ i, w i * cellProb (B i) C) + (∑ i, w i)*a ≤ (M+1)*a := by
    have := mul_le_mul_of_nonneg_right hW ha
    dsimp [a] at *
    linarith
  calc
    _ ≤ (∑ i, w i * (cellProb (B i) C - a)^2) -
        ε*((∑ i, w i * cellProb (B i) C)+(∑ i, w i)*a) := by
      have := mul_le_mul_of_nonneg_left hc hε
      dsimp [a] at *
      nlinarith
    _ = ∑ i, w i * ((cellProb (B i) C - a)^2 - ε*(cellProb (B i) C+a)) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_mul]
      rw [sub_add_eq_sub_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (signedCell_lower (B i) C (hB i) ε (hk i) hn) (hw i)

lemma family_large (C : Finset P) (M ε τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hτ : 0 < τ) (hC : 2 ≤ C.card) (ha : τ ≤ cellProb Finset.univ C)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hmean : (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C) :
    (∑ i, w i * (cellProb (B i) C - cellProb Finset.univ C)^2) -
      (2*ε*(M+1)/τ)*pairCell Finset.univ C ≤ (∑ i, w i * signedCell (B i) C) := by
  have hcomp := (uniform_pair_comparison C hC).1
  have ha0 := cellProb_nonneg (Finset.univ : Finset P) C
  have hmass : cellProb Finset.univ C ≤ 2*pairCell Finset.univ C/τ := by
    apply (le_div_iff₀ hτ).mpr
    nlinarith [mul_le_mul_of_nonneg_right ha ha0]
  have herr := mul_le_mul_of_nonneg_left hmass (show 0 ≤ ε*(M+1) by positivity)
  have h := family_large_raw w B C M ε hw hW hε hB hk hn hmean
  have he : ε*(M+1)*(2*pairCell Finset.univ C/τ) =
      (2*ε*(M+1)/τ)*pairCell Finset.univ C := by ring
  rw [he] at herr
  linarith

lemma family_small (C : Finset P) (M : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hM : 0 ≤ M) (hC : 2 ≤ C.card)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hmean : (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C) :
    (1/2) * (∑ i, w i * (if 2 / ((B i).card : ℝ) ≤ cellProb (B i) C then
      (cellProb (B i) C)^2 else 0)) - 4*M*pairCell Finset.univ C ≤
      (∑ i, w i * signedCell (B i) C) := by
  let a := cellProb Finset.univ C
  have ha0 : 0 ≤ a := cellProb_nonneg _ _
  have hp0 := pairCell_nonneg (Finset.univ : Finset P) C
  have hc := (uniform_pair_comparison C hC).1
  have hterm (i : I) :
      (1/2)*(if 2 / ((B i).card : ℝ) ≤ cellProb (B i) C then
        (cellProb (B i) C)^2 else 0) - 2*a*cellProb (B i) C ≤ signedCell (B i) C := by
    have h₁ := fiber_pair_lower (B i) C (hB i)
    have h₂ := mixedCell_le_product (B i) C (hB i)
    dsimp [signedCell, a] at *
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hterm i) (hw i))
  have he : (∑ i, w i * ((1/2)*(if 2 / ((B i).card : ℝ) ≤ cellProb (B i) C then
        (cellProb (B i) C)^2 else 0) - 2*a*cellProb (B i) C)) =
      (1/2)*(∑ i, w i * (if 2 / ((B i).card : ℝ) ≤ cellProb (B i) C then
        (cellProb (B i) C)^2 else 0)) - 2*a*(∑ i, w i * cellProb (B i) C) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hs
  have hmean' := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 2*a by positivity)
  have hcomp := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*M by positivity)
  dsimp [a] at *
  nlinarith

end Family

section CellIntegral
variable {Ω : Type u3} [MeasurableSpace Ω]

section Quantitative
local instance instMeasurableSpaceFinset_solutions_r146789_1 : MeasurableSpace (Finset P) := ⊤
local instance instDiscreteMeasurableSpaceFinset_solutions_r146789_1 : DiscreteMeasurableSpace (Finset P) := ⟨fun _ => trivial⟩
variable {I : Type u5} [Fintype I]

lemma varianceCell_bound (w : I → ℝ) (B : I → Finset P) (T M ε τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1)
    (hT : 1 ≤ T) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hτ : 0 < τ)
    (hscale : τ * Fintype.card P ≤ T)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M * prob Finset.univ x)
    (D : Finset P) :
    varianceCell w B T D ≤ (∑ i, w i * signedCell (B i) D) +
      (2*ε*(M+1)/τ)*pairCell Finset.univ D +
      4*M*(if (D.card : ℝ) ≤ T then pairCell Finset.univ D else 0) := by
  have hmean := mean_cell_bound w B D M hdom
  have herr : 0 ≤ (2*ε*(M+1)/τ)*pairCell Finset.univ D := by
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε)
      (by linarith)) hτ.le) (pairCell_nonneg _ _)
  by_cases hD : T < (D.card : ℝ)
  · have hd2 : 2 ≤ D.card := by
      have : (1 : ℝ) < D.card := hT.trans_lt hD
      exact_mod_cast (show 1 < D.card by exact_mod_cast this)
    have hnp : 0 < (Fintype.card P : ℝ) := by
      exact_mod_cast (show 0 < Fintype.card P by have := Finset.card_le_univ D; omega)
    have ha : τ ≤ cellProb Finset.univ D := by
      simp only [cellProb, Finset.univ_inter, Finset.card_univ]
      exact (le_div_iff₀ hnp).mpr (hscale.trans hD.le)
    have hh := family_large w B D M ε τ hw hW hM hε hτ hd2 ha hB hk hn hmean
    simp only [varianceCell, hD, reduceIte, not_le.mpr hD, mul_zero, add_zero]
    linarith
  · simp only [varianceCell, hD, reduceIte, not_lt.mp hD]
    by_cases hd2 : 2 ≤ D.card
    · have hh := family_small w B D M hw hM hd2 hB hmean
      linarith
    · have hd1 : D.card ≤ 1 := by omega
      simp [singleton_fiber_term _ _ (hB _) hd1, singleton_signedCell _ _ hd1,
        singleton_pairCell _ _ hd1]

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

namespace WeakPinned.Variance
variable {P : Type u3} [Fintype P] [DecidableEq P]

lemma weighted_cancel (m : Finset P → ℝ) (b : ℝ) (S : P → ℝ)
    (hL : ∀ x y, x ≠ y → weightedOverlap m x y = b+S x+S y)
    (B : Finset P) (hB : 2 ≤ B.card) : weightedIntegral m (signedCell B) = 0 := by
  have he : weightedIntegral m (signedCell B) =
      ∑ x, ∑ y, signedPair B x y * weightedOverlap m x y := by
    simp only [weightedIntegral, signedCell_eq]
    have hc (C : Finset P) : (∑ x ∈ C, ∑ y ∈ C, signedPair B x y) =
        ∑ x, ∑ y, signedPair B x y * (if x ∈ C ∧ y ∈ C then (1:ℝ) else 0) := by
      simp only [mul_ite, mul_one, mul_zero, ite_and]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
      simp
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp only [weightedOverlap, weightedIntegral, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  rw [he]
  exact variance_cancel B hB _ b S hL

lemma weighted_variance {I : Type u4} [Fintype I]
    (m : Finset P → ℝ) (hm : ∀ C, 0 ≤ m C) (b : ℝ) (S : P → ℝ)
    (hL : ∀ x y, x ≠ y → weightedOverlap m x y = b+S x+S y)
    (w : I → ℝ) (B : I → Finset P) (T M ε τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1)
    (hT : 1 ≤ T) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hτ : 0 < τ)
    (hscale : τ * Fintype.card P ≤ T)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M * prob Finset.univ x) :
    weightedIntegral m (varianceCell w B T) ≤
      (2*ε*(M+1)/τ)*weightedIntegral m (pairCell Finset.univ) +
      4*M*weightedIntegral m (fun C => if (C.card : ℝ) ≤ T then pairCell Finset.univ C else 0) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun C _ =>
    mul_le_mul_of_nonneg_left
      (varianceCell_bound w B T M ε τ hw hW hT hM hε hτ hscale hB hk hn hdom C) (hm C))
  simp only [mul_add, Finset.sum_add_distrib] at hh
  have hz : (∑ C, m C * ∑ i, w i * signedCell (B i) C) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hi (i : I) : (∑ C, m C * (w i * signedCell (B i) C)) = 0 := by
      calc
        _ = w i * weightedIntegral m (signedCell (B i)) := by
          simp only [weightedIntegral, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro C _
          ring
        _ = 0 := by rw [weighted_cancel m b S hL _ (hB i),mul_zero]
    simp_rw [hi]
    exact Finset.sum_const_zero
  rw [hz,zero_add] at hh
  simp only [← mul_add] at hh
  change weightedIntegral m (varianceCell w B T) ≤ _ at hh
  have he₁ : (∑ C, m C * (2*ε*(M+1)/τ * pairCell Finset.univ C)) =
      (2*ε*(M+1)/τ)*weightedIntegral m (pairCell Finset.univ) := by
    simp only [weightedIntegral, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  have he₂ : (∑ C, m C * (4*M*(if (C.card : ℝ) ≤ T then pairCell Finset.univ C else 0))) =
      4*M*weightedIntegral m (fun C => if (C.card : ℝ) ≤ T then pairCell Finset.univ C else 0) := by
    simp only [weightedIntegral, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  rwa [he₁,he₂] at hh
end WeakPinned.Variance

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

/-- Unconditional arithmetic-hierarchy instance of the quantitative variance
    bound. The overlap identity follows from the product formula, and the
    family hypotheses are exactly finite sampling data. -/
theorem arithmetic_variance {I : Type u7} [Fintype I]
    (hnP : 2 ≤ Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (T M₀ ε τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1)
    (hT : 1 ≤ T) (hM : 0 ≤ M₀) (hε : 0 ≤ ε) (hτ : 0 < τ)
    (hscale : τ * Fintype.card P ≤ T)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M₀ * prob Finset.univ x) :
    weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (varianceCell w B T) ≤
      (2*ε*(M₀+1)/τ)*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (pairCell Finset.univ) +
      4*M₀*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂)
        (fun C => if (C.card : ℝ) ≤ T then pairCell Finset.univ C else 0) :=
  weighted_variance _ (totalMass_nonneg Z₁ Z₂ h₁ h₂) _ _
    (totalMass_overlap Z₁ Z₂ h₁ h₂ hnP) w B T M₀ ε τ hw hW hT hM hε hτ hscale hB hk hn hdom
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

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

omit [DecidableEq P] in
lemma sourceGiant_mono (x : P) {r t : ℝ} (htr : t ≤ r) (hr : d.sourceGiant x r) :
    d.sourceGiant x t := by
  classical
  have hc := Finset.card_le_card (d.cell_mono htr x)
  unfold sourceGiant at *
  omega

omit [DecidableEq P] in
lemma sourceGiant_iff (x : P) (r : ℝ) : d.sourceGiant x r ↔
    ∃ C : Finset P, Fintype.card P < 2*C.card ∧ ∀ y ∈ C, d.share r x y := by
  classical
  constructor
  · intro h; exact ⟨d.cell r x,h,fun y hy => (d.mem_cell r x y).mp hy⟩
  · rintro ⟨C,hc,hC⟩
    have hsub : C ⊆ d.cell r x := fun y hy => (d.mem_cell r x y).mpr (hC y hy)
    have := Finset.card_le_card hsub
    unfold sourceGiant
    omega

lemma isClosed_sourceGiant (x : P) : IsClosed {r : ℝ | d.sourceGiant x r} := by
  classical
  simp_rw [d.sourceGiant_iff, Set.ofPred_exists]
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
    · simp [share,hxy]
    · simp only [share,hxy,false_or]
      exact isClosed_le continuous_id continuous_const

lemma sourceGiant_cutoff (hn : 2 ≤ Fintype.card P) (x : P) (r : ℝ) :
    d.sourceGiant x r ↔ r ≤ d.sourceM x := by
  classical
  have hlo : d.sourceGiant x (-d.radius) := by
    classical
    unfold sourceGiant
    rw [d.cell_of_low le_rfl,Finset.card_univ]
    omega
  have hle : ∀ t, d.sourceGiant x t → t ≤ d.radius := by
    classical
    intro t ht
    exact d.giants_le_radius hn ⟨d.cell t x, (d.mem_giants t _).mpr ⟨d.cell_mem_cells t x,ht⟩⟩
  have hne : Set.Nonempty {t : ℝ | d.sourceGiant x t} := ⟨-d.radius,hlo⟩
  have hbd : BddAbove {t : ℝ | d.sourceGiant x t} := ⟨d.radius, fun t ht => hle t ht⟩
  have hmem : d.sourceGiant x (d.sourceM x) := (d.isClosed_sourceGiant x).csSup_mem hne hbd
  exact ⟨fun hr => le_csSup hbd hr, fun hr => d.sourceGiant_mono x hr hmem⟩

lemma sourceGiant_mem_giant (x : P) (r : ℝ) :
    d.sourceGiant x r ↔ (d.giants r).Nonempty ∧ x ∈ d.giant r := by
  classical
  constructor
  · intro hs
    have hc : d.cell r x ∈ d.giants r := (d.mem_giants r _).mpr ⟨d.cell_mem_cells r x,hs⟩
    exact ⟨⟨_,hc⟩,by rw [d.giant_eq hc]; exact d.self_mem_cell r x⟩
  · rintro ⟨⟨G,hG⟩,hx⟩
    rw [d.giant_eq hG] at hx
    obtain ⟨hGc,hGm⟩ := (d.mem_giants r G).mp hG
    rwa [d.cell_of_mem hGc hx] at hGm

/-- The level set is an interval of length 2H, regardless of the fiber center-level h. -/

lemma straddle_integral (hn : 2 ≤ Fintype.card P) (x : P) (h H : ℝ) (hH : 0 ≤ H) :
    (∫ r : ℝ, if d.sourceGiant x (h-r-H) ∧ ¬d.sourceGiant x (h-r+H) then (1:ℝ) else 0) = 2*H := by
  classical
  have he : (fun r : ℝ => if d.sourceGiant x (h-r-H) ∧ ¬d.sourceGiant x (h-r+H) then (1:ℝ) else 0) =
      (Set.Ico (h-H-d.sourceM x) (h+H-d.sourceM x)).indicator (fun _ => (1:ℝ)) := by
    classical
    funext r
    simp only [d.sourceGiant_cutoff hn, not_le,Set.indicator_apply,Set.mem_Ico]
    congr 1
    apply propext
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [he,integral_indicator measurableSet_Ico]
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : h-H-d.sourceM x ≤ h+H-d.sourceM x), intervalIntegral.integral_const]
  simp
  ring

omit [DecidableEq P] in
lemma smallCells_chain (y : P) (T : ℝ) {C E : Finset P}
    (hC : C ∈ d.smallCells y T) (hE : E ∈ d.smallCells y T) : C ⊆ E ∨ E ⊆ C := by
  classical
  obtain ⟨r,rfl,hr⟩ := (Finset.mem_filter.mp hC).2
  obtain ⟨t,rfl,ht⟩ := (Finset.mem_filter.mp hE).2
  rcases le_total t r with h | h
  · exact Or.inl (d.cell_mono h y)
  · exact Or.inr (d.cell_mono h y)

lemma smallNeighbors_card (y : P) (T : ℝ) (hT : 0 < T) :
    ((d.smallNeighbors y T).card : ℝ) < T := by
  classical
  by_cases hne : (d.smallCells y T).Nonempty
  · obtain ⟨C,hC,hmax⟩ := Finset.exists_max_image (d.smallCells y T) Finset.card hne
    have he : d.smallNeighbors y T = C := by
      classical
      apply Finset.Subset.antisymm
      · intro x hx
        obtain ⟨E,hE,hx⟩ := Finset.mem_biUnion.mp hx
        change x ∈ E at hx
        rcases d.smallCells_chain y T hE hC with h | h
        · exact h hx
        · have he : C = E := Finset.eq_of_subset_of_card_le h (hmax E hE)
          simpa only [he] using hx
      · intro x hx
        exact Finset.mem_biUnion.mpr ⟨C,hC,hx⟩
    rw [he]
    obtain ⟨r,hr,ht⟩ := (Finset.mem_filter.mp hC).2
    exact ht
  · rw [smallNeighbors,Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa using hT

lemma source_mem_smallNeighbors (y x : P) (r T : ℝ)
    (hxy : y ∈ d.cell r x) (hT : ((d.cell r x).card : ℝ) < T) :
    x ∈ d.smallNeighbors y T := by
  classical
  have he := d.cell_eq_of_share ((d.mem_cell r x y).mp hxy)
  apply Finset.mem_biUnion.mpr
  refine ⟨d.cell r y, ?_, (d.mem_cell r y x).mpr (d.share_symm ((d.mem_cell r x y).mp hxy))⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,r,rfl,by rwa [← he]⟩
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u2} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma smallNeighbors_self (y : P) (T : ℝ) (hne : (d.smallNeighbors y T).Nonempty) :
    y ∈ d.smallNeighbors y T := by
  classical
  obtain ⟨x,hx⟩ := hne
  obtain ⟨C,hC,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨r,rfl,hr⟩ := (Finset.mem_filter.mp hC).2
  apply Finset.mem_biUnion.mpr
  exact ⟨d.cell r y,hC,d.self_mem_cell r y⟩

lemma smallNeighbors_erase_bound (hn : 2 ≤ Fintype.card P) (y : P)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ((d.smallNeighbors y (τ*Fintype.card P)).erase y).card ≤ τ*((Fintype.card P : ℝ)-1) := by
  classical
  have hn0 : 0 < (Fintype.card P : ℝ) := by exact_mod_cast (show 0 < Fintype.card P by omega)
  have hn1 : 0 ≤ (Fintype.card P : ℝ)-1 := by
    have : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
    linarith
  by_cases hne : (d.smallNeighbors y (τ*Fintype.card P)).Nonempty
  · have hy := d.smallNeighbors_self y _ hne
    have hc := d.smallNeighbors_card y (τ*Fintype.card P) (mul_pos hτ hn0)
    rw [Finset.card_erase_of_mem hy,Nat.cast_sub (Finset.one_le_card.mpr hne),Nat.cast_one]
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.erase_empty,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg hτ.le hn1

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.SmallFiber
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
lemma mass_nonneg {p : P → ℝ} (hp : ∀ y, 0 ≤ p y) (C : Finset P) : 0 ≤ mass p C :=
  Finset.sum_nonneg (fun y _ => hp y)

omit [Fintype P] [DecidableEq P] in
lemma mass_mono {p : P → ℝ} (hp : ∀ y, 0 ≤ p y) {C D : Finset P} (h : C ⊆ D) :
    mass p C ≤ mass p D := Finset.sum_le_sum_of_subset_of_nonneg h (fun y _ _ => hp y)

omit [DecidableEq P] in
lemma mass_le_one {p : P → ℝ} (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) (C : Finset P) :
    mass p C ≤ 1 := by rw [← h1]; exact mass_mono hp (Finset.subset_univ C)

omit [Fintype P] in
lemma mass_diff_inter (p : P → ℝ) (C D : Finset P) :
    mass p C = mass p (C \ D) + mass p (C ∩ D) := by
  classical
  symm
  have hh := Finset.sum_sdiff (f:=p) (Finset.inter_subset_left (s₁:=C) (s₂:=D))
  have he : C \ (C ∩ D) = C \ D := by ext y; simp
  rw [he] at hh
  exact hh

lemma mass_cover (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1)
    (C D : Finset P) : 1 ≤ mass p C + mass p D + mass p (C ∪ D)ᶜ := by
  classical
  rw [← h1]
  have he := Finset.sum_compl_add_sum (C ∪ D) p
  have hu := (Finset.sum_union_inter (s₁:=C) (s₂:=D) (f:=p))
  have hn := mass_nonneg hp (C ∩ D)
  unfold mass at *
  linarith

lemma small_case_one (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1)
    (C D : Finset P) (lam : ℝ) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hC : mass p C ≤ lam) :
    mass p C ≤ 2*lam*mass p D + mass p (C ∪ D)ᶜ := by
  classical
  have hc := mass_cover p hp h1 C D
  have hnC := mass_nonneg hp C
  have hnD := mass_nonneg hp D
  have hnE := mass_nonneg hp (C∪D)ᶜ
  have hp2 : mass p C ≤ 1/2 := hC.trans hlam2
  nlinarith

end WeakPinned.SmallFiber

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma nongiant_share_overlap {r : ℝ} {x y : P} (hg : ¬ d.sourceGiant x r)
    (hy : y ∈ d.cell r x) : 1 ≤ d.pairOverlap r x y := by
  classical
  have hs := (d.mem_cell r x y).mp hy
  rw [d.pairOverlap_formula, ite_eq_left hs]
  by_cases he : (d.giants r).Nonempty
  · have hx : x ∉ d.giant r := by
      intro hx
      exact hg ((d.sourceGiant_mem_giant x r).mpr ⟨he,hx⟩)
    have hy' : y ∉ d.giant r := by
      intro hy'
      have hgy := (d.sourceGiant_mem_giant y r).mpr ⟨he,hy'⟩
      exact hg (by simpa only [sourceGiant, d.cell_eq_of_share hs] using hgy)
    simp [giantIndicator,outsideIndicator,he,hx,hy']
  · simp [giantIndicator,outsideIndicator,he]

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy
variable {P : Type u5} [Fintype P] [DecidableEq P]

lemma mass_as_sum (p : P → ℝ) (C : Finset P) :
    mass p C = ∑ y, if y ∈ C then p y else 0 := by
  classical
  simp [mass]

lemma mass_as_sum_off (p : P → ℝ) (x : P) (hx : p x = 0) (C : Finset P) :
    mass p C = ∑ y, if x ≠ y ∧ y ∈ C then p y else 0 := by
  classical
  rw [mass_as_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x = y
  · subst y; simp [hx]
  · simp [hxy]

lemma nongiant_mass_bound (d : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (x : P) (r : ℝ) :
    (if ¬d.sourceGiant x r then mass p (d.cell r x) else 0) ≤
      ∑ y, p y * d.pairOverlap r x y := by
  classical
  by_cases hg : d.sourceGiant x r
  · simp only [hg,not_true_eq_false,ite_false]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hp y) (d.pairOverlap_bounds r x y).1)
  · simp only [hg,not_false_eq_true,ite_true]
    rw [mass_as_sum]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : y ∈ d.cell r x
    · simp only [hy,ite_true]
      nlinarith [d.nongiant_share_overlap hg hy, hp y]
    · simpa only [hy,ite_false] using mul_nonneg (hp y) (d.pairOverlap_bounds r x y).1

lemma integral_open_interval (a b : ℝ) :
    (∫ r : ℝ, if a < r ∧ r < b then (1:ℝ) else 0) = max (b-a) 0 := by
  have he : (fun r : ℝ => if a < r ∧ r < b then (1:ℝ) else 0) =
      (Set.Ioo a b).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r; simp [Set.indicator_apply]
  rw [he, integral_indicator measurableSet_Ioo]
  simp [integral_const,measureReal_def,Real.volume_Ioo,ENNReal.toReal_ofReal']

lemma integral_closed_interval (a b : ℝ) :
    (∫ r : ℝ, if a ≤ r ∧ r ≤ b then (1:ℝ) else 0) = max (b-a) 0 := by
  have he : (fun r : ℝ => if a ≤ r ∧ r ≤ b then (1:ℝ) else 0) =
      (Set.Icc a b).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r; simp [Set.indicator_apply]
  rw [he, integral_indicator measurableSet_Icc]
  simp [integral_const,measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal']

lemma integrable_open_interval (a b : ℝ) :
    Integrable (fun r : ℝ => if a < r ∧ r < b then (1:ℝ) else 0) := by
  have he : (fun r : ℝ => if a < r ∧ r < b then (1:ℝ) else 0) =
      (Set.Ioo a b).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r; simp [Set.indicator_apply]
  rw [he, integrable_indicator_iff measurableSet_Ioo]
  exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)

lemma integrable_closed_interval (a b : ℝ) :
    Integrable (fun r : ℝ => if a ≤ r ∧ r ≤ b then (1:ℝ) else 0) := by
  have he : (fun r : ℝ => if a ≤ r ∧ r ≤ b then (1:ℝ) else 0) =
      (Set.Icc a b).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r; simp [Set.indicator_apply]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

lemma minusError_formula (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H r : ℝ) :
    minusError d d' p x h H r = ∑ y, p y *
      (if d.value x y < r ∧ r < h-H-d'.value x y then (1:ℝ) else 0) := by
  classical
  rw [minusError,mass_as_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x = y
  · subst y; simp [hx]
  · simp only [Finset.mem_compl,Finset.mem_union,Depth.mem_cell,Depth.share,hxy,false_or,not_or,not_le]
    have he : (d.value x y < r ∧ d'.value x y < h-r-H) ↔
        d.value x y < r ∧ r < h-H-d'.value x y := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
    simp only [he]
    split_ifs <;> simp

lemma plusError_formula (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H r : ℝ) :
    plusError d d' p x h H r = ∑ y, p y *
      (if h+H-d'.value x y ≤ r ∧ r ≤ d.value x y then (1:ℝ) else 0) := by
  classical
  rw [plusError,mass_as_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x = y
  · subst y; simp [hx]
  · simp only [Finset.mem_inter,Depth.mem_cell,Depth.share,hxy,false_or]
    have he : (r ≤ d.value x y ∧ h-r+H ≤ d'.value x y) ↔
        h+H-d'.value x y ≤ r ∧ r ≤ d.value x y := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
    simp only [he]
    split_ifs <;> simp

lemma minusError_integrable (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) : Integrable (minusError d d' p x h H) := by
  change Integrable (fun r => minusError d d' p x h H r)
  simp_rw [minusError_formula d d' p x hx]
  exact integrable_finsetSum _ (fun y _ => (integrable_open_interval _ _).const_mul (p y))

lemma plusError_integrable (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) : Integrable (plusError d d' p x h H) := by
  change Integrable (fun r => plusError d d' p x h H r)
  simp_rw [plusError_formula d d' p x hx]
  exact integrable_finsetSum _ (fun y _ => (integrable_closed_interval _ _).const_mul (p y))

lemma minusError_integral (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) : (∫ r, minusError d d' p x h H r) =
      ∑ y, p y * max (h-d.value x y-d'.value x y-H) 0 := by
  simp_rw [minusError_formula d d' p x hx]
  rw [integral_finsetSum _ (fun y _ => (integrable_open_interval _ _).const_mul (p y))]
  simp_rw [integral_const_mul,integral_open_interval]
  apply Finset.sum_congr rfl
  intro y _
  congr 2; ring

lemma plusError_integral (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) : (∫ r, plusError d d' p x h H r) =
      ∑ y, p y * max (d.value x y+d'.value x y-h-H) 0 := by
  simp_rw [plusError_formula d d' p x hx]
  rw [integral_finsetSum _ (fun y _ => (integrable_closed_interval _ _).const_mul (p y))]
  simp_rw [integral_const_mul,integral_closed_interval]
  apply Finset.sum_congr rfl
  intro y _
  congr 2; ring

lemma two_truncations (a H : ℝ) (hH : 0 ≤ H) :
    max (-a-H) 0 + max (a-H) 0 = max (|a|-H) 0 := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha,max_eq_right (by linarith : -a-H ≤ 0),zero_add]
  · rw [abs_of_nonpos ha,max_eq_right (by linarith : a-H ≤ 0),add_zero]

lemma errors_integral (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) (hH : 0 ≤ H) :
    (∫ r, minusError d d' p x h H r + plusError d d' p x h H r) =
      ∑ y, p y * max (|d.value x y+d'.value x y-h|-H) 0 := by
  rw [integral_add (minusError_integrable d d' p x hx h H) (plusError_integrable d d' p x hx h H),
    minusError_integral d d' p x hx, plusError_integral d d' p x hx,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  have he : h-d.value x y-d'.value x y-H = -(d.value x y+d'.value x y-h)-H := by ring
  rw [he,← mul_add,two_truncations _ H hH]

end WeakPinned.SmallFiber

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy
variable {P : Type u6} [Fintype P] [DecidableEq P]

lemma neighborMass_nonneg (d d' : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (x : P) (T t : ℝ) : 0 ≤ neighborMass d d' p x T t := by
  classical
  exact Finset.sum_nonneg (fun y _ => mul_nonneg (hp y) (by split_ifs; exact (d'.outsideIndicator_bounds t y).1; rfl))

omit [DecidableEq P] in
lemma nongiantMass_nonneg (d : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (x : P) (r : ℝ) : 0 ≤ nongiantMass d p x r := by
  unfold nongiantMass
  split_ifs <;> first | exact mass_nonneg hp _ | rfl

lemma case_three_bound (d d' : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (x : P) (hx : p x = 0) (r t T : ℝ)
    (hT : ((d.cell r x).card : ℝ) < T) (hg : d'.sourceGiant x t) :
    mass p (d.cell r x \ d'.cell t x) ≤ neighborMass d d' p x T t := by
  classical
  rw [mass_as_sum_off p x hx]
  unfold neighborMass
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : x ≠ y ∧ y ∈ d.cell r x \ d'.cell t x
  · obtain ⟨hxy,hyD⟩ := hy
    obtain ⟨hyU,hyV⟩ := Finset.mem_sdiff.mp hyD
    have hn : x ∈ (d.smallNeighbors y T).erase y :=
      Finset.mem_erase.mpr ⟨hxy, d.source_mem_smallNeighbors y x r T hyU hT⟩
    have hG : d'.cell t x ∈ d'.giants t := (d'.mem_giants t _).mpr ⟨d'.cell_mem_cells t x,hg⟩
    have he : (d'.giants t).Nonempty := ⟨_,hG⟩
    have hyo : y ∉ d'.giant t := by rwa [d'.giant_eq hG]
    simp [hxy,hyD,hn,Depth.outsideIndicator,he,hyo]
  · simp only [hy,ite_false]
    exact mul_nonneg (hp y) (by split_ifs; exact (d'.outsideIndicator_bounds t y).1; rfl)

/-- The pointwise small-fiber bound. The only independent error is the exact
    pair of intervals already evaluated. -/
lemma active_pointwise (d d' : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (h1 : ∑ y, p y = 1) (x : P) (hx : p x = 0) (h H T lam r : ℝ)
    (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2) :
    activeMass d p x T lam r ≤
      2*lam*nongiantMass d' p x (h-r-H) + lam*straddle d' x h H r +
      minusError d d' p x h H r + plusError d d' p x h H r +
      neighborMass d d' p x T (h-r+H) := by
  classical
  have hminus : 0 ≤ minusError d d' p x h H r := mass_nonneg hp _
  have hplus : 0 ≤ plusError d d' p x h H r := mass_nonneg hp _
  have hnbr := neighborMass_nonneg d d' p hp x T (h-r+H)
  have hng := nongiantMass_nonneg d' p hp x (h-r-H)
  have hstr : 0 ≤ straddle d' x h H r := by unfold straddle; split_ifs <;> norm_num
  unfold activeMass
  split_ifs with ha
  · obtain ⟨haG,haT,haP⟩ := ha
    by_cases hg : d'.sourceGiant x (h-r-H)
    · by_cases hg' : d'.sourceGiant x (h-r+H)
      · have hthree := case_three_bound d d' p hp x hx r (h-r+H) T haT hg'
        have he := mass_diff_inter p (d.cell r x) (d'.cell (h-r+H) x)
        change mass p (d.cell r x) = _ + plusError d d' p x h H r at he
        nlinarith
      · have hs : straddle d' x h H r = 1 := by simp [straddle,hg,hg']
        rw [hs]
        nlinarith
    · have hone := small_case_one p hp h1 (d.cell r x) (d'.cell (h-r-H) x) lam hlam hlam2 haP.le
      have hnge : nongiantMass d' p x (h-r-H) = mass p (d'.cell (h-r-H) x) := by
        simp [nongiantMass,hg]
      rw [hnge]
      change mass p (d.cell r x) ≤ _ + minusError d d' p x h H r at hone
      nlinarith
  · positivity

omit [DecidableEq P] in
lemma nongiantMass_measurable (d : Depth P) (p : P → ℝ) (x : P) :
    Measurable (nongiantMass d p x) := by
  classical
  let f : Finset P → ℝ := fun C => if ¬Fintype.card P < 2*C.card then mass p C else 0
  have h := (measurable_of_finite f).comp (d.measurable_cell x)
  have he : nongiantMass d p x = f ∘ (fun r => d.cell r x) := by
    funext r
    by_cases hg : Fintype.card P < 2*(d.cell r x).card
    · simp [nongiantMass,f,Depth.sourceGiant,hg]
    · simp [nongiantMass,f,Depth.sourceGiant,hg]
  rw [he]
  exact h

omit [DecidableEq P] in
lemma activeMass_measurable (d : Depth P) (p : P → ℝ) (x : P) (T lam : ℝ) :
    Measurable (activeMass d p x T lam) := by
  classical
  let f : Finset P → ℝ := fun C => if ¬Fintype.card P < 2*C.card ∧ (C.card : ℝ) < T ∧ mass p C < lam
      then mass p C else 0
  have h := (measurable_of_finite f).comp (d.measurable_cell x)
  have he : activeMass d p x T lam = f ∘ (fun r => d.cell r x) := by
    funext r
    by_cases hg : Fintype.card P < 2*(d.cell r x).card
    · simp [activeMass,f,Depth.sourceGiant,hg]
    · simp [activeMass,f,Depth.sourceGiant,hg,Nat.not_lt.mp hg]
  rw [he]
  exact h

omit [DecidableEq P] in
lemma nongiantMass_integrable (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) (x : P) (hx : p x = 0) :
    Integrable (nongiantMass d p x) := by
  classical
  apply Depth.integrable_supported_Icc (nongiantMass_measurable d p x) (a:=-d.radius) (b:=d.radius) (C:=1)
  · intro r
    rw [Real.norm_eq_abs,abs_of_nonneg (nongiantMass_nonneg d p hp x r)]
    unfold nongiantMass
    split_ifs <;> first | exact mass_le_one hp h1 _ | norm_num
  · intro r hr
    by_cases hlo : r ≤ -d.radius
    · have hG : d.sourceGiant x r := by
        unfold Depth.sourceGiant
        rw [d.cell_of_low hlo x,Finset.card_univ]
        omega
      simp [nongiantMass,hG]
    · have hhi : d.radius < r := by
        by_contra! hhi
        exact hr ⟨(not_le.mp hlo).le,hhi⟩
      simp only [nongiantMass]
      rw [d.cell_of_high hhi x]
      have he : mass p {x} = 0 := by simp [mass,hx]
      split_ifs <;> simp [he]

omit [DecidableEq P] in
lemma activeMass_integrable (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) (x : P) (hx : p x = 0)
    (T lam : ℝ) : Integrable (activeMass d p x T lam) := by
  classical
  apply (nongiantMass_integrable d hn p hp h1 x hx).mono'
    (activeMass_measurable d p x T lam).aestronglyMeasurable
  filter_upwards with r
  unfold activeMass nongiantMass
  split_ifs <;> simp_all [abs_of_nonneg (mass_nonneg hp (d.cell r x)),mass_nonneg hp]

lemma straddle_integrable (d : Depth P) (hn : 2 ≤ Fintype.card P) (x : P) (h H : ℝ) :
    Integrable (straddle d x h H) := by
  classical
  have he : straddle d x h H =
      (Set.Ico (h-H-d.sourceM x) (h+H-d.sourceM x)).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r
    simp only [straddle,d.sourceGiant_cutoff hn,not_le,Set.indicator_apply,Set.mem_Ico]
    congr 1
    apply propext
    constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
  rw [he,integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)

lemma neighborMass_integrable (d d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (x : P) (T : ℝ) : Integrable (neighborMass d d' p x T) := by
  classical
  unfold neighborMass
  apply integrable_finsetSum
  intro y _
  apply Integrable.const_mul
  by_cases h : x ∈ (d.smallNeighbors y T).erase y
  · simpa only [h,ite_true] using d'.integrable_outsideIndicator hn y
  · simp only [h,ite_false]
    exact integrable_zero _ _ _

lemma neighborMass_integral (d d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (x : P) (T : ℝ) :
    (∫ r, neighborMass d d' p x T r) =
      ∑ y, p y * (if x ∈ (d.smallNeighbors y T).erase y then d'.potential y else 0) := by
  classical
  unfold neighborMass
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [integral_const_mul]
    by_cases hh : x ∈ (d.smallNeighbors y T).erase y
    · simp only [hh,ite_true,Depth.potential]
    · simp only [hh,ite_false,integral_zero]
  · intro y _
    apply Integrable.const_mul
    by_cases hh : x ∈ (d.smallNeighbors y T).erase y
    · simpa only [hh,ite_true] using d'.integrable_outsideIndicator hn y
    · simp only [hh,ite_false]; exact integrable_zero _ _ _

end WeakPinned.SmallFiber

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy
variable {P : Type u7} [Fintype P] [DecidableEq P]

lemma pairMass_integrable (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (x : P) (hx : p x = 0) :
    Integrable (fun r => ∑ y, p y * d.pairOverlap r x y) := by
  apply integrable_finsetSum
  intro y _
  by_cases hxy : x = y
  · subst y; simp only [hx,zero_mul]; exact integrable_zero _ _ _
  · exact (d.integrable_pairOverlap hn x y hxy).const_mul _

lemma integral_nongiantMass_bound (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) (x : P) (hx : p x = 0) :
    (∫ r, nongiantMass d p x r) ≤ ∑ y, p y * ∫ r, d.pairOverlap r x y := by
  calc
    _ ≤ ∫ r : ℝ, ∑ y, p y * d.pairOverlap r x y :=
      integral_mono (nongiantMass_integrable d hn p hp h1 x hx) (pairMass_integrable d hn p x hx)
        (fun r => nongiant_mass_bound d p hp x r)
    _ = _ := by
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl (fun y _ => integral_const_mul (p y) _)
      · intro y _
        by_cases hxy : x = y
        · subst y; simp only [hx,zero_mul]; exact integrable_zero _ _ _
        · exact (d.integrable_pairOverlap hn x y hxy).const_mul _

/-- The local small-fiber bound for two entire realized hierarchies. This
    includes the exact signed-depth error; it will vanish at finite places
    and have an exponentially small grid mean at archimedean places. -/
lemma active_integral (d d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1)
    (x : P) (hx : p x = 0) (h H T lam : ℝ)
    (hH : 0 ≤ H) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2) :
    (∫ r, activeMass d p x T lam r) ≤
      2*lam*(∑ y, p y * ∫ r, d'.pairOverlap r x y) + 2*lam*H +
      (∑ y, p y * max (|d.value x y+d'.value x y-h|-H) 0) +
      ∑ y, p y * (if x ∈ (d.smallNeighbors y T).erase y then d'.potential y else 0) := by
  classical
  have hshift₁ (r : ℝ) : h-r-H = (h-H)-r := by ring
  have hshift₂ (r : ℝ) : h-r+H = (h+H)-r := by ring
  have hi₁ : Integrable (fun r => 2*lam*nongiantMass d' p x (h-r-H)) := by
    simp_rw [hshift₁]
    exact ((integrable_comp_sub_left _ (h-H)).mpr (nongiantMass_integrable d' hn p hp h1 x hx)).const_mul _
  have hi₂ : Integrable (fun r => lam*straddle d' x h H r) :=
    (straddle_integrable d' hn x h H).const_mul _
  have hi₃ := (minusError_integrable d d' p x hx h H).add (plusError_integrable d d' p x hx h H)
  have hi₄ : Integrable (fun r => neighborMass d d' p x T (h-r+H)) := by
    simp_rw [hshift₂]
    exact (integrable_comp_sub_left _ (h+H)).mpr (neighborMass_integrable d d' hn p x T)
  have hb := integral_mono (activeMass_integrable d hn p hp h1 x hx T lam)
    (((hi₁.add hi₂).add hi₃).add hi₄) (fun r => by
      have hh := active_pointwise d d' p hp h1 x hx h H T lam r hlam hlam2
      dsimp only [Pi.add_apply]
      linarith)
  simp only [Pi.add_apply] at hb
  have he₁ := integral_add ((hi₁.add hi₂).add hi₃) hi₄
  have he₂ := integral_add (hi₁.add hi₂) hi₃
  have he₃ := integral_add hi₁ hi₂
  simp only [Pi.add_apply] at he₁ he₂ he₃
  rw [he₁,he₂,he₃] at hb
  rw [integral_const_mul,integral_const_mul] at hb
  simp_rw [hshift₁,hshift₂] at hb
  rw [integral_sub_left_eq_self,integral_sub_left_eq_self,
    neighborMass_integral d d' hn p x T,errors_integral d d' p x hx h H hH] at hb
  have hs : (∫ r, straddle d' x h H r) = 2*H := d'.straddle_integral hn x h H hH
  rw [hs] at hb
  have hng := mul_le_mul_of_nonneg_left (integral_nongiantMass_bound d' hn p hp h1 x hx)
    (show 0 ≤ 2*lam by positivity)
  linarith

lemma fiber_neighbor_bound {I : Type u9} [Fintype I]
    (d d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ i, w i * ∑ y, p i y *
      (if x i ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y then d'.potential y else 0)) ≤
      B*τ/Fintype.card P * ∑ y, d'.potential y := by
  classical
  have hn0 : 0 < (Fintype.card P:ℝ) := by exact_mod_cast (show 0 < Fintype.card P by omega)
  have hn1 : 0 < (Fintype.card P:ℝ)-1 := by
    have : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
    linarith
  have hid (y : P) :
      (∑ i, w i * (p i y * (if x i ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y then d'.potential y else 0))) =
      (∑ a ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y, edgeLaw w p x a y) * d'.potential y := by
    rw [Finset.sum_mul]
    simp only [edgeLaw,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    have he : (∑ a ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y,
        if x i = a then w i*p i y else 0) =
        if x i ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y then w i*p i y else 0 := by
      simp [eq_comm]
    rw [he]
    split_ifs <;> ring
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hid]
  have hb (y : P) : (∑ a ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y, edgeLaw w p x a y) ≤ B*τ/Fintype.card P := by
    calc
      _ ≤ ((d.smallNeighbors y (τ*Fintype.card P)).erase y).card *
          (B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) := by
        calc
          _ ≤ ∑ a ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y,
              B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1)) :=
            Finset.sum_le_sum (fun a ha => hdom a y (Finset.ne_of_mem_erase ha))
          _ = _ := by simp
      _ ≤ (τ*((Fintype.card P:ℝ)-1)) * (B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :=
        mul_le_mul_of_nonneg_right (d.smallNeighbors_erase_bound hn y τ hτ hτ1) (by positivity)
      _ = _ := by field_simp
  exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hb y) (d'.potential_nonneg y))

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

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy Variance
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

omit [Fintype P] in
lemma edgeCell_formula (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (C : Finset P) :
    edgeCell w p x C = ∑ i, w i * (if x i ∈ C then mass (p i) C else 0) := by
  classical
  unfold edgeCell edgeLaw
  calc
    _ = ∑ a ∈ C, ∑ i, ∑ b ∈ C, if x i = a then w i * p i b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ i, ∑ a ∈ C, ∑ b ∈ C, if x i = a then w i * p i b else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have he (a : P) : (∑ b ∈ C, if x i = a then w i*p i b else 0) =
          if x i = a then w i*mass (p i) C else 0 := by
        by_cases h : x i = a <;> simp [h,mass,Finset.mul_sum]
      simp_rw [he]
      by_cases h : x i ∈ C <;> simp [h,eq_comm]

omit [Fintype P] in
lemma slice_le_edgeCell (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i y, 0 ≤ p i y) (lam : ℝ) (C : Finset P) :
    slice w p x lam C ≤ edgeCell w p x C := by
  rw [edgeCell_formula]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  split_ifs <;> simp_all [mass_nonneg (hp i)]

omit [Fintype P] in
lemma slice_le_lam (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (lam : ℝ) (hlam : 0 ≤ lam) (C : Finset P) :
    slice w p x lam C ≤ lam := by
  calc
    _ ≤ ∑ i, w i * lam := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      split_ifs with h
      · exact h.2.le
      · exact hlam
    _ = _ := by rw [← Finset.sum_mul,hW,one_mul]

omit [Fintype P] in
lemma edgeLaw_diag (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hx : ∀ i, p i (x i) = 0) (a : P) : edgeLaw w p x a a = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : x i = a
  · rw [ite_eq_left h,← h,hx i,mul_zero]
  · simp [h]

lemma edgeCell_dom (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hx : ∀ i, p i (x i) = 0) (B : ℝ)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1)))
    (C : Finset P) : edgeCell w p x C ≤ B*pairCell Finset.univ C := by
  classical
  simp only [pairCell,Finset.mul_sum,edgeCell]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases hab : a = b
  · subst b; simp [edgeLaw_diag w p x hx,pairProb_diag]
  · simpa [pairProb,hab,div_eq_mul_inv] using hdom a b hab

omit [Fintype P] in
lemma slice_singleton (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hx : ∀ i, p i (x i) = 0) (lam : ℝ) (C : Finset P) (hC : C.card ≤ 1) :
    slice w p x lam C = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : x i ∈ C
  · have he : C = {x i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi,fun y hy => (Finset.card_le_one.mp hC y hy (x i) hi)⟩
    simp [he,mass,hx]
  · simp [hi]

lemma large_slice_bound (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hn : 2 ≤ Fintype.card P)
    (lam τ : ℝ) (hlam : 0 ≤ lam) (hτ : 0 < τ)
    (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (C : Finset P)
    (hC : τ*(Fintype.card P:ℝ) ≤ C.card) :
    slice w p x lam C ≤ (2*lam/τ^2)*pairCell Finset.univ C := by
  have hn0 : 0 < (Fintype.card P:ℝ) := by exact_mod_cast (show 0 < Fintype.card P by omega)
  have hm : 2 ≤ C.card := by exact_mod_cast hτn.trans hC
  have hcomp := (uniform_pair_comparison C hm).1
  have ha : τ ≤ cellProb Finset.univ C := by
    simpa [cellProb] using (le_div_iff₀ hn0).mpr hC
  have hτsq : τ^2 ≤ (cellProb Finset.univ C)^2 := sq_le_sq₀ hτ.le (hτ.le.trans ha) |>.mpr ha
  have hlow : τ^2 ≤ 2*pairCell Finset.univ C := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlow hlam
  have he : lam ≤ (2*lam/τ^2)*pairCell Finset.univ C := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    nlinarith
  exact (slice_le_lam w p x hw hW lam hlam C).trans he

lemma small_slice_bound (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i y, 0 ≤ p i y) (hx : ∀ i, p i (x i) = 0)
    (B τ lam : ℝ) (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1)))
    (C : Finset P) (hC : (C.card:ℝ) < τ*Fintype.card P) :
    slice w p x lam C ≤ B*τ*cellProb Finset.univ C := by
  by_cases hm : 2 ≤ C.card
  · have hn : 0 < (Fintype.card P:ℝ) := by exact_mod_cast (show 0 < Fintype.card P from lt_of_lt_of_le (by omega) (Finset.card_le_univ C))
    have ha : cellProb Finset.univ C ≤ τ := by
      simpa [cellProb] using (div_le_iff₀ hn).mpr hC.le
    have ha0 : 0 ≤ cellProb (Finset.univ : Finset P) C := cellProb_nonneg _ _
    calc
      _ ≤ B*pairCell Finset.univ C := (slice_le_edgeCell w p x hw hp lam C).trans (edgeCell_dom w p x hx B hdom C)
      _ ≤ B*(cellProb Finset.univ C)^2 := mul_le_mul_of_nonneg_left (uniform_pair_comparison C hm).2 hB
      _ ≤ B*τ*cellProb Finset.univ C := by nlinarith [mul_nonneg hB (mul_nonneg ha0 (sub_nonneg.mpr ha))]
  · rw [slice_singleton w p x hx lam C (by omega)]
    exact mul_nonneg (mul_nonneg hB hτ) (cellProb_nonneg _ _)

end WeakPinned.SmallFiber

namespace WeakPinned.Hierarchy.Depth
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)
lemma sum_source_cell (f : Finset P → ℝ) (r : ℝ) (x : P) :
    (∑ C ∈ d.cells r, if x ∈ C then f C else 0) = f (d.cell r x) := by
  classical
  have he : ∀ C ∈ d.cells r, (if x ∈ C then f C else 0) =
      if C = d.cell r x then f (d.cell r x) else 0 := by
    intro C hC
    by_cases hx : x ∈ C
    · rw [d.cell_of_mem hC hx]; simp [d.share_refl]
    · have hn : C ≠ d.cell r x := by intro h; apply hx; rw [h]; exact d.self_mem_cell r x
      simp [hx,hn]
  rw [Finset.sum_congr rfl he]
  simp [d.cell_mem_cells r x]

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

lemma sum_complement_prob (r : ℝ) :
    (∑ C ∈ d.giants r, Variance.cellProb Finset.univ Cᶜ) =
      (∑ y, d.outsideIndicator r y)/(Fintype.card P:ℝ) := by
  classical
  by_cases hg : (d.giants r).Nonempty
  · obtain ⟨G,hG⟩ := hg
    have hs : d.giants r = {G} := Finset.ext fun C => by
      simp only [Finset.mem_singleton]
      exact ⟨fun hC => d.giants_unique hC hG,fun h => h ▸ hG⟩
    have hne : (d.giants r).Nonempty := ⟨G,hG⟩
    have hi (y : P) : d.outsideIndicator r y = if y ∈ Gᶜ then 1 else 0 := by
      simp [outsideIndicator,hne,d.giant_eq hG]
    simp_rw [hi]
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp [hs,Variance.cellProb]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hg,outsideIndicator]
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy Variance
variable {P : Type u4} {I : Type u5} [Fintype P] [DecidableEq P] [Fintype I]

lemma nongiant_small_slice (d : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (T lam r : ℝ) :
    (∑ C ∈ d.cells r, if ¬Fintype.card P < 2*C.card ∧ (C.card:ℝ) < T then slice w p x lam C else 0) =
      ∑ i, w i * activeMass d (p i) (x i) T lam r := by
  classical
  have he (C : Finset P) :
      (if ¬Fintype.card P < 2*C.card ∧ (C.card:ℝ) < T then slice w p x lam C else 0) =
      ∑ i, w i * (if x i ∈ C then
        (if ¬Fintype.card P < 2*C.card ∧ (C.card:ℝ) < T ∧ mass (p i) C < lam then mass (p i) C else 0) else 0) := by
    by_cases h : ¬Fintype.card P < 2*C.card ∧ (C.card:ℝ) < T
    · simp only [h,slice]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : x i ∈ C <;> simp [hx]
    · simp only [h,ite_false]
      symm
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hx hh
      · exact False.elim (h ⟨hh.1,hh.2.1⟩)
      · exact mul_zero _
      · exact mul_zero _
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.mul_sum,d.sum_source_cell]
  congr 1
  unfold activeMass Depth.sourceGiant
  split_ifs <;> rfl

lemma pointwise_split (d : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hp : ∀ i y, 0 ≤ p i y)
    (hx : ∀ i, p i (x i) = 0) (hn : 2 ≤ Fintype.card P)
    (B τ lam r : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hτ : 0 < τ)
    (hτn : 2 ≤ τ*(Fintype.card P:ℝ))
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    d.sumCells (slice w p x lam) r ≤
      (2*lam/τ^2)*d.sumCells (pairCell Finset.univ) r +
      B*τ/(Fintype.card P:ℝ)*(∑ y, d.outsideIndicator r y) +
      ∑ i, w i*activeMass d (p i) (x i) (τ*Fintype.card P) lam r := by
  classical
  have hcoef : 0 ≤ 2*lam/τ^2 := by positivity
  have hnng : ∀ C : Finset P, 0 ≤ (2*lam/τ^2)*pairCell Finset.univ C :=
    fun C => mul_nonneg hcoef (pairCell_nonneg _ _)
  have hactual :
      (∑ C ∈ d.cells r, if ¬Fintype.card P < 2*C.card then slice w p x lam C else 0) ≤
      (2*lam/τ^2)*(∑ C ∈ d.cells r, if ¬Fintype.card P < 2*C.card then pairCell Finset.univ C else 0) +
      ∑ i, w i*activeMass d (p i) (x i) (τ*Fintype.card P) lam r := by
    rw [←nongiant_small_slice,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro C _
    by_cases hg : ¬Fintype.card P < 2*C.card
    · by_cases hc : (C.card:ℝ) < τ*Fintype.card P
      · simp only [hg,hc,not_false_eq_true,true_and,ite_true]
        linarith [hnng C]
      · simp only [hg,hc,not_false_eq_true,true_and,ite_true,ite_false,add_zero]
        exact large_slice_bound w p x hw hW hn lam τ hlam hτ hτn C (le_of_not_gt hc)
    · simp [hg]
  have hgiant : (∑ C ∈ d.giants r, slice w p x lam Cᶜ) ≤
      (2*lam/τ^2)*(∑ C ∈ d.giants r, pairCell Finset.univ Cᶜ) +
      B*τ*(∑ C ∈ d.giants r, cellProb Finset.univ Cᶜ) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro C _
    by_cases hc : (Cᶜ.card:ℝ) < τ*Fintype.card P
    · exact (small_slice_bound w p x hw hp hx B τ lam hB hτ.le hdom Cᶜ hc).trans (le_add_of_nonneg_left (hnng Cᶜ))
    · exact (large_slice_bound w p x hw hW hn lam τ hlam hτ hτn Cᶜ (le_of_not_gt hc)).trans
        (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hB hτ.le) (cellProb_nonneg _ _)))
  rw [d.sum_complement_prob] at hgiant
  rw [d.sumCells_split,d.sumCells_split]
  have he : B*τ*((∑ y, d.outsideIndicator r y)/(Fintype.card P:ℝ)) =
      B*τ/(Fintype.card P:ℝ)*(∑ y, d.outsideIndicator r y) := by ring
  rw [he] at hgiant
  linarith

end WeakPinned.SmallFiber

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

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy Variance
variable {P : Type u7} {I : Type u8} [Fintype P] [DecidableEq P] [Fintype I]

lemma integral_split (d : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y = 1) (hx : ∀ i, p i (x i) = 0) (hn : 2 ≤ Fintype.card P)
    (B τ lam : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hτ : 0 < τ)
    (hτn : 2 ≤ τ*(Fintype.card P:ℝ))
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, d.mass C * slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, d.mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*(∑ y, d.potential y) +
      ∑ i, w i*(∫ r, activeMass d (p i) (x i) (τ*Fintype.card P) lam r) := by
  classical
  have hi₁ := (d.integrable_sumCells hn (pairCell Finset.univ) (singleton_pairCell _)).const_mul (2*lam/τ^2)
  have hi₂ := (integrable_finsetSum (s:=Finset.univ) (fun y _ => d.integrable_outsideIndicator hn y)).const_mul (B*τ/Fintype.card P)
  have hi₃ := integrable_finsetSum (s:=Finset.univ) (fun i _ =>
    (activeMass_integrable d hn (p i) (hp i) (hp1 i) (x i) (hx i) (τ*Fintype.card P) lam).const_mul (w i))
  have hb := integral_mono (d.integrable_sumCells hn _ (slice_singleton w p x hx lam))
    ((hi₁.add hi₂).add hi₃) (fun r => pointwise_split d w p x hw hW hp hx hn B τ lam r hB hlam hτ hτn hdom)
  have ha := integral_add (hi₁.add hi₂) hi₃
  have hb' := integral_add hi₁ hi₂
  simp only [Pi.add_apply] at hb ha hb'
  rw [ha,hb',integral_const_mul,integral_const_mul,
    d.integral_sumCells hn _ (singleton_pairCell _),
    d.integral_sumCells hn _ (slice_singleton w p x hx lam),
    integral_finsetSum _ (fun y _ => d.integrable_outsideIndicator hn y),
    integral_finsetSum _ (fun i _ =>
      (activeMass_integrable d hn (p i) (hp i) (hp1 i) (x i) (hx i) (τ*Fintype.card P) lam).const_mul (w i))] at hb
  simpa only [integral_const_mul,Depth.potential] using hb

lemma local_small_fiber (d d' : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y = 1) (hx : ∀ i, p i (x i) = 0) (hn : 2 ≤ Fintype.card P)
    (h : I → ℝ) (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, d.mass C * slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, d.mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, d.potential y)+(∑ y, d'.potential y)) +
      2*lam*(∑ i, w i*∑ y, p i y*∫ r, d'.pairOverlap r (x i) y) + 2*lam*H +
      ∑ i, w i*∑ y, p i y*max (|d.value (x i) y+d'.value (x i) y-h i|-H) 0 := by
  have hb := integral_split d w p x hw hW hp hp1 hx hn B τ lam hB hlam hτ hτn hdom
  have ha := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left
    (active_integral d d' hn (p i) (hp i) (hp1 i) (x i) (hx i) (h i) H (τ*Fintype.card P) lam hH hlam hlam2) (hw i))
  have hnbr := fiber_neighbor_bound d d' hn w p x B τ hB hτ hτ1 hdom
  simp only [mul_add,Finset.sum_add_distrib] at ha
  have hc : (∑ i, w i*(2*lam*H)) = 2*lam*H := by rw [←Finset.sum_mul,hW,one_mul]
  have hi : (∑ i, w i*(2*lam*(∑ y, p i y*∫ r, d'.pairOverlap r (x i) y))) =
      2*lam*(∑ i, w i*(∑ y, p i y*∫ r, d'.pairOverlap r (x i) y)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hc,hi] at ha
  linarith

end WeakPinned.SmallFiber

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy Variance
variable {P : Type u9} {I : Type u10} [Fintype P] [DecidableEq P] [Fintype I]

lemma pair_integral_edgeCell (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (hx : ∀ i, p i (x i) = 0) :
    (∑ i, w i*∑ y, p i y * ∫ r, d.pairOverlap r (x i) y) =
      ∑ C, d.mass C * edgeCell w p x C := by
  classical
  have hpair (i : I) (y : P) :
      p i y * (∫ r, d.pairOverlap r (x i) y) =
      ∑ C, d.mass C * (if x i ∈ C ∧ y ∈ C then p i y else 0) := by
    by_cases hxy : x i = y
    · subst y; simp [hx]
    · have h := d.mass_overlap hn (x i) y hxy
      dsimp [Depth.overlapLength] at h
      rw [← h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C _
      split_ifs <;> ring
  simp_rw [hpair,Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [edgeCell_formula,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ∈ C
  · simp only [hi,true_and,ite_true,mass_as_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  · simp [hi]

lemma local_small_fiber_reduced (d d' : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y = 1) (hx : ∀ i, p i (x i) = 0) (hn : 2 ≤ Fintype.card P)
    (h : I → ℝ) (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, d.mass C * slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, d.mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, d.potential y)+(∑ y, d'.potential y)) +
      2*lam*B*(∑ C, d'.mass C*pairCell Finset.univ C) + 2*lam*H +
      ∑ i, w i*∑ y, p i y*max (|d.value (x i) y+d'.value (x i) y-h i|-H) 0 := by
  have hb := local_small_fiber d d' w p x hw hW hp hp1 hx hn h B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom
  rw [pair_integral_edgeCell d' hn w p x hx] at hb
  have hd : (∑ C, d'.mass C*edgeCell w p x C) ≤ B*∑ C, d'.mass C*pairCell Finset.univ C := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C _
    calc
      _ ≤ d'.mass C*(B*pairCell Finset.univ C) := mul_le_mul_of_nonneg_left (edgeCell_dom w p x hx B hdom C) (d'.mass_nonneg C)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*lam by positivity)
  nlinarith
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

lemma arch_small_fiber (hn : 2 ≤ Fintype.card P) (v : InfinitePlace K)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (t : I → K)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, (∫ ω, (arch Z₁ v ω).mass C ∂Grid.fullLaw)*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, (∫ ω, (arch Z₁ v ω).mass C ∂Grid.fullLaw)*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, ∫ ω, (arch Z₁ v ω).potential y ∂Grid.fullLaw)+
        (∑ y, ∫ ω, (arch Z₂ v ω).potential y ∂Grid.fullLaw)) +
      2*lam*B*(∑ C, (∫ ω, (arch Z₂ v ω).mass C ∂Grid.fullLaw)*pairCell Finset.univ C) + 2*lam*H +
      16*Real.exp (-H/2) := by
  have hiM₁ (C : Finset P) := Depth.integrable_mass_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn C
  have hiM₂ (C : Finset P) := Depth.integrable_mass_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn C
  have hiS₁ (y : P) := Depth.integrable_potential_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn y
  have hiS₂ (y : P) := Depth.integrable_potential_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn y
  have hiE (i : I) (y : P) : Integrable (fun ω => max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0) Grid.fullLaw := by
    have hd := ((arch_integrable Z₁ h₁ v (x i) y).add (arch_integrable Z₂ h₂ v (x i) y)).add
      (integrable_const (Real.log (v (t i))))
    exact (hd.abs.sub (integrable_const H)).sup (integrable_zero _ _ _)
  have hA := (integrable_finsetSum (s:=Finset.univ) (fun C _ => (hiM₁ C).mul_const (pairCell Finset.univ C))).const_mul (2*lam/τ^2)
  have hS := ((integrable_finsetSum (s:=Finset.univ) (fun y _ => hiS₁ y)).add
    (integrable_finsetSum (s:=Finset.univ) (fun y _ => hiS₂ y))).const_mul (B*τ/Fintype.card P)
  have hA' := (integrable_finsetSum (s:=Finset.univ) (fun C _ => (hiM₂ C).mul_const (pairCell Finset.univ C))).const_mul (2*lam*B)
  have hE := integrable_finsetSum (s:=Finset.univ) (fun i _ =>
    (integrable_finsetSum (s:=Finset.univ) (fun y _ => (hiE i y).const_mul (p i y))).const_mul (w i))
  have hb := integral_mono (integrable_finsetSum (s:=Finset.univ) (fun C _ => (hiM₁ C).mul_const (slice w p x lam C)))
    ((((hA.add hS).add hA').add (integrable_const (2*lam*H))).add hE)
    (fun ω => by
      simpa only [Pi.add_apply,sub_neg_eq_add] using
        (local_small_fiber_reduced (arch Z₁ v ω) (arch Z₂ v ω) w p x hw hW hp hp1 hx hn
          (fun i => -Real.log (v (t i))) B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom))
  have hI₁ := integral_add (((hA.add hS).add hA').add (integrable_const (2*lam*H))) hE
  have hI₂ := integral_add ((hA.add hS).add hA') (integrable_const (2*lam*H))
  have hI₃ := integral_add (hA.add hS) hA'
  have hI₄ := integral_add hA hS
  have hI₅ := integral_add (integrable_finsetSum (s:=Finset.univ) (fun y _ => hiS₁ y))
    (integrable_finsetSum (s:=Finset.univ) (fun y _ => hiS₂ y))
  simp only [Pi.add_apply] at hb hI₁ hI₂ hI₃ hI₄ hI₅
  rw [hI₁,hI₂,hI₃,hI₄] at hb
  simp only [integral_const,probReal_univ,one_smul,integral_const_mul] at hb
  rw [hI₅] at hb
  rw [integral_finsetSum _ (fun C _ => (hiM₁ C).mul_const (slice w p x lam C)),
    integral_finsetSum _ (fun C _ => (hiM₁ C).mul_const (pairCell Finset.univ C)),
    integral_finsetSum _ (fun C _ => (hiM₂ C).mul_const (pairCell Finset.univ C)),
    integral_finsetSum _ (fun y _ => hiS₁ y),integral_finsetSum _ (fun y _ => hiS₂ y)] at hb
  simp only [integral_mul_const] at hb
  have he := arch_weighted_defect Z₁ Z₂ h₁ h₂ v w p x t hw hW hp hp1 hx ht H hH
  linarith

lemma finite_small_fiber (hn : 2 ≤ Fintype.card P) (v : FinitePlace K)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (t : I → K)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ))
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, (finite Z₁ h₁ v).mass C*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, (finite Z₁ h₁ v).mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, (finite Z₁ h₁ v).potential y)+(∑ y, (finite Z₂ h₂ v).potential y)) +
      2*lam*B*(∑ C, (finite Z₂ h₂ v).mass C*pairCell Finset.univ C) := by
  have hb := local_small_fiber_reduced (finite Z₁ h₁ v) (finite Z₂ h₂ v) w p x hw hW hp hp1 hx hn
    (fun i => -Real.log (v (t i))) B τ lam 0 hB hlam hlam2 hτ hτ1 hτn (le_refl _) hdom
  have he (i : I) (y : P) : p i y * max (|(finite Z₁ h₁ v).value (x i) y+
      (finite Z₂ h₂ v).value (x i) y- -Real.log (v (t i))|-0) 0=0 := by
    by_cases hy : p i y=0
    · simp [hy]
    · have hxy : x i ≠ y := by intro he; rw [← he,hx i] at hy; exact hy rfl
      have hh := Arithmetic.raw_fiber_identity v.val (Z₁ (x i)-Z₁ y) (Z₂ (x i)-Z₂ y)
        (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
      change -Real.log (v (Z₁ (x i)-Z₁ y)) + -Real.log (v (Z₂ (x i)-Z₂ y)) =
        -Real.log (v ((Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y))) at hh
      rw [ht i y hy] at hh
      simp only [finite,hxy,reduceIte,hh,sub_self,abs_zero,max_self,mul_zero]
  simpa only [he,Finset.sum_const_zero,mul_zero,add_zero] using hb

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
lemma placeAverage_add (V : Finset (FinitePlace K)) (A A' : InfinitePlace K → ℝ) (F F' : FinitePlace K → ℝ) :
    placeAverage V (fun v => A v+A' v) (fun v => F v+F' v) = placeAverage V A F + placeAverage V A' F' := by
  simp only [placeAverage,mul_add,Finset.sum_add_distrib]
  ring

omit h₁ h₂ in
lemma placeAverage_mul (V : Finset (FinitePlace K)) (a : ℝ) (A : InfinitePlace K → ℝ) (F : FinitePlace K → ℝ) :
    placeAverage V (fun v => a*A v) (fun v => a*F v) = a*placeAverage V A F := by
  simp only [placeAverage,Finset.mul_sum,mul_add]
  congr 1
  · exact Finset.sum_congr rfl (fun v _ => by ring)
  · exact Finset.sum_congr rfl (fun v _ => by ring)

omit h₁ h₂ in
lemma placeAverage_arch_const (V : Finset (FinitePlace K)) (a : ℝ) :
    placeAverage V (fun _ => a) (fun _ => 0) = a := by
  simp only [placeAverage,Finset.sum_const_zero,mul_zero,add_zero,← Finset.sum_mul,Arithmetic.sum_archWeight,one_mul]

omit h₁ h₂ in
lemma cellIntegral_placeAverage {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (f : Finset P → ℝ) :
    weightedIntegral (cellMass Z hZ) f = placeAverage V
      (fun v => ∑ C, (∫ ω, (arch Z v ω).mass C ∂Grid.fullLaw)*f C)
      (fun v => ∑ C, (finite Z hZ v).mass C*f C) := by
  simp only [weightedIntegral,cellMass,placeAverage,add_mul,Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    exact Finset.sum_congr rfl (fun C _ => by ring)
  · rw [Finset.sum_comm (s:=V)]
    simp_rw [← Finset.sum_mul, sum_finite_mass hZ hn V hV,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun C _ => by rw [← Finset.mul_sum]; ring)

omit h₁ h₂ in
lemma potentialIntegral_placeAverage {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) :
    (∑ y, S Z hZ y) = placeAverage V
      (fun v => ∑ y, ∫ ω, (arch Z v ω).potential y ∂Grid.fullLaw)
      (fun v => ∑ y, (finite Z hZ v).potential y) := by
  simp only [S,placeAverage,Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm (s:=V)]
    simp_rw [sum_finite_potential hZ hn V hV,Finset.mul_sum]

lemma arithmetic_small_fiber_one (hn : 2 ≤ Fintype.card P)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (t : I → K)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    weightedIntegral (cellMass Z₁ h₁) (slice w p x lam) ≤
      (2*lam/τ^2)*weightedIntegral (cellMass Z₁ h₁) (pairCell Finset.univ) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, S Z₁ h₁ y)+(∑ y, S Z₂ h₂ y)) +
      2*lam*B*weightedIntegral (cellMass Z₂ h₂) (pairCell Finset.univ) + 2*lam*H +
      16*Real.exp (-H/2) := by
  classical
  let V := badPlaces Z₁ h₁ ∪ badPlaces Z₂ h₂
  have hV₁ : badPlaces Z₁ h₁ ⊆ V := Finset.subset_union_left
  have hV₂ : badPlaces Z₂ h₂ ⊆ V := Finset.subset_union_right
  have hf (v : FinitePlace K) : (∑ C, (finite Z₁ h₁ v).mass C*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, (finite Z₁ h₁ v).mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, (finite Z₁ h₁ v).potential y)+(∑ y, (finite Z₂ h₂ v).potential y)) +
      2*lam*B*(∑ C, (finite Z₂ h₂ v).mass C*pairCell Finset.univ C) + 0 + 0 := by
    simpa only [add_zero] using finite_small_fiber Z₁ Z₂ h₁ h₂ hn v w p x t hw hW hp hp1 hx ht B τ lam hB hlam hlam2 hτ hτ1 hτn hdom
  have hb := placeAverage_mono V
    (fun v => arch_small_fiber Z₁ Z₂ h₁ h₂ hn v w p x t hw hW hp hp1 hx ht B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom)
    (fun v _ => hf v)
  simp only [placeAverage_add,placeAverage_mul,placeAverage_arch_const] at hb
  rw [← cellIntegral_placeAverage h₁ hn V hV₁,← cellIntegral_placeAverage h₁ hn V hV₁,
    ← cellIntegral_placeAverage h₂ hn V hV₂,← potentialIntegral_placeAverage h₁ hn V hV₁,
    ← potentialIntegral_placeAverage h₂ hn V hV₂] at hb
  exact hb

/-- The global small-fiber estimate, uniformly over number fields, places and configurations. -/

lemma arithmetic_small_fiber (hn : 2 ≤ Fintype.card P)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (t : I → K)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (slice w p x lam) ≤
      (2*lam/τ^2+2*lam*B)*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (pairCell Finset.univ) +
      2*B*τ/(Fintype.card P:ℝ)*(∑ y, totalPotential Z₁ Z₂ h₁ h₂ y) + 4*lam*H +
      32*Real.exp (-H/2) := by
  have hA := arithmetic_small_fiber_one Z₁ Z₂ h₁ h₂ hn w p x t hw hW hp hp1 hx ht B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom
  have ht' : ∀ i y, p i y ≠ 0 → (Z₂ (x i)-Z₂ y)*(Z₁ (x i)-Z₁ y)=t i := by
    intro i y hy
    rw [mul_comm]
    exact ht i y hy
  have hB' := arithmetic_small_fiber_one Z₂ Z₁ h₂ h₁ hn w p x t hw hW hp hp1 hx ht' B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom
  simp only [weightedIntegral,totalMass,totalPotential,add_mul,Finset.sum_add_distrib] at hA hB' ⊢
  linear_combination hA+hB'

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
lemma incoming_domination (B : ℝ) (hdom : ∀ x y, G.edgeLaw x y ≤ B*pairProb Finset.univ x y)
    (hn : 2 ≤ Fintype.card V) (x : V) :
    (∑ y, G.incomingWeight y*prob (G.incoming y) x) ≤ B*prob Finset.univ x := by
  simp_rw [G.sampling_incoming]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hdom x y)
  simpa only [← Finset.mul_sum,sum_pairProb Finset.univ (by simpa using hn)] using hh

end WeakPinned.Core.Fibers

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u5} {I : Type u6} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype I] in
lemma degree_marginal (x : V) : (∑ y, G.edgeLaw x y)+(∑ y, G.edgeLaw y x)=
    G.degree (-1) Finset.univ x/G.edgeCount := by
  simp only [edgeLaw,edges,edgeSet,Finset.mem_filter,Finset.mem_univ,true_and,
    ← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,degree,add_div,mul_one_div]

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

lemma PreparedGraph.degree_law (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η) (x : V) :
    2*((θ-η)/(θ+η/8))*prob Finset.univ x ≤ (∑ y, G.edgeLaw x y)+(∑ y, G.edgeLaw y x) := by
  rw [G.degree_marginal]
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hn0 : (0:ℝ)<Fintype.card V := by linarith
  have hnm : 0<(Fintype.card V : ℝ)-1 := by linarith
  have hθ : 0<θ+η/8 := by linarith
  have hd := h.degree x
  have hu := h.upper
  have hh : (2*(θ-η)*((Fintype.card V : ℝ)-1))/((θ+η/8)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) ≤
      G.degree (-1) Finset.univ x/G.edgeCount := by
    apply div_le_div₀ _ hd (h.edgeCount_pos hη) hu
    exact (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hη.le)) hnm.le).trans hd
  have he : (2*(θ-η)*((Fintype.card V : ℝ)-1))/((θ+η/8)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) =
      2*((θ-η)/(θ+η/8))*prob Finset.univ x := by
    simp only [prob,Finset.mem_univ,ite_true,Finset.card_univ]
    field_simp
  rwa [he] at hh

lemma PreparedGraph.heavy_bound (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η) (D : Finset V) :
    G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D / G.edgeCount ≤
      ((θ+η)/(θ-η))*pairCell Finset.univ D := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hden : 0<(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) := mul_pos (by linarith) (by linarith)
  have hD : 0 ≤ (D.card : ℝ)*((D.card : ℝ)-1) := by
    by_cases hz : D.card=0
    · simp [hz]
    · have hh : (1:ℝ)≤D.card := by exact_mod_cast (show 1≤D.card by omega)
      positivity
  have hb := h.subset D
  have hcmp : G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D / G.edgeCount ≤
      ((θ+η)*(D.card : ℝ)*((D.card : ℝ)-1))/((θ-η)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) := by
    apply div_le_div₀ _ hb (mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)) h.lower
    simpa only [mul_assoc] using mul_nonneg (show 0≤θ+η by linarith) hD
  convert hcmp using 1
  rw [pairCell_formula]
  simp only [Finset.univ_inter,Finset.card_univ]
  field_simp

lemma PreparedGraph.small_heavy_bound (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η)
    (D : Finset V) (hDsz : (D.card : ℝ)≤(Fintype.card V : ℝ)^(1-c)) :
    G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D / G.edgeCount ≤
      (η/(θ-η))*pairCell Finset.univ D := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hD : 0 ≤ (D.card : ℝ)*((D.card : ℝ)-1) := by
    by_cases hz : D.card=0
    · simp [hz]
    · have hh : (1:ℝ)≤D.card := by exact_mod_cast (show 1≤D.card by omega)
      positivity
  have hcmp : G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D / G.edgeCount ≤
      (η*(D.card : ℝ)*((D.card : ℝ)-1))/((θ-η)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) := by
    apply div_le_div₀ _ (h.small D hDsz) (mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)) h.lower
    simpa only [mul_assoc] using mul_nonneg hη0 hD
  convert hcmp using 1
  rw [pairCell_formula]
  simp only [Finset.univ_inter,Finset.card_univ]
  field_simp

end WeakPinned

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance SmallFiber
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

lemma qCell_eq (C : Finset V) : G.qCell C = SmallFiber.edgeCell G.fiberWeight (fun e => prob (G.targets e)) G.source C := by
  unfold qCell SmallFiber.edgeCell SmallFiber.edgeLaw
  simp_rw [G.sampling_fiber]

omit [Fintype V] in
omit [Fintype I] in
lemma fiber_mass (e : I) (C : Finset V) : mass (prob (G.targets e)) C=(G.size C e : ℝ)/(G.targets e).card := by
  rw [mass,sum_prob_cell]
  rfl

lemma qCell_split (hne : ∀ e, (G.targets e).Nonempty) (lam : ℝ) (C : Finset V) :
    G.qCell C = slice G.fiberWeight (fun e => prob (G.targets e)) G.source lam C + G.heavyCount lam C/G.edgeCount := by
  classical
  rw [G.qCell_eq,edgeCell_formula]
  unfold slice heavyCount
  simp only [Finset.sum_div,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hk : (0:ℝ)<(G.targets e).card := by exact_mod_cast Finset.card_pos.mpr (hne e)
  have hm := G.fiber_mass e C
  have hprod : G.fiberWeight e*mass (prob (G.targets e)) C=(G.size C e : ℝ)/G.edgeCount := by
    rw [hm,fiberWeight]
    field_simp
  have hcmp : lam*((G.targets e).card : ℝ) ≤ (G.size C e : ℝ) ↔ lam ≤ mass (prob (G.targets e)) C := by
    rw [hm,le_div_iff₀ hk]
  simp only [hcmp]
  by_cases hx : G.source e ∈ C <;> by_cases hp : mass (prob (G.targets e)) C<lam
  · simp [hx,hp,not_le.mpr hp]
  · simp [hx,hp,le_of_not_gt hp,hprod]
  · simp [hx]
  · simp [hx]

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
open Variance SmallFiber
variable {V : Type u6} {I : Type u7} [Fintype V] [Fintype I] [DecidableEq V]
variable {G : Core.Fibers V I} {θ γ c η : ℝ}

lemma PreparedGraph.overlap_lower (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η)
    (m : Finset V → ℝ) (b : ℝ) (S : V → ℝ) (hS : ∀ x, 0≤S x)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y) :
    weightedIntegral m (pairCell Finset.univ) -
      (2-2*((θ-η)/(θ+η/8)))*(∑ x, prob Finset.univ x*S x) ≤ weightedIntegral m G.qCell := by
  change _ ≤ weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, G.edgeLaw x y)
  rw [weighted_additive m b S hL G.edgeLaw G.edgeLaw_diag (G.sum_edgeLaw (h.edgeCount_pos hη)),
    uniform_additive m b S hL h.card_ge]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_right (h.degree_law hη hη0 x) (hS x))
  have he : (∑ x : V, 2*((θ-η)/(θ+η/8))*prob Finset.univ x*S x)=
      (2*((θ-η)/(θ+η/8)))*(∑ x : V, prob Finset.univ x*S x) := by
    simp only [Finset.mul_sum,mul_assoc]
  rw [he] at hh
  linarith

/-- A fully quantitative version of small-overlap before either scale branch.
The slice is the actual original fiber mass, not an assumed error term. -/
lemma PreparedGraph.small_overlap (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η)
    (m : Finset V → ℝ) (hm : ∀ C, 0 ≤ m C) (b : ℝ) (S : V → ℝ) (hS : ∀ x, 0≤S x)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y) :
    (θ/(θ-η))*weightedIntegral m (fun C => if (C.card : ℝ)≤(Fintype.card V : ℝ)^(1-c)
      then pairCell Finset.univ C else 0) ≤
      weightedIntegral m (slice G.fiberWeight (fun e => prob (G.targets e)) G.source (1/Real.log (Fintype.card V : ℝ))) +
      ((θ+η)/(θ-η)-1)*weightedIntegral m (pairCell Finset.univ) +
      (2-2*((θ-η)/(θ+η/8)))*(∑ x, prob Finset.univ x*S x) := by
  have hlo := h.overlap_lower hη hη0 m b S hS hL
  have hne : ∀ e, (G.targets e).Nonempty := by
    intro e
    have hn : (0:ℝ)<Fintype.card V := by exact_mod_cast (show 0<Fintype.card V by have := h.card_ge; omega)
    exact Finset.card_pos.mp (by exact_mod_cast ((Real.rpow_pos_of_pos hn γ).trans (h.fiber e)))
  have hpoint (C : Finset V) : G.qCell C ≤
      slice G.fiberWeight (fun e => prob (G.targets e)) G.source (1/Real.log (Fintype.card V : ℝ)) C +
      ((θ+η)/(θ-η))*pairCell Finset.univ C -
      (θ/(θ-η))*(if (C.card : ℝ)≤(Fintype.card V : ℝ)^(1-c) then pairCell Finset.univ C else 0) := by
    rw [G.qCell_split hne (1/Real.log (Fintype.card V : ℝ)) C]
    by_cases hC : (C.card : ℝ)≤(Fintype.card V : ℝ)^(1-c)
    · rw [ite_eq_left hC]
      have hh := h.small_heavy_bound hη hη0 C hC
      have he : (θ+η)/(θ-η)-θ/(θ-η)=η/(θ-η) := by ring
      calc
        _ ≤ slice G.fiberWeight (fun e => prob (G.targets e)) G.source (1/Real.log (Fintype.card V : ℝ)) C + (η/(θ-η))*pairCell Finset.univ C := add_le_add_right hh _
        _ = _ := by rw [← he]; ring
    · simp only [ite_eq_right hC,mul_zero,sub_zero]
      exact add_le_add_right (h.heavy_bound hη hη0 C) _
  have hint := Finset.sum_le_sum (s:=Finset.univ) (fun C _ => mul_le_mul_of_nonneg_left (hpoint C) (hm C))
  change weightedIntegral m G.qCell ≤ _ at hint
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hint
  have hcomm (a : ℝ) (f : Finset V → ℝ) : (∑ C, m C*(a*f C))=a*weightedIntegral m f := by
    simp only [weightedIntegral,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun C _ => by ring)
  simp only [hcomm] at hint
  change weightedIntegral m G.qCell ≤ weightedIntegral m _+_ - _ at hint
  nlinarith

end WeakPinned

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

lemma smallOverlapScale_nonneg (c : ℝ) : 0 ≤ smallOverlapScale Z₁ Z₂ h₁ h₂ c := by
  apply Finset.sum_nonneg
  intro C _
  apply mul_nonneg (totalMass_nonneg Z₁ Z₂ h₁ h₂ C)
  dsimp only
  split_ifs
  · exact pairCell_nonneg _ _
  · exact le_refl _

lemma PreparedGraph.arithmetic_slice (h : PreparedGraph V I G θ γ c η) (hη : η < θ)
    (t : I → K) (ht : ∀ e y, y ∈ G.targets e → (Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e)
    (τ lam H : ℝ) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card V:ℝ)) (hH : 0 ≤ H) :
    weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (slice G.fiberWeight (fun e => prob (G.targets e)) G.source lam) ≤
      (2*lam/τ^2+2*lam/(θ-η))*overlapScale Z₁ Z₂ h₁ h₂ +
      (2*τ/(θ-η))*potentialScale Z₁ Z₂ h₁ h₂ + 4*lam*H + 32*Real.exp (-H/2) := by
  have hne : ∀ e, (G.targets e).Nonempty := by
    intro e
    have hn : (0:ℝ)<Fintype.card V := by exact_mod_cast (show 0<Fintype.card V by have := h.card_ge; omega)
    exact Finset.card_pos.mp (by exact_mod_cast ((Real.rpow_pos_of_pos hn γ).trans (h.fiber e)))
  have hp : ∀ e y, 0 ≤ prob (G.targets e) y := by intro e y; unfold prob; split_ifs <;> positivity
  have hx : ∀ e, prob (G.targets e) (G.source e)=0 := by intro e; simp [prob,G.no_loop]
  have ht' : ∀ e y, prob (G.targets e) y ≠ 0 → (Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e := by
    intro e y hy
    apply ht e y
    by_contra hn
    exact hy (by simp [prob,hn])
  have hdom : ∀ a b, a ≠ b → SmallFiber.edgeLaw G.fiberWeight (fun e => prob (G.targets e)) G.source a b ≤
      (1/(θ-η))/((Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)) := by
    intro a b hab
    have hh := h.edge_domination hη a b
    simpa [SmallFiber.edgeLaw,G.sampling_fiber,pairProb,hab, div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  have hh := arithmetic_small_fiber Z₁ Z₂ h₁ h₂ h.card_ge G.fiberWeight (fun e => prob (G.targets e)) G.source t
    G.fiberWeight_nonneg (G.sum_fiberWeight (h.edgeCount_pos hη)) hp (fun e => sum_prob _ (hne e)) hx ht'
    (1/(θ-η)) τ lam H (by positivity) hlam hlam2 hτ hτ1 hτn hH hdom
  have he : (∑ x : V, totalPotential Z₁ Z₂ h₁ h₂ x)/(Fintype.card V:ℝ) = potentialScale Z₁ Z₂ h₁ h₂ := by
    simp only [potentialScale,prob,Finset.mem_univ,ite_true,Finset.card_univ,Finset.sum_div]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have ha : 2*(1/(θ-η))*τ/(Fintype.card V:ℝ)*(∑ x, totalPotential Z₁ Z₂ h₁ h₂ x) =
      (2*τ/(θ-η))*potentialScale Z₁ Z₂ h₁ h₂ := by rw [← he]; ring
  rw [ha] at hh
  convert hh using 1; unfold overlapScale; ring

/-- The genuine scale estimate, valid for every prepared arithmetic model.
All error terms are explicit and can be sent to zero uniformly in the field. -/
lemma PreparedGraph.arithmetic_small_overlap (h : PreparedGraph V I G θ γ c η) (hη : η < θ) (hη0 : 0 ≤ η)
    (t : I → K) (ht : ∀ e y, y ∈ G.targets e → (Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e)
    (τ H : ℝ) (hlam : 0 ≤ 1/Real.log (Fintype.card V:ℝ)) (hlam2 : 1/Real.log (Fintype.card V:ℝ) ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card V:ℝ)) (hH : 0 ≤ H) :
    smallOverlapScale Z₁ Z₂ h₁ h₂ c ≤
      (2*(1/Real.log (Fintype.card V:ℝ))/τ^2+2*(1/Real.log (Fintype.card V:ℝ))/(θ-η)+((θ+η)/(θ-η)-1))*overlapScale Z₁ Z₂ h₁ h₂ +
      (2*τ/(θ-η)+(2-2*((θ-η)/(θ+η/8))))*potentialScale Z₁ Z₂ h₁ h₂ +
      4*(1/Real.log (Fintype.card V:ℝ))*H + 32*Real.exp (-H/2) := by
  have hs := h.small_overlap hη hη0 (totalMass Z₁ Z₂ h₁ h₂) (totalMass_nonneg Z₁ Z₂ h₁ h₂)
    (baseConstant Z₁ Z₂ h₁ h₂) (totalPotential Z₁ Z₂ h₁ h₂) (totalPotential_nonneg Z₁ Z₂ h₁ h₂)
    (totalMass_overlap Z₁ Z₂ h₁ h₂ h.card_ge)
  have htS := h.arithmetic_slice Z₁ Z₂ h₁ h₂ hη t ht τ (1/Real.log (Fintype.card V:ℝ)) H hlam hlam2 hτ hτ1 hτn hH
  have hf : 1 ≤ θ/(θ-η) := (one_le_div (sub_pos.mpr hη)).mpr (by linarith)
  have he := mul_le_mul_of_nonneg_right hf (smallOverlapScale_nonneg Z₁ Z₂ h₁ h₂ c)
  change (θ/(θ-η))*smallOverlapScale Z₁ Z₂ h₁ h₂ c ≤ _ at hs
  change _ ≤ _ + ((θ+η)/(θ-η)-1)*overlapScale Z₁ Z₂ h₁ h₂ +
    (2-2*((θ-η)/(θ+η/8)))*potentialScale Z₁ Z₂ h₁ h₂ at hs
  nlinarith
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

lemma reciprocal_card_sub_one {n k : ℝ} (hn : 2≤n) (hnk : n≤k) :
    1/(k-1) ≤ 2/n := by
  apply (div_le_div_iff₀ (by linarith : 0<k-1) (by linarith : 0<n)).mpr
  nlinarith

end WeakPinned.Variance

namespace WeakPinned
open scoped BigOperators Topology
open Filter Variance Global
variable {V : ℕ → Type u13} {I : ℕ → Type u14} {K : ℕ → Type u15} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

/-- Asymptotic arithmetic variance for arbitrary genuine uniform-subset
families. The domination and size assumptions are finite sampling data.
The exact arithmetic cancellation and small-overlap rate are already proved. -/
theorem arithmetic_variance_rate (w : ∀ j, I j → ℝ) (B : ∀ j, I j → Finset (V j))
    (γ c M₀ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) (hcγ : c<γ) (_hc1 : c<1) (hM : 0≤M₀)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hw : ∀ j i, 0≤w j i) (hW : ∀ j, (∑ i, w j i)≤1)
    (hsize : ∀ᶠ j in atTop, ∀ i, (Fintype.card (V j):ℝ)^γ ≤ ((B j i).card:ℝ))
    (hdom : ∀ᶠ j in atTop, ∀ x, (∑ i, w j i*prob (B j i) x)≤ M₀*prob Finset.univ x)
    (hsmall : Tendsto (fun j => smallOverlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) c /
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0)) :
    Tendsto (fun j => weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
      (varianceCell (w j) (B j) ((Fintype.card (V j):ℝ)^(1-c))) /
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) := by
  let n := fun j => (Fintype.card (V j):ℝ)
  let U := fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let A := fun j => potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let D := fun j => smallOverlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) c
  have hU (j) : 0≤U j := overlapScale_nonneg _ _ _ _
  have hA (j) : 0≤A j := potentialScale_nonneg _ _ _ _
  have hden (j) : 0<U j+A j+1 := by linarith [hU j,hA j]
  have hNγ : Tendsto (fun j => n j^γ) atTop atTop := (tendsto_rpow_atTop hγ).comp hn
  have hcT : Tendsto (fun j => n j^(c-γ)) atTop (𝓝 0) :=
    by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0<γ-c)).comp hn
    convert h using 1; funext j; congr 1; ring
  have hlim : Tendsto (fun j => 4*(M₀+1)*n j^(c-γ)+4*M₀*(D j/(U j+A j+1))) atTop (𝓝 0) := by
    convert (hcT.const_mul (4*(M₀+1))).add (hsmall.const_mul (4*M₀)) using 1; simp
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun j => div_nonneg
      (Finset.sum_nonneg fun C _ => mul_nonneg (totalMass_nonneg _ _ _ _ C)
        (varianceCell_nonneg _ _ _ (hw j) C)) (hden j).le
  · filter_upwards [hn.eventually (eventually_ge_atTop (2:ℝ)),
      hNγ.eventually (eventually_ge_atTop (2:ℝ)), hsize,hdom] with j hjn hjγ hjs hjd
    have hnpos : 0<n j := by linarith
    have hnγpos : 0<n j^γ := Real.rpow_pos_of_pos hnpos _
    have hnP : 2≤Fintype.card (V j) := by exact_mod_cast hjn
    have hbs : ∀ i, 2≤(B j i).card := fun i => by exact_mod_cast (hjγ.trans (hjs i))
    have hbn : n j^γ ≤ n j := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1≤n j by linarith) hγ1.le
    have hk : ∀ i, 1/(((B j i).card:ℝ)-1)≤2/(n j^γ) := fun i => reciprocal_card_sub_one hjγ (hjs i)
    have hnerr : 1/(n j-1)≤2/(n j^γ) := reciprocal_card_sub_one hjγ hbn
    have hT : 1≤n j^(1-c) := Real.one_le_rpow (by linarith) (by linarith)
    have hτ : 0<n j^(-c) := Real.rpow_pos_of_pos hnpos _
    have hscale : n j^(-c)*n j≤n j^(1-c) := by
      calc
        _ = n j^(-c)*n j^(1:ℝ) := by rw [Real.rpow_one]
        _ = n j^((-c)+1) := (Real.rpow_add hnpos _ _).symm
        _ = n j^(1-c) := by congr 1;ring
        _ ≤ n j^(1-c) := le_rfl
    have hv := arithmetic_variance (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) hnP (w j) (B j)
      (n j^(1-c)) M₀ (2/(n j^γ)) (n j^(-c)) (hw j) (hW j) hT hM
      (by positivity) hτ hscale hbs hk hnerr hjd
    have he : 2*(2/(n j^γ))*(M₀+1)/(n j^(-c))=4*(M₀+1)*n j^(c-γ) := by
      rw [Real.rpow_sub hnpos,Real.rpow_neg hnpos.le]
      field_simp
      ring
    rw [he] at hv
    change _≤4*(M₀+1)*n j^(c-γ)*U j+4*M₀*D j at hv
    have hratio : U j/(U j+A j+1)≤1 := (div_le_one (hden j)).mpr (by linarith [hA j])
    have hcoeff : 0≤4*(M₀+1)*n j^(c-γ) := by positivity
    calc
      _ ≤ (4*(M₀+1)*n j^(c-γ)*U j+4*M₀*D j)/(U j+A j+1) := div_le_div_of_nonneg_right hv (hden j).le
      _ = (4*(M₀+1)*n j^(c-γ))*(U j/(U j+A j+1))+4*M₀*(D j/(U j+A j+1)) := by ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hratio hcoeff]
end WeakPinned
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

namespace WeakPinned

/-- The scalar limiting step for small overlap, with fixed positive τ and H. -/

theorem small_overlap_rate (n η U A D : ℕ → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hn : Tendsto n atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ j, 0 ≤ η j) (hU : ∀ j, 0 ≤ U j) (hA : ∀ j, 0 ≤ A j) (hD : ∀ j, 0 ≤ D j)
    (hbound : ∀ τ H : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ H → ∀ᶠ j in atTop,
      D j ≤ (2*(1/Real.log (n j))/τ^2+2*(1/Real.log (n j))/(θ-η j)+((θ+η j)/(θ-η j)-1))*U j +
        (2*τ/(θ-η j)+(2-2*((θ-η j)/(θ+η j/8))))*A j +
        4*(1/Real.log (n j))*H + 32*Real.exp (-H/2)) :
    Tendsto (fun j => D j/(U j+A j+1)) atTop (𝓝 0) := by
  have hlamT : Tendsto (fun j => 1/Real.log (n j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hn)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun j => ha.trans_le (div_nonneg (hD j) (by linarith [hU j,hA j]))
  · intro ε hε
    let τ := min 1 (ε*θ/16)
    have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
    have hτ1 : τ ≤ 1 := min_le_left _ _
    have hτb : 2*τ/θ ≤ ε/8 := by
      apply (div_le_iff₀ hθ).mpr
      have := min_le_right (1:ℝ) (ε*θ/16)
      dsimp [τ] at ⊢
      linarith
    have htExp : Tendsto (fun H : ℝ => 32*Real.exp (-H/2)) atTop (𝓝 0) := by
      have hd : Tendsto (fun H : ℝ => H/2) atTop atTop := by
        simpa only [div_eq_mul_inv, mul_comm, id_eq, one_mul] using
          (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<1/2)).mpr tendsto_id
      simpa only [Function.comp_def,neg_div,mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp hd).const_mul 32
    obtain ⟨H,hH,hHb⟩ := (eventually_ge_atTop (0:ℝ) |>.and (htExp.eventually (eventually_lt_nhds (show (0:ℝ)<ε/8 by linarith)))).exists
    let a := fun j => 2*(1/Real.log (n j))/τ^2+2*(1/Real.log (n j))/(θ-η j)+((θ+η j)/(θ-η j)-1)
    let b := fun j => 2*τ/(θ-η j)+(2-2*((θ-η j)/(θ+η j/8)))
    let e := fun j => 4*(1/Real.log (n j))*H+32*Real.exp (-H/2)
    have hθm : Tendsto (fun j => θ-η j) atTop (𝓝 θ) := by
      simpa using (tendsto_const_nhds (x:=θ)).sub hη
    have hθp : Tendsto (fun j => θ+η j) atTop (𝓝 θ) := by
      simpa using (tendsto_const_nhds (x:=θ)).add hη
    have hθp8 : Tendsto (fun j => θ+η j/8) atTop (𝓝 θ) := by
      simpa using (tendsto_const_nhds (x:=θ)).add (hη.div_const 8)
    have ha : Tendsto a atTop (𝓝 0) := by
      have ha1 : Tendsto (fun j => 2*(1/Real.log (n j))/τ^2) atTop (𝓝 0) := by
        simpa using (hlamT.const_mul 2).div_const (τ^2)
      have ha2 : Tendsto (fun j => 2*(1/Real.log (n j))/(θ-η j)) atTop (𝓝 0) := by
        convert (hlamT.const_mul 2).div hθm hθ.ne' using 1 <;> first | rfl | simp
      have ha3 : Tendsto (fun j => (θ+η j)/(θ-η j)-1) atTop (𝓝 0) := by
        simpa [hθ.ne',Pi.div_apply] using (hθp.div hθm hθ.ne').sub (tendsto_const_nhds (x:=1))
      simpa [a] using (ha1.add ha2).add ha3
    have hb : Tendsto b atTop (𝓝 (2*τ/θ)) := by
      have hb1 := (tendsto_const_nhds (x:=2*τ)).div hθm hθ.ne'
      have hb2 : Tendsto (fun j => 2-2*((θ-η j)/(θ+η j/8))) atTop (𝓝 0) := by
        simpa [hθ.ne',Pi.div_apply] using (tendsto_const_nhds (x:= (2:ℝ))).sub ((hθm.div hθp8 hθ.ne').const_mul 2)
      simpa [b,Pi.div_apply] using hb1.add hb2
    have he : Tendsto e atTop (𝓝 (32*Real.exp (-H/2))) := by
      simpa [e] using ((hlamT.const_mul 4).mul_const H).add (tendsto_const_nhds (x:=32*Real.exp (-H/2)))
    have hlt : 2*τ/θ+32*Real.exp (-H/2)<ε := by linarith
    have hsum := (ha.add hb |>.add he).eventually (eventually_lt_nhds (by simpa using hlt))
    filter_upwards [hbound τ H hτ hτ1 hH,hsum,hη.eventually (eventually_lt_nhds hθ),
      (Real.tendsto_log_atTop.comp hn).eventually (eventually_gt_atTop (0:ℝ))] with j hj hjlt hjη hjlog
    have ha0 : 0 ≤ a j := by
      have hr : 1 ≤ (θ+η j)/(θ-η j) := (one_le_div (sub_pos.mpr hjη)).mpr (by linarith [hη0 j])
      dsimp [a]
      positivity
    have hb0 : 0 ≤ b j := by
      have hr : (θ-η j)/(θ+η j/8) ≤ 1 := (div_le_one (by linarith [hη0 j] : 0<θ+η j/8)).mpr (by linarith [hη0 j])
      have hr0 : 0 ≤ 2-2*((θ-η j)/(θ+η j/8)) := by linarith
      dsimp [b]
      positivity
    have he0 : 0 ≤ e j := by dsimp [e]; positivity
    have hden : 0 < U j+A j+1 := by linarith [hU j,hA j]
    have hupper : D j ≤ (a j+b j+e j)*(U j+A j+1) := by
      have hj' : D j ≤ a j*U j+b j*A j+e j := by
        simpa only [a,b,e,add_assoc] using hj
      nlinarith only [hj',hU j,hA j,ha0,hb0,he0,mul_nonneg ha0 (hA j),mul_nonneg hb0 (hU j),mul_nonneg he0 (hU j),mul_nonneg he0 (hA j)]
    exact (div_le_iff₀ hden).mpr hupper |>.trans_lt hjlt
end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology
open Global
variable (V : ℕ → Type u1) (I : ℕ → Type u2) (K : ℕ → Type u3) [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

/-- Application of the scalar rate to the genuinely prepared arithmetic graphs,
with no degree bound on the sequence of number fields. -/
theorem arithmetic_small_overlap_rate (hθ : 0<θ)
    (hn : Tendsto (fun j => (Fintype.card (V j) : ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j)
    (ht : ∀ j e y, y ∈ (G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    Tendsto (fun j => smallOverlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) c /
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1))
      atTop (𝓝 0) := by
  apply small_overlap_rate (fun j => (Fintype.card (V j):ℝ)) η _ _ _ θ hθ hn hη hη0
    (fun j => overlapScale_nonneg _ _ _ _) (fun j => potentialScale_nonneg _ _ _ _)
    (fun j => smallOverlapScale_nonneg _ _ _ _ c)
  intro τ H hτ hτ1 hH
  filter_upwards [hη.eventually (eventually_lt_nhds hθ),
    (Real.tendsto_log_atTop.comp hn).eventually (eventually_ge_atTop (2:ℝ)),
    hn.eventually (eventually_ge_atTop (2/τ))] with j hjη hjlog hjn
  have hlog : 0 ≤ 1/Real.log (Fintype.card (V j):ℝ) := by positivity
  have hlog2 : 1/Real.log (Fintype.card (V j):ℝ) ≤ 1/2 := by
    exact one_div_le_one_div_of_le (by norm_num) hjlog
  have hτn : 2≤τ*(Fintype.card (V j):ℝ) := by
    have := (div_le_iff₀ hτ).mp hjn
    nlinarith
  exact (hG j).arithmetic_small_overlap (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) hjη (hη0 j)
    (t j) (ht j) τ H hlog hlog2 hτ hτ1 hτn hH

end WeakPinned

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

omit [Fintype I] in
lemma retained_domination (T M : ℝ) (hdom : ∀ x y, G.edgeLaw x y≤M*pairProb Finset.univ x y)
    (hn : 2≤Fintype.card V) (x : V) :
    (∑ y, G.retainedWeight T y*prob (G.retainedSet T y) x)≤M*prob Finset.univ x := by
  refine le_trans (Finset.sum_le_sum (fun y _ => ?_)) (G.incoming_domination M hdom hn x)
  unfold retainedWeight retainedSet
  split_ifs
  · exact le_rfl
  · simp only [zero_mul]
    unfold incomingWeight edgeCount prob
    split_ifs <;> positivity
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

/-- Both source sampling families satisfy the proved vanishing arithmetic
variance estimate, on every sequence of prepared models. No uniform degree
bound on the number fields is used. -/
theorem sampling_variance_rates_oai (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y ∈ (G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    Tendsto (fun j => fiberVariance G c Z₁ Z₂ h₁ h₂ j /
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) ∧
    Tendsto (fun j => incomingVariance G γ c Z₁ Z₂ h₁ h₂ j /
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) := by
  have hsmall := arithmetic_small_overlap_rate V I K G θ γ c η Z₁ Z₂ h₁ h₂ hθ hn hη hη0 hG t ht
  have hηlt (j) : η j<θ := by linarith [hηb j]
  have hpos (j) : 0<(G j).edgeCount := (hG j).edgeCount_pos (hηlt j)
  have hdom (j x y) := (hG j).uniform_domination hθ (hηb j) x y
  constructor
  · exact arithmetic_variance_rate Z₁ Z₂ h₁ h₂ (fun j => (G j).fiberWeight) (fun j => (G j).targets)
      γ c (2/θ) hγ hγ1 hcγ (hcγ.trans hγ1) (by positivity) hn
      (fun j => (G j).fiberWeight_nonneg) (fun j => (G j).sum_fiberWeight (hpos j) |>.le)
      (Eventually.of_forall fun j e => (hG j).fiber e |>.le)
      (Eventually.of_forall fun j x => (G j).fiber_domination _ (hdom j) (hG j).card_ge x) hsmall
  · apply arithmetic_variance_rate Z₁ Z₂ h₁ h₂
      (fun j => (G j).retainedWeight ((Fintype.card (V j):ℝ)^γ))
      (fun j => (G j).retainedSet ((Fintype.card (V j):ℝ)^γ)) γ c (2/θ)
      hγ hγ1 hcγ (hcγ.trans hγ1) (by positivity) hn
      (fun j y => (G j).retainedWeight_nonneg _ y)
      (fun j => (G j).sum_retainedWeight _ (hpos j)) _ _ hsmall
    · apply Eventually.of_forall
      intro j y
      apply (G j).retainedSet_size
      have hn1 : (1:ℝ)≤Fintype.card (V j) := by exact_mod_cast (by have := (hG j).card_ge; omega : 1≤Fintype.card (V j))
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hγ1.le
    · exact Eventually.of_forall fun j x => (G j).retained_domination _ _ (hdom j) (hG j).card_ge x

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

theorem solution.{u6, u7, u8} : type_of% @OAI.WeakPinned.sampling_variance_rates_oai.{u6, u7, u8} := @OAI.WeakPinned.sampling_variance_rates_oai.{u6, u7, u8}
