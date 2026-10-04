-- Prove2me | solution 1 for RelativeZimmer.isAmenableRel_orbit_of_isCoamenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:28:25.112996+00:00
-- url     : https://prove2.me/submissions/8897a700-c2fe-45fa-a709-2086f82419c9

import Definitions.Def_ThompsonAmenability
import Definitions.Def_CannonFloydParry
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_Garrido_Amenability
import Mathlib


section
section
section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-!
# Blueprint: Monod 2023, Theorem 5.1

`H_ℚ(ℤ)` (`Monod.HRat`) is not co-amenable in `H_ℚ(ℚ)` (`HB ratSubring Monod.ratPoints`) nor in
`H^{C¹}_ℚ(ℚ)` (`HC1RatRat`).

Route (Monod 2023, Theorem 4.6, "the same statement holds with Γ∅ replaced throughout by
Thompson's group", and Proposition 4.7):
* Part A — the containments `HRat ≤ HC1RatRat ≤ HB ratSubring ratPoints`.
* Part B — every element of `HB ratSubring ratPoints` agrees with a Möbius map of `SL₂(ℚ)` at each
  irrational point and preserves Lebesgue-null sets.
* Part C — cut-and-paste: one explicit element of `HRat` realises `x ↦ -1/x` on `(1, 2)`; with the
  rational affine maps (in `HC1RatRat`) it realises every `g ∈ SL₂(ℚ)` at every irrational point.
* Part D — relative Zimmer (Monod 2023, Proposition 4.7), for means: if `Γ ≤ Λ` is co-amenable and
  the `Γ`-orbit relation is amenable, then so is any relation `R` that agrees with the `Λ`-orbit
  relation on a conull saturated set.
* Part E — the orbit relation of `HRat` on `P¹` is amenable: via the published conjugacy of `HRat`
  with Thompson's `F` on `(0,1)`, it is the orbit relation of the amenable dyadic affine group.
* Assembly — co-amenability would make the `SL₂(ℚ)` orbit relation amenable, contradicting
  `Monod.not_isAmenableRel_mob` (Carrière–Ghys, the dense subring `ℚ`).
-/
/-- Homeomorphisms of `P¹`. -/
abbrev Hom := OnePoint ℝ ≃ₜ OnePoint ℝ

/-- Homeomorphisms of `P¹` act on `P¹` by evaluation. -/
instance instMulActionHom : MulAction Hom (OnePoint ℝ) where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- `SL₂(ℚ)`, with `ℚ` as the subring `ratSubring` of `ℝ`. -/
abbrev SLQ := Matrix.SpecialLinearGroup (Fin 2) ratSubring

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-!
# Monod 2023, Theorem 5.1 — Part A (and Part E3)

* The containments `HRat ≤ HC1RatRat ≤ HB ratSubring ratPoints`, and `HRat ≤ HB ratSubring ratPoints`.
* `ratSubring` is countable and dense; `volP1` is σ-finite.
* Part E3: amenability of a measured relation passes to a relation that agrees with it on a
  conull set saturated for the new relation.
-/
/-! ## Containments -/

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part A: containments and the subring `ℚ` -/

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-! ## The subring `ℚ` -/

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
variable {A : Subring ℝ}
/-!
# Monod 2023, Theorem 5.1 — Part B: elements of `H_ℚ(ℚ)` at irrational points

* `X0ᶜ = {∞} ∪ ℚ` is countable, hence measurable and `volP1`-null.
* A Möbius map with rational entries preserves the irrational points (and so does its inverse).
* Every generator of `H_ℚ(ℚ)` agrees at every point of `P¹` with a Möbius map of `SL₂(ℚ)`: off the
  breakpoints by definition, and at a breakpoint by the identity theorem on an adjacent interval
  free of breakpoints together with continuity. Closure induction then gives
  `exists_mob_of_mem_HB`.
* Möbius maps are smooth off their pole, so they pull null sets back to null sets; an element of
  `H_ℚ(ℚ)` pulls a null set back into `X0ᶜ` union countably many Möbius preimages.

The basic Möbius facts (formulas, group law, continuity, identity theorem) are adapted from
`Solutions/Monod/DynBasic.lean`, `DynGerm.lean`, `RedMob.lean` and `RedNull.lean`.
-/
/-! ### Möbius maps: formulas, group law, continuity -/

/-! ### Identity theorem -/

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-! ### The subring `ℚ` and `SL₂(ℚ)` are countable -/
instance countable_ratSubring' : Countable ratSubring := by
  have hs : Function.Surjective (fun q : ℚ => (⟨(q : ℝ), RingHom.mem_range_self _ q⟩ : ratSubring)) := by
    rintro ⟨x, hx⟩
    obtain ⟨q, rfl⟩ := RingHom.mem_range.1 hx
    exact ⟨q, rfl⟩
  exact hs.countable

instance countable_SLQ : Countable SLQ :=
  inferInstanceAs (Countable {M : Fin 2 → Fin 2 → ratSubring // Matrix.det M = 1})

/-! ### The irrational points -/

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part B: elements of `H_ℚ(ℚ)` at irrational points -/

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-! ### Elements of `H_ℚ(ℚ)` at irrational points -/

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-! ### Null sets -/

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open Filter Topology Set OnePoint
namespace ThompsonAmenability.M51.PartC
variable {A : Subring ℝ}
/-!
# Part C: cut-and-paste

One explicit element `hS` of `H_ℚ(ℤ)` realises `y ↦ -1/y` on `(1, 2]`: it is the order
automorphism `psi` of `ℝ` (pieces `y - 2`, `-1/y`, `(y - 3)/(4 - y)`, `y - 3`, breakpoints `1, 2, 3`,
all in `SL₂(ℤ)`), extended to `P¹` fixing `∞`. With the rational affine maps
`aff a b : t ↦ a² t + a b` (Möbius maps of `!![a, b; 0, a⁻¹] ∈ SL₂(ℚ)`, in `H^{C¹}_ℚ(ℚ)`) it realises
`y ↦ -1/y` at every `y ≠ 0`, and then every `g ∈ SL₂(ℚ)` at every irrational point:
`g = τ_{a/c} ∘ S ∘ A_{c,d}` when `c ≠ 0`, `g = A_{a,b}` when `c = 0`.
-/
/-! ### Möbius maps: entries and formulas -/

/-! ### Order automorphisms of `ℝ`, extended to `P¹` -/

/-! ### The element `hS` -/

/-! ### The rational affine maps -/

/-! ### The countable subgroup `CC` -/

/-! ### Realising `y ↦ -1/y` -/

/-! ### Every `g ∈ SL₂(ℚ)` at every irrational point -/

end ThompsonAmenability.M51.PartC
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part C: cut-and-paste -/

end ThompsonAmenability.M51
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {X : Type*} (m : Set X → ℝ≥0∞)
/-!
# Part D: relative Zimmer (Monod 2023, Proposition 4.7), for means

If `Γ ≤ Λ` is co-amenable and the `Γ`-orbit relation is amenable, then any relation `R` agreeing
with the `Λ`-orbit relation on a conull saturated set (realised there by a countable set `C`) is
amenable.

Route.  After replacing `μ` by an equivalent finite measure:
* the invariant finitely additive probability on `Q = Λ ⧸ Γ` gives a mean `Mn` on bounded
  functions on `Q` (the upper Darboux integral, as in `MEAN_Bridge.lean`);
* for `λ ∈ Λ` and `g` bounded on `R` over `X₀`, `Fl λ g := P_Γ (g_λ) ∘ λ⁻¹`, where
  `g_λ (w, z) = g (λ w, z)` for `λ w ∈ X₀` (and `0` otherwise); up to null sets it depends only on
  the coset `λ Γ`;
* `P g ∈ L²(μ)` is the Riesz representative of `h ↦ Mn (q ↦ ⟪Fl (rep q) g, h⟫)`;
* the axioms follow from those of `P_Γ`; translation invariance `P (g ∘ κ⁻¹) = (P g) ∘ κ⁻¹`
  from the invariance of `Mn` under `Λ`; invariance under an arbitrary partial transformation
  `φ` from translation invariance and locality, on the countably many measurable pieces
  `{y | P g (φ⁻¹ y) = P g (κ⁻¹ y), g (φ⁻¹ y, c y) = g (κ⁻¹ y, c y) ∀ c ∈ C}`, `κ ∈ C`.
-/
/-! ## The mean on a set with a finitely additive probability (after `MEAN_Bridge.lean`) -/
/-- Finite additivity over the fibres of a map. -/
theorem mean_fam_fiber (hm : IsFinitelyAdditiveMeasure m) {α : Type*} [DecidableEq α]
    (π : X → α) (T : Finset α) :
    m (π ⁻¹' (T : Set α)) = ∑ a ∈ T, m (π ⁻¹' {a}) := by
  induction T using Finset.induction_on with
  | empty => simp [hm.1]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.coe_insert, Set.insert_eq, Set.preimage_union]
    apply hm.2
    exact Disjoint.preimage π (Set.disjoint_singleton_left.2 (by simpa using ha))

theorem mean_mono (hm : IsFinitelyAdditiveMeasure m) {s t : Set X} (h : s ⊆ t) : m s ≤ m t := by
  have : t = s ∪ (t \ s) := (Set.union_sdiff_cancel h).symm
  rw [this, hm.2 _ _ Set.disjoint_sdiff_right]
  exact le_self_add

theorem mean_ne_top (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : Set X) :
    m s ≠ ∞ :=
  ne_top_of_le_ne_top (by rw [h1]; exact ENNReal.one_ne_top) (mean_mono m hm (subset_univ s))

/-- The integral of a finitely valued function. -/
noncomputable def meanI (s : X → ℝ) : ℝ := ∑ᶠ v : ℝ, v * (m (s ⁻¹' {v})).toReal

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {X : Type*} (m : Set X → ℝ≥0∞)
variable {m}
theorem meanI_factor (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    {α : Type*} [DecidableEq α] (π : X → α) (T : Finset α) (hT : ∀ x, π x ∈ T) (ψ : α → ℝ) :
    meanI m (ψ ∘ π) = ∑ a ∈ T, ψ a * (m (π ⁻¹' {a})).toReal := by
  classical
  rw [meanI, finsum_eq_sum_of_support_subset _ (s := T.image ψ) ?_]
  · have e : ∀ v, (ψ ∘ π) ⁻¹' {v} = π ⁻¹' ((T.filter (fun a => ψ a = v) : Finset α) : Set α) := by
      intro v; ext x; simp [hT x]
    simp_rw [e, mean_fam_fiber m hm, ENNReal.toReal_sum (fun a _ => mean_ne_top m hm h1 _),
      Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (g := ψ) (t := T.image ψ)
      (fun a ha => Finset.mem_image_of_mem ψ ha)]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  · intro v hv
    rw [Function.mem_support] at hv
    by_contra h
    apply hv
    have : (ψ ∘ π) ⁻¹' {v} = ∅ := by
      ext x
      simp only [mem_preimage, Function.comp_apply, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      intro hx
      exact h (by simpa using ⟨π x, hT x, hx⟩)
    simp [this, hm.1]

theorem meanI_eq_sum (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    (s : X → ℝ) (T : Finset ℝ) (hT : ∀ x, s x ∈ T) :
    meanI m s = ∑ v ∈ T, v * (m (s ⁻¹' {v})).toReal :=
  meanI_factor hm h1 s T hT id

theorem mean_range_pair {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => (s x, t x)).Finite :=
  (hs.prod ht).subset (by rintro _ ⟨x, rfl⟩; exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩)

theorem mean_range_map {s : X → ℝ} (hs : (range s).Finite) (φ : ℝ → ℝ) :
    (range fun x => φ (s x)).Finite :=
  (hs.image φ).subset (by rintro _ ⟨x, rfl⟩; exact ⟨s x, ⟨x, rfl⟩, rfl⟩)

theorem mean_range_add {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => s x + t x).Finite :=
  ((mean_range_pair hs ht).image (fun p => p.1 + p.2)).subset
    (by rintro _ ⟨x, rfl⟩; exact ⟨(s x, t x), ⟨x, rfl⟩, rfl⟩)

theorem mean_range_const (c : ℝ) : (range fun _ : X => c).Finite :=
  (Set.finite_singleton c).subset Set.range_const_subset

theorem meanI_add (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) :
    meanI m (fun x => s x + t x) = meanI m s + meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hT : ∀ x, π x ∈ hs.toFinset ×ˢ ht.toFinset := fun x => by simp [π]
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  have e3 := meanI_factor hm h1 π _ hT (fun p => p.1 + p.2)
  simp only [Function.comp_def, π] at e1 e2 e3
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => add_mul _ _ _

theorem meanI_map (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s : X → ℝ}
    (hs : (range s).Finite) (c : ℝ) : meanI m (fun x => c * s x) = c * meanI m s := by
  classical
  have hT : ∀ x, s x ∈ hs.toFinset := fun x => by simp
  have e1 := meanI_factor hm h1 s _ hT (fun v => c * v)
  have e2 := meanI_eq_sum hm h1 s _ hT
  simp only [Function.comp_def] at e1
  rw [e1, e2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

theorem meanI_const (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (c : ℝ) :
    meanI m (fun _ : X => c) = c := by
  have e := meanI_factor hm h1 (fun _ : X => ()) Finset.univ (fun _ => Finset.mem_univ _)
    (fun _ => c)
  simp only [Function.comp_def] at e
  rw [e]
  simp [h1]

theorem meanI_mono (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) (hst : ∀ x, s x ≤ t x) :
    meanI m s ≤ meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hπ := mean_range_pair hs ht
  have hT : ∀ x, π x ∈ hπ.toFinset := fun x => (Set.Finite.mem_toFinset hπ).2 ⟨x, rfl⟩
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  simp only [Function.comp_def, π] at e1 e2
  rw [e1, e2]
  refine Finset.sum_le_sum fun a ha => ?_
  obtain ⟨x, rfl⟩ := (Set.Finite.mem_toFinset hπ).1 ha
  exact mul_le_mul_of_nonneg_right (hst x) ENNReal.toReal_nonneg

theorem meanI_smul_inv' {H Y : Type*} [Group H] [MulAction H Y] {m : Set Y → ℝ≥0∞}
    (hinv : IsInvariant H m) (s : Y → ℝ) (g : H) :
    meanI m (fun x => s (g⁻¹ • x)) = meanI m s := by
  unfold meanI
  congr 1
  funext v
  have : (fun x => s (g⁻¹ • x)) ⁻¹' {v} = g • (s ⁻¹' {v}) := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    rfl
  rw [this, hinv]

/-! ### The upper integral on `ℓ∞` -/
local notation "E" X => lp (fun _ : X => ℝ) ∞

variable (m) in
/-- Upper Darboux integral of a bounded function. -/
noncomputable def meanP (f : E X) : ℝ :=
  sInf {r | ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧ meanI m s = r}

theorem mean_abs_le (f : E X) (x : X) : |(f : X → ℝ) x| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero f x
  simpa [Real.norm_eq_abs] using this

theorem meanP_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {f : E X} {s : X → ℝ}
    (hs : (range s).Finite) (hfs : ∀ x, (f : X → ℝ) x ≤ s x) : meanP m f ≤ meanI m s := by
  refine csInf_le ⟨-‖f‖, ?_⟩ ⟨s, hs, hfs, rfl⟩
  rintro _ ⟨t, ht, hft, rfl⟩
  rw [← meanI_const hm h1 (-‖f‖)]
  exact meanI_mono hm h1 (mean_range_const _) ht
    (fun x => le_trans (neg_le_of_abs_le (mean_abs_le f x)) (hft x))

theorem le_meanP {f : E X} {r : ℝ}
    (h : ∀ s : X → ℝ, (range s).Finite → (∀ x, (f : X → ℝ) x ≤ s x) → r ≤ meanI m s) :
    r ≤ meanP m f := by
  refine le_csInf ⟨_, fun _ => ‖f‖, mean_range_const _,
    fun x => le_trans (le_abs_self _) (mean_abs_le f x), rfl⟩ ?_
  rintro _ ⟨s, hs, hfs, rfl⟩
  exact h s hs hfs

/-- Approximation from above by a finitely valued function, within `ε`. -/
theorem mean_approx (f : E X) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧
      ∀ x, s x ≤ (f : X → ℝ) x + ε := by
  refine ⟨fun x => ε * ⌈(f : X → ℝ) x / ε⌉, ?_, fun x => ?_, fun x => ?_⟩
  · refine ((Set.finite_Icc ⌈-‖f‖ / ε⌉ ⌈‖f‖ / ε⌉).image (fun k : ℤ => ε * k)).subset ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨_, ⟨Int.ceil_mono ?_, Int.ceil_mono ?_⟩, rfl⟩
    · exact div_le_div_of_nonneg_right (neg_le_of_abs_le (mean_abs_le f x)) hε.le
    · exact div_le_div_of_nonneg_right (le_trans (le_abs_self _) (mean_abs_le f x)) hε.le
  · have := Int.le_ceil ((f : X → ℝ) x / ε)
    calc (f : X → ℝ) x = ε * ((f : X → ℝ) x / ε) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hε.le
  · have := Int.ceil_lt_add_one ((f : X → ℝ) x / ε)
    calc ε * (⌈(f : X → ℝ) x / ε⌉ : ℝ) ≤ ε * ((f : X → ℝ) x / ε + 1) :=
          mul_le_mul_of_nonneg_left this.le hε.le
      _ = (f : X → ℝ) x + ε := by field_simp

/-- A finitely valued function as an element of `ℓ∞`. -/
noncomputable def meanOfFin (s : X → ℝ) (hs : (range s).Finite) : E X :=
  ⟨s, memℓp_infty_iff.2 (by
    have : (range fun i => ‖s i‖) = (fun v => ‖v‖) '' range s := by
      rw [← Set.range_comp]; rfl
    rw [this]
    exact (hs.image _).bddAbove)⟩

@[simp] theorem meanOfFin_apply (s : X → ℝ) (hs : (range s).Finite) (x : X) :
    (meanOfFin s hs : X → ℝ) x = s x := rfl

theorem meanP_ofFin (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : X → ℝ)
    (hs : (range s).Finite) : meanP m (meanOfFin s hs) = meanI m s :=
  le_antisymm (meanP_le hm h1 hs fun _ => le_rfl)
    (le_meanP fun t ht hst => meanI_mono (t := t) hm h1 hs ht hst)

theorem meanP_smul_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) ≤ c * meanP m f := by
  have : meanP m (c • f) / c ≤ meanP m f := by
    refine le_meanP fun s hs hfs => ?_
    rw [div_le_iff₀ hc]
    calc meanP m (c • f) ≤ meanI m (fun x => c * s x) :=
          meanP_le hm h1 (mean_range_map hs _) (fun x => by
            simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
            exact mul_le_mul_of_nonneg_left (hfs x) hc.le)
      _ = meanI m s * c := by rw [meanI_map hm h1 hs, mul_comm]
  rwa [div_le_iff₀ hc, mul_comm] at this

theorem meanP_smul (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) = c * meanP m f := by
  refine le_antisymm (meanP_smul_le hm h1 hc f) ?_
  have := meanP_smul_le hm h1 (inv_pos.2 hc) (c • f)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  calc c * meanP m f ≤ c * (c⁻¹ * meanP m (c • f)) := mul_le_mul_of_nonneg_left this hc.le
    _ = _ := by field_simp

theorem meanP_add_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f g : E X) :
    meanP m (f + g) ≤ meanP m f + meanP m g := by
  have h2 : meanP m (f + g) - meanP m f ≤ meanP m g := by
    refine le_meanP fun t ht hgt => ?_
    have : meanP m (f + g) - meanI m t ≤ meanP m f := by
      refine le_meanP fun s hs hfs => ?_
      have := meanP_le hm h1 (f := f + g) (mean_range_add hs ht)
        (fun x => by simp only [lp.coeFn_add, Pi.add_apply]; exact add_le_add (hfs x) (hgt x))
      rw [meanI_add hm h1 hs ht] at this
      linarith
    linarith
  linarith

theorem meanP_zero (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    meanP m (0 : E X) = 0 := by
  refine le_antisymm ?_ ?_
  · calc meanP m (0 : E X) ≤ meanI m (fun _ => 0) :=
          meanP_le hm h1 (mean_range_const _) (fun x => by simp)
      _ = 0 := meanI_const hm h1 0
  · refine le_meanP fun s hs hfs => ?_
    rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
    exact meanI_mono hm h1 (mean_range_const _) hs (fun x => by simpa using hfs x)

/-- The upper integral is linear (Hahn–Banach plus uniform approximation). -/
theorem mean_exists_linear (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    ∃ L : (E X) →ₗ[ℝ] ℝ, ∀ f, L f = meanP m f := by
  obtain ⟨L, -, hL⟩ := exists_extension_of_le_sublinear
    ({ domain := ⊥, toFun := 0 } : (E X) →ₗ.[ℝ] ℝ) (meanP m)
    (fun c hc f => meanP_smul hm h1 hc f) (meanP_add_le hm h1)
    (fun x => by
      have hx : (x : E X) = 0 := (Submodule.mem_bot ℝ).1 x.2
      simp [hx, meanP_zero hm h1])
  refine ⟨L, fun f => le_antisymm (hL f) ?_⟩
  -- `L` agrees with `meanI` on finitely valued functions.
  have hLs : ∀ s hs, L (meanOfFin s hs) = meanI m s := by
    intro s hs
    refine le_antisymm ((hL _).trans (meanP_ofFin hm h1 s hs).le) ?_
    have hns := mean_range_map hs (fun v => -1 * v)
    have e : -(meanOfFin s hs) = meanOfFin (fun x => -1 * s x) hns := by
      ext x; simp
    have := hL (-(meanOfFin s hs))
    rw [map_neg, e, meanP_ofFin hm h1 _ hns, meanI_map hm h1 hs] at this
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨s, hs, hfs, hsf⟩ := mean_approx f hε
  have hs' := mean_range_map hs (fun v => v + -ε)
  have h3 : meanI m (fun x => s x + -ε) = meanI m s - ε := by
    rw [meanI_add hm h1 hs (mean_range_const _), meanI_const hm h1]; ring
  have h4 : L (meanOfFin _ hs') ≤ L f := by
    have := hL (meanOfFin _ hs' - f)
    have h0 : meanP m (meanOfFin _ hs' - f) ≤ 0 := by
      calc meanP m (meanOfFin _ hs' - f) ≤ meanI m (fun _ => 0) :=
            meanP_le hm h1 (mean_range_const _) (fun x => by
              simp only [lp.coeFn_sub, Pi.sub_apply, meanOfFin_apply]; linarith [hsf x])
        _ = 0 := meanI_const hm h1 0
    rw [map_sub] at this
    linarith
  rw [hLs] at h4
  calc meanP m f ≤ meanI m s := meanP_le hm h1 hs hfs
    _ ≤ L f + ε := by linarith

/-- **The integral** `∫ · dm` of a bounded function against a finitely additive probability
measure. -/
noncomputable def mean_integral (m : Set X → ℝ≥0∞) (hm : IsFinitelyAdditiveMeasure m)
    (h1 : m univ = 1) : (E X) →ₗ[ℝ] ℝ where
  toFun := meanP m
  map_add' f g := by
    obtain ⟨L, hL⟩ := mean_exists_linear hm h1
    rw [← hL, ← hL, ← hL, map_add]
  map_smul' c f := by
    obtain ⟨L, hL⟩ := mean_exists_linear hm h1
    rw [← hL, ← hL, map_smul]; rfl

theorem mean_integral_apply (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X) :
    mean_integral m hm h1 f = meanP m f := rfl

theorem mean_integral_nonneg (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (hf : ∀ x, 0 ≤ (f : X → ℝ) x) : 0 ≤ mean_integral m hm h1 f := by
  refine le_meanP fun s hs hfs => ?_
  rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
  exact meanI_mono hm h1 (mean_range_const _) hs (fun x => (hf x).trans (hfs x))

theorem mean_integral_eq_const (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (c : ℝ) (hf : ∀ x, (f : X → ℝ) x = c) : mean_integral m hm h1 f = c := by
  have : f = meanOfFin (fun _ => c) (mean_range_const c) := by ext x; simp [hf]
  rw [this, mean_integral_apply, meanP_ofFin hm h1, meanI_const hm h1]

theorem mean_range_indicator (A : Set X) : (range (A.indicator (1 : X → ℝ))).Finite :=
  (Set.toFinite ({0, 1} : Set ℝ)).subset (by
    rintro _ ⟨x, rfl⟩; by_cases h : x ∈ A <;> simp [h])

/-- The indicator function of `A` as an element of `ℓ∞`. -/
noncomputable def mean_ind (A : Set X) : E X := meanOfFin _ (mean_range_indicator A)

@[simp] theorem mean_ind_apply (A : Set X) (x : X) :
    (mean_ind A : X → ℝ) x = A.indicator 1 x := rfl

theorem mean_integral_abs_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X) :
    |mean_integral m hm h1 f| ≤ ‖f‖ := by
  rw [mean_integral_apply, abs_le]
  constructor
  · refine le_meanP fun s hs hfs => ?_
    rw [← meanI_const hm h1 (-‖f‖) (X := X)]
    exact meanI_mono hm h1 (mean_range_const _) hs
      (fun x => (neg_le_of_abs_le (mean_abs_le f x)).trans (hfs x))
  · exact (meanP_le hm h1 (mean_range_const ‖f‖) (fun x => (le_abs_self _).trans
      (mean_abs_le f x))).trans (meanI_const hm h1 _).le

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {Q : Type*} (m : Set Q → ℝ≥0∞)
/-! ### The mean as a function on bounded functions -/
/-- A bounded function as an element of `ℓ∞`. -/
noncomputable def toLinf (a : Q → ℝ) (B : ℝ) (ha : ∀ q, |a q| ≤ B) :
    lp (fun _ : Q => ℝ) ∞ :=
  ⟨a, memℓp_infty_iff.2 ⟨B, by rintro _ ⟨q, rfl⟩; simpa [Real.norm_eq_abs] using ha q⟩⟩

/-- The mean of a function on `Q` (junk `0` if unbounded). -/
noncomputable def Mn (a : Q → ℝ) : ℝ :=
  open Classical in
  if h : BddAbove (Set.range fun q => ‖a q‖) then meanP m ⟨a, memℓp_infty_iff.2 h⟩ else 0

lemma Mn_eq {a : Q → ℝ} {B : ℝ} (ha : ∀ q, |a q| ≤ B) : Mn m a = meanP m (toLinf a B ha) := by
  have h : BddAbove (Set.range fun q => ‖a q‖) :=
    ⟨B, by rintro _ ⟨q, rfl⟩; simpa [Real.norm_eq_abs] using ha q⟩
  simp only [Mn, dif_pos h]
  rfl

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {Q : Type*} (m : Set Q → ℝ≥0∞)
variable {m} (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
include hm h1
lemma Mn_add {a b : Q → ℝ} {A B : ℝ} (ha : ∀ q, |a q| ≤ A) (hb : ∀ q, |b q| ≤ B) :
    Mn m (fun q => a q + b q) = Mn m a + Mn m b := by
  have hab : ∀ q, |a q + b q| ≤ A + B := fun q =>
    (abs_add_le _ _).trans (add_le_add (ha q) (hb q))
  rw [Mn_eq m hab, Mn_eq m ha, Mn_eq m hb, ← mean_integral_apply hm h1,
    ← mean_integral_apply hm h1, ← mean_integral_apply hm h1, ← map_add]
  rfl

lemma Mn_smul (c : ℝ) {a : Q → ℝ} {A : ℝ} (ha : ∀ q, |a q| ≤ A) :
    Mn m (fun q => c * a q) = c * Mn m a := by
  have hca : ∀ q, |c * a q| ≤ |c| * A := fun q => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ha q) (abs_nonneg c)
  have e : toLinf (fun q => c * a q) _ hca = c • toLinf a A ha := by ext; rfl
  rw [Mn_eq m hca, Mn_eq m ha, ← mean_integral_apply hm h1, ← mean_integral_apply hm h1, e,
    map_smul, smul_eq_mul]

lemma Mn_nonneg {a : Q → ℝ} {A : ℝ} (ha : ∀ q, |a q| ≤ A) (h0 : ∀ q, 0 ≤ a q) :
    0 ≤ Mn m a := by
  rw [Mn_eq m ha, ← mean_integral_apply hm h1]
  exact mean_integral_nonneg hm h1 _ h0

lemma Mn_const (c : ℝ) : Mn m (fun _ : Q => c) = c := by
  rw [Mn_eq m (B := |c|) (fun _ => le_rfl), ← mean_integral_apply hm h1]
  exact mean_integral_eq_const hm h1 _ c (fun _ => rfl)

lemma Mn_abs_le {a : Q → ℝ} {A : ℝ} (ha : ∀ q, |a q| ≤ A) : |Mn m a| ≤ A := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · exfalso
    have : (Set.univ : Set Q) = ∅ := Set.univ_eq_empty_iff.2 hQ
    rw [this, hm.1] at h1
    exact zero_ne_one h1
  obtain ⟨q⟩ := hQ
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha q)
  rw [Mn_eq m ha, ← mean_integral_apply hm h1]
  refine (mean_integral_abs_le hm h1 _).trans (lp.norm_le_of_forall_le hA fun q => ?_)
  rw [Real.norm_eq_abs]
  exact ha q

lemma Mn_sub_le {a b : Q → ℝ} {B ε : ℝ} (hb : ∀ q, |b q| ≤ B)
    (hab : ∀ q, |a q - b q| ≤ ε) : |Mn m a - Mn m b| ≤ ε := by
  have e : Mn m a = Mn m (fun q => (a q - b q) + b q) + 0 := by simp
  rw [e, Mn_add hm h1 hab hb]
  simpa using Mn_abs_le hm h1 hab

lemma meanP_comp_le {H : Type*} [Group H] [MulAction H Q] (hinv : IsInvariant H m) (g : H)
    {a : Q → ℝ} {B : ℝ} (ha : ∀ q, |a q| ≤ B) (ha' : ∀ q, |a (g⁻¹ • q)| ≤ B) :
    meanP m (toLinf (fun q => a (g⁻¹ • q)) B ha') ≤ meanP m (toLinf a B ha) := by
  refine le_meanP fun s hs hfs => ?_
  rw [← meanI_smul_inv' hinv s g]
  exact meanP_le hm h1 ((hs.image id).subset (by rintro _ ⟨x, rfl⟩; exact ⟨_, ⟨_, rfl⟩, rfl⟩))
    (fun x => hfs _)

lemma Mn_inv {H : Type*} [Group H] [MulAction H Q] (hinv : IsInvariant H m) (g : H)
    {a : Q → ℝ} {B : ℝ} (ha : ∀ q, |a q| ≤ B) :
    Mn m (fun q => a (g⁻¹ • q)) = Mn m a := by
  have ha' : ∀ q, |a (g⁻¹ • q)| ≤ B := fun q => ha _
  rw [Mn_eq m ha', Mn_eq m ha]
  refine le_antisymm (meanP_comp_le hm h1 hinv g ha ha') ?_
  have := meanP_comp_le hm h1 hinv g⁻¹ ha' (fun q => ha' _)
  have e : toLinf (fun q => a (g⁻¹ • g⁻¹⁻¹ • q)) B (fun q => ha' _) = toLinf a B ha := by
    ext q
    show a (g⁻¹ • g⁻¹⁻¹ • q) = a q
    simp
  rw [e] at this
  exact this

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
open Monod
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
/-! ## Generic facts about left invariant means -/
lemma isBddMeasOn_add' {R : Set (X × X)} {f g : X × X → ℝ} (hf : IsBddMeasOn R f)
    (hg : IsBddMeasOn R g) : IsBddMeasOn R (f + g) := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := hg.2
  exact ⟨hf.1.add hg.1, C + D, fun p hp => (abs_add_le _ _).trans (add_le_add (hC p hp) (hD p hp))⟩

lemma isBddMeasOn_smul' {R : Set (X × X)} (c : ℝ) {f : X × X → ℝ} (hf : IsBddMeasOn R f) :
    IsBddMeasOn R (c • f) := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨hf.1.const_smul c, |c| * C, fun p hp => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg c)

lemma isBddMeasOn_const' {R : Set (X × X)} (c : ℝ) : IsBddMeasOn R (fun _ => c) :=
  ⟨measurable_const, |c|, fun _ _ => le_rfl⟩

lemma isBddMeasOn_one' {R : Set (X × X)} : IsBddMeasOn R (1 : X × X → ℝ) :=
  ⟨measurable_const, 1, fun _ _ => by simp⟩

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
open Monod
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {R : Set (X × X)} {P : (X × X → ℝ) → X → ℝ} (hP : IsLeftInvariantMean μ R P)
include hP
lemma lim_le_of_le {f g : X × X → ℝ} (hf : IsBddMeasOn R f) (hg : IsBddMeasOn R g)
    (hfg : ∀ p ∈ R, f p ≤ g p) : ∀ᵐ x ∂μ, P f x ≤ P g x := by
  have hb := isBddMeasOn_smul' (-1 : ℝ) hf
  have h := hP.nonneg (g + (-1 : ℝ) • f) (isBddMeasOn_add' hg hb) (fun p hp => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hfg p hp])
  filter_upwards [h, hP.add g ((-1 : ℝ) • f) hg hb, hP.smul (-1) f hf] with x h1 h2 h3
  rw [h2, Pi.add_apply, h3] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  linarith

lemma lim_const (c : ℝ) : P (fun _ => c) =ᵐ[μ] fun _ => c := by
  have e : (fun _ : X × X => c) = c • (1 : X × X → ℝ) := by funext; simp
  rw [e]
  filter_upwards [hP.smul c 1 isBddMeasOn_one', hP.one] with x h1 h2
  rw [h1, Pi.smul_apply, h2]
  simp

lemma lim_abs_le {f : X × X → ℝ} (hf : IsBddMeasOn R f) {C : ℝ} (hC : ∀ p ∈ R, |f p| ≤ C) :
    ∀ᵐ x ∂μ, |P f x| ≤ C := by
  have h1 := lim_le_of_le hP hf (isBddMeasOn_const' C) (fun p hp => (le_abs_self _).trans (hC p hp))
  have h2 := lim_le_of_le hP (isBddMeasOn_const' (-C)) hf (fun p hp => neg_le_of_abs_le (hC p hp))
  filter_upwards [h1, h2, lim_const hP C, lim_const hP (-C)] with x a b c e
  rw [c] at a
  rw [e] at b
  exact abs_le.2 ⟨b, a⟩

open Classical in
lemma lim_loc (hrefl : ∀ x, (x, x) ∈ R) {B : Set X} (hB : MeasurableSet B) {f : X × X → ℝ}
    (hf : IsBddMeasOn R f) :
    P (fun p => if p.1 ∈ B then f p else 0) =ᵐ[μ] fun y => if y ∈ B then P f y else 0 := by
  let φ : PartialTransformation R :=
    { dom := B, cod := B, measurableSet_dom := hB, measurableSet_cod := hB,
      e := MeasurableEquiv.refl B, graph_subset := fun a => hrefl a }
  have h1 : φ.shiftRel f = fun p => if p.1 ∈ B then f p else 0 := by
    funext p
    by_cases h : p.1 ∈ B <;> simp [PartialTransformation.shiftRel, h, φ]
  have h2 : φ.shiftBase (P f) = fun y => if y ∈ B then P f y else 0 := by
    funext y
    by_cases h : y ∈ B <;> simp [PartialTransformation.shiftBase, h, φ]
  rw [← h1, ← h2]
  exact hP.invariant φ f hf

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
/-- Transfer of a left invariant mean between measures with the same null sets. -/
lemma lim_of_ae_eq {X : Type*} [MeasurableSpace X] {μ ν : Measure X} (h : ae μ = ae ν)
    {R : Set (X × X)} {P : (X × X → ℝ) → X → ℝ} (hP : Monod.IsLeftInvariantMean μ R P) :
    Monod.IsLeftInvariantMean ν R P := by
  have h0 : ∀ s, μ s = 0 ↔ ν s = 0 := fun s => by
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem, h]
  refine
    { aemeasurable := fun f hf => ?_
      congr := fun f g hf hg hfg => ?_
      add := fun f g hf hg => ?_
      smul := fun c f hf => ?_
      nonneg := fun f hf hpos => ?_
      one := ?_
      invariant := fun φ f hf => ?_ }
  · obtain ⟨g, hg, he⟩ := hP.aemeasurable f hf
    exact ⟨g, hg, by rw [← h]; exact he⟩
  · have := hP.congr f g hf hg ((h0 _).2 hfg)
    rwa [h] at this
  · have := hP.add f g hf hg
    rwa [h] at this
  · have := hP.smul c f hf
    rwa [h] at this
  · have := hP.nonneg f hf hpos
    rwa [h] at this
  · have := hP.one
    rwa [h] at this
  · have := hP.invariant φ f hf
    rwa [h] at this

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
open Monod
variable {X : Type*} [MeasurableSpace X] {R : Set (X × X)} (φ : PartialTransformation R)
/-! ## Partial transformations -/
open Classical in
/-- `φ⁻¹` on the image of `φ`, extended by the identity. -/
noncomputable def psi (y : X) : X := if h : y ∈ φ.cod then (φ.e.symm ⟨y, h⟩ : X) else y

lemma psi_of_mem {y : X} (h : y ∈ φ.cod) : psi φ y = φ.e.symm ⟨y, h⟩ := by
  simp only [psi, dif_pos h]

lemma measurable_psi : Measurable (psi φ) := by
  classical
  unfold psi
  exact Measurable.dite (measurable_subtype_coe.comp φ.e.symm.measurable) measurable_subtype_coe
    φ.measurableSet_cod

lemma psi_mem_R {y : X} (h : y ∈ φ.cod) : (psi φ y, y) ∈ R := by
  have := φ.graph_subset (φ.e.symm ⟨y, h⟩)
  rw [psi_of_mem φ h]
  simpa using this

open Classical in
lemma shiftRel_eq' (f : X × X → ℝ) :
    φ.shiftRel f = fun p => if p.1 ∈ φ.cod then f (psi φ p.1, p.2) else 0 := by
  funext p
  by_cases h : p.1 ∈ φ.cod
  · simp [PartialTransformation.shiftRel, h, psi_of_mem φ h]
  · simp [PartialTransformation.shiftRel, h]

open Classical in
lemma shiftBase_eq' (F : X → ℝ) :
    φ.shiftBase F = fun y => if y ∈ φ.cod then F (psi φ y) else 0 := by
  funext y
  by_cases h : y ∈ φ.cod
  · simp [PartialTransformation.shiftBase, h, psi_of_mem φ h]
  · simp [PartialTransformation.shiftBase, h]

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
/-! ## Integration helpers -/
lemma ae_eq_of_setInt {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ A, MeasurableSet A → ∫ x in A, f x ∂μ = ∫ x in A, g x ∂μ) : f =ᵐ[μ] g :=
  Integrable.ae_eq_of_forall_setIntegral_eq f g hf hg (fun A hA _ => h A hA)

lemma abs_setInt_le [IsFiniteMeasure μ] {u : X → ℝ} {C : ℝ} (hb : ∀ᵐ x ∂μ, |u x| ≤ C)
    (A : Set X) : |∫ x in A, u x ∂μ| ≤ C * μ.real A := by
  rw [← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top μ A)
    (ae_restrict_of_ae (by filter_upwards [hb] with x hx; rwa [Real.norm_eq_abs]))

lemma abs_integral_mul_le {u D : X → ℝ} {C : ℝ}
    (hb : ∀ᵐ x ∂μ, |u x| ≤ C) (hD : Integrable D μ) :
    |∫ x, u x * D x ∂μ| ≤ C * ∫ x, |D x| ∂μ := by
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hD.abs.const_mul C) ?_
  filter_upwards [hb] with x hx
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

lemma integrable_mul_of_bdd {u D : X → ℝ} {C : ℝ} (hu : AEStronglyMeasurable u μ)
    (hb : ∀ᵐ x ∂μ, |u x| ≤ C) (hD : Integrable D μ) : Integrable (fun x => u x * D x) μ :=
  hD.bdd_mul hu (by filter_upwards [hb] with x hx; rwa [Real.norm_eq_abs])

lemma abs_integral_mul_sub_le' {u D D' : X → ℝ} {C : ℝ} (hu : AEStronglyMeasurable u μ)
    (hb : ∀ᵐ x ∂μ, |u x| ≤ C) (hD : Integrable D μ) (hD' : Integrable D' μ) :
    |∫ x, u x * D x ∂μ - ∫ x, u x * D' x ∂μ| ≤ C * ∫ x, |D x - D' x| ∂μ := by
  rw [← integral_sub (integrable_mul_of_bdd μ hu hb hD) (integrable_mul_of_bdd μ hu hb hD')]
  have : (fun x => u x * D x - u x * D' x) = fun x => u x * (D x - D' x) := by
    funext x; ring
  rw [this]
  exact abs_integral_mul_le μ hb (hD.sub hD')

lemma indicator_one_mul' (A : Set X) (h : X → ℝ) :
    (fun x => h x * A.indicator 1 x) = A.indicator h := by
  funext x
  by_cases hx : x ∈ A <;> simp [hx]

lemma abs_sub_clamp_le' (d M : ℝ) (hM : 0 ≤ M) : |d - max (min d M) (-M)| ≤ |d| := by
  rcases le_total d M with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total d (-M) with h2 | h2
    · rw [max_eq_right h2, abs_of_nonpos (by linarith : d - -M ≤ 0),
        abs_of_nonpos (by linarith : d ≤ 0)]
      linarith
    · rw [max_eq_left h2]
      simp
  · rw [min_eq_right h1, max_eq_left (by linarith : -M ≤ M),
      abs_of_nonneg (by linarith : 0 ≤ d - M), abs_of_nonneg (by linarith : 0 ≤ d)]
    linarith

lemma clamp_eq' {d M : ℝ} (h : |d| ≤ M) : max (min d M) (-M) = d := by
  rw [min_eq_left (abs_le.1 h).2, max_eq_left (abs_le.1 h).1]

/-- Truncations of an integrable function converge to it in `L¹`. -/
lemma tendsto_clamp {D : X → ℝ} (hD : Measurable D) (hDi : Integrable D μ) :
    Tendsto (fun M : ℕ => ∫ x, |D x - max (min (D x) M) (-M)| ∂μ) atTop (𝓝 0) := by
  have hclm : ∀ M : ℕ, Measurable (fun x => max (min (D x) M) (-(M : ℝ))) := fun M =>
    (hD.min measurable_const).max measurable_const
  have := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun (M : ℕ) x => |D x - max (min (D x) M) (-M)|) (f := fun _ => (0 : ℝ))
    (fun x => |D x|)
    (fun M => (hD.sub (hclm M)).abs.aestronglyMeasurable) hDi.abs
    (fun M => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_sub_clamp_le' _ _ (Nat.cast_nonneg M))
    (Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|D x|⌉₊] with M hM
      have : |D x| ≤ M := (Nat.le_ceil _).trans (by exact_mod_cast hM)
      simp only [clamp_eq' this, sub_self, abs_zero])
  simpa using this

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-! ## Riesz representation -/
open Classical in
/-- The Riesz representative of a functional (junk `0` if there is none). -/
noncomputable def Rep (L : E → ℝ) : E :=
  if h : ∃ v, ∀ w, inner ℝ v w = L w then h.choose else 0

lemma inner_Rep {L : E → ℝ} (hadd : ∀ a b, L (a + b) = L a + L b)
    (hsmul : ∀ (c : ℝ) a, L (c • a) = c * L a) {B : ℝ} (hB : ∀ a, |L a| ≤ B * ‖a‖) (w : E) :
    inner ℝ (Rep L) w = L w := by
  let L' : E →ₗ[ℝ] ℝ := { toFun := L, map_add' := hadd, map_smul' := hsmul }
  let Φ : StrongDual ℝ E := L'.mkContinuous B (fun a => by rw [Real.norm_eq_abs]; exact hB a)
  have h : ∃ v, ∀ w, inner ℝ v w = L w := ⟨(InnerProductSpace.toDual ℝ E).symm Φ, fun w => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl⟩
  simp only [Rep, dif_pos h]
  exact h.choose_spec w

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
/-! ## The data of the relative Zimmer theorem -/
/-- The orbit relation of a subgroup. -/
def RG {X G : Type*} [Group G] [MulAction G X] (Γ : Subgroup G) : Set (X × X) :=
  {p | ∃ g ∈ Γ, g • p.1 = p.2}

/-- All hypotheses of the theorem, for a finite measure, with the mean `P_Γ` and the invariant
finitely additive probability `m` on `Λ ⧸ Γ` chosen. -/
structure Data {X : Type*} [MeasurableSpace X] (μ : Measure X) (G : Type*) [Group G]
    [MulAction G X] where
  Γ : Subgroup G
  Λ : Subgroup G
  hΓΛ : Γ ≤ Λ
  hmeas : ∀ g ∈ Λ, Measurable (fun x : X => g • x)
  hnull : ∀ g ∈ Λ, ∀ s : Set X, μ s = 0 → μ ((fun x : X => g • x) ⁻¹' s) = 0
  PΓ : (X × X → ℝ) → X → ℝ
  hPΓ : Monod.IsLeftInvariantMean μ (RG Γ) PΓ
  R : Set (X × X)
  X₀ : Set X
  hX₀ : MeasurableSet X₀
  hX₀c : μ X₀ᶜ = 0
  hsat : ∀ p ∈ R, (p.1 ∈ X₀ ↔ p.2 ∈ X₀)
  hΛR : ∀ g ∈ Λ, ∀ x ∈ X₀, (x, g • x) ∈ R
  C : Set G
  hC : C.Countable
  hCΛ : C ⊆ Λ
  hRC : ∀ p ∈ R, p.1 ∈ X₀ → ∃ g ∈ C, g • p.1 = p.2
  m : Set (Λ ⧸ Γ.subgroupOf Λ) → ℝ≥0∞
  hm : IsFinitelyAdditiveMeasure m
  hm1 : m univ = 1
  hminv : IsInvariant Λ m

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
namespace Data
open Monod Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [Group G] [MulAction G X]
  (d : Data μ G)
/-- The coset space `Λ ⧸ Γ`. -/
abbrev Q := d.Λ ⧸ d.Γ.subgroupOf d.Λ

lemma refl (x : X) : (x, x) ∈ (RG d.Γ : Set (X × X)) := ⟨1, d.Γ.one_mem, one_smul _ _⟩

lemma smul_mem_X₀ {g : G} (hg : g ∈ d.Λ) {x : X} (hx : x ∈ d.X₀) : g • x ∈ d.X₀ :=
  (d.hsat _ (d.hΛR g hg x hx)).1 hx

lemma smul_mem_X₀_iff {g : G} (hg : g ∈ d.Λ) {x : X} : g • x ∈ d.X₀ ↔ x ∈ d.X₀ :=
  ⟨fun h => by simpa using d.smul_mem_X₀ (inv_mem hg) h, d.smul_mem_X₀ hg⟩

lemma qmp {g : G} (hg : g ∈ d.Λ) : Measure.QuasiMeasurePreserving (fun x : X => g • x) μ μ :=
  ⟨d.hmeas g hg, Measure.AbsolutelyContinuous.mk fun s hs h0 => by
    rw [Measure.map_apply (d.hmeas g hg) hs]
    exact d.hnull g hg s h0⟩

/-- Measurable, and bounded by `C` on the `Λ`-orbit relation over `X₀`. -/
def BddMC (g : X × X → ℝ) (C : ℝ) : Prop :=
  Measurable g ∧ 0 ≤ C ∧ ∀ x ∈ d.X₀, ∀ k ∈ d.Λ, |g (x, k • x)| ≤ C

/-- `g_λ (w, z) = g (λ w, z)` when `λ w ∈ X₀`. -/
noncomputable def Gl (l : d.Λ) (g : X × X → ℝ) : X × X → ℝ := fun p =>
  if (l : G) • p.1 ∈ d.X₀ then g ((l : G) • p.1, p.2) else 0

/-- `F_λ = P_Γ (g_λ) ∘ λ⁻¹`. -/
noncomputable def Fl (l : d.Λ) (g : X × X → ℝ) : X → ℝ := fun y =>
  d.PΓ (d.Gl l g) ((l : G)⁻¹ • y)

lemma measurable_Gl (l : d.Λ) {g : X × X → ℝ} (hg : Measurable g) : Measurable (d.Gl l g) :=
  Measurable.ite ((d.hX₀).preimage ((d.hmeas _ l.2).comp measurable_fst))
    (hg.comp (((d.hmeas _ l.2).comp measurable_fst).prodMk measurable_snd)) measurable_const

lemma abs_Gl_le (l : d.Λ) {g : X × X → ℝ} {C : ℝ} (hg : d.BddMC g C) :
    ∀ p ∈ (RG d.Γ : Set (X × X)), |d.Gl l g p| ≤ C := by
  rintro ⟨w, z⟩ ⟨γ, hγ, hz⟩
  simp only at hz
  subst hz
  simp only [Gl]
  split_ifs with h
  · have := hg.2.2 _ h (γ * (l : G)⁻¹) (mul_mem (d.hΓΛ hγ) (inv_mem l.2))
    simpa [mul_smul] using this
  · simpa using hg.2.1

lemma bdd_Gl (l : d.Λ) {g : X × X → ℝ} {C : ℝ} (hg : d.BddMC g C) :
    IsBddMeasOn (RG d.Γ) (d.Gl l g) :=
  ⟨d.measurable_Gl l hg.1, C, d.abs_Gl_le l hg⟩

lemma PΓ_shift {γ : G} (hγ : γ ∈ d.Γ) {g : X × X → ℝ} (hg : IsBddMeasOn (RG d.Γ) g) :
    d.PΓ (fun p => g (γ • p.1, p.2)) =ᵐ[μ] fun w => d.PΓ g (γ • w) := by
  have hm := d.hmeas γ (d.hΓΛ hγ)
  have hm' := d.hmeas γ⁻¹ (inv_mem (d.hΓΛ hγ))
  let e : (univ : Set X) ≃ᵐ (univ : Set X) :=
    { toFun := fun a => ⟨γ⁻¹ • (a : X), trivial⟩
      invFun := fun b => ⟨γ • (b : X), trivial⟩
      left_inv := fun a => by ext; simp
      right_inv := fun b => by ext; simp
      measurable_toFun := (hm'.comp measurable_subtype_coe).subtype_mk
      measurable_invFun := (hm.comp measurable_subtype_coe).subtype_mk }
  let φ : PartialTransformation (RG d.Γ : Set (X × X)) :=
    { dom := univ, cod := univ, measurableSet_dom := MeasurableSet.univ,
      measurableSet_cod := MeasurableSet.univ, e := e,
      graph_subset := fun a => ⟨γ⁻¹, inv_mem hγ, rfl⟩ }
  have h1 : φ.shiftRel g = fun p => g (γ • p.1, p.2) := by
    funext p
    simp [PartialTransformation.shiftRel, φ, e]
  have h2 : φ.shiftBase (d.PΓ g) = fun w => d.PΓ g (γ • w) := by
    funext w
    simp [PartialTransformation.shiftBase, φ, e]
  rw [← h1, ← h2]
  exact d.hPΓ.invariant φ g hg

end Data
end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
namespace Data
open Monod Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [Group G] [MulAction G X]
  (d : Data μ G)
variable {g g' : X × X → ℝ} {C C' : ℝ}
/-! ### The functions `F_λ` -/
lemma aesm_Fl (l : d.Λ) (hg : d.BddMC g C) : AEStronglyMeasurable (d.Fl l g) μ :=
  ((d.hPΓ.aemeasurable _ (d.bdd_Gl l hg)).comp_quasiMeasurePreserving
    (d.qmp (inv_mem l.2))).aestronglyMeasurable

lemma ae_abs_Fl_le (l : d.Λ) (hg : d.BddMC g C) : ∀ᵐ y ∂μ, |d.Fl l g y| ≤ C :=
  (d.qmp (inv_mem l.2)).ae (lim_abs_le d.hPΓ (d.bdd_Gl l hg) (d.abs_Gl_le l hg))

lemma Fl_add (l : d.Λ) (hg : d.BddMC g C) (hg' : d.BddMC g' C') :
    d.Fl l (g + g') =ᵐ[μ] d.Fl l g + d.Fl l g' := by
  have e : d.Gl l (g + g') = d.Gl l g + d.Gl l g' := by
    funext p
    simp only [Gl, Pi.add_apply]
    split_ifs <;> simp
  have := d.hPΓ.add _ _ (d.bdd_Gl l hg) (d.bdd_Gl l hg')
  rw [← e] at this
  exact (d.qmp (inv_mem l.2)).ae_eq this

lemma Fl_smul (l : d.Λ) (c : ℝ) (hg : d.BddMC g C) :
    d.Fl l (c • g) =ᵐ[μ] c • d.Fl l g := by
  have e : d.Gl l (c • g) = c • d.Gl l g := by
    funext p
    simp only [Gl, Pi.smul_apply]
    split_ifs <;> simp
  have := d.hPΓ.smul c _ (d.bdd_Gl l hg)
  rw [← e] at this
  exact (d.qmp (inv_mem l.2)).ae_eq this

lemma Fl_congr (l : d.Λ) (hg : d.BddMC g C) (hg' : d.BddMC g' C') {N : Set X} (hN : μ N = 0)
    (h : ∀ x ∈ d.X₀, x ∉ N → ∀ k ∈ d.Λ, g (x, k • x) = g' (x, k • x)) :
    d.Fl l g =ᵐ[μ] d.Fl l g' := by
  have hrn : RelNull μ (RG d.Γ) {p | d.Gl l g p ≠ d.Gl l g' p} := by
    refine measure_mono_null ?_ (d.hnull _ l.2 N hN)
    rintro _ ⟨⟨w, z⟩, ⟨hne, γ, hγ, hz⟩, rfl⟩
    simp only at hz
    subst hz
    simp only [mem_preimage]
    by_contra hwN
    apply hne
    simp only [Gl]
    split_ifs with hw
    · have := h _ hw hwN (γ * (l : G)⁻¹) (mul_mem (d.hΓΛ hγ) (inv_mem l.2))
      simpa [mul_smul] using this
    · rfl
  exact (d.qmp (inv_mem l.2)).ae_eq (d.hPΓ.congr _ _ (d.bdd_Gl l hg) (d.bdd_Gl l hg') hrn)

lemma bddMC_one : d.BddMC (1 : X × X → ℝ) 1 :=
  ⟨measurable_const, zero_le_one, fun _ _ _ _ => by simp⟩

lemma Fl_one (l : d.Λ) : d.Fl l (1 : X × X → ℝ) =ᵐ[μ] 1 := by
  have hrn : RelNull μ (RG d.Γ) {p | d.Gl l (1 : X × X → ℝ) p ≠ (1 : X × X → ℝ) p} := by
    refine measure_mono_null ?_ (d.hnull _ l.2 _ d.hX₀c)
    rintro _ ⟨⟨w, z⟩, ⟨hne, -⟩, rfl⟩
    simp only [mem_preimage, mem_compl_iff]
    intro hw
    apply hne
    simp [Gl, hw]
  have h1 := d.hPΓ.congr _ _ (d.bdd_Gl l d.bddMC_one) isBddMeasOn_one' hrn
  exact (d.qmp (inv_mem l.2)).ae_eq (h1.trans d.hPΓ.one)

lemma Fl_nonneg (l : d.Λ) (hg : d.BddMC g C)
    (h0 : ∀ x ∈ d.X₀, ∀ k ∈ d.Λ, 0 ≤ g (x, k • x)) : ∀ᵐ y ∂μ, 0 ≤ d.Fl l g y := by
  refine (d.qmp (inv_mem l.2)).ae (d.hPΓ.nonneg _ (d.bdd_Gl l hg) ?_)
  rintro ⟨w, z⟩ ⟨γ, hγ, hz⟩
  simp only at hz
  subst hz
  simp only [Gl]
  split_ifs with h
  · have := h0 _ h (γ * (l : G)⁻¹) (mul_mem (d.hΓΛ hγ) (inv_mem l.2))
    simpa [mul_smul] using this
  · exact le_rfl

lemma Fl_loc (l : d.Λ) (hg : d.BddMC g C) {B : Set X} (hB : MeasurableSet B) :
    d.Fl l (fun p => if p.1 ∈ B then g p else 0) =ᵐ[μ] B.indicator (d.Fl l g) := by
  set B' := (fun w : X => (l : G) • w) ⁻¹' B
  have hB' : MeasurableSet B' := hB.preimage (d.hmeas _ l.2)
  have e : d.Gl l (fun p => if p.1 ∈ B then g p else 0) =
      fun p => if p.1 ∈ B' then d.Gl l g p else 0 := by
    funext p
    simp only [Gl, B', mem_preimage]
    split_ifs <;> rfl
  have := lim_loc d.hPΓ d.refl hB' (d.bdd_Gl l hg)
  rw [← e] at this
  filter_upwards [(d.qmp (inv_mem l.2)).ae_eq this] with y hy
  simp only [Function.comp_apply] at hy
  rw [Set.indicator_apply]
  simp only [Fl, hy, B', mem_preimage, smul_inv_smul]

lemma Fl_rep {l l' : d.Λ} (h : (l : d.Q) = (l' : d.Q)) (hg : d.BddMC g C) :
    d.Fl l g =ᵐ[μ] d.Fl l' g := by
  have hmem := QuotientGroup.eq.1 h
  set γ : G := ((l⁻¹ * l' : d.Λ) : G)
  have hγ : γ ∈ d.Γ := Subgroup.mem_subgroupOf.1 hmem
  have hl' : (l' : G) = (l : G) * γ := by simp [γ]
  have e : d.Gl l' g = fun p => d.Gl l g (γ • p.1, p.2) := by
    funext p
    simp [Gl, hl', mul_smul]
  have := d.PΓ_shift hγ (d.bdd_Gl l hg)
  rw [← e] at this
  filter_upwards [(d.qmp (inv_mem l'.2)).ae_eq this] with y hy
  simp only [Function.comp_apply] at hy
  show d.PΓ (d.Gl l g) ((l : G)⁻¹ • y) = d.PΓ (d.Gl l' g) ((l' : G)⁻¹ • y)
  rw [hy, hl', mul_inv_rev, mul_smul, smul_inv_smul]

/-- The translate `g ∘ (κ⁻¹ × id)` over `X₀`. -/
noncomputable def tr (κ : d.Λ) (g : X × X → ℝ) : X × X → ℝ := fun p =>
  if p.1 ∈ d.X₀ then g ((κ : G)⁻¹ • p.1, p.2) else 0

lemma Gl_tr (κ l : d.Λ) (g : X × X → ℝ) : d.Gl l (d.tr κ g) = d.Gl (κ⁻¹ * l) g := by
  funext p
  simp only [Gl, tr, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
  rw [d.smul_mem_X₀_iff (inv_mem κ.2)]
  split_ifs <;> rfl

lemma Fl_tr (κ l : d.Λ) (g : X × X → ℝ) (y : X) :
    d.Fl l (d.tr κ g) y = d.Fl (κ⁻¹ * l) g ((κ : G)⁻¹ • y) := by
  simp only [Fl, Gl_tr, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_smul,
    smul_inv_smul]

end Data
end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
namespace Data
open Monod Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [Group G] [MulAction G X]
  (d : Data μ G)
variable [IsFiniteMeasure μ] {g g' : X × X → ℝ} {C C' : ℝ}
/-! ### The mean `P` -/
/-- `F_λ` in `L²`. -/
noncomputable def FL (l : d.Λ) (g : X × X → ℝ) : Lp ℝ 2 μ :=
  if h : MemLp (d.Fl l g) 2 μ then h.toLp _ else 0

/-- `P g ∈ L²`: the Riesz representative of `h ↦ Mn (q ↦ ⟪F_{rep q}, h⟫)`. -/
noncomputable def PL (g : X × X → ℝ) : Lp ℝ 2 μ :=
  Rep (fun w => Mn d.m (fun q : d.Q => inner ℝ (d.FL q.out g) w))

/-- The mean `P` on `R`. -/
noncomputable def P (g : X × X → ℝ) : X → ℝ := (d.PL g : X → ℝ)

/-- The constant `μ(X)^{1/2}`. -/
noncomputable def Kμ (μ : Measure X) : ℝ :=
  ((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : NNReal) : ℝ)

lemma memLp_Fl (l : d.Λ) (hg : d.BddMC g C) : MemLp (d.Fl l g) 2 μ :=
  MemLp.of_bound (d.aesm_Fl l hg) C (by
    filter_upwards [d.ae_abs_Fl_le l hg] with y hy
    rwa [Real.norm_eq_abs])

lemma FL_eq (l : d.Λ) (hg : d.BddMC g C) : d.FL l g = (d.memLp_Fl l hg).toLp _ := by
  simp only [FL, dif_pos (d.memLp_Fl l hg)]

lemma coe_FL (l : d.Λ) (hg : d.BddMC g C) : (d.FL l g : X → ℝ) =ᵐ[μ] d.Fl l g := by
  rw [d.FL_eq l hg]
  exact MemLp.coeFn_toLp _

lemma norm_FL_le (l : d.Λ) (hg : d.BddMC g C) : ‖d.FL l g‖ ≤ Kμ μ * C := by
  refine Lp.norm_le_of_ae_bound hg.2.1 ?_
  filter_upwards [d.coe_FL l hg, d.ae_abs_Fl_le l hg] with y h1 h2
  rw [h1, Real.norm_eq_abs]
  exact h2

lemma inner_PL (hg : d.BddMC g C) (w : Lp ℝ 2 μ) :
    inner ℝ (d.PL g) w = Mn d.m (fun q : d.Q => inner ℝ (d.FL q.out g) w) := by
  have hb : ∀ (w : Lp ℝ 2 μ) (q : d.Q), |inner ℝ (d.FL q.out g) w| ≤ Kμ μ * C * ‖w‖ :=
    fun w q => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (d.norm_FL_le _ hg) (norm_nonneg _))
  refine inner_Rep (fun a b => ?_) (fun c a => ?_) (B := Kμ μ * C) (fun a => ?_) w
  · simp only [inner_add_right]
    exact Mn_add d.hm d.hm1 (hb a) (hb b)
  · simp only [real_inner_smul_right]
    exact Mn_smul d.hm d.hm1 c (hb a)
  · exact Mn_abs_le d.hm d.hm1 (hb a)

lemma KEYW_bdd (hg : d.BddMC g C) {D : X → ℝ} (hD : Measurable D) {M : ℝ}
    (hM : ∀ x, |D x| ≤ M) :
    ∫ x, d.P g x * D x ∂μ = Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ) := by
  have hDL : MemLp D 2 μ := MemLp.of_bound hD.aestronglyMeasurable M
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  have e1 : inner ℝ (d.PL g) (hDL.toLp D) = ∫ x, d.P g x * D x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hDL.coeFn_toLp] with x hx
    rw [hx, Real.inner_apply]
    rfl
  have e2 : ∀ l : d.Λ, inner ℝ (d.FL l g) (hDL.toLp D) = ∫ x, d.Fl l g x * D x ∂μ := by
    intro l
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hDL.coeFn_toLp, d.coe_FL l hg] with x hx hx'
    rw [hx, hx', Real.inner_apply]
  rw [← e1, d.inner_PL hg]
  simp only [e2]

lemma setInt_P (hg : d.BddMC g C) {A : Set X} (hA : MeasurableSet A) :
    ∫ x in A, d.P g x ∂μ = Mn d.m (fun q : d.Q => ∫ x in A, d.Fl q.out g x ∂μ) := by
  have := d.KEYW_bdd hg (D := A.indicator 1) (measurable_const.indicator hA) (M := 1)
    (fun x => by by_cases hx : x ∈ A <;> simp [hx])
  simp only [indicator_one_mul', integral_indicator hA] at this
  exact this

lemma integrable_P (g : X × X → ℝ) : Integrable (d.P g) μ :=
  (Lp.memLp _).integrable (by norm_num)

lemma aesm_P (g : X × X → ℝ) : AEStronglyMeasurable (d.P g) μ :=
  Lp.aestronglyMeasurable _

lemma measurable_P (g : X × X → ℝ) : Measurable (d.P g) :=
  (Lp.stronglyMeasurable _).measurable

lemma integrable_Fl (l : d.Λ) (hg : d.BddMC g C) : Integrable (d.Fl l g) μ :=
  Integrable.of_bound (d.aesm_Fl l hg) C (by
    filter_upwards [d.ae_abs_Fl_le l hg] with y hy
    rwa [Real.norm_eq_abs])

lemma abs_setInt_Fl_le (l : d.Λ) (hg : d.BddMC g C) (A : Set X) :
    |∫ x in A, d.Fl l g x ∂μ| ≤ C * μ.real A :=
  abs_setInt_le μ (d.ae_abs_Fl_le l hg) A

lemma P_bound (hg : d.BddMC g C) : ∀ᵐ x ∂μ, |d.P g x| ≤ C := by
  have key : ∀ A, MeasurableSet A → |∫ x in A, d.P g x ∂μ| ≤ C * μ.real A := fun A hA => by
    rw [d.setInt_P hg hA]
    exact Mn_abs_le d.hm d.hm1 (fun q => d.abs_setInt_Fl_le _ hg A)
  have h1 : d.P g ≤ᵐ[μ] fun _ => C :=
    ae_le_of_forall_setIntegral_le (d.integrable_P g) (integrable_const C) (fun A hA _ => by
      rw [setIntegral_const, smul_eq_mul]
      have := key A hA
      linarith [le_abs_self (∫ x in A, d.P g x ∂μ)])
  have h2 : (fun _ => -C) ≤ᵐ[μ] d.P g :=
    ae_le_of_forall_setIntegral_le (integrable_const (-C)) (d.integrable_P g) (fun A hA _ => by
      rw [setIntegral_const, smul_eq_mul]
      have := key A hA
      linarith [neg_abs_le (∫ x in A, d.P g x ∂μ)])
  filter_upwards [h1, h2] with x h1 h2
  exact abs_le.2 ⟨h2, h1⟩

lemma KEYW (hg : d.BddMC g C) {D : X → ℝ} (hD : Measurable D) (hDi : Integrable D μ) :
    ∫ x, d.P g x * D x ∂μ = Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ) := by
  set cl : ℕ → X → ℝ := fun M x => max (min (D x) M) (-M) with hcl
  have hclm : ∀ M, Measurable (cl M) := fun M => (hD.min measurable_const).max measurable_const
  have hclb : ∀ M x, |cl M x| ≤ M := fun M x => abs_le.2 ⟨le_max_right _ _,
    max_le (min_le_right _ _) (by have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith)⟩
  have hcli : ∀ M, Integrable (cl M) μ := fun M =>
    Integrable.of_bound (hclm M).aestronglyMeasurable M
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hclb M x)
  have hconv : Tendsto (fun M : ℕ => 2 * C * ∫ x, |D x - cl M x| ∂μ) atTop (𝓝 0) := by
    simpa using (tendsto_clamp μ hD hDi).const_mul (2 * C)
  have hdiff : ∀ M : ℕ, |(∫ x, d.P g x * D x ∂μ) -
      Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ)| ≤
        2 * C * ∫ x, |D x - cl M x| ∂μ := by
    intro M
    have e1 := d.KEYW_bdd hg (hclm M) (hclb M)
    have h1 := abs_integral_mul_sub_le' μ (d.aesm_P g) (d.P_bound hg) hDi (hcli M)
    have h2 : |Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ) -
        Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * cl M x ∂μ)| ≤
          C * ∫ x, |D x - cl M x| ∂μ :=
      Mn_sub_le d.hm d.hm1 (B := C * ∫ x, |cl M x| ∂μ)
        (fun q => abs_integral_mul_le μ (d.ae_abs_Fl_le _ hg) (hcli M))
        (fun q => abs_integral_mul_sub_le' μ (d.aesm_Fl _ hg) (d.ae_abs_Fl_le _ hg) hDi (hcli M))
    rw [e1] at h1
    have := abs_sub_le (∫ x, d.P g x * D x ∂μ)
      (Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * cl M x ∂μ))
      (Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ))
    rw [abs_sub_comm (Mn d.m _) (Mn d.m _)] at this
    linarith
  have := ge_of_tendsto' hconv hdiff
  have h0 := abs_nonneg ((∫ x, d.P g x * D x ∂μ) -
      Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ))
  have : |(∫ x, d.P g x * D x ∂μ) -
      Mn d.m (fun q : d.Q => ∫ x, d.Fl q.out g x * D x ∂μ)| = 0 := le_antisymm this h0
  exact sub_eq_zero.1 (abs_eq_zero.1 this)

/-! ### The axioms of a mean -/
lemma bddMC_add (hg : d.BddMC g C) (hg' : d.BddMC g' C') : d.BddMC (g + g') (C + C') :=
  ⟨hg.1.add hg'.1, add_nonneg hg.2.1 hg'.2.1, fun x hx k hk =>
    (abs_add_le _ _).trans (add_le_add (hg.2.2 x hx k hk) (hg'.2.2 x hx k hk))⟩

lemma bddMC_smul (c : ℝ) (hg : d.BddMC g C) : d.BddMC (c • g) (|c| * C) :=
  ⟨hg.1.const_smul c, mul_nonneg (abs_nonneg c) hg.2.1, fun x hx k hk => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg.2.2 x hx k hk) (abs_nonneg c)⟩

lemma bddMC_loc (hg : d.BddMC g C) {B : Set X} (hB : MeasurableSet B) :
    d.BddMC (fun p => if p.1 ∈ B then g p else 0) C :=
  ⟨Measurable.ite (hB.preimage measurable_fst) hg.1 measurable_const, hg.2.1, fun x hx k hk => by
    dsimp only
    split_ifs
    · exact hg.2.2 x hx k hk
    · simpa using hg.2.1⟩

lemma bddMC_tr (κ : d.Λ) (hg : d.BddMC g C) : d.BddMC (d.tr κ g) C :=
  ⟨Measurable.ite (d.hX₀.preimage measurable_fst)
    (hg.1.comp (((d.hmeas _ (inv_mem κ.2)).comp measurable_fst).prodMk measurable_snd))
    measurable_const, hg.2.1, fun x hx k hk => by
    simp only [tr, if_pos hx]
    have := hg.2.2 _ (d.smul_mem_X₀ (inv_mem κ.2) hx) (k * κ) (mul_mem hk κ.2)
    simpa [mul_smul] using this⟩

lemma P_add (hg : d.BddMC g C) (hg' : d.BddMC g' C') :
    d.P (g + g') =ᵐ[μ] d.P g + d.P g' := by
  refine ae_eq_of_setInt μ (d.integrable_P _) ((d.integrable_P g).add (d.integrable_P g'))
    fun A hA => ?_
  simp only [Pi.add_apply]
  rw [integral_add (d.integrable_P g).integrableOn (d.integrable_P g').integrableOn,
    d.setInt_P (d.bddMC_add hg hg') hA, d.setInt_P hg hA, d.setInt_P hg' hA,
    ← Mn_add d.hm d.hm1 (fun q => d.abs_setInt_Fl_le _ hg A)
      (fun q => d.abs_setInt_Fl_le _ hg' A)]
  congr 1
  funext q
  rw [← integral_add (d.integrable_Fl _ hg).integrableOn (d.integrable_Fl _ hg').integrableOn]
  exact integral_congr_ae (ae_restrict_of_ae (d.Fl_add _ hg hg'))

lemma P_smul (c : ℝ) (hg : d.BddMC g C) : d.P (c • g) =ᵐ[μ] c • d.P g := by
  refine ae_eq_of_setInt μ (d.integrable_P _) ((d.integrable_P g).smul c) fun A hA => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, d.setInt_P (d.bddMC_smul c hg) hA, d.setInt_P hg hA,
    ← Mn_smul d.hm d.hm1 c (fun q => d.abs_setInt_Fl_le _ hg A)]
  congr 1
  funext q
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [d.Fl_smul q.out c hg] with x hx
  rw [hx]
  rfl

lemma P_zero : d.P (0 : X × X → ℝ) =ᵐ[μ] 0 := by
  have h0 : d.BddMC (0 : X × X → ℝ) 0 := ⟨measurable_const, le_rfl, fun _ _ _ _ => by simp⟩
  have := d.P_smul 0 h0
  rw [zero_smul] at this
  filter_upwards [this] with x hx
  rw [hx]
  simp

lemma P_nonneg (hg : d.BddMC g C) (h0 : ∀ x ∈ d.X₀, ∀ k ∈ d.Λ, 0 ≤ g (x, k • x)) :
    ∀ᵐ x ∂μ, 0 ≤ d.P g x := by
  refine ae_nonneg_of_forall_setIntegral_nonneg (d.integrable_P g) fun A hA _ => ?_
  rw [d.setInt_P hg hA]
  refine Mn_nonneg d.hm d.hm1 (fun q => d.abs_setInt_Fl_le _ hg A) fun q => ?_
  exact integral_nonneg_of_ae (ae_restrict_of_ae (d.Fl_nonneg _ hg h0))

lemma P_one : d.P (1 : X × X → ℝ) =ᵐ[μ] 1 := by
  refine ae_eq_of_setInt μ (d.integrable_P _) (integrable_const 1) fun A hA => ?_
  rw [d.setInt_P d.bddMC_one hA]
  have : ∀ q : d.Q, ∫ x in A, d.Fl q.out (1 : X × X → ℝ) x ∂μ = μ.real A := fun q => by
    rw [integral_congr_ae (ae_restrict_of_ae (d.Fl_one q.out))]
    simp
  simp only [this, Mn_const d.hm d.hm1]
  simp

lemma P_congr (hg : d.BddMC g C) (hg' : d.BddMC g' C') {N : Set X} (hN : μ N = 0)
    (h : ∀ x ∈ d.X₀, x ∉ N → ∀ k ∈ d.Λ, g (x, k • x) = g' (x, k • x)) :
    d.P g =ᵐ[μ] d.P g' := by
  refine ae_eq_of_setInt μ (d.integrable_P _) (d.integrable_P _) fun A hA => ?_
  rw [d.setInt_P hg hA, d.setInt_P hg' hA]
  congr 1
  funext q
  exact integral_congr_ae (ae_restrict_of_ae (d.Fl_congr _ hg hg' hN h))

lemma P_loc (hg : d.BddMC g C) {B : Set X} (hB : MeasurableSet B) :
    d.P (fun p => if p.1 ∈ B then g p else 0) =ᵐ[μ] B.indicator (d.P g) := by
  refine ae_eq_of_setInt μ (d.integrable_P _) ((d.integrable_P g).indicator hB) fun A hA => ?_
  rw [setIntegral_indicator hB, d.setInt_P (d.bddMC_loc hg hB) hA, d.setInt_P hg (hA.inter hB)]
  congr 1
  funext q
  rw [integral_congr_ae (ae_restrict_of_ae (d.Fl_loc q.out hg hB)), setIntegral_indicator hB]

/-- Change of variables along `κ`. -/
lemma cv {κ : G} (hκ : κ ∈ d.Λ) (A : Set X) {u : X → ℝ}
    (hu : AEStronglyMeasurable u μ) :
    ∫ y in A, u (κ • y) ∂μ = ∫ x, u x *
      ((Measure.map (fun y : X => κ • y) (μ.restrict A)).rnDeriv μ x).toReal ∂μ := by
  have hac : Measure.map (fun y : X => κ • y) (μ.restrict A) ≪ μ :=
    (Measure.absolutelyContinuous_of_le
      (Measure.map_mono Measure.restrict_le_self (d.hmeas κ hκ))).trans
      (d.qmp hκ).absolutelyContinuous
  rw [← integral_map (d.hmeas κ hκ).aemeasurable (hu.mono_ac hac), ← integral_rnDeriv_smul hac]
  simp only [smul_eq_mul, mul_comm]

/-- **Translation invariance**: `P (g ∘ κ⁻¹) = (P g) ∘ κ⁻¹`. -/
lemma P_tr (κ : d.Λ) (hg : d.BddMC g C) :
    d.P (d.tr κ g) =ᵐ[μ] fun y => d.P g ((κ : G)⁻¹ • y) := by
  have hq := d.qmp (inv_mem κ.2)
  have hint : Integrable (fun y => d.P g ((κ : G)⁻¹ • y)) μ :=
    Integrable.of_bound ((d.aesm_P g).comp_quasiMeasurePreserving hq) C (by
      filter_upwards [hq.ae (d.P_bound hg)] with y hy
      rwa [Real.norm_eq_abs])
  refine ae_eq_of_setInt μ (d.integrable_P _) hint fun A hA => ?_
  set D : X → ℝ := fun x =>
    ((Measure.map (fun y : X => (κ : G)⁻¹ • y) (μ.restrict A)).rnDeriv μ x).toReal with hD
  have hDm : Measurable D := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hDi : Integrable D μ := Measure.integrable_toReal_rnDeriv
  rw [d.cv (inv_mem κ.2) A (d.aesm_P g)]
  change _ = ∫ x, d.P g x * D x ∂μ
  rw [d.KEYW hg hDm hDi,
    d.setInt_P (d.bddMC_tr κ hg) hA]
  have step1 : ∀ q : d.Q, ∫ x in A, d.Fl q.out (d.tr κ g) x ∂μ =
      ∫ x in A, d.Fl (κ⁻¹ • q).out g ((κ : G)⁻¹ • x) ∂μ := by
    intro q
    simp only [d.Fl_tr]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    have hrep : ((κ⁻¹ * q.out : d.Λ) : d.Q) = (((κ⁻¹ • q).out : d.Λ) : d.Q) := by
      rw [QuotientGroup.out_eq', ← MulAction.Quotient.mk_smul_out]
      rfl
    exact hq.ae_eq (d.Fl_rep hrep hg)
  have step2 : ∀ q : d.Q, ∫ x in A, d.Fl q.out g ((κ : G)⁻¹ • x) ∂μ =
      ∫ x, d.Fl q.out g x * D x ∂μ := fun q => d.cv (inv_mem κ.2) A (d.aesm_Fl _ hg)
  simp only [step1]
  rw [Mn_inv d.hm d.hm1 d.hminv κ (a := fun q : d.Q => ∫ x in A, d.Fl q.out g ((κ : G)⁻¹ • x) ∂μ)
    (fun q => abs_setInt_le μ (hq.ae (d.ae_abs_Fl_le q.out hg)) A)]
  simp only [step2]

/-! ### Invariance under the partial transformations of `R` -/
lemma P_loc_congr (hg : d.BddMC g C) (hg' : d.BddMC g' C') {B : Set X} (hB : MeasurableSet B)
    (h : ∀ x ∈ B, x ∈ d.X₀ → ∀ k ∈ d.Λ, g (x, k • x) = g' (x, k • x)) :
    ∀ᵐ y ∂μ, y ∈ B → d.P g y = d.P g' y := by
  have hc := d.P_congr (d.bddMC_loc hg hB) (d.bddMC_loc hg' hB) (N := ∅) measure_empty
    (fun x hx _ k hk => by
      dsimp only
      split_ifs with hxB
      · exact h x hxB hx k hk
      · rfl)
  filter_upwards [hc, d.P_loc hg hB, d.P_loc hg' hB] with y h1 h2 h3 hy
  rw [h2, h3, Set.indicator_of_mem hy, Set.indicator_of_mem hy] at h1
  exact h1

lemma bddMC_of_isBddMeasOn {f : X × X → ℝ} (hf : IsBddMeasOn d.R f) : ∃ C, d.BddMC f C := by
  obtain ⟨C, hC⟩ := hf.2
  exact ⟨max C 0, hf.1, le_max_right _ _, fun x hx k hk =>
    (hC _ (d.hΛR k hk x hx)).trans (le_max_left _ _)⟩

lemma bddMC_shiftRel (φ : PartialTransformation d.R) {f : X × X → ℝ} (hf : IsBddMeasOn d.R f) :
    ∃ C, d.BddMC (φ.shiftRel f) C := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨max C 0, ?_, le_max_right _ _, fun x hx k hk => ?_⟩
  · rw [shiftRel_eq']
    exact Measurable.ite (φ.measurableSet_cod.preimage measurable_fst)
      (hf.1.comp (((measurable_psi φ).comp measurable_fst).prodMk measurable_snd))
      measurable_const
  · rw [shiftRel_eq']
    dsimp only
    split_ifs with hxc
    · have hR := psi_mem_R φ hxc
      have hψ : psi φ x ∈ d.X₀ := (d.hsat _ hR).2 hx
      obtain ⟨c, hc, hcx⟩ := d.hRC _ hR hψ
      simp only at hcx
      have hR' : (psi φ x, k • x) ∈ d.R := by
        have := d.hΛR (k * c) (mul_mem hk (d.hCΛ hc)) _ hψ
        rwa [mul_smul, hcx] at this
      exact (hC _ hR').trans (le_max_left _ _)
    · simp

theorem P_invariant (φ : PartialTransformation d.R) {f : X × X → ℝ} (hf : IsBddMeasOn d.R f) :
    d.P (φ.shiftRel f) =ᵐ[μ] φ.shiftBase (d.P f) := by
  obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
  obtain ⟨C', hsC⟩ := d.bddMC_shiftRel φ hf
  let B : G → Set X := fun κ => φ.cod ∩ d.X₀ ∩ {y | d.P f (psi φ y) = d.P f (κ⁻¹ • y)} ∩
    ⋂ c ∈ d.C, {y | f (psi φ y, c • y) = f (κ⁻¹ • y, c • y)}
  have hBm : ∀ κ ∈ d.Λ, MeasurableSet (B κ) := by
    intro κ hκ
    have hκm := d.hmeas _ (inv_mem hκ)
    refine ((φ.measurableSet_cod.inter d.hX₀).inter (measurableSet_eq_fun
      ((d.measurable_P f).comp (measurable_psi φ)) ((d.measurable_P f).comp hκm))).inter
      (MeasurableSet.biInter d.hC fun c hc => measurableSet_eq_fun ?_ ?_)
    · exact hf.1.comp ((measurable_psi φ).prodMk (d.hmeas c (d.hCΛ hc)))
    · exact hf.1.comp (hκm.prodMk (d.hmeas c (d.hCΛ hc)))
  have hi : ∀ᵐ y ∂μ, ∀ κ ∈ d.C, y ∈ B κ → d.P (φ.shiftRel f) y = d.P f (κ⁻¹ • y) := by
    rw [eventually_countable_ball d.hC]
    intro κ hκ
    have h1 := d.P_loc_congr hsC (d.bddMC_tr ⟨κ, d.hCΛ hκ⟩ hfC) (hBm κ (d.hCΛ hκ))
      (fun x hxB hx k hk => by
        rw [shiftRel_eq']
        simp only [tr, if_pos hxB.1.1.1, if_pos hx]
        obtain ⟨c, hc, hcx⟩ := d.hRC _ (d.hΛR k hk x hx) hx
        simp only at hcx
        rw [← hcx]
        exact mem_iInter₂.1 hxB.2 c hc)
    filter_upwards [h1, d.P_tr ⟨κ, d.hCΛ hκ⟩ hfC] with y h1 h2 hy
    rw [h1 hy, h2]
  have h0 : d.BddMC (0 : X × X → ℝ) 0 := ⟨measurable_const, le_rfl, fun _ _ _ _ => by simp⟩
  have hiii := d.P_loc_congr hsC h0 φ.measurableSet_cod.compl (fun x hxB _ k _ => by
    rw [shiftRel_eq']
    simp only [if_neg (show x ∉ φ.cod from hxB)]
    rfl)
  filter_upwards [hi, hiii, d.P_zero, measure_eq_zero_iff_ae_notMem.1 d.hX₀c]
    with y h1 h3 h4 h5
  rw [shiftBase_eq']
  dsimp only
  split_ifs with hy
  · have hX : y ∈ d.X₀ := by simpa using h5
    have hR := psi_mem_R φ hy
    have hψ : psi φ y ∈ d.X₀ := (d.hsat _ hR).2 hX
    obtain ⟨κ, hκ, hκy⟩ := d.hRC _ hR hψ
    simp only at hκy
    have hψy : psi φ y = κ⁻¹ • y := eq_inv_smul_iff.2 hκy
    have hyB : y ∈ B κ := by
      refine ⟨⟨⟨hy, hX⟩, ?_⟩, mem_iInter₂.2 fun c hc => ?_⟩
      · show d.P f (psi φ y) = d.P f (κ⁻¹ • y)
        rw [hψy]
      · show f (psi φ y, c • y) = f (κ⁻¹ • y, c • y)
        rw [hψy]
    rw [h1 κ hκ hyB, hψy]
  · rw [h3 hy, h4]
    rfl

/-- The mean `P` is a left invariant mean on `R`. -/
theorem isLeftInvariantMean : IsLeftInvariantMean μ d.R d.P where
  aemeasurable f _ := (d.aesm_P f).aemeasurable
  congr f g hf hg hfg := by
    obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
    obtain ⟨C', hgC⟩ := d.bddMC_of_isBddMeasOn hg
    refine d.P_congr hfC hgC hfg fun x hx hxN k hk => ?_
    by_contra hne
    exact hxN ⟨(x, k • x), ⟨hne, d.hΛR k hk x hx⟩, rfl⟩
  add f g hf hg := by
    obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
    obtain ⟨C', hgC⟩ := d.bddMC_of_isBddMeasOn hg
    exact d.P_add hfC hgC
  smul c f hf := by
    obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
    exact d.P_smul c hfC
  nonneg f hf hpos := by
    obtain ⟨C, hfC⟩ := d.bddMC_of_isBddMeasOn hf
    exact d.P_nonneg hfC fun x hx k hk => hpos _ (d.hΛR k hk x hx)
  one := d.P_one
  invariant φ f hf := d.P_invariant φ hf

end Data
end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
/-! ## The theorem -/
theorem isAmenableRel_of_isCoamenable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] {G : Type*} [Group G] [MulAction G X] (Γ Λ : Subgroup G) (hΓΛ : Γ ≤ Λ)
    (hmeas : ∀ g ∈ Λ, Measurable (fun x : X => g • x))
    (hnull : ∀ g ∈ Λ, ∀ s : Set X, μ s = 0 → μ ((fun x : X => g • x) ⁻¹' s) = 0)
    (hco : Monod.IsCoamenable (Γ.subgroupOf Λ))
    (hΓ : Monod.IsAmenableRel μ {p : X × X | ∃ g ∈ Γ, g • p.1 = p.2})
    (R : Set (X × X)) (X₀ : Set X) (hX₀ : MeasurableSet X₀) (hX₀c : μ X₀ᶜ = 0)
    (hsat : ∀ p ∈ R, (p.1 ∈ X₀ ↔ p.2 ∈ X₀))
    (hΛR : ∀ g ∈ Λ, ∀ x ∈ X₀, (x, g • x) ∈ R)
    (C : Set G) (hC : C.Countable) (hCΛ : C ⊆ Λ)
    (hRC : ∀ p ∈ R, p.1 ∈ X₀ → ∃ g ∈ C, g • p.1 = p.2) :
    Monod.IsAmenableRel μ R := by
  obtain ⟨m, hm, hm1, hminv⟩ := hco
  obtain ⟨PΓ, hPΓ⟩ := hΓ
  have hae : ae μ.toFinite = ae μ := ae_toFinite
  have h0 : ∀ s, μ.toFinite s = 0 ↔ μ s = 0 := fun s => by
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem, hae]
  let d : Data μ.toFinite G :=
    { Γ := Γ, Λ := Λ, hΓΛ := hΓΛ, hmeas := hmeas,
      hnull := fun g hg s hs => (h0 _).2 (hnull g hg s ((h0 s).1 hs)),
      PΓ := PΓ, hPΓ := lim_of_ae_eq hae.symm hPΓ, R := R, X₀ := X₀, hX₀ := hX₀,
      hX₀c := (h0 _).2 hX₀c, hsat := hsat, hΛR := hΛR, C := C, hC := hC, hCΛ := hCΛ,
      hRC := hRC, m := m, hm := hm, hm1 := hm1, hminv := hminv }
  exact ⟨d.P, lim_of_ae_eq hae d.isLeftInvariantMean⟩

end ThompsonAmenability.M51.PartD
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part D: relative Zimmer (Monod 2023, Proposition 4.7) -/

/-! ## Part E1: Thompson's group `F` at non-dyadic points -/

end ThompsonAmenability.M51
end

section
namespace ThompsonAmenability.M51.PartE1
open CannonFloydParry
/-!
# Part E1: Thompson's group `F` at non-dyadic points

* `F_apply_nonDyadic_daff`: at a non-dyadic point `t ∈ (0,1)` an element of `F` acts by a dyadic
  affine map `y ↦ 2ⁿ y + c` (`c` dyadic), and the image is again non-dyadic in `(0,1)`.
* `exists_F_of_daff`: two non-dyadic points of `(0,1)` related by a dyadic affine map lie in one
  `F`-orbit: glue the affine map on a small dyadic interval around `t` to an element of `F` that
  agrees with it at the two endpoints (`exists_mem_F_map_partition`).
-/
/-! ### Dyadic rationals -/

/-! ### Gaps in a finite set -/

/-! ### `extend` -/

/-! ### Target 1 -/

end ThompsonAmenability.M51.PartE1
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
namespace ThompsonAmenability.M51.PartE1
open CannonFloydParry
/-! ### Gluing an affine piece into an element of `F` -/

/-! ### Target 2 -/

end ThompsonAmenability.M51.PartE1
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
/-!
# Part E2: the orbit relation of `H_ℚ(ℤ)` on `P¹` is amenable

Route. The published conjugacy `Monod.contDiff_and_exists_mulEquiv_HRat_F` gives `c` (strictly
monotone from `(0,1)` onto `ℝ`) and `φ : HRat ≃* F` with `h (c t) = c (extend (φ h) t)`.
* `alpha : ℝ → (0,1)` is an increasing bijection that is dyadic affine on every `[n, n+1]`
  (`alpha y = 2^e y + b`, `b` dyadic), so `Psi := c ∘ alpha` is an order isomorphism of `ℝ`.
* `Aff` is the group of dyadic affine maps `y ↦ 2ⁿ y + b` of `ℝ`: countable and solvable, hence
  amenable; it acts on `P¹` through `Psi` (the subgroup `Lam` of homeomorphisms of `P¹`).
* On the conull set `X1 = c '' (non-dyadic points)`, the `Lam`-orbits and the `HRat`-orbits
  coincide (Blueprint `F_apply_nonDyadic_daff`, `exists_F_of_daff`), so `Lam` preserves null sets
  (Blueprint `exists_mob_of_mem_HB`, `null_preimage_mob`), the published C1 theorem makes the
  `Lam`-orbit relation amenable, and the Blueprint's `isAmenableRel_of_agree` transfers it.
-/
/-! ## Section 1: dyadic rationals -/
lemma isDyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma isDyadic_zpow_mul {n : ℤ} {x : ℝ} (hx : IsDyadic x) : IsDyadic (2 ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  by_cases hn : 0 ≤ n
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine ⟨m * 2 ^ j, k, ?_⟩
    push_cast
    rw [zpow_natCast]
    ring
  · push Not at hn
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨(-n).toNat, by omega⟩
    refine ⟨m, k + j, ?_⟩
    rw [zpow_neg, zpow_natCast]
    field_simp
    ring

lemma isDyadic_intCast (m : ℤ) : IsDyadic (m : ℝ) := ⟨m, 0, by simp⟩

lemma isDyadic_zero : IsDyadic 0 := by simpa using isDyadic_intCast 0

lemma isDyadic_zpow (n : ℤ) : IsDyadic ((2 : ℝ) ^ n) := by
  simpa using isDyadic_zpow_mul (n := n) (isDyadic_intCast 1)

lemma countable_isDyadic : {x : ℝ | IsDyadic x}.Countable := by
  have : {x : ℝ | IsDyadic x} = Set.range (fun p : ℤ × ℕ => (p.1 : ℝ) / 2 ^ p.2) := by
    ext x
    simp only [Set.mem_range, Prod.exists, IsDyadic]
    constructor
    · rintro ⟨m, k, rfl⟩; exact ⟨m, k, rfl⟩
    · rintro ⟨m, k, rfl⟩; exact ⟨m, k, rfl⟩
  rw [this]
  exact Set.countable_range _

/-! ## Section 2: the dyadic affine relation `DAff` -/

/-! ## Section 3: the increasing dyadic bijection `alpha : ℝ → (0,1)` -/
/-- The knots: `2^(n-1)` for `n ≤ 0`, `1 - 2^(-n-1)` for `n ≥ 0`. -/
noncomputable def knot (n : ℤ) : ℝ := if n ≤ 0 then 2 ^ (n - 1) else 1 - 2 ^ (-n - 1)

/-- The exponent of the slope on `[n, n+1]`. -/
def ex (n : ℤ) : ℤ := if n < 0 then n - 1 else -n - 2

lemma knot_succ (n : ℤ) : knot (n + 1) = knot n + 2 ^ ex n := by
  unfold knot ex
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [if_pos (by omega), if_pos hn.le, if_pos hn]
    have : n + 1 - 1 = (n - 1) + 1 := by ring
    rw [this, zpow_add_one₀ two_ne_zero]
    ring
  · norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h1 : -(n + 1) - 1 = -n - 2 := by ring
    have h2 : -n - 1 = (-n - 2) + 1 := by ring
    rw [h1, h2, zpow_add_one₀ two_ne_zero]
    ring

lemma knot_pos (n : ℤ) : 0 < knot n := by
  unfold knot
  split_ifs with h
  · positivity
  · have : (2 : ℝ) ^ (-n - 1) < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by omega)
    linarith

lemma knot_lt_one (n : ℤ) : knot n < 1 := by
  unfold knot
  split_ifs with h
  · exact zpow_lt_one_of_neg₀ (by norm_num) (by omega)
  · have : (0 : ℝ) < 2 ^ (-n - 1) := by positivity
    linarith

lemma knot_strictMono : StrictMono knot :=
  strictMono_int_of_lt_succ fun n => by rw [knot_succ]; linarith [zpow_pos (two_pos (α := ℝ)) (ex n)]

/-- The increasing bijection `ℝ → (0,1)`, affine with slope `2 ^ ex n` on `[n, n+1]`. -/
noncomputable def alpha (y : ℝ) : ℝ := knot ⌊y⌋ + (y - ⌊y⌋) * 2 ^ ex ⌊y⌋

lemma knot_le_alpha (y : ℝ) : knot ⌊y⌋ ≤ alpha y := by
  unfold alpha
  have := Int.floor_le y
  have : (0 : ℝ) < 2 ^ ex ⌊y⌋ := by positivity
  nlinarith

lemma alpha_lt_knot (y : ℝ) : alpha y < knot (⌊y⌋ + 1) := by
  unfold alpha
  rw [knot_succ]
  have := Int.lt_floor_add_one y
  have : (0 : ℝ) < 2 ^ ex ⌊y⌋ := by positivity
  nlinarith

lemma alpha_strictMono : StrictMono alpha := by
  intro y z hyz
  rcases (Int.floor_mono hyz.le).eq_or_lt with h | h
  · unfold alpha
    rw [h]
    have : (0 : ℝ) < 2 ^ ex ⌊z⌋ := by positivity
    nlinarith
  · calc alpha y < knot (⌊y⌋ + 1) := alpha_lt_knot y
      _ ≤ knot ⌊z⌋ := knot_strictMono.monotone (by omega)
      _ ≤ alpha z := knot_le_alpha z

lemma alpha_mem (y : ℝ) : alpha y ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨(knot_pos _).trans_le (knot_le_alpha y), (alpha_lt_knot y).trans (knot_lt_one _)⟩

lemma alpha_surj {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : ∃ y, alpha y = t := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr ht1) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨k', hk'⟩ := exists_pow_lt_of_lt_one ht0 (by norm_num : (1 / 2 : ℝ) < 1)
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, knot z ≤ t → z ≤ b := by
    refine ⟨k, fun z hz => ?_⟩
    by_contra hzk
    push Not at hzk
    have hz0 : ¬ z ≤ 0 := by omega
    unfold knot at hz
    rw [if_neg hz0] at hz
    have : (2 : ℝ) ^ (-z - 1) ≤ (1 / 2) ^ k := by
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  have hne : ∃ z : ℤ, knot z ≤ t := by
    refine ⟨-(k' : ℤ), ?_⟩
    unfold knot
    rw [if_pos (by omega)]
    have : (2 : ℝ) ^ (-(k' : ℤ) - 1) ≤ (1 / 2) ^ k' := by
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  have hlt : t < knot (n + 1) := by
    by_contra h
    push Not at h
    have := hmax _ h
    omega
  rw [knot_succ] at hlt
  have hpos : (0 : ℝ) < 2 ^ ex n := by positivity
  set y : ℝ := n + (t - knot n) / 2 ^ ex n with hy
  have hfl : ⌊y⌋ = n := by
    rw [Int.floor_eq_iff]
    constructor
    · have : 0 ≤ (t - knot n) / 2 ^ ex n := div_nonneg (by linarith) hpos.le
      linarith
    · have : (t - knot n) / 2 ^ ex n < 1 := by rw [div_lt_one hpos]; linarith
      linarith
  refine ⟨y, ?_⟩
  unfold alpha
  rw [hfl, hy]
  field_simp
  ring

/-! ## Section 4: the dyadic affine group `Aff` -/
/-- `y ↦ 2ⁿ y + b` as an order isomorphism of `ℝ`. -/
noncomputable def affIso (n : ℤ) (b : ℝ) : ℝ ≃o ℝ :=
  (OrderIso.mulLeft₀ ((2 : ℝ) ^ n) (by positivity)).trans (OrderIso.addRight b)

@[simp] lemma affIso_apply (n : ℤ) (b y : ℝ) : affIso n b y = 2 ^ n * y + b := rfl

/-- A dyadic affine map `y ↦ 2ⁿ y + b`, `b` dyadic. -/
def IsDAffMap (f : ℝ ≃o ℝ) : Prop := ∃ (n : ℤ) (b : ℝ), IsDyadic b ∧ ∀ y, f y = 2 ^ n * y + b

/-- The dyadic affine group. -/
def Aff : Subgroup (ℝ ≃o ℝ) where
  carrier := {f | IsDAffMap f}
  mul_mem' := by
    rintro f g ⟨n, b, hb, hf⟩ ⟨m, b', hb', hg⟩
    refine ⟨n + m, 2 ^ n * b' + b, isDyadic_add (isDyadic_zpow_mul hb') hb, fun y => ?_⟩
    rw [RelIso.mul_apply, hg, hf, zpow_add₀ two_ne_zero]
    ring
  one_mem' := ⟨0, 0, isDyadic_zero, fun y => by simp [RelIso.one_apply]⟩
  inv_mem' := by
    rintro f ⟨n, b, hb, hf⟩
    refine ⟨-n, -(2 ^ (-n) * b), isDyadic_neg (isDyadic_zpow_mul hb), fun y => ?_⟩
    apply f.injective
    rw [RelIso.apply_inv_self, hf]
    have h2 : (2 : ℝ) ^ n * 2 ^ (-n) = 1 := by rw [← zpow_add₀ two_ne_zero]; simp
    linear_combination (b - y) * h2

lemma isDyadic_apply_zero (f : Aff) : IsDyadic ((f : ℝ ≃o ℝ) 0) := by
  obtain ⟨n, b, hb, hf⟩ := f.2
  rw [hf]; simpa using hb

lemma isDyadic_apply_one (f : Aff) : IsDyadic ((f : ℝ ≃o ℝ) 1) := by
  obtain ⟨n, b, hb, hf⟩ := f.2
  rw [hf, mul_one]; exact isDyadic_add (isDyadic_zpow n) hb

instance countable_Aff : Countable Aff := by
  have : Countable {x : ℝ // IsDyadic x} := countable_isDyadic.to_subtype
  refine Function.Injective.countable
    (f := fun f : Aff => ((⟨_, isDyadic_apply_zero f⟩ : {x : ℝ // IsDyadic x}),
      (⟨_, isDyadic_apply_one f⟩ : {x : ℝ // IsDyadic x}))) ?_
  intro f g hfg
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hfg
  obtain ⟨n, b, -, hf⟩ := f.2
  obtain ⟨m, b', -, hg⟩ := g.2
  rw [hf, hf, hg, hg] at hfg
  apply Subtype.ext; ext y
  rw [hf, hg]
  have hb : b = b' := by simpa using hfg.1
  have hn : (2 : ℝ) ^ n = 2 ^ m := by linarith [hfg.2]
  rw [hb, hn]

/-! ## Section 5: the conjugated action on `P¹` -/
/-- The data of the published conjugacy of `HRat` with Thompson's group `F`. -/
structure Conj where
  c : ℝ → ℝ
  mono : StrictMonoOn c (Set.Ioo 0 1)
  surj : c '' Set.Ioo 0 1 = Set.univ
  φ : Monod.HRat ≃* CannonFloydParry.F
  hφ : ∀ (h : Monod.HRat), ∀ t ∈ Set.Ioo (0 : ℝ) 1,
    (h : OnePoint ℝ ≃ₜ OnePoint ℝ) (c t : OnePoint ℝ) =
      (c (CannonFloydParry.extend (φ h : CannonFloydParry.UI ≃o CannonFloydParry.UI) t) :
        OnePoint ℝ)

end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
namespace Conj
variable (K : Conj)
lemma exists_eq (r : ℝ) : ∃ t ∈ Set.Ioo (0 : ℝ) 1, K.c t = r := by
  have : r ∈ K.c '' Set.Ioo 0 1 := by rw [K.surj]; trivial
  exact this

lemma psi_strictMono : StrictMono (K.c ∘ alpha) := fun _ _ h =>
  K.mono (alpha_mem _) (alpha_mem _) (alpha_strictMono h)

lemma psi_surj : Function.Surjective (K.c ∘ alpha) := by
  intro r
  obtain ⟨t, ht, rfl⟩ := K.exists_eq r
  obtain ⟨y, rfl⟩ := alpha_surj ht
  exact ⟨y, rfl⟩

/-- `Psi = c ∘ alpha`, an order isomorphism of `ℝ`. -/
noncomputable def Psi : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ K.psi_strictMono K.psi_surj

/-- Conjugation by `Psi`, then extension to `P¹`. -/
noncomputable def rho : (ℝ ≃o ℝ) →* Hom where
  toFun f := Homeomorph.onePointCongr (K.Psi.symm.trans (f.trans K.Psi)).toHomeomorph
  map_one' := by
    ext x
    induction x using OnePoint.rec <;> simp
  map_mul' f g := by
    ext x
    induction x using OnePoint.rec <;> simp

/-- The dyadic affine group acting on `P¹` through `Psi`. -/
noncomputable def Lam : Subgroup Hom := Aff.map K.rho

instance countable_Lam : Countable K.Lam :=
  (K.rho.subgroupMap_surjective Aff).countable

end Conj
end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
/-! ## Section 5b: `SL₂(ℚ)` is countable -/

/-! ## Section 6: the conull set `X1 = c '' (non-dyadic points)` -/
lemma volP1_singleton (x : OnePoint ℝ) : Monod.volP1 {x} = 0 := by
  unfold Monod.volP1
  rw [Measure.map_apply OnePoint.continuous_coe.measurable (measurableSet_singleton x)]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  exact OnePoint.coe_injective (ha.trans hb.symm)

instance : NullSingletonClass Monod.volP1 := ⟨volP1_singleton⟩

end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
namespace Conj
variable (K : Conj)

/-! ## Section 7: on `X1` the two orbit relations agree -/

/-! ## Section 8: `Lam` preserves null sets -/

end Conj
end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-! ## `volP1` is σ-finite -/

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
variable {X : Type*}
/-! ## Part E3: relations agreeing on a conull saturated set -/

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part E3: amenability passes between relations that agree on a conull saturated set -/

/-! ## Assembly -/

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
/-! ## Section 9: assembly -/

end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part E2: the orbit relation of `H_ℚ(ℤ)` is amenable -/

end ThompsonAmenability.M51
end

end
end

section
section
namespace RelativeZimmer

open scoped Pointwise

/-- The canonical map `Λ ⧸ Γ → (⊤ : Subgroup Λ) ⧸ Γ.subgroupOf ⊤`. -/
def toTopQuot {Λ : Type*} [Group Λ] (Γ : Subgroup Λ) :
    Λ ⧸ Γ → (⊤ : Subgroup Λ) ⧸ Γ.subgroupOf ⊤ :=
  Quotient.map' (fun x : Λ => (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup Λ))) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [Subgroup.mem_subgroupOf]
    exact hab)

theorem toTopQuot_smul {Λ : Type*} [Group Λ] (Γ : Subgroup Λ) (g : (⊤ : Subgroup Λ))
    (q : Λ ⧸ Γ) : toTopQuot Γ ((g : Λ) • q) = g • toTopQuot Γ q := by
  induction q using QuotientGroup.induction_on with
  | H x => rfl

/-- Coamenability of `Γ ≤ Λ` transfers to `Γ.subgroupOf ⊤ ≤ ⊤`. -/
theorem isCoamenable_subgroupOf_top {Λ : Type*} [Group Λ] (Γ : Subgroup Λ)
    (hco : Monod.IsCoamenable Γ) : Monod.IsCoamenable (Γ.subgroupOf ⊤) := by
  obtain ⟨m, ⟨hm0, hmadd⟩, hm1, hminv⟩ := hco
  refine ⟨fun s => m (toTopQuot Γ ⁻¹' s), ⟨by simpa using hm0, fun s t hst => ?_⟩, ?_, ?_⟩
  · show m _ = m _ + m _
    rw [Set.preimage_union]
    exact hmadd _ _ (hst.preimage _)
  · simpa using hm1
  · intro g s
    have : toTopQuot Γ ⁻¹' (g • s) = (g : Λ) • (toTopQuot Γ ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
      rw [← toTopQuot_smul]
      rfl
    show m _ = m _
    rw [this, hminv]

theorem isAmenableRel_orbit_of_isCoamenable {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    {Λ : Type*} [Group Λ] [Countable Λ] [MulAction Λ X] (Γ : Subgroup Λ)
    (hmeas : ∀ g : Λ, Measurable (fun x : X => g • x))
    (hnull : ∀ (g : Λ) (s : Set X), μ s = 0 → μ ((fun x : X => g • x) ⁻¹' s) = 0)
    (hco : Monod.IsCoamenable Γ)
    (hΓ : Monod.IsAmenableRel μ {p : X × X | ∃ g ∈ Γ, g • p.1 = p.2}) :
    Monod.IsAmenableRel μ {p : X × X | ∃ g : Λ, g • p.1 = p.2} := by
  refine ThompsonAmenability.M51.PartD.isAmenableRel_of_isCoamenable μ Γ ⊤ le_top
    (fun g _ => hmeas g) (fun g _ => hnull g) (isCoamenable_subgroupOf_top Γ hco) hΓ
    _ Set.univ MeasurableSet.univ (by simp) (fun _ _ => by simp)
    (fun g _ x _ => ⟨g, rfl⟩) Set.univ Set.countable_univ (fun g _ => Subgroup.mem_top g) ?_
  rintro p ⟨g, hg⟩ _
  exact ⟨g, Set.mem_univ _, hg⟩

end RelativeZimmer

end
end

section
open RelativeZimmer

theorem solution {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    {Λ : Type*} [Group Λ] [Countable Λ] [MulAction Λ X] (Γ : Subgroup Λ)
    (hmeas : ∀ g : Λ, Measurable (fun x : X => g • x))
    (hnull : ∀ (g : Λ) (s : Set X), μ s = 0 → μ ((fun x : X => g • x) ⁻¹' s) = 0)
    (hco : Monod.IsCoamenable Γ)
    (hΓ : Monod.IsAmenableRel μ {p : X × X | ∃ g ∈ Γ, g • p.1 = p.2}) :
    Monod.IsAmenableRel μ {p : X × X | ∃ g : Λ, g • p.1 = p.2} := by
  apply RelativeZimmer.isAmenableRel_orbit_of_isCoamenable <;> assumption

end
