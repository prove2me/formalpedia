-- Prove2me | solution 1 for SteinitzExchange.Duality.mconcave_intersection_optimality
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T21:31:33.419063+00:00
-- url     : https://prove2.me/submissions/d355a3cc-e7f9-4415-bc3a-18abd71fac0c

import Theorems.Thm_SteinitzExchange_Extension_exc_iff_argmax_isIntegralBaseSet
import Theorems.Thm_SteinitzExchange_Extension_exc_add_linear
import Theorems.Thm_SteinitzExchange_Extension_exists_perturb_hull_argmax
import Theorems.Thm_SteinitzExchange_Duality_baseSet_iff_submodular_system
import Theorems.Thm_SteinitzExchange_Duality_frank_separation_integer
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

/- This proof reuses the proved Murota extension, support, base-characterization, and integer
Frank results through their public theorem statements. The accepted perturbation formalization is by WillR;
the Extension 4.4 reduction is due to choi with dependencies by mrfancypants and our geometric
leaves. No private implementation helper from an imported platform theorem is assumed. -/

/- Component: SteinitzHullIntersection -/
section

set_option autoImplicit false

open scoped BigOperators
open SteinitzExchange.Duality

namespace SteinitzIntersection

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def IntegerSandwichProperty (V : Type*) [Fintype V] [DecidableEq V] : Prop :=
  ∀ f g : Finset V → ℤ, IsSubmodular f → IsSupermodular g → f ∅ = 0 → g ∅ = 0 →
    (∀ S, g S ≤ f S) → ∃ z : V → ℤ, ∀ S, g S ≤ (∑ i ∈ S, z i) ∧ (∑ i ∈ S, z i) ≤ f S

lemma realSum_linear (S : Finset V) : IsLinearMap ℝ (fun z : V → ℝ => ∑ i ∈ S, z i) := by
  constructor
  · intro x y
    simp [Finset.sum_add_distrib]
  · intro a x
    simp [Finset.mul_sum]

lemma hull_sum_le {B : Finset (V → ℤ)} (S : Finset V) (r : ℤ)
    (h : ∀ x ∈ B, sumOn x S ≤ r) {c : V → ℝ} (hc : c ∈ hull B) :
    (∑ i ∈ S, c i) ≤ (r : ℝ) := by
  apply convexHull_min (t := {z : V → ℝ | (∑ i ∈ S, z i) ≤ (r : ℝ)}) ?_
    (convex_halfSpace_le (realSum_linear S) (r : ℝ)) hc
  rintro _ ⟨x, hx, rfl⟩
  have hi := h x hx
  change (∑ i ∈ S, (x i : ℝ)) ≤ (r : ℝ)
  unfold sumOn at hi
  exact_mod_cast hi

lemma hull_sum_ge {B : Finset (V → ℤ)} (S : Finset V) (r : ℤ)
    (h : ∀ x ∈ B, r ≤ sumOn x S) {c : V → ℝ} (hc : c ∈ hull B) :
    (r : ℝ) ≤ ∑ i ∈ S, c i := by
  apply convexHull_min (t := {z : V → ℝ | (r : ℝ) ≤ ∑ i ∈ S, z i}) ?_
    (convex_halfSpace_ge (realSum_linear S) (r : ℝ)) hc
  rintro _ ⟨x, hx, rfl⟩
  have hi := h x hx
  change (r : ℝ) ≤ ∑ i ∈ S, (x i : ℝ)
  unfold sumOn at hi
  exact_mod_cast hi

lemma hull_sum_eq {B : Finset (V → ℤ)} (S : Finset V) (r : ℤ)
    (h : ∀ x ∈ B, sumOn x S = r) {c : V → ℝ} (hc : c ∈ hull B) :
    (∑ i ∈ S, c i) = (r : ℝ) :=
  le_antisymm (hull_sum_le S r (fun x hx => (h x hx).le) hc)
    (hull_sum_ge S r (fun x hx => (h x hx).ge) hc)

/-- Integer Frank separation upgrades a common real hull point of finite integral bases
into a common lattice base. The separation hypothesis will be supplied by the checked generic
coordinate-elimination theorem; there is no assumed lattice-intersection property. -/
theorem common_integer_of_hull_intersect (hseparator : IntegerSandwichProperty V)
    {B₁ B₂ : Finset (V → ℤ)} (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    {c : V → ℝ} (hc₁ : c ∈ hull B₁) (hc₂ : c ∈ hull B₂) :
    ∃ z : V → ℤ, z ∈ B₁ ∧ z ∈ B₂ := by
  obtain ⟨f, hf, hf0, hrep₁⟩ := (SteinitzExchange.Duality.baseSet_iff_submodular_system B₁ hB₁.1).1.mp hB₁
  obtain ⟨g, hg, hg0, hrep₂⟩ := (SteinitzExchange.Duality.baseSet_iff_submodular_system B₂ hB₂.1).2.1.mp hB₂
  have hupper : ∀ S, (∑ i ∈ S, c i) ≤ (f S : ℝ) := by
    intro S
    exact hull_sum_le S (f S) (fun x hx => ((hrep₁ x).mp hx).1 S) hc₁
  have hlower : ∀ S, (g S : ℝ) ≤ ∑ i ∈ S, c i := by
    intro S
    exact hull_sum_ge S (g S) (fun x hx => ((hrep₂ x).mp hx).1 S) hc₂
  have htotal₁ : (∑ i ∈ Finset.univ, c i) = (f Finset.univ : ℝ) :=
    hull_sum_eq Finset.univ (f Finset.univ) (fun x hx => ((hrep₁ x).mp hx).2) hc₁
  have htotal₂ : (∑ i ∈ Finset.univ, c i) = (g Finset.univ : ℝ) :=
    hull_sum_eq Finset.univ (g Finset.univ) (fun x hx => ((hrep₂ x).mp hx).2) hc₂
  have htot : f Finset.univ = g Finset.univ := by exact_mod_cast htotal₁.symm.trans htotal₂
  have hgf : ∀ S, g S ≤ f S := by
    intro S
    exact_mod_cast (hlower S).trans (hupper S)
  obtain ⟨z, hz⟩ := hseparator f g hf hg hf0 hg0 hgf
  have hztot : (∑ i, z i) = f Finset.univ := by
    have h := hz Finset.univ
    rw [← htot] at h
    exact le_antisymm h.2 h.1
  refine ⟨z, (hrep₁ z).mpr ⟨fun S => (hz S).2, hztot⟩,
    (hrep₂ z).mpr ⟨fun S => (hz S).1, ?_⟩⟩
  exact hztot.trans htot

#print axioms common_integer_of_hull_intersect

end SteinitzIntersection
end


/- Component: SteinitzLocalOptimality -/
section

set_option autoImplicit false

open scoped BigOperators


open scoped BigOperators

namespace SteinitzIntersectionMetric

open SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem base_eq_of_coordinatewise_le {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (hxy : ∀ w, x w ≤ y w) : x = y := by
  ext u
  by_contra hne
  have hu : 0 < (y - x) u := by
    change 0 < y u - x u
    have := hxy u
    omega
  obtain ⟨v, hv, _⟩ := hB.2 y hy x hx u hu
  change y v - x v < 0 at hv
  have := hxy v
  omega

def positiveDeviation (x y : V → ℤ) : ℤ :=
  ∑ w, max (x w - y w) 0

theorem positiveDeviation_exchange (x y : V → ℤ) (u v : V)
    (hu : 0 < (x - y) u) (hv : (x - y) v < 0) :
    positiveDeviation (x - chi u + chi v) y = positiveDeviation x y - 1 := by
  have huv : u ≠ v := by
    intro h
    subst v
    omega
  have hpoint : ∀ w, max ((x - chi u + chi v) w - y w) 0 =
      max (x w - y w) 0 - (if w = u then 1 else 0) := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
        if_pos rfl, if_neg huv, sub_self]
      change 0 < x u - y u at hu
      omega
    · by_cases hwv : w = v
      · subst w
        simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
          if_pos rfl, if_neg hwu, sub_zero]
        change x v - y v < 0 at hv
        omega
      · simp [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply, hwu, hwv]
  simp only [positiveDeviation, hpoint, Finset.sum_sub_distrib]
  simp

end SteinitzIntersectionMetric

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For an M-concave function on a finite integral base, unit-exchange local optimality is global. -/
theorem local_maximum_is_global {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω)
    (xs : V → ℤ) (hxs : xs ∈ B)
    (hloc : ∀ u v : V, xs - chi u + chi v ∈ B → ω (xs - chi u + chi v) ≤ ω xs) :
    ∀ y ∈ B, ω y ≤ ω xs := by
  classical
  intro y hy
  by_contra hbad
  let S := B.filter (fun z => ω xs < ω z)
  have hS : S.Nonempty := ⟨y, Finset.mem_filter.mpr ⟨hy, lt_of_not_ge hbad⟩⟩
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image S (fun z => SteinitzIntersectionMetric.positiveDeviation z xs) hS
  have hzB : z ∈ B := (Finset.mem_filter.mp hz).1
  have hzbad : ω xs < ω z := (Finset.mem_filter.mp hz).2
  have hzle : ∀ u, z u ≤ xs u := by
    intro u
    by_contra hnot
    have hu : 0 < (z - xs) u := by
      change 0 < z u - xs u
      omega
    obtain ⟨v, hv, hz', hxs', hex⟩ := hω z hzB xs hxs u hu
    have heq : xs + chi u - chi v = xs - chi v + chi u := by abel
    rw [heq] at hxs' hex
    have hl := hloc v u hxs'
    have hzbad' : ω xs < ω (z - chi u + chi v) := by linarith
    have hmem : z - chi u + chi v ∈ S := Finset.mem_filter.mpr ⟨hz', hzbad'⟩
    have hmin' := hmin _ hmem
    rw [SteinitzIntersectionMetric.positiveDeviation_exchange z xs u v hu hv] at hmin'
    omega
  have hzx : z = xs := SteinitzIntersectionMetric.base_eq_of_coordinatewise_le hB hzB hxs hzle
  subst z
  exact (lt_irrefl _ hzbad)

/-- Flooring a real potential preserves every integral lower bound on a coordinate difference. -/
theorem floor_preserves_integer_difference (p : V → ℝ) (u v : V) (k : ℤ)
    (h : (k : ℝ) ≤ p u - p v) :
    k ≤ Int.floor (p u) - Int.floor (p v) := by
  have h' : p v + (k : ℝ) ≤ p u := by linarith
  have hf := Int.floor_mono h'
  rw [Int.floor_add_intCast] at hf
  omega

#print axioms local_maximum_is_global
#print axioms floor_preserves_integer_difference

end SteinitzExchange.Extension

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pairing_unit_exchange (p : V → ℝ) (x : V → ℤ) (u v : V) :
    pairing p (toReal (x - chi u + chi v)) = pairing p (toReal x) - p u + p v := by
  classical
  simp [pairing, toReal, chi, Pi.single_apply, Pi.sub_apply, Pi.add_apply,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite]

/-- Any change of potential preserving integral coordinate-difference bounds preserves maximizers
of integral-valued M-concave functions. This applies to flooring, with either potential sign. -/
theorem integer_potential_rounding [Nonempty V] {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω)
    (hwint : ∀ x ∈ B, ∃ k : ℤ, ω x = k)
    (xs : V → ℤ) (hxs : xs ∈ B) (p q : V → ℝ)
    (hpq : ∀ u v : V, ∀ k : ℤ, (k : ℝ) ≤ p u - p v → (k : ℝ) ≤ q u - q v)
    (hmax : ∀ x ∈ B, perturb ω p x ≤ perturb ω p xs) :
    ∀ x ∈ B, perturb ω q x ≤ perturb ω q xs := by
  apply local_maximum_is_global hB (perturb ω q) (exc_add_linear B hB ω hω q) xs hxs
  intro u v hx'
  obtain ⟨k, hk⟩ := hwint (xs - chi u + chi v) hx'
  obtain ⟨ks, hks⟩ := hwint xs hxs
  have hp := hmax (xs - chi u + chi v) hx'
  simp only [perturb, pairing_unit_exchange] at hp ⊢
  have hdiff : ((k - ks : ℤ) : ℝ) ≤ p u - p v := by
    rw [Int.cast_sub]
    rw [hk, hks] at hp
    linarith
  have hq := hpq u v (k - ks) hdiff
  rw [Int.cast_sub] at hq
  rw [hk, hks]
  linarith

#print axioms pairing_unit_exchange
#print axioms integer_potential_rounding

end SteinitzExchange.Extension
end


/- Component: SteinitzPairedSupport -/
section

set_option autoImplicit false

open scoped BigOperators Pointwise
open SteinitzExchange.Extension

namespace SteinitzIntersection

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma paired_score (ω₁ ω₂ : (V → ℤ) → ℝ) (p : V → ℝ) (x y : V → ℤ) :
    ω₁ x + ω₂ y + (∑ v, p v * (toReal x - toReal y) v) =
      perturb ω₁ p x + perturb ω₂ (-p) y := by
  simp only [perturb, pairing, Pi.sub_apply, Pi.neg_apply, mul_sub, neg_mul,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

lemma toReal_sub_pair (x y : V → ℤ) : toReal (x-y) = toReal x - toReal y := by
  ext v
  simp [toReal]

/-- Apply the proved support theorem to the integer difference set. On each difference fiber,
use the maximum pair score, so duplicate differences retain the correct exposed maximizers. -/
theorem exists_paired_support {B₁ B₂ : Finset (V → ℤ)}
    (ω₁ ω₂ : (V → ℤ) → ℝ) (xs : V → ℤ) (hx₁ : xs ∈ B₁) (hx₂ : xs ∈ B₂) :
    ∃ p : V → ℝ, ∃ c : V → ℝ,
      c ∈ hull (argmaxB B₁ (perturb ω₁ (-p))) ∧
      c ∈ hull (argmaxB B₂ (perturb ω₂ p)) := by
  classical
  let P := B₁.product B₂
  let D : Finset (V → ℤ) := P.image (fun a => a.1 - a.2)
  let fiber : (V → ℤ) → Finset ((V → ℤ) × (V → ℤ)) := fun d =>
    P.filter (fun a => a.1 - a.2 = d)
  let score : ((V → ℤ) × (V → ℤ)) → ℝ := fun a => ω₁ a.1 + ω₂ a.2
  let g : (V → ℤ) → ℝ := fun d =>
    if h : (fiber d).Nonempty then (fiber d).sup' h score else 0
  have hscore : ∀ a ∈ P, score a ≤ g (a.1 - a.2) := by
    intro a ha
    have hmem : a ∈ fiber (a.1 - a.2) := Finset.mem_filter.mpr ⟨ha, rfl⟩
    have hne : (fiber (a.1 - a.2)).Nonempty := ⟨a, hmem⟩
    dsimp only [g]
    rw [dif_pos hne]
    exact Finset.le_sup' score hmem
  have hattain : ∀ d ∈ D, ∃ a ∈ P, a.1 - a.2 = d ∧ g d = score a := by
    intro d hd
    obtain ⟨a, ha, had⟩ := Finset.mem_image.mp hd
    have hne : (fiber d).Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, had⟩⟩
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (fiber d) score hne
    refine ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2, ?_⟩
    dsimp only [g]
    rw [dif_pos hne]
    exact le_antisymm (Finset.sup'_le hne score hmax) (Finset.le_sup' score ha)
  have hzeroD : (0 : V → ℤ) ∈ D := Finset.mem_image.mpr
    ⟨(xs,xs), Finset.mem_product.mpr ⟨hx₁,hx₂⟩, sub_self xs⟩
  have hzero : (0 : V → ℝ) ∈ hull D := by
    have h : toReal (0 : V → ℤ) ∈ hull D :=
      subset_convexHull ℝ _ ⟨0, hzeroD, rfl⟩
    have hz : SteinitzExchange.Extension.toReal (0 : V → ℤ) = (0 : V → ℝ) := by
      funext v
      change ((0 : ℤ) : ℝ) = 0
      exact Int.cast_zero
    exact hz ▸ h
  obtain ⟨q, hq⟩ := exists_perturb_hull_argmax D ⟨0,hzeroD⟩ g 0 hzero
  let A₁ := argmaxB B₁ (perturb ω₁ q)
  let A₂ := argmaxB B₂ (perturb ω₂ (-q))
  have hsub : toReal '' (argmaxB D (perturb g q) : Set (V → ℤ)) ⊆ hull A₁ - hull A₂ := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hdD, hdmax⟩ := Finset.mem_filter.mp hd
    obtain ⟨a, ha, had, hga⟩ := hattain d hdD
    have haP := Finset.mem_product.mp ha
    have hae : perturb g q d = perturb ω₁ q a.1 + perturb ω₂ (-q) a.2 := by
      calc
        perturb g q d = score a + pairing q (toReal (a.1 - a.2)) := by
          rw [perturb, hga, had]
        _ = perturb ω₁ q a.1 + perturb ω₂ (-q) a.2 := by
          simpa only [score, pairing, toReal_sub_pair] using paired_score ω₁ ω₂ q a.1 a.2
    have hpair : ∀ b ∈ P, perturb ω₁ q b.1 + perturb ω₂ (-q) b.2 ≤
        perturb ω₁ q a.1 + perturb ω₂ (-q) a.2 := by
      intro b hb
      have hlow : perturb ω₁ q b.1 + perturb ω₂ (-q) b.2 ≤ perturb g q (b.1 - b.2) := by
        rw [← paired_score]
        have h := add_le_add_right (hscore b hb) (pairing q (toReal (b.1 - b.2)))
        simpa only [score, perturb, toReal_sub_pair, pairing, add_comm] using h
      have hhigh := hdmax (b.1 - b.2) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
      exact hlow.trans (hhigh.trans_eq hae)
    have hA₁ : a.1 ∈ A₁ := by
      apply Finset.mem_filter.mpr
      refine ⟨haP.1, ?_⟩
      intro x hx
      have h := hpair (x,a.2) (Finset.mem_product.mpr ⟨hx,haP.2⟩)
      exact (add_le_add_iff_right _).mp h
    have hA₂ : a.2 ∈ A₂ := by
      apply Finset.mem_filter.mpr
      refine ⟨haP.2, ?_⟩
      intro y hy
      have h := hpair (a.1,y) (Finset.mem_product.mpr ⟨haP.1,hy⟩)
      exact (add_le_add_iff_left _).mp h
    refine Set.mem_sub.mpr ⟨toReal a.1, subset_convexHull ℝ _ ⟨_,hA₁,rfl⟩,
      toReal a.2, subset_convexHull ℝ _ ⟨_,hA₂,rfl⟩, ?_⟩
    rw [← toReal_sub_pair, had]
  have hzero' : (0 : V → ℝ) ∈ hull A₁ - hull A₂ :=
    convexHull_min hsub ((convex_convexHull ℝ _).sub (convex_convexHull ℝ _)) hq
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.mp hzero'
  have hab' : a = b := sub_eq_zero.mp hab
  refine ⟨-q, a, ?_, ?_⟩
  · simpa only [neg_neg] using ha
  · simpa only [hab'] using hb

#print axioms exists_paired_support

end SteinitzIntersection
end


/- Component: SteinitzIntersectionOptimality -/
section

set_option autoImplicit false

open scoped BigOperators
open SteinitzExchange.Extension

namespace SteinitzIntersection

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma perturb_pair_cancel (ω₁ ω₂ : (V → ℤ) → ℝ) (p : V → ℝ) (x : V → ℤ) :
    perturb ω₁ (-p) x + perturb ω₂ p x = ω₁ x + ω₂ x := by
  simp only [perturb, pairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

theorem real_intersection_potential (hseparator : IntegerSandwichProperty V)
    {B₁ B₂ : Finset (V → ℤ)} (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω₁ ω₂ : (V → ℤ) → ℝ) (hω₁ : SatisfiesEXC B₁ ω₁) (hω₂ : SatisfiesEXC B₂ ω₂)
    (xs : V → ℤ) (hx₁ : xs ∈ B₁) (hx₂ : xs ∈ B₂)
    (hopt : ∀ x ∈ B₁, x ∈ B₂ → ω₁ x + ω₂ x ≤ ω₁ xs + ω₂ xs) :
    ∃ p : V → ℝ, (∀ x ∈ B₁, perturb ω₁ (-p) x ≤ perturb ω₁ (-p) xs) ∧
      (∀ x ∈ B₂, perturb ω₂ p x ≤ perturb ω₂ p xs) := by
  classical
  obtain ⟨p, c, hc₁, hc₂⟩ := exists_paired_support ω₁ ω₂ xs hx₁ hx₂
  have hA₁ := (exc_iff_argmax_isIntegralBaseSet B₁ hB₁ ω₁).mp hω₁ (-p)
  have hA₂ := (exc_iff_argmax_isIntegralBaseSet B₂ hB₂ ω₂).mp hω₂ p
  obtain ⟨z, hz₁, hz₂⟩ := common_integer_of_hull_intersect hseparator hA₁ hA₂ hc₁ hc₂
  obtain ⟨hzB₁, hzmax₁⟩ := Finset.mem_filter.mp hz₁
  obtain ⟨hzB₂, hzmax₂⟩ := Finset.mem_filter.mp hz₂
  have hs₁ := hzmax₁ xs hx₁
  have hs₂ := hzmax₂ xs hx₂
  have hsum : perturb ω₁ (-p) z + perturb ω₂ p z ≤
      perturb ω₁ (-p) xs + perturb ω₂ p xs := by
    rw [perturb_pair_cancel, perturb_pair_cancel]
    exact hopt z hzB₁ hzB₂
  refine ⟨p, ?_, ?_⟩
  · intro x hx
    have h := hzmax₁ x hx
    linarith
  · intro x hx
    have h := hzmax₂ x hx
    linarith

/-- The opposite signs of one potential can be rounded together: both directions of every
integral coordinate-difference inequality are preserved by coordinatewise floor. -/
theorem integral_intersection_potential (hseparator : IntegerSandwichProperty V)
    {B₁ B₂ : Finset (V → ℤ)} (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω₁ ω₂ : (V → ℤ) → ℝ) (hω₁ : SatisfiesEXC B₁ ω₁) (hω₂ : SatisfiesEXC B₂ ω₂)
    (hwint₁ : ∀ x ∈ B₁, ∃ k : ℤ, ω₁ x = k) (hwint₂ : ∀ x ∈ B₂, ∃ k : ℤ, ω₂ x = k)
    (xs : V → ℤ) (hx₁ : xs ∈ B₁) (hx₂ : xs ∈ B₂)
    (hopt : ∀ x ∈ B₁, x ∈ B₂ → ω₁ x + ω₂ x ≤ ω₁ xs + ω₂ xs) :
    ∃ p : V → ℤ, (∀ x ∈ B₁, perturb ω₁ (-toReal p) x ≤ perturb ω₁ (-toReal p) xs) ∧
      (∀ x ∈ B₂, perturb ω₂ (toReal p) x ≤ perturb ω₂ (toReal p) xs) := by
  obtain ⟨p, hp₁, hp₂⟩ := real_intersection_potential hseparator hB₁ hB₂ ω₁ ω₂ hω₁ hω₂ xs hx₁ hx₂ hopt
  let q : V → ℤ := fun v => Int.floor (p v)
  have hround : ∀ u v : V, ∀ k : ℤ, (k : ℝ) ≤ p u - p v →
      (k : ℝ) ≤ toReal q u - toReal q v := by
    intro u v k hk
    have h := floor_preserves_integer_difference p u v k hk
    change (k : ℝ) ≤ (Int.floor (p u) : ℝ) - (Int.floor (p v) : ℝ)
    exact_mod_cast h
  have hroundneg : ∀ u v : V, ∀ k : ℤ, (k : ℝ) ≤ (-p) u - (-p) v →
      (k : ℝ) ≤ (-toReal q) u - (-toReal q) v := by
    intro u v k hk
    have h := hround v u k (by simpa only [Pi.neg_apply, neg_sub_neg] using hk)
    simpa only [Pi.neg_apply, neg_sub_neg] using h
  exact ⟨q, integer_potential_rounding hB₁ ω₁ hω₁ hwint₁ xs hx₁ (-p) (-toReal q) hroundneg hp₁,
    integer_potential_rounding hB₂ ω₂ hω₂ hwint₂ xs hx₂ p (toReal q) hround hp₂⟩

#print axioms real_intersection_potential
#print axioms integral_intersection_potential


theorem intersection_optimality_of_integer_sandwich (hseparator : IntegerSandwichProperty V)
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω₁ ω₂ : (V → ℤ) → ℝ) (hω₁ : SatisfiesEXC B₁ ω₁) (hω₂ : SatisfiesEXC B₂ ω₂)
    (xs : V → ℤ) (hx₁ : xs ∈ B₁) (hx₂ : xs ∈ B₂) :
    ((∀ x ∈ B₁, x ∈ B₂ → ω₁ x + ω₂ x ≤ ω₁ xs + ω₂ xs) ↔
      ∃ p : V → ℝ, (∀ x ∈ B₁, perturb ω₁ (-p) x ≤ perturb ω₁ (-p) xs) ∧
        (∀ x ∈ B₂, perturb ω₂ p x ≤ perturb ω₂ p xs)) ∧
    ((∀ x ∈ B₁, ∃ k : ℤ, ω₁ x = k) → (∀ x ∈ B₂, ∃ k : ℤ, ω₂ x = k) →
      (∀ x ∈ B₁, x ∈ B₂ → ω₁ x + ω₂ x ≤ ω₁ xs + ω₂ xs) →
      ∃ p : V → ℤ, (∀ x ∈ B₁, perturb ω₁ (-toReal p) x ≤ perturb ω₁ (-toReal p) xs) ∧
        (∀ x ∈ B₂, perturb ω₂ (toReal p) x ≤ perturb ω₂ (toReal p) xs)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact real_intersection_potential hseparator hB₁ hB₂ ω₁ ω₂ hω₁ hω₂ xs hx₁ hx₂
  · rintro ⟨p, hp₁, hp₂⟩ x hx₁' hx₂'
    have h := add_le_add (hp₁ x hx₁') (hp₂ x hx₂')
    simpa only [perturb_pair_cancel] using h
  · intro hi₁ hi₂ ho
    exact integral_intersection_potential hseparator hB₁ hB₂ ω₁ ω₂ hω₁ hω₂ hi₁ hi₂ xs hx₁ hx₂ ho

#print axioms intersection_optimality_of_integer_sandwich

end SteinitzIntersection
end


/- Component: SteinitzPublicIntegerSandwich -/
section

set_option autoImplicit false

namespace SteinitzIntersectionFrank

open Finset SteinitzExchange.Duality

/-- This bridge uses only the public theorem exported by the tracked platform
    module, so downstream proofs do not require private helper declarations. -/
theorem integer_sandwich {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (f g : Finset V → ℤ) (hf : IsSubmodular f) (hg : IsSupermodular g)
    (hf0 : f ∅ = 0) (hg0 : g ∅ = 0) (hgf : ∀ X : Finset V, g X ≤ f X) :
    ∃ x : V → ℤ, ∀ X : Finset V,
      g X ≤ ∑ v ∈ X, x v ∧ (∑ v ∈ X, x v) ≤ f X := by
  let fR : Finset V → ℝ := fun X => (f X : ℝ)
  let gR : Finset V → ℝ := fun X => (g X : ℝ)
  have hfR : IsSubmodular fR := by
    intro X Y
    change (f (X ∪ Y) : ℝ) + (f (X ∩ Y) : ℝ) ≤ (f X : ℝ) + (f Y : ℝ)
    exact_mod_cast hf X Y
  have hgR : IsSupermodular gR := by
    intro X Y
    change (g X : ℝ) + (g Y : ℝ) ≤ (g (X ∪ Y) : ℝ) + (g (X ∩ Y) : ℝ)
    exact_mod_cast hg X Y
  have hfR0 : fR ∅ = 0 := by simp [fR, hf0]
  have hgR0 : gR ∅ = 0 := by simp [gR, hg0]
  have hgfR : ∀ X, gR X ≤ fR X := by
    intro X
    change (g X : ℝ) ≤ (f X : ℝ)
    exact_mod_cast hgf X
  obtain ⟨x, hx⟩ := frank_separation_integer fR gR hfR hgR hfR0 hgR0 hgfR
    (fun X => ⟨f X, rfl⟩) (fun X => ⟨g X, rfl⟩)
  refine ⟨x, fun X => ?_⟩
  have h := hx X
  change (g X : ℝ) ≤ ((∑ v ∈ X, x v : ℤ) : ℝ) ∧
    ((∑ v ∈ X, x v : ℤ) : ℝ) ≤ (f X : ℝ) at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

#print axioms integer_sandwich

end SteinitzIntersectionFrank
end


/- Component: SteinitzIntersectionIntegerAdapter -/
section

set_option autoImplicit false

namespace SteinitzIntersection

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Use the standalone public-theorem cast adapter, shared with the dual-boundedness proof. -/
theorem integer_sandwich_of_public_frank : IntegerSandwichProperty V :=
  fun f g hf hg hf0 hg0 hgf => SteinitzIntersectionFrank.integer_sandwich f g hf hg hf0 hg0 hgf

#print axioms integer_sandwich_of_public_frank

end SteinitzIntersection
end


/- Component: Sol_Steinitz_IntersectionOptimality -/
section

set_option autoImplicit false

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : SteinitzExchange.Duality.IsIntegralBaseSet B₁)
    (hB₂ : SteinitzExchange.Duality.IsIntegralBaseSet B₂)
    (ω₁ ω₂ : (V → ℤ) → ℝ) (hω₁ : SteinitzExchange.Duality.SatisfiesEXC B₁ ω₁)
    (hω₂ : SteinitzExchange.Duality.SatisfiesEXC B₂ ω₂)
    (xs : V → ℤ) (hx₁ : xs ∈ B₁) (hx₂ : xs ∈ B₂) :
    ((∀ x ∈ B₁, x ∈ B₂ → ω₁ x + ω₂ x ≤ ω₁ xs + ω₂ xs) ↔
      ∃ p : V → ℝ,
        (∀ x ∈ B₁, SteinitzExchange.Duality.perturb ω₁ (-p) x ≤ SteinitzExchange.Duality.perturb ω₁ (-p) xs) ∧
        (∀ x ∈ B₂, SteinitzExchange.Duality.perturb ω₂ p x ≤ SteinitzExchange.Duality.perturb ω₂ p xs)) ∧
    ((∀ x ∈ B₁, ∃ k : ℤ, ω₁ x = k) → (∀ x ∈ B₂, ∃ k : ℤ, ω₂ x = k) →
      (∀ x ∈ B₁, x ∈ B₂ → ω₁ x + ω₂ x ≤ ω₁ xs + ω₂ xs) →
      ∃ p : V → ℤ,
        (∀ x ∈ B₁, SteinitzExchange.Duality.perturb ω₁ (-SteinitzExchange.Duality.toReal p) x ≤
          SteinitzExchange.Duality.perturb ω₁ (-SteinitzExchange.Duality.toReal p) xs) ∧
        (∀ x ∈ B₂, SteinitzExchange.Duality.perturb ω₂ (SteinitzExchange.Duality.toReal p) x ≤
          SteinitzExchange.Duality.perturb ω₂ (SteinitzExchange.Duality.toReal p) xs)) := by
  exact SteinitzIntersection.intersection_optimality_of_integer_sandwich
    SteinitzIntersection.integer_sandwich_of_public_frank B₁ B₂ hB₁ hB₂ ω₁ ω₂ hω₁ hω₂ xs hx₁ hx₂

#print axioms solution
end

