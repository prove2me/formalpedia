-- Prove2me | solution 1 for SteinitzExchange.Duality.dual_bounded_iff
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T21:36:40.180292+00:00
-- url     : https://prove2.me/submissions/552324aa-4b61-488d-949a-1feca409f5dd

import Mathlib.Data.EReal.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Definitions.Def_SteinitzExchange_Duality_Conjugate
import Mathlib.Tactic.Ring
import Definitions.Def_SteinitzExchange_Duality_Problems
import Theorems.Thm_SteinitzExchange_Duality_baseSet_iff_submodular_system
import Theorems.Thm_SteinitzExchange_Duality_frank_separation_integer

set_option autoImplicit false

/- Verified-component candidate: CoordinatorDualBounds.lean -/

namespace SteinitzDualBounds

lemma inf_ne_bot_of_lower {ι : Type*} (f : ι → ℝ) (a : ℝ)
    (ha : ∀ i, a ≤ f i) : (⨅ i, (f i : EReal)) ≠ ⊥ := by
  have hle : (a : EReal) ≤ ⨅ i, (f i : EReal) :=
    le_iInf (fun i => EReal.coe_le_coe_iff.mpr (ha i))
  exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe a) hle)

lemma inf_eq_bot_of_negative_ray {ι : Type*} (f : ι → ℝ) (p : ℕ → ι)
    (d C : ℝ) (hd : d < 0) (hp : ∀ n, f (p n) ≤ (n : ℝ) * d + C) :
    (⨅ i, (f i : EReal)) = ⊥ := by
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - y) / (-d))
  have hdpos : 0 < -d := neg_pos.mpr hd
  have hmul := (div_lt_iff₀ hdpos).mp hn
  have hlinear : (n : ℝ) * d + C < y := by nlinarith
  exact lt_of_le_of_lt (iInf_le _ (p n))
    (EReal.coe_lt_coe_iff.mpr (lt_of_le_of_lt (hp n) hlinear))

lemma finite_gap_ray_bound {ι κ : Type*} [Finite ι] [Finite κ] [Nonempty ι] [Nonempty κ]
    (a ω : ι → ℝ) (b ζ : κ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (⨆ j, t * b j - ζ j) - (⨅ i, t * a i - ω i) ≤
      t * ((⨆ j, b j) - (⨅ i, a i)) + ((⨆ i, ω i) - (⨅ j, ζ j)) := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j => t * b j - ζ j)
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => t * a i - ω i)
  rw [← hj, ← hi]
  have hbj : b j ≤ ⨆ j, b j := le_ciSup (Set.finite_range b).bddAbove j
  have hai : (⨅ i, a i) ≤ a i := ciInf_le (Set.finite_range a).bddBelow i
  have hωi : ω i ≤ ⨆ i, ω i := le_ciSup (Set.finite_range ω).bddAbove i
  have hζj : (⨅ j, ζ j) ≤ ζ j := ciInf_le (Set.finite_range ζ).bddBelow j
  have htb := mul_le_mul_of_nonneg_left hbj ht
  have hta := mul_le_mul_of_nonneg_left hai ht
  nlinarith

lemma finite_gap_ge_at {ι κ : Type*} [Finite ι] [Finite κ] [Nonempty ι] [Nonempty κ]
    (a ω : ι → ℝ) (b ζ : κ → ℝ) (i : ι) (j : κ) (hab : a i = b j) :
    ω i - ζ j ≤ (⨆ j, b j - ζ j) - (⨅ i, a i - ω i) := by
  have hj : b j - ζ j ≤ ⨆ j, b j - ζ j :=
    le_ciSup (Set.finite_range (fun j => b j - ζ j)).bddAbove j
  have hi : (⨅ i, a i - ω i) ≤ a i - ω i :=
    ciInf_le (Set.finite_range (fun i => a i - ω i)).bddBelow i
  linarith

lemma finite_gap_ge_support {ι κ : Type*} [Finite ι] [Finite κ] [Nonempty ι] [Nonempty κ]
    (a ω : ι → ℝ) (b ζ : κ → ℝ) :
    ((⨆ j, b j) - (⨅ i, a i)) + ((⨅ i, ω i) - (⨆ j, ζ j)) ≤
      (⨆ j, b j - ζ j) - (⨅ i, a i - ω i) := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := a)
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := b)
  rw [← hi, ← hj]
  have hbj : b j - ζ j ≤ ⨆ j, b j - ζ j :=
    le_ciSup (Set.finite_range (fun j => b j - ζ j)).bddAbove j
  have hai : (⨅ i, a i - ω i) ≤ a i - ω i :=
    ciInf_le (Set.finite_range (fun i => a i - ω i)).bddBelow i
  have hωi : (⨅ i, ω i) ≤ ω i := ciInf_le (Set.finite_range ω).bddBelow i
  have hζj : ζ j ≤ ⨆ j, ζ j := le_ciSup (Set.finite_range ζ).bddAbove j
  linarith

#print axioms finite_gap_ge_support

lemma ciSup_cast_finset_sup {α : Type*} (B : Finset α) (hne : B.Nonempty) (f : α → ℤ) :
    (⨆ x : (B : Set α), (f x : ℝ)) = ((B.sup' hne f : ℤ) : ℝ) := by
  classical
  letI : Nonempty (B : Set α) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  apply le_antisymm
  · apply ciSup_le
    intro x
    exact_mod_cast (Finset.le_sup' f x.property)
  · obtain ⟨x, hx, he⟩ := B.exists_mem_eq_sup' hne f
    rw [he]
    exact le_ciSup (Set.finite_range (fun x : (B : Set α) => (f x : ℝ))).bddAbove ⟨x, hx⟩

lemma ciInf_cast_finset_inf {α : Type*} (B : Finset α) (hne : B.Nonempty) (f : α → ℤ) :
    (⨅ x : (B : Set α), (f x : ℝ)) = ((B.inf' hne f : ℤ) : ℝ) := by
  classical
  letI : Nonempty (B : Set α) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := B.exists_mem_eq_inf' hne f
    rw [he]
    exact ciInf_le (Set.finite_range (fun x : (B : Set α) => (f x : ℝ))).bddBelow ⟨x, hx⟩
  · apply le_ciInf
    intro x
    exact_mod_cast (Finset.inf'_le f x.property)

#print axioms ciSup_cast_finset_sup
#print axioms ciInf_cast_finset_inf
#print axioms finite_gap_ge_at
#print axioms finite_gap_ray_bound
#print axioms inf_ne_bot_of_lower
#print axioms inf_eq_bot_of_negative_ray
end SteinitzDualBounds

/- Verified-component candidate: CoordinatorDualityRays.lean -/

open scoped BigOperators
namespace SteinitzDualityRays
open SteinitzExchange.Duality
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pairing_indicator (X : Finset V) (x : V → ℤ) :
    pairing (fun v => if v ∈ X then 1 else 0) (toReal x) = (sumOn x X : ℝ) := by
  simp [pairing, toReal, sumOn]

lemma pairing_nat_indicator (n : ℕ) (X : Finset V) (x : V → ℤ) :
    pairing (toReal (fun v => if v ∈ X then (n : ℤ) else 0)) (toReal x) =
      (n : ℝ) * (sumOn x X : ℝ) := by
  simp [pairing, toReal, sumOn, ← Finset.mul_sum]

lemma pairing_const (t : ℝ) (x : V → ℤ) :
    pairing (fun _ => t) (toReal x) = t * (sumOn x Finset.univ : ℝ) := by
  simp [pairing, toReal, sumOn, ← Finset.mul_sum]

lemma pairing_int_scale (n : ℕ) (q x : V → ℤ) :
    pairing (toReal (fun v => (n : ℤ) * q v)) (toReal x) =
      (n : ℝ) * pairing (toReal q) (toReal x) := by
  simp [pairing, toReal, Int.cast_mul, mul_assoc, ← Finset.mul_sum]

lemma supportMin_indicator (B : Finset (V → ℤ)) (X : Finset V) :
    supportMin B (fun v => if v ∈ X then 1 else 0) = setMin B X := by
  unfold supportMin setMin
  congr 1
  funext x
  exact pairing_indicator X x

lemma supportMax_indicator (B : Finset (V → ℤ)) (X : Finset V) :
    supportMax B (fun v => if v ∈ X then 1 else 0) = setMax B X := by
  unfold supportMax setMax
  congr 1
  funext x
  exact pairing_indicator X x

#print axioms pairing_nat_indicator
#print axioms supportMin_indicator
#print axioms supportMax_indicator
end SteinitzDualityRays

/- Verified-component candidate: CoordinatorDualValue.lean -/

open scoped BigOperators
open SteinitzExchange.Duality
namespace SteinitzDualValue
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma conjugate_gap_ge_common (B₁ B₂ : Finset (V → ℤ))
    (ω ζ : (V → ℤ) → ℝ) (x : V → ℤ) (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂)
    (p : V → ℝ) : ω x - ζ x ≤ convexConj B₂ ζ p - concaveConj B₁ ω p := by
  letI : Nonempty (B₁ : Set (V → ℤ)) := ⟨⟨x, hx₁⟩⟩
  letI : Nonempty (B₂ : Set (V → ℤ)) := ⟨⟨x, hx₂⟩⟩
  exact SteinitzDualBounds.finite_gap_ge_at
    (fun y : (B₁ : Set (V → ℤ)) => pairing p (toReal y))
    (fun y : (B₁ : Set (V → ℤ)) => ω y)
    (fun y : (B₂ : Set (V → ℤ)) => pairing p (toReal y))
    (fun y : (B₂ : Set (V → ℤ)) => ζ y) ⟨x, hx₁⟩ ⟨x, hx₂⟩ rfl

lemma dual_values_ne_bot_of_common (B₁ B₂ : Finset (V → ℤ))
    (ω ζ : (V → ℤ) → ℝ) (x : V → ℤ) (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂) :
    dualValue B₁ B₂ ω ζ ≠ ⊥ ∧ dualValueInt B₁ B₂ ω ζ ≠ ⊥ := by
  constructor
  · exact SteinitzDualBounds.inf_ne_bot_of_lower
      (fun p => convexConj B₂ ζ p - concaveConj B₁ ω p) (ω x - ζ x)
      (conjugate_gap_ge_common B₁ B₂ ω ζ x hx₁ hx₂)
  · exact SteinitzDualBounds.inf_ne_bot_of_lower
      (fun p : V → ℤ => convexConj B₂ ζ (toReal p) - concaveConj B₁ ω (toReal p))
      (ω x - ζ x) (fun p => conjugate_gap_ge_common B₁ B₂ ω ζ x hx₁ hx₂ (toReal p))

lemma real_dual_le_integer_dual (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ) :
    dualValue B₁ B₂ ω ζ ≤ dualValueInt B₁ B₂ ω ζ := by
  apply le_iInf
  intro p
  exact iInf_le _ (toReal p)

lemma integer_dual_ne_bot_of_real (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ)
    (h : dualValue B₁ B₂ ω ζ ≠ ⊥) : dualValueInt B₁ B₂ ω ζ ≠ ⊥ := by
  intro he
  have hle := real_dual_le_integer_dual B₁ B₂ ω ζ
  rw [he] at hle
  exact h (le_antisymm hle bot_le)

lemma support_le_of_common (B₁ B₂ : Finset (V → ℤ))
    (x : V → ℤ) (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂) (p : V → ℝ) :
    supportMin B₁ p ≤ supportMax B₂ p := by
  letI : Nonempty (B₁ : Set (V → ℤ)) := ⟨⟨x, hx₁⟩⟩
  letI : Nonempty (B₂ : Set (V → ℤ)) := ⟨⟨x, hx₂⟩⟩
  have h₁ : supportMin B₁ p ≤ pairing p (toReal x) :=
    ciInf_le (Set.finite_range (fun y : (B₁ : Set (V → ℤ)) => pairing p (toReal y))).bddBelow ⟨x, hx₁⟩
  have h₂ : pairing p (toReal x) ≤ supportMax B₂ p :=
    le_ciSup (Set.finite_range (fun y : (B₂ : Set (V → ℤ)) => pairing p (toReal y))).bddAbove ⟨x, hx₂⟩
  exact h₁.trans h₂

#print axioms dual_values_ne_bot_of_common
#print axioms integer_dual_ne_bot_of_real
#print axioms support_le_of_common
end SteinitzDualValue

/- Verified-component candidate: CoordinatorRankSandwich.lean -/

open scoped BigOperators
open SteinitzExchange.Duality
namespace SteinitzRankSandwich
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma setMax_eq_sup (B : Finset (V → ℤ)) (hne : B.Nonempty) (X : Finset V) :
    setMax B X = ((B.sup' hne (fun x => sumOn x X) : ℤ) : ℝ) :=
  SteinitzDualBounds.ciSup_cast_finset_sup B hne (fun x => sumOn x X)

lemma setMin_eq_inf (B : Finset (V → ℤ)) (hne : B.Nonempty) (X : Finset V) :
    setMin B X = ((B.inf' hne (fun x => sumOn x X) : ℤ) : ℝ) :=
  SteinitzDualBounds.ciInf_cast_finset_inf B hne (fun x => sumOn x X)

/-- The canonical subset inequalities and equal total rank imply a common integral base. -/
theorem common_of_canonical_rank_sandwich (hseparator : ∀ f g : Finset V → ℤ,
      IsSubmodular f → IsSupermodular g → f ∅ = 0 → g ∅ = 0 →
      (∀ X, g X ≤ f X) → ∃ x : V → ℤ, ∀ X, g X ≤ (∑ v ∈ X, x v) ∧ (∑ v ∈ X, x v) ≤ f X)
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (hle : ∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X)
    (ht : setMax B₂ Finset.univ = setMin B₁ Finset.univ) :
    ∃ x : V → ℤ, x ∈ B₁ ∧ x ∈ B₂ := by
  have hchar₁ := SteinitzExchange.Duality.baseSet_iff_submodular_system B₁ hB₁.1
  have hchar₂ := SteinitzExchange.Duality.baseSet_iff_submodular_system B₂ hB₂.1
  obtain ⟨g, hg, hg0, hrep₁⟩ := hchar₁.2.1.mp hB₁
  obtain ⟨f, hf, hf0, hrep₂⟩ := hchar₂.1.mp hB₂
  have hgcanon := hchar₁.2.2.2 g hg hg0 hrep₁
  have hfcanon := hchar₂.2.2.1 f hf hf0 hrep₂
  have hgreal : ∀ X, setMin B₁ X = (g X : ℝ) := by
    intro X
    rw [setMin_eq_inf B₁ hB₁.1 X, ← hgcanon X]
  have hfreal : ∀ X, setMax B₂ X = (f X : ℝ) := by
    intro X
    rw [setMax_eq_sup B₂ hB₂.1 X, ← hfcanon X]
  have hgf : ∀ X, g X ≤ f X := by
    intro X
    have h := hle X
    rw [hgreal X, hfreal X] at h
    exact_mod_cast h
  have htotal : f Finset.univ = g Finset.univ := by
    rw [hgreal, hfreal] at ht
    exact_mod_cast ht
  obtain ⟨x, hx⟩ := hseparator f g hf hg hf0 hg0 hgf
  have hxt : (∑ v, x v) = f Finset.univ := by
    have h := hx Finset.univ
    rw [← htotal] at h
    exact le_antisymm h.2 h.1
  exact ⟨x, (hrep₁ x).mpr ⟨fun X => (hx X).1, hxt.trans htotal⟩,
    (hrep₂ x).mpr ⟨fun X => (hx X).2, hxt⟩⟩

#print axioms common_of_canonical_rank_sandwich
end SteinitzRankSandwich

/- Verified-component candidate: CoordinatorDualRaysBound.lean -/

open scoped BigOperators
open SteinitzExchange.Duality
namespace SteinitzDualRaysBound
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma integer_dual_bottom_of_direction (B₁ B₂ : Finset (V → ℤ))
    (hne₁ : B₁.Nonempty) (hne₂ : B₂.Nonempty) (ω ζ : (V → ℤ) → ℝ) (q : V → ℤ)
    (hneg : supportMax B₂ (toReal q) < supportMin B₁ (toReal q)) :
    dualValueInt B₁ B₂ ω ζ = ⊥ := by
  classical
  letI : Nonempty (B₁ : Set (V → ℤ)) := ⟨⟨hne₁.choose, hne₁.choose_spec⟩⟩
  letI : Nonempty (B₂ : Set (V → ℤ)) := ⟨⟨hne₂.choose, hne₂.choose_spec⟩⟩
  let C : ℝ := (⨆ x : (B₁ : Set (V → ℤ)), ω x) - (⨅ y : (B₂ : Set (V → ℤ)), ζ y)
  let d : ℝ := supportMax B₂ (toReal q) - supportMin B₁ (toReal q)
  refine SteinitzDualBounds.inf_eq_bot_of_negative_ray
    (fun p : V → ℤ => convexConj B₂ ζ (toReal p) - concaveConj B₁ ω (toReal p))
    (fun n v => (n : ℤ) * q v) d C (sub_neg.mpr hneg) ?_
  intro n
  have h := SteinitzDualBounds.finite_gap_ray_bound
    (fun x : (B₁ : Set (V → ℤ)) => pairing (toReal q) (toReal x))
    (fun x : (B₁ : Set (V → ℤ)) => ω x)
    (fun y : (B₂ : Set (V → ℤ)) => pairing (toReal q) (toReal y))
    (fun y : (B₂ : Set (V → ℤ)) => ζ y) (n : ℝ) (Nat.cast_nonneg n)
  simpa only [convexConj, concaveConj, SteinitzDualityRays.pairing_int_scale,
    d, C, supportMax, supportMin] using h

lemma integer_support_of_bounded (B₁ B₂ : Finset (V → ℤ))
    (hne₁ : B₁.Nonempty) (hne₂ : B₂.Nonempty) (ω ζ : (V → ℤ) → ℝ)
    (hb : dualValueInt B₁ B₂ ω ζ ≠ ⊥) :
    ∀ q : V → ℤ, supportMin B₁ (toReal q) ≤ supportMax B₂ (toReal q) := by
  intro q
  by_contra hn
  exact hb (integer_dual_bottom_of_direction B₁ B₂ hne₁ hne₂ ω ζ q (lt_of_not_ge hn))

lemma real_bounded_of_support (B₁ B₂ : Finset (V → ℤ))
    (hne₁ : B₁.Nonempty) (hne₂ : B₂.Nonempty) (ω ζ : (V → ℤ) → ℝ)
    (hs : ∀ p : V → ℝ, supportMin B₁ p ≤ supportMax B₂ p) :
    dualValue B₁ B₂ ω ζ ≠ ⊥ := by
  classical
  letI : Nonempty (B₁ : Set (V → ℤ)) := ⟨⟨hne₁.choose, hne₁.choose_spec⟩⟩
  letI : Nonempty (B₂ : Set (V → ℤ)) := ⟨⟨hne₂.choose, hne₂.choose_spec⟩⟩
  let C : ℝ := (⨅ x : (B₁ : Set (V → ℤ)), ω x) - (⨆ y : (B₂ : Set (V → ℤ)), ζ y)
  apply SteinitzDualBounds.inf_ne_bot_of_lower
    (fun p : V → ℝ => convexConj B₂ ζ p - concaveConj B₁ ω p) C
  intro p
  have h := SteinitzDualBounds.finite_gap_ge_support
    (fun x : (B₁ : Set (V → ℤ)) => pairing p (toReal x))
    (fun x : (B₁ : Set (V → ℤ)) => ω x)
    (fun y : (B₂ : Set (V → ℤ)) => pairing p (toReal y))
    (fun y : (B₂ : Set (V → ℤ)) => ζ y)
  change (supportMax B₂ p - supportMin B₁ p) + C ≤ convexConj B₂ ζ p - concaveConj B₁ ω p at h
  have hp := hs p
  linarith

lemma ranks_of_integer_support (B₁ B₂ : Finset (V → ℤ))
    (hs : ∀ q : V → ℤ, supportMin B₁ (toReal q) ≤ supportMax B₂ (toReal q)) :
    ∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X := by
  intro X
  let q : V → ℤ := fun v => if v ∈ X then 1 else 0
  have hq : toReal q = (fun v => if v ∈ X then (1 : ℝ) else 0) := by
    funext v
    simp [toReal, q]
  have h := hs q
  rw [hq, SteinitzDualityRays.supportMin_indicator, SteinitzDualityRays.supportMax_indicator] at h
  exact h

lemma totals_extrema (B : Finset (V → ℤ)) (hne : B.Nonempty) (r : ℤ)
    (hr : ∀ x ∈ B, sumOn x Finset.univ = r) :
    setMin B Finset.univ = (r : ℝ) ∧ setMax B Finset.univ = (r : ℝ) := by
  classical
  letI : Nonempty (B : Set (V → ℤ)) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have he : (fun x : (B : Set (V → ℤ)) => (sumOn x.val Finset.univ : ℝ)) =
      (fun _ => (r : ℝ)) := by
    funext x
    rw [hr x x.property]
  constructor
  · unfold setMin
    rw [he]
    simp
  · unfold setMax
    rw [he]
    simp

lemma constant_support (B : Finset (V → ℤ)) (hne : B.Nonempty) (r : ℤ)
    (hr : ∀ x ∈ B, sumOn x Finset.univ = r) (t : ℝ) :
    supportMin B (fun _ => t) = t * (r : ℝ) ∧
      supportMax B (fun _ => t) = t * (r : ℝ) := by
  classical
  letI : Nonempty (B : Set (V → ℤ)) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have he : (fun x : (B : Set (V → ℤ)) => pairing (fun _ => t) (toReal x.val)) =
      (fun _ => t * (r : ℝ)) := by
    funext x
    rw [SteinitzDualityRays.pairing_const, hr x x.property]
  constructor
  · unfold supportMin
    rw [he]
    simp
  · unfold supportMax
    rw [he]
    simp

lemma ranks_and_total_of_integer_support [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (hs : ∀ q : V → ℤ, supportMin B₁ (toReal q) ≤ supportMax B₂ (toReal q)) :
    (∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X) ∧
      setMax B₂ Finset.univ = setMin B₁ Finset.univ := by
  have hle := ranks_of_integer_support B₁ B₂ hs
  refine ⟨hle, le_antisymm ?_ (hle Finset.univ)⟩
  obtain ⟨f₁, _, _, hrep₁⟩ := (SteinitzExchange.Duality.baseSet_iff_submodular_system B₁ hB₁.1).1.mp hB₁
  obtain ⟨f₂, _, _, hrep₂⟩ := (SteinitzExchange.Duality.baseSet_iff_submodular_system B₂ hB₂.1).1.mp hB₂
  have hr₁ : ∀ x ∈ B₁, sumOn x Finset.univ = f₁ Finset.univ := fun x hx => ((hrep₁ x).mp hx).2
  have hr₂ : ∀ x ∈ B₂, sumOn x Finset.univ = f₂ Finset.univ := fun x hx => ((hrep₂ x).mp hx).2
  have he₁ := totals_extrema B₁ hB₁.1 (f₁ Finset.univ) hr₁
  have he₂ := totals_extrema B₂ hB₂.1 (f₂ Finset.univ) hr₂
  have hm₁ := constant_support B₁ hB₁.1 (f₁ Finset.univ) hr₁ (-1)
  have hm₂ := constant_support B₂ hB₂.1 (f₂ Finset.univ) hr₂ (-1)
  have h := hs (fun _ => -1)
  have hc : toReal (fun _ : V => (-1 : ℤ)) = (fun _ => (-1 : ℝ)) := by
    funext v
    simp [toReal]
  rw [hc, hm₁.1, hm₂.2] at h
  rw [he₂.2, he₁.1]
  linarith

#print axioms integer_dual_bottom_of_direction
#print axioms real_bounded_of_support
#print axioms ranks_and_total_of_integer_support
end SteinitzDualRaysBound

/- Verified-component candidate: CoordinatorDualBounded.lean -/

open scoped BigOperators
open SteinitzExchange.Duality
namespace SteinitzDualBounded
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem dual_bounded_iff_of_separator
    (hseparator : ∀ f g : Finset V → ℤ,
      IsSubmodular f → IsSupermodular g → f ∅ = 0 → g ∅ = 0 →
      (∀ X, g X ≤ f X) → ∃ x : V → ℤ, ∀ X, g X ≤ (∑ v ∈ X, x v) ∧ (∑ v ∈ X, x v) ≤ f X)
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω ζ : (V → ℤ) → ℝ) :
    (dualValueInt B₁ B₂ ω ζ ≠ ⊥ ↔ dualValue B₁ B₂ ω ζ ≠ ⊥) ∧
    (dualValue B₁ B₂ ω ζ ≠ ⊥ ↔ ∀ p : V → ℝ, supportMin B₁ p ≤ supportMax B₂ p) ∧
    ((∀ p : V → ℝ, supportMin B₁ p ≤ supportMax B₂ p) ↔
      (∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X) ∧
        setMax B₂ Finset.univ = setMin B₁ Finset.univ) := by
  have hIntToRank (h : dualValueInt B₁ B₂ ω ζ ≠ ⊥) :
      (∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X) ∧
        setMax B₂ Finset.univ = setMin B₁ Finset.univ :=
    SteinitzDualRaysBound.ranks_and_total_of_integer_support B₁ B₂ hB₁ hB₂
      (SteinitzDualRaysBound.integer_support_of_bounded B₁ B₂ hB₁.1 hB₂.1 ω ζ h)
  have hRankToCommon (h : (∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X) ∧
      setMax B₂ Finset.univ = setMin B₁ Finset.univ) :
      ∃ x : V → ℤ, x ∈ B₁ ∧ x ∈ B₂ :=
    SteinitzRankSandwich.common_of_canonical_rank_sandwich hseparator B₁ B₂ hB₁ hB₂ h.1 h.2
  have hRankToReal (h : (∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X) ∧
      setMax B₂ Finset.univ = setMin B₁ Finset.univ) : dualValue B₁ B₂ ω ζ ≠ ⊥ := by
    obtain ⟨x, hx₁, hx₂⟩ := hRankToCommon h
    exact (SteinitzDualValue.dual_values_ne_bot_of_common B₁ B₂ ω ζ x hx₁ hx₂).1
  have hRankToSupport (h : (∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X) ∧
      setMax B₂ Finset.univ = setMin B₁ Finset.univ) :
      ∀ p : V → ℝ, supportMin B₁ p ≤ supportMax B₂ p := by
    obtain ⟨x, hx₁, hx₂⟩ := hRankToCommon h
    exact SteinitzDualValue.support_le_of_common B₁ B₂ x hx₁ hx₂
  have hRealToInt := SteinitzDualValue.integer_dual_ne_bot_of_real B₁ B₂ ω ζ
  have hSupportToReal := SteinitzDualRaysBound.real_bounded_of_support B₁ B₂ hB₁.1 hB₂.1 ω ζ
  exact ⟨⟨fun h => hRankToReal (hIntToRank h), hRealToInt⟩,
    ⟨fun h => hRankToSupport (hIntToRank (hRealToInt h)), hSupportToReal⟩,
    ⟨fun h => hIntToRank (hRealToInt (hSupportToReal h)), hRankToSupport⟩⟩

#print axioms dual_bounded_iff_of_separator
end SteinitzDualBounded

/- Verified-component candidate: SteinitzPublicIntegerSandwich.lean -/

set_option autoImplicit false

namespace SteinitzSeparationPublic

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

end SteinitzSeparationPublic

open SteinitzExchange.Duality

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω ζ : (V → ℤ) → ℝ) :
    (dualValueInt B₁ B₂ ω ζ ≠ ⊥ ↔ dualValue B₁ B₂ ω ζ ≠ ⊥) ∧
    (dualValue B₁ B₂ ω ζ ≠ ⊥ ↔ ∀ p : V → ℝ, supportMin B₁ p ≤ supportMax B₂ p) ∧
    ((∀ p : V → ℝ, supportMin B₁ p ≤ supportMax B₂ p) ↔
      (∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X) ∧
        setMax B₂ Finset.univ = setMin B₁ Finset.univ) := by
  exact SteinitzDualBounded.dual_bounded_iff_of_separator
    SteinitzSeparationPublic.integer_sandwich B₁ B₂ hB₁ hB₂ ω ζ

#print axioms solution
