-- Prove2me | solution 1 for SteinitzExchange.Duality.fenchel_min_max
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T22:48:32.972423+00:00
-- url     : https://prove2.me/submissions/199e191b-7d61-499d-a658-20947f91eab3

import Theorems.Thm_SteinitzExchange_Duality_baseSet_iff_submodular_system
import Mathlib.Data.EReal.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Theorems.Thm_SteinitzExchange_Duality_frank_discrete_separation
import Definitions.Def_SteinitzExchange_Duality_Problems
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Theorems.Thm_SteinitzExchange_Duality_weak_duality
import Theorems.Thm_SteinitzExchange_Duality_dual_bounded_iff
import Theorems.Thm_SteinitzExchange_Duality_mconcave_intersection_optimality

namespace SteinitzFenchelBounds

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


end SteinitzFenchelBounds


open scoped BigOperators
open SteinitzExchange.Duality
namespace SteinitzFenchelRankSandwich
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma setMax_eq_sup (B : Finset (V → ℤ)) (hne : B.Nonempty) (X : Finset V) :
    setMax B X = ((B.sup' hne (fun x => sumOn x X) : ℤ) : ℝ) :=
  SteinitzFenchelBounds.ciSup_cast_finset_sup B hne (fun x => sumOn x X)

lemma setMin_eq_inf (B : Finset (V → ℤ)) (hne : B.Nonempty) (X : Finset V) :
    setMin B X = ((B.inf' hne (fun x => sumOn x X) : ℤ) : ℝ) :=
  SteinitzFenchelBounds.ciInf_cast_finset_inf B hne (fun x => sumOn x X)

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
end SteinitzFenchelRankSandwich


set_option autoImplicit false

namespace SteinitzFenchelInteger

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
  obtain ⟨x, hx⟩ := (frank_discrete_separation fR gR hfR hgR hfR0 hgR0 hgfR).2
    (fun X => ⟨f X, rfl⟩) (fun X => ⟨g X, rfl⟩)
  refine ⟨x, fun X => ?_⟩
  have h := hx X
  change (g X : ℝ) ≤ ((∑ v ∈ X, x v : ℤ) : ℝ) ∧
    ((∑ v ∈ X, x v : ℤ) : ℝ) ≤ (f X : ℝ) at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

#print axioms integer_sandwich

end SteinitzFenchelInteger


set_option autoImplicit false

namespace SteinitzFenchel

open Finset SteinitzExchange.Duality

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pairing_neg_left (p b : V → ℝ) : pairing (-p) b = -pairing p b := by
  simp [pairing, Finset.sum_neg_distrib]

lemma gap_ge_common (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ)
    (x : V → ℤ) (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂) (p : V → ℝ) :
    ω x - ζ x ≤ convexConj B₂ ζ p - concaveConj B₁ ω p := by
  have h₁ : concaveConj B₁ ω p ≤ pairing p (toReal x) - ω x :=
    ciInf_le (Set.finite_range (fun y : (B₁ : Set (V → ℤ)) =>
      pairing p (toReal y.val) - ω y.val)).bddBelow ⟨x, hx₁⟩
  have h₂ : pairing p (toReal x) - ζ x ≤ convexConj B₂ ζ p :=
    le_ciSup (Set.finite_range (fun y : (B₂ : Set (V → ℤ)) =>
      pairing p (toReal y.val) - ζ y.val)).bddAbove ⟨x, hx₂⟩
  linarith

lemma primal_le_gap (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ)
    (p : V → ℝ) : primalValue B₁ B₂ ω ζ ≤
      ((convexConj B₂ ζ p - concaveConj B₁ ω p : ℝ) : EReal) := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx₁
  apply iSup_le
  intro hx₂
  exact EReal.coe_le_coe_iff.mpr (gap_ge_common B₁ B₂ ω ζ x hx₁ hx₂ p)

lemma primal_le_real_dual (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ) :
    primalValue B₁ B₂ ω ζ ≤ dualValue B₁ B₂ ω ζ := by
  exact le_iInf (fun p => primal_le_gap B₁ B₂ ω ζ p)

lemma primal_le_integer_dual (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ) :
    primalValue B₁ B₂ ω ζ ≤ dualValueInt B₁ B₂ ω ζ := by
  exact le_iInf (fun p => primal_le_gap B₁ B₂ ω ζ (toReal p))

lemma real_dual_le_integer_dual (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ) :
    dualValue B₁ B₂ ω ζ ≤ dualValueInt B₁ B₂ ω ζ := by
  apply le_iInf
  intro p
  exact iInf_le _ (toReal p)

lemma primal_eq_of_max (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ)
    (x : V → ℤ) (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂)
    (hmax : ∀ y ∈ B₁, y ∈ B₂ → ω y - ζ y ≤ ω x - ζ x) :
    primalValue B₁ B₂ ω ζ = ((ω x - ζ x : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy₁
    apply iSup_le
    intro hy₂
    exact EReal.coe_le_coe_iff.mpr (hmax y hy₁ hy₂)
  · exact le_iSup_of_le x (le_iSup_of_le hx₁ (le_iSup_of_le hx₂ le_rfl))

lemma exists_primal_max (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ)
    (hne : (B₁ ∩ B₂).Nonempty) :
    ∃ x ∈ B₁ ∩ B₂, (∀ y ∈ B₁, y ∈ B₂ → ω y - ζ y ≤ ω x - ζ x) ∧
      primalValue B₁ B₂ ω ζ = ((ω x - ζ x : ℝ) : EReal) := by
  classical
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (B₁ ∩ B₂) (fun y => ω y - ζ y) hne
  have hm : ∀ y ∈ B₁, y ∈ B₂ → ω y - ζ y ≤ ω x - ζ x := by
    intro y hy₁ hy₂
    exact hmax y (Finset.mem_inter.mpr ⟨hy₁, hy₂⟩)
  exact ⟨x, hx, hm, primal_eq_of_max B₁ B₂ ω ζ x
    (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2 hm⟩

lemma primal_eq_bot_of_empty (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ)
    (hne : ¬(B₁ ∩ B₂).Nonempty) : primalValue B₁ B₂ ω ζ = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro x
  apply iSup_le
  intro hx₁
  apply iSup_le
  intro hx₂
  exact (hne ⟨x, Finset.mem_inter.mpr ⟨hx₁, hx₂⟩⟩).elim

lemma gap_eq_of_support (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ)
    (x : V → ℤ) (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂) (p : V → ℝ)
    (h₁ : ∀ y ∈ B₁, perturb ω (-p) y ≤ perturb ω (-p) x)
    (h₂ : ∀ y ∈ B₂, perturb (fun z => -ζ z) p y ≤ perturb (fun z => -ζ z) p x) :
    convexConj B₂ ζ p - concaveConj B₁ ω p = ω x - ζ x := by
  letI : Nonempty (B₁ : Set (V → ℤ)) := ⟨⟨x, hx₁⟩⟩
  letI : Nonempty (B₂ : Set (V → ℤ)) := ⟨⟨x, hx₂⟩⟩
  have hc₁ : concaveConj B₁ ω p = pairing p (toReal x) - ω x := by
    apply le_antisymm
    · exact ciInf_le (Set.finite_range (fun y : (B₁ : Set (V → ℤ)) =>
        pairing p (toReal y.val) - ω y.val)).bddBelow ⟨x, hx₁⟩
    · apply le_ciInf
      intro y
      have h := h₁ y.val y.property
      simp only [perturb, pairing_neg_left] at h
      linarith
  have hc₂ : convexConj B₂ ζ p = pairing p (toReal x) - ζ x := by
    apply le_antisymm
    · apply ciSup_le
      intro y
      have h := h₂ y.val y.property
      simp only [perturb] at h
      linarith
    · exact le_ciSup (Set.finite_range (fun y : (B₂ : Set (V → ℤ)) =>
        pairing p (toReal y.val) - ζ y.val)).bddAbove ⟨x, hx₂⟩
  rw [hc₁, hc₂]
  ring

lemma real_dual_eq_of_support (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ)
    (x : V → ℤ) (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂) (p : V → ℝ)
    (h₁ : ∀ y ∈ B₁, perturb ω (-p) y ≤ perturb ω (-p) x)
    (h₂ : ∀ y ∈ B₂, perturb (fun z => -ζ z) p y ≤ perturb (fun z => -ζ z) p x) :
    dualValue B₁ B₂ ω ζ = ((ω x - ζ x : ℝ) : EReal) := by
  apply le_antisymm
  · rw [← gap_eq_of_support B₁ B₂ ω ζ x hx₁ hx₂ p h₁ h₂]
    exact iInf_le _ p
  · apply le_iInf
    intro q
    exact EReal.coe_le_coe_iff.mpr (gap_ge_common B₁ B₂ ω ζ x hx₁ hx₂ q)

lemma integer_dual_eq_of_support (B₁ B₂ : Finset (V → ℤ)) (ω ζ : (V → ℤ) → ℝ)
    (x : V → ℤ) (hx₁ : x ∈ B₁) (hx₂ : x ∈ B₂) (p : V → ℤ)
    (h₁ : ∀ y ∈ B₁, perturb ω (-toReal p) y ≤ perturb ω (-toReal p) x)
    (h₂ : ∀ y ∈ B₂, perturb (fun z => -ζ z) (toReal p) y ≤
      perturb (fun z => -ζ z) (toReal p) x) :
    dualValueInt B₁ B₂ ω ζ = ((ω x - ζ x : ℝ) : EReal) := by
  apply le_antisymm
  · rw [← gap_eq_of_support B₁ B₂ ω ζ x hx₁ hx₂ (toReal p) h₁ h₂]
    exact iInf_le _ p
  · apply le_iInf
    intro q
    exact EReal.coe_le_coe_iff.mpr (gap_ge_common B₁ B₂ ω ζ x hx₁ hx₂ (toReal q))

#print axioms exists_primal_max
#print axioms gap_eq_of_support
#print axioms integer_dual_eq_of_support

end SteinitzFenchel


set_option autoImplicit false

namespace SteinitzFenchel
open SteinitzExchange.Duality

theorem fenchel_min_max_checked {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω ζ : (V → ℤ) → ℝ) (hω : SatisfiesEXC B₁ ω) (hζ : SatisfiesEXC B₂ (fun x => -ζ x)) :
    -- (1)
    (primalValue B₁ B₂ ω ζ = relaxedValue B₁ B₂ ω ζ ∧
      relaxedValue B₁ B₂ ω ζ = dualValue B₁ B₂ ω ζ) ∧
    -- (P1)
    (dualValue B₁ B₂ ω ζ ≠ ⊥ → (B₁ ∩ B₂).Nonempty) ∧
    -- (P2)
    ((B₁ ∩ B₂).Nonempty →
      ∃ x ∈ B₁ ∩ B₂, ∃ b ∈ hull B₁ ∩ hull B₂, ∃ p : V → ℝ,
        primalValue B₁ B₂ ω ζ = ((ω x - ζ x : ℝ) : EReal) ∧
        relaxedValue B₁ B₂ ω ζ =
          ((concaveClosure B₁ ω b - convexClosure B₂ ζ b : ℝ) : EReal) ∧
        dualValue B₁ B₂ ω ζ = ((convexConj B₂ ζ p - concaveConj B₁ ω p : ℝ) : EReal) ∧
        ω x - ζ x = concaveClosure B₁ ω b - convexClosure B₂ ζ b ∧
        ω x - ζ x = convexConj B₂ ζ p - concaveConj B₁ ω p) ∧
    -- (2)
    ((∀ x ∈ B₁, ∃ k : ℤ, ω x = k) → (∀ x ∈ B₂, ∃ k : ℤ, ζ x = k) →
      primalValue B₁ B₂ ω ζ = dualValueInt B₁ B₂ ω ζ ∧
      (dualValueInt B₁ B₂ ω ζ ≠ ⊥ →
        ∃ p : V → ℤ, dualValueInt B₁ B₂ ω ζ =
          ((convexConj B₂ ζ (toReal p) - concaveConj B₁ ω (toReal p) : ℝ) : EReal))) := by
  classical
  have hw := weak_duality B₁ B₂ hB₁.1 hB₂.1 ω ζ
  have hb := dual_bounded_iff B₁ B₂ hB₁ hB₂ ω ζ
  have hcommon : dualValue B₁ B₂ ω ζ ≠ ⊥ → (B₁ ∩ B₂).Nonempty := by
    intro hfinite
    have hr := hb.2.2.mp (hb.2.1.mp hfinite)
    obtain ⟨x, hx₁, hx₂⟩ := SteinitzFenchelRankSandwich.common_of_canonical_rank_sandwich
      (fun f g hf hg hf0 hg0 hgf =>
        SteinitzFenchelInteger.integer_sandwich f g hf hg hf0 hg0 hgf)
      B₁ B₂ hB₁ hB₂ hr.1 hr.2
    exact ⟨x, Finset.mem_inter.mpr ⟨hx₁, hx₂⟩⟩
  have hreal : (B₁ ∩ B₂).Nonempty →
      ∃ x ∈ B₁ ∩ B₂, ∃ p : V → ℝ,
        primalValue B₁ B₂ ω ζ = ((ω x - ζ x : ℝ) : EReal) ∧
        dualValue B₁ B₂ ω ζ = ((ω x - ζ x : ℝ) : EReal) ∧
        convexConj B₂ ζ p - concaveConj B₁ ω p = ω x - ζ x := by
    intro hne
    obtain ⟨x, hx, hmax, hprimal⟩ := exists_primal_max B₁ B₂ ω ζ hne
    have hx₁ := (Finset.mem_inter.mp hx).1
    have hx₂ := (Finset.mem_inter.mp hx).2
    have hm : ∀ y ∈ B₁, y ∈ B₂ → ω y + (-ζ y) ≤ ω x + (-ζ x) := by
      simpa only [sub_eq_add_neg] using hmax
    obtain ⟨p, hp₁, hp₂⟩ :=
      (mconcave_intersection_optimality B₁ B₂ hB₁ hB₂ ω (fun y => -ζ y)
        hω hζ x hx₁ hx₂).1.mp hm
    exact ⟨x, hx, p, hprimal, real_dual_eq_of_support B₁ B₂ ω ζ x hx₁ hx₂ p hp₁ hp₂,
      gap_eq_of_support B₁ B₂ ω ζ x hx₁ hx₂ p hp₁ hp₂⟩
  have heq : primalValue B₁ B₂ ω ζ = relaxedValue B₁ B₂ ω ζ ∧
      relaxedValue B₁ B₂ ω ζ = dualValue B₁ B₂ ω ζ := by
    refine ⟨?_, hw.2.1⟩
    by_cases hne : (B₁ ∩ B₂).Nonempty
    · obtain ⟨x, hx, p, hp, hd, hgap⟩ := hreal hne
      exact (hp.trans hd.symm).trans hw.2.1.symm
    · have hd : dualValue B₁ B₂ ω ζ = ⊥ := by
        by_contra hd
        exact hne (hcommon hd)
      exact (primal_eq_bot_of_empty B₁ B₂ ω ζ hne).trans (hw.2.1.trans hd).symm
  refine ⟨heq, hcommon, ?_, ?_⟩
  · intro hne
    obtain ⟨x, hx, p, hp, hd, hgap⟩ := hreal hne
    have hx₁ := (Finset.mem_inter.mp hx).1
    have hx₂ := (Finset.mem_inter.mp hx).2
    have hxhull : toReal x ∈ hull B₁ ∩ hull B₂ :=
      ⟨subset_convexHull ℝ _ ⟨x, hx₁, rfl⟩, subset_convexHull ℝ _ ⟨x, hx₂, rfl⟩⟩
    obtain ⟨b, hb, hr⟩ := hw.2.2 ⟨toReal x, hxhull⟩
    refine ⟨x, hx, b, hb, p, hp, hr, ?_, ?_, hgap.symm⟩
    · rw [hgap]
      exact hd
    · have he : ((ω x - ζ x : ℝ) : EReal) =
          ((concaveClosure B₁ ω b - convexClosure B₂ ζ b : ℝ) : EReal) :=
        hp.symm.trans (heq.1.trans hr)
      exact_mod_cast he
  · intro hωi hζi
    have hnζi : ∀ x ∈ B₂, ∃ k : ℤ, -ζ x = k := by
      intro x hx
      obtain ⟨k, hk⟩ := hζi x hx
      exact ⟨-k, by simp [hk]⟩
    by_cases hne : (B₁ ∩ B₂).Nonempty
    · obtain ⟨x, hx, hmax, hprimal⟩ := exists_primal_max B₁ B₂ ω ζ hne
      have hx₁ := (Finset.mem_inter.mp hx).1
      have hx₂ := (Finset.mem_inter.mp hx).2
      have hm : ∀ y ∈ B₁, y ∈ B₂ → ω y + (-ζ y) ≤ ω x + (-ζ x) := by
        simpa only [sub_eq_add_neg] using hmax
      obtain ⟨p, hp₁, hp₂⟩ :=
        (mconcave_intersection_optimality B₁ B₂ hB₁ hB₂ ω (fun y => -ζ y)
          hω hζ x hx₁ hx₂).2 hωi hnζi hm
      have hd := integer_dual_eq_of_support B₁ B₂ ω ζ x hx₁ hx₂ p hp₁ hp₂
      have hgap := gap_eq_of_support B₁ B₂ ω ζ x hx₁ hx₂ (toReal p) hp₁ hp₂
      refine ⟨hprimal.trans hd.symm, fun _ => ⟨p, ?_⟩⟩
      rw [hgap]
      exact hd
    · have hd : dualValueInt B₁ B₂ ω ζ = ⊥ := by
        by_contra hd
        exact hne (hcommon (hb.1.mp hd))
      exact ⟨(primal_eq_bot_of_empty B₁ B₂ ω ζ hne).trans hd.symm,
        fun hfinite => (hfinite hd).elim⟩

#print axioms fenchel_min_max_checked

end SteinitzFenchel

open SteinitzExchange.Duality

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω ζ : (V → ℤ) → ℝ) (hω : SatisfiesEXC B₁ ω) (hζ : SatisfiesEXC B₂ (fun x => -ζ x)) :
    -- (1)
    (primalValue B₁ B₂ ω ζ = relaxedValue B₁ B₂ ω ζ ∧
      relaxedValue B₁ B₂ ω ζ = dualValue B₁ B₂ ω ζ) ∧
    -- (P1)
    (dualValue B₁ B₂ ω ζ ≠ ⊥ → (B₁ ∩ B₂).Nonempty) ∧
    -- (P2)
    ((B₁ ∩ B₂).Nonempty →
      ∃ x ∈ B₁ ∩ B₂, ∃ b ∈ hull B₁ ∩ hull B₂, ∃ p : V → ℝ,
        primalValue B₁ B₂ ω ζ = ((ω x - ζ x : ℝ) : EReal) ∧
        relaxedValue B₁ B₂ ω ζ =
          ((concaveClosure B₁ ω b - convexClosure B₂ ζ b : ℝ) : EReal) ∧
        dualValue B₁ B₂ ω ζ = ((convexConj B₂ ζ p - concaveConj B₁ ω p : ℝ) : EReal) ∧
        ω x - ζ x = concaveClosure B₁ ω b - convexClosure B₂ ζ b ∧
        ω x - ζ x = convexConj B₂ ζ p - concaveConj B₁ ω p) ∧
    -- (2)
    ((∀ x ∈ B₁, ∃ k : ℤ, ω x = k) → (∀ x ∈ B₂, ∃ k : ℤ, ζ x = k) →
      primalValue B₁ B₂ ω ζ = dualValueInt B₁ B₂ ω ζ ∧
      (dualValueInt B₁ B₂ ω ζ ≠ ⊥ →
        ∃ p : V → ℤ, dualValueInt B₁ B₂ ω ζ =
          ((convexConj B₂ ζ (toReal p) - concaveConj B₁ ω (toReal p) : ℝ) : EReal))) := by
  exact SteinitzFenchel.fenchel_min_max_checked B₁ B₂ hB₁ hB₂ ω ζ hω hζ

#print axioms solution
