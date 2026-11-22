-- Prove2me | solution 1 for UpperTheory.Reformulated.B.JumpSetsAlt.hostReal_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:11.154818+00:00
-- url     : https://prove2.me/submissions/03a3e40f-1787-4452-b468-c9da0f41c664

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_JumpSets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open scoped Classical
namespace UpperTheory.Reformulated.B.JumpSetsAlt
theorem _root_.solution :
    UpperTheory.Reformulated.B.JumpSetsAlt.HostGalois → UpperTheory.Reformulated.B.JumpSetsAlt.HostGalSpec → UpperTheory.Reformulated.B.JumpSetsAlt.HostConj → UpperTheory.Reformulated.B.JumpSetsAlt.HostReal := by
  intro hG hS hC e q d hqd L _ _ ζ a b hL
  obtain ⟨hgal, hfin, hmul, hbij⟩ := hG e q d hqd L ζ a b hL
  obtain ⟨hCM, hconj⟩ := hC e q d hqd L ζ a b hL
  have hspec := hS e q d hqd L ζ a b hL
  obtain ⟨σ₀, hσ₀⟩ := hbij.2 (UpperTheory.Reformulated.B.JumpSetsAlt.cc e)
  have hone : UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hfix : ∀ x : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b), x ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b ↔ σ₀ x = x := by
    intro x
    rw [NumberField.mem_maximalRealSubfield_iff]
    constructor
    · intro hx
      obtain ⟨φ⟩ : Nonempty (↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) →+* ℂ) := inferInstance
      apply φ.injective
      rw [(hconj φ σ₀).mpr hσ₀ x]
      exact hx φ
    · intro hx φ
      have h := (hconj φ σ₀).mpr hσ₀ x
      rw [hx] at h
      exact h.symm
  have hval : ((1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val = 1 := by
    haveI : Fact (1 < 2 ^ (e + 2)) := ⟨Nat.one_lt_two_pow (by omega)⟩
    rw [Units.val_one, ZMod.val_one]
  have hth : ∀ σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ), (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).2 = 1 ↔
      σ (UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b) = UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b := by
    intro σ
    have h := (hspec σ).2.2.1 1
    rw [hval, pow_one, pow_one] at h
    exact h.trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hab : ∀ σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ),
      ((σ (UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b * UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b) : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) : L) =
        ((((UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.1 * (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * (a * b) := by
    intro σ
    rw [map_mul, IntermediateField.coe_mul, (hspec σ).1, (hspec σ).2.1]
    push_cast
    ring
  have ha : a ≠ 0 := by
    rintro rfl
    have h := hL.2.1
    have hq : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hqd.1.ne_zero
    exact hq (by simpa using h)
  have hb : b ≠ 0 := by
    rintro rfl
    have h := hL.2.2.1
    have hd : (d : L) ≠ 0 := Nat.cast_ne_zero.mpr hqd.2.1.ne_zero
    exact hd (by simpa using h)
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · have h := Module.finrank_mul_finrank ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b) ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b) ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b),
      hfin, show 2 ^ (e + 2) = 2 ^ (e + 1) * 2 from pow_succ 2 (e + 1)] at h
    exact Nat.eq_of_mul_eq_mul_right two_pos h
  · rw [hfix]
    exact ⟨fun hx σ hσ => by rw [hbij.1 (hσ.trans hσ₀.symm)]; exact hx, fun hx => hx σ₀ hσ₀⟩
  · set K : IntermediateField ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
      ℚ⟮UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b * UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b, UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b⟯ with hK
    have hlift : (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯ ↔ x ∈ K := by
      have h1 := IntermediateField.lift_adjoin ℚ (UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)
        {UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b * UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b, UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b}
      rw [Set.image_pair] at h1
      have h2 := IntermediateField.mem_lift (F := UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)
        (E := ℚ⟮UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b * UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b, UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b⟯) x
      exact (SetLike.ext_iff.mp h1 (x : L)).symm.trans h2
    rw [hlift, hfix]
    constructor
    · intro hx
      rw [← IsGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      have h1 := hab σ
      rw [hσ _ (IntermediateField.subset_adjoin ℚ _ (by simp))] at h1
      have h2 := (hth σ).mpr (hσ _ (IntermediateField.subset_adjoin ℚ _ (by simp)))
      have h3 : (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.1 * (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.2 = 1 := by
        have h4 : a * b = ((((UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.1 *
          (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * (a * b) := h1
        have h5 := (right_eq_mul₀ (mul_ne_zero ha hb)).mp h4
        exact Units.ext (Int.cast_injective (α := L) (by simpa using h5))
      have h6 : UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = 1 ∨ UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = UpperTheory.Reformulated.B.JumpSetsAlt.cc e := by
        generalize UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = g at h2 h3
        obtain ⟨⟨s, t⟩, u⟩ := g
        dsimp only at h2 h3
        subst h2
        rcases Int.units_eq_one_or s with rfl | rfl
        · left
          rw [one_mul] at h3
          rw [h3]
          rfl
        · right
          have : t = -1 := by
            rw [neg_mul, one_mul, neg_eq_iff_eq_neg] at h3
            exact h3
          rw [this]
          rfl
      rcases h6 with h6 | h6
      · rw [hbij.1 (h6.trans hone.symm)]
        rfl
      · rw [hbij.1 (h6.trans hσ₀.symm)]
        exact hx
    · intro hx
      have hle : K ≤ IntermediateField.fixedField (Subgroup.zpowers σ₀) := by
        rw [hK, IntermediateField.adjoin_le_iff]
        have hgen : ∀ y, σ₀ y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers σ₀) := by
          intro y hy
          rw [IntermediateField.mem_fixedField_iff, Subgroup.forall_mem_zpowers]
          exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := σ₀)).mpr hy
        rintro y (rfl | rfl)
        · refine hgen _ (Subtype.ext ?_)
          rw [hab σ₀, hσ₀]
          simp [UpperTheory.Reformulated.B.JumpSetsAlt.cc, UpperTheory.Reformulated.B.JumpSetsAlt.c0, UpperTheory.Reformulated.B.JumpSetsAlt.aE, UpperTheory.Reformulated.B.JumpSetsAlt.bE]
        · exact hgen _ ((hth σ₀).mp (by rw [hσ₀]; rfl))
      exact (IntermediateField.mem_fixedField_iff _ x).mp (hle hx) σ₀ (Subgroup.mem_zpowers σ₀)
end UpperTheory.Reformulated.B.JumpSetsAlt
