-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.chartRing_frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:39.269394+00:00
-- url     : https://prove2.me/submissions/5bffcfc0-8fc2-4b40-b126-2235ffaae84f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : IsFractionRing (chartRing x e l) (fnField (x ∘ e)) := by
  classical

  have hne : ∀ i, x (e i) ≠ 0 := by
    intro i hi
    have hk : MvPolynomial.X i ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [hfree, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero i hk
  let R : Subring Ω := ((chartRing x e l).toSubring).map (fnField (x ∘ e)).val.toRingHom
  have hR : ∀ w ∈ R, ∃ a : chartRing x e l, ((a : fnField (x ∘ e)) : Ω) = w := by
    rintro w ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  let T : Set Ω := Set.range fun k : {k // k ≠ l} => x (e k) / x (e l)
  have hTR : Subring.closure T ≤ R := by
    rw [Subring.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨chartGen x e l k, Algebra.subset_adjoin ⟨k, rfl⟩, rfl⟩
  let F : IntermediateField ℚ Ω := (Subfield.closure T).toIntermediateField (fun q => by
    rw [eq_ratCast]
    exact SubfieldClass.ratCast_mem _ q)
  have hgen : ∀ i, x (e i) / x (e l) ∈ Subfield.closure T := by
    intro i
    by_cases h : i = l
    · subst h
      rw [div_self (hne i)]
      exact one_mem _
    · exact Subfield.subset_closure ⟨⟨i, h⟩, rfl⟩
  have hle : fnField (x ∘ e) ≤ F := by
    unfold fnField
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, j, rfl⟩
    have h3 : (x ∘ e) i / (x ∘ e) j = x (e i) / x (e l) / (x (e j) / x (e l)) := by
      simp only [Function.comp_apply]
      first
        | rw [div_div_div_cancel_right₀ (hne l)]
        | field_simp
    show _ ∈ Subfield.closure T
    rw [h3]
    exact div_mem (hgen i) (hgen j)
  have hsurj : ∀ z : fnField (x ∘ e), ∃ a b : chartRing x e l, b ≠ 0 ∧
      z * (b : fnField (x ∘ e)) = a := by
    intro z
    have hz : (z : Ω) ∈ Subfield.closure T := hle z.2
    obtain ⟨p, hp, q, hq, hpq⟩ := Subfield.mem_closure_iff.1 hz
    obtain ⟨a, ha⟩ := hR p (hTR hp)
    obtain ⟨b, hb⟩ := hR q (hTR hq)
    by_cases hq0 : q = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      apply Subtype.ext
      simp [← hpq, hq0]
    · refine ⟨a, b, ?_, ?_⟩
      · intro hb0
        apply hq0
        simp [← hb, hb0]
      · apply Subtype.ext
        show (z : Ω) * ((b : fnField (x ∘ e)) : Ω) = ((a : fnField (x ∘ e)) : Ω)
        rw [ha, hb, ← hpq, div_mul_cancel₀ _ hq0]
  have hinj : Function.Injective (algebraMap (chartRing x e l) (fnField (x ∘ e))) :=
    Subtype.val_injective
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, hb⟩
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb))
  · intro z
    obtain ⟨a, b, hb, h⟩ := hsurj z
    exact ⟨⟨a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩⟩, h⟩
  · intro a b h
    exact ⟨1, by simp [hinj h]⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
