-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.coord_div_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:37.149814+00:00
-- url     : https://prove2.me/submissions/3688a887-4df9-4148-a96c-d6662b5f15bb

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
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e)
    (l : Fin (D + 1)) (i : κ) : IsIntegral (chartRing x e l) (x i / x (e l)) := by
  classical
  have hne : x (e l) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X l ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero l hk
  let R : Subring Ω := ((chartRing x e l).toSubring).map (fnField (x ∘ e)).val.toRingHom
  have hgen : ∀ k, x (e k) / x (e l) ∈ R := by
    intro k
    by_cases hk : k = l
    · subst hk
      rw [div_self hne]
      exact one_mem _
    · exact ⟨chartGen x e l ⟨k, hk⟩, Algebra.subset_adjoin ⟨⟨k, hk⟩, rfl⟩, rfl⟩

  have hcone : ∀ q : MvPolynomial (Fin (D + 1)) ℤ,
      Polynomial.evalRingHom (x (e l))⁻¹ (coneMap ℤ (x ∘ e) q) ∈ R := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      unfold coneMap
      rw [MvPolynomial.aeval_C, eq_intCast, map_intCast]
      exact intCast_mem R a
    next p1 p2 h1 h2 =>
      rw [map_add, map_add]
      exact add_mem h1 h2
    next p1 k h1 =>
      rw [map_mul, map_mul]
      refine mul_mem h1 ?_
      unfold coneMap
      rw [MvPolynomial.aeval_X]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Function.comp_apply]
      rw [← div_eq_mul_inv]
      exact hgen k
  have hmem : ∀ v : coneRing ℤ (x ∘ e),
      ((Polynomial.evalRingHom (x (e l))⁻¹).comp (coneRing ℤ (x ∘ e)).val.toRingHom) v ∈ R := by
    rintro ⟨v, q, rfl⟩
    exact hcone q
  let φ : coneRing ℤ (x ∘ e) →+* R :=
    ((Polynomial.evalRingHom (x (e l))⁻¹).comp (coneRing ℤ (x ∘ e)).val.toRingHom).codRestrict R hmem
  let eqv : (chartRing x e l).toSubring ≃+* R :=
    Subring.equivMapOfInjective _ _ (fun a b hab => Subtype.ext hab)
  let ψ : R →+* chartRing x e l := eqv.symm.toRingHom
  obtain ⟨p, hm, hp⟩ := h.integral i
  refine ⟨(p.map φ).map ψ, (hm.map _).map _, ?_⟩
  rw [Polynomial.eval₂_map, Polynomial.eval₂_map]
  have hcomp : ((algebraMap (chartRing x e l) Ω).comp ψ).comp φ =
      (Polynomial.evalRingHom (x (e l))⁻¹).comp (algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω)) := by
    refine RingHom.ext fun v => ?_
    have h2 := congrArg Subtype.val (eqv.apply_symm_apply (φ v))
    first
      | exact h2
      | (simp only [eqv, Subring.coe_equivMapOfInjective_apply] at h2; exact h2)
  have hpt : x i / x (e l) = Polynomial.evalRingHom (x (e l))⁻¹ (Polynomial.C (x i) * Polynomial.X) := by
    simp [div_eq_mul_inv]
  rw [hcomp, hpt, ← Polynomial.hom_eval₂, hp, map_zero]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
