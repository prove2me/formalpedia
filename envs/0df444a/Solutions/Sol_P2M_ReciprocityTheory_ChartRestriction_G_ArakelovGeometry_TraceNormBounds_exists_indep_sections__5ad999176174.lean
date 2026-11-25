-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_exists_indep_sections__5ad999176174
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:01.669256+00:00
-- url     : https://prove2.me/submissions/5a124cb3-1eff-4fff-92e5-19f1685ffda8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_closure_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_div_mem_fnField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_sec_div_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
private theorem gens_lemma_2 [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    (∀ i, IsIntegral (fnField (x ∘ e)) (x i / x (e 0))) ∧
      IntermediateField.extendScalars (fnField_comp_le' x e) =
        IntermediateField.adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  classical
  have hne : x (e 0) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X 0 ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero 0 hk
  have hgen : ∀ k, x (e k) / x (e 0) ∈ fnField (x ∘ e) := fun k => div_mem_fnField (x ∘ e) k 0
  have hcone : ∀ q : MvPolynomial (Fin (D + 1)) ℚ,
      Polynomial.evalRingHom (x (e 0))⁻¹ (coneMap ℚ (x ∘ e) q) ∈ fnField (x ∘ e) := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      unfold coneMap
      rw [MvPolynomial.aeval_C]
      first
        | (rw [Polynomial.algebraMap_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
           exact IntermediateField.algebraMap_mem _ a)
        | simpa using IntermediateField.algebraMap_mem (fnField (x ∘ e)) a
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
  have hmem : ∀ v : coneRing ℚ (x ∘ e),
      ((Polynomial.evalRingHom (x (e 0))⁻¹).comp (coneRing ℚ (x ∘ e)).val.toRingHom) v ∈
        fnField (x ∘ e) := by
    rintro ⟨v, q, rfl⟩
    exact hcone q
  let φ : coneRing ℚ (x ∘ e) →+* fnField (x ∘ e) :=
    ((Polynomial.evalRingHom (x (e 0))⁻¹).comp (coneRing ℚ (x ∘ e)).val.toRingHom).codRestrict
      (fnField (x ∘ e)) hmem
  have hint : ∀ i, IsIntegral (fnField (x ∘ e)) (x i / x (e 0)) := by
    intro i
    obtain ⟨p, hm, hp⟩ := h.integral i
    refine ⟨p.map φ, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (fnField (x ∘ e)) Ω).comp φ =
        (Polynomial.evalRingHom (x (e 0))⁻¹).comp
          (algebraMap (coneRing ℚ (x ∘ e)) (Polynomial Ω)) := RingHom.ext fun _ => rfl
    have hpt : x i / x (e 0) =
        Polynomial.evalRingHom (x (e 0))⁻¹ (Polynomial.C (x i) * Polynomial.X) := by
      simp [div_eq_mul_inv]
    rw [hcomp, hpt, ← Polynomial.hom_eval₂, hp, map_zero]
  let S : Set Ω := Set.range fun i => x i / x (e 0)
  have heq : IntermediateField.extendScalars (fnField_comp_le' x e) =
      IntermediateField.adjoin (fnField (x ∘ e)) S := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ fnField x := (IntermediateField.mem_extendScalars _).1 hz
      have hle : IntermediateField.adjoin ℚ {t | ∃ i j, t = x i / x j} ≤
          (IntermediateField.adjoin (fnField (x ∘ e)) S).restrictScalars ℚ := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨i, j, rfl⟩
        have h3 : x i / x j = x i / x (e 0) / (x j / x (e 0)) := by
          first
            | rw [div_div_div_cancel_right₀ hne]
            | field_simp
        show x i / x j ∈ IntermediateField.adjoin (fnField (x ∘ e)) S
        rw [h3]
        have hi : x i / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e)) S :=
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
        have hj : x j / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e)) S :=
          IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
        exact div_mem hi hj
      exact hle hz'
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact (IntermediateField.mem_extendScalars _).2 (div_mem_fnField x i (e 0))
  exact ⟨hint, heq⟩
private theorem finrat_lemma [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  obtain ⟨hint, heq⟩ := gens_lemma_2 x e h
  rw [heq]
  exact IntermediateField.finiteDimensional_adjoin fun z hz => by
    obtain ⟨i, rfl⟩ := hz
    exact hint i
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ)
    (h : IsRatProjFrame x e) :
    ∃ (k : ℕ) (ε : Fin (projDeg x e) → Ω), (∀ l, ε l ∈ sec ℤ x k) ∧
      LinearIndependent (fnField (x ∘ e)) ε := by
  classical
  obtain ⟨hint, heq⟩ := gens_lemma_2 x e h
  haveI := finrat_lemma x e h
  have hne : x (e 0) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X 0 ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero 0 hk

  let T : Set Ω := Submonoid.closure (Set.range fun i => x i / x (e 0))
  have hTL : ∀ z ∈ T, z ∈ IntermediateField.extendScalars (fnField_comp_le' x e) := by
    intro z hz
    obtain ⟨d, σ, hσ, rfl⟩ := closure_mem x e z hz
    exact sec_div_mem x (e 0) hσ
  let s : Set (IntermediateField.extendScalars (fnField_comp_le' x e)) := {z | (z : Ω) ∈ T}
  have hspanΩ : ∀ z ∈ IntermediateField.extendScalars (fnField_comp_le' x e),
      z ∈ Submodule.span (fnField (x ∘ e)) T := by
    intro z hz
    rw [heq] at hz
    have h1 : z ∈ (IntermediateField.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0))).toSubalgebra := hz
    have hSi : ∀ w ∈ Set.range (fun i => x i / x (e 0)), IsIntegral (fnField (x ∘ e)) w := by
      rintro w ⟨i, rfl⟩
      exact hint i
    first
      | rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun w hw => (hSi w hw).isAlgebraic)] at h1
      | rw [IntermediateField.adjoin_toSubalgebra_of_isIntegral hSi] at h1
      | rw [IntermediateField.adjoin_algebraic_toSubalgebra (fun w hw => (hSi w hw).isAlgebraic)] at h1
      | rw [IntermediateField.adjoin_integral_toSubalgebra hSi] at h1
    have h2 : z ∈ Subalgebra.toSubmodule (Algebra.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0))) := h1
    rwa [Algebra.adjoin_eq_span] at h2
  have hspan : Submodule.span (fnField (x ∘ e)) s = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have h1 := hspanΩ z z.2
    have h2 : Submodule.span (fnField (x ∘ e)) T = (Submodule.span (fnField (x ∘ e)) s).map
        (IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap := by
      rw [Submodule.map_span]
      congr 1
      ext w
      constructor
      · intro hw
        exact ⟨⟨w, hTL w hw⟩, hw, rfl⟩
      · rintro ⟨w', hw', rfl⟩
        exact hw'
    rw [h2] at h1
    obtain ⟨w, hw, hwz⟩ := h1
    have hwz' : w = z := Subtype.ext hwz
    rwa [← hwz']
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (fnField (x ∘ e)) s
  have hbtop : ⊤ ≤ Submodule.span (fnField (x ∘ e))
      (Set.range (Subtype.val : b → IntermediateField.extendScalars (fnField_comp_le' x e))) := by
    first
      | rw [Subtype.range_coe, hbspan, hspan]
      | rw [Subtype.range_val, hbspan, hspan]
  let B := Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis B
  haveI : Fintype b := Fintype.ofFinite b
  have hpd : projDeg x e = Module.finrank (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
    unfold projDeg
    first
      | exact IntermediateField.relfinrank_eq_finrank_of_le (fnField_comp_le' x e)
      | rfl
  have hcard : Fintype.card b = projDeg x e := by
    rw [hpd, Module.finrank_eq_card_basis B]
  let eqv : Fin (projDeg x e) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hdec : ∀ j, ∃ d, ∃ σ ∈ sec ℤ x d, (((eqv j : b) : IntermediateField.extendScalars
      (fnField_comp_le' x e)) : Ω) = σ / x (e 0) ^ d :=
    fun j => closure_mem x e _ (hbs (eqv j).2)
  choose d σ hσ hdeq using hdec
  obtain ⟨k, hk⟩ : ∃ k, k = Finset.univ.sup d := ⟨_, rfl⟩
  have hdk : ∀ j, d j ≤ k := fun j => hk ▸ Finset.le_sup (Finset.mem_univ j)
  refine ⟨k, fun j => σ j * x (e 0) ^ (k - d j), fun j => ?_, ?_⟩
  · obtain ⟨p, hp, hps⟩ := Submodule.mem_map.1 (hσ j)
    refine Submodule.mem_map.2 ⟨p * MvPolynomial.X (e 0) ^ (k - d j), ?_, ?_⟩
    · have h3 := ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp).mul
        ((MvPolynomial.isHomogeneous_X ℤ (e 0)).pow (k - d j))
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa [Nat.add_sub_of_le (hdk j)] using h3
    · show (MvPolynomial.aeval x).toLinearMap (p * MvPolynomial.X (e 0) ^ (k - d j)) =
        σ j * x (e 0) ^ (k - d j)
      rw [← hps]
      simp
  · have hli1 : LinearIndependent (fnField (x ∘ e))
        (fun j => (((eqv j : b) : IntermediateField.extendScalars (fnField_comp_le' x e)) : Ω)) :=
      (hbli.comp eqv eqv.injective).map'
        (IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap
        (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    have hli2 := hli1.map' (LinearMap.mulRight (fnField (x ∘ e)) (x (e 0) ^ k))
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (pow_ne_zero k hne)))
    have hfun : (⇑(LinearMap.mulRight (fnField (x ∘ e)) (x (e 0) ^ k)) ∘
        fun j => (((eqv j : b) : IntermediateField.extendScalars (fnField_comp_le' x e)) : Ω)) =
        fun j => σ j * x (e 0) ^ (k - d j) := by
      funext j
      simp only [Function.comp_apply, LinearMap.mulRight_apply, hdeq j]
      have hk' : x (e 0) ^ k = x (e 0) ^ d j * x (e 0) ^ (k - d j) := by
        rw [← pow_add, Nat.add_sub_of_le (hdk j)]
      rw [hk']
      have hc := pow_ne_zero (d j) hne
      field_simp
      try ring
    rw [hfun] at hli2
    exact hli2
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
