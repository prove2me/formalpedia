-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ModelLocalizationMaximalPoint_proof_1cc86273a304
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:49.456916+00:00
-- url     : https://prove2.me/submissions/01d293b4-45a8-4711-befe-01f64192bc85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PModelLocalizationMaximalPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ModelLocalizationMaximalPoint
theorem _root_.solution : ModelLocalizationMaximalPoint.Statement := by
  intro n J q M P hP
  let A := MvPolynomial (Fin n) ℂ
  let R' := MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal
  let L := Localization (normalModelSubmonoid M q)
  let ι : A →+* MvPolynomial (Fin n ⊕ Fin M.m) ℂ :=
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
  let φ : A →+* R' := (Ideal.Quotient.mk M.ideal).comp ι
  let _ : Algebra A R' := φ.toAlgebra
  have hφ : ∀ f : A, algebraMap A R' f = Ideal.Quotient.mk M.ideal (rename Sum.inl f) := fun _ ↦ rfl

  have hint : Algebra.IsIntegral A R' := by
    constructor
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C c =>
      have h : algebraMap A R' (C c) = Ideal.Quotient.mk M.ideal (C c) := by rw [hφ, rename_C]
      exact h ▸ isIntegral_algebraMap
    | add p r hp hr => rw [map_add]; exact hp.add hr
    | mul_X p s hp =>
      rw [map_mul]
      refine hp.mul ?_
      cases s with
      | inl i =>
        have h : algebraMap A R' (X i) = Ideal.Quotient.mk M.ideal (X (Sum.inl i)) := by rw [hφ, rename_X]
        exact h ▸ isIntegral_algebraMap
      | inr i =>
        obtain ⟨F, hmon, hF⟩ := M.integral i
        refine ⟨F, hmon, ?_⟩
        rw [RingHom.algebraMap_toAlgebra, show φ = (Ideal.Quotient.mk M.ideal).comp ι from rfl,
          ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
        exact hF

  let m : Ideal A := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, eval_C c⟩
  let Q : Ideal R' := P.comap (algebraMap R' L)
  have hQm : Q.comap (algebraMap A R') ≤ m := by
    intro f hf
    by_contra hfm
    have hS : algebraMap A R' f ∈ normalModelSubmonoid M q := Submonoid.mem_map_of_mem _ hfm
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (IsLocalization.map_units L ⟨_, hS⟩))

  obtain ⟨Q', hQQ', hQ'prime, hQ'm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral m Q hQm
  have hdisj : Disjoint (normalModelSubmonoid M q : Set R') Q' := by
    rw [Set.disjoint_left]
    rintro _ ⟨f, hf, rfl⟩ hfQ
    apply hf
    have h : f ∈ Q'.comap (algebraMap A R') := hfQ
    rw [hQ'm] at h
    exact h
  have hPQ' : P = Q'.map (algebraMap R' L) := by
    have hne : Q'.map (algebraMap R' L) ≠ ⊤ :=
      (IsLocalization.isPrime_of_isPrime_disjoint (normalModelSubmonoid M q) L Q' hQ'prime hdisj).ne_top
    refine hP.eq_of_le hne ?_
    rw [← IsLocalization.map_under (normalModelSubmonoid M q) L P]
    exact Ideal.map_mono hQQ'
  have hQeq : P.comap (algebraMap R' L) = Q' := by
    rw [hPQ']
    exact IsLocalization.under_map_of_isPrime_disjoint (normalModelSubmonoid M q) L hQ'prime hdisj
  have hQ'max : Q'.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q' (hQ'm ▸ hm)

  let N := P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))
  have hNmax : N.IsMaximal := by
    show (P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))).IsMaximal
    rw [← Ideal.comap_comap, hQeq]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hNmax
  have key : ∀ p, p ∈ N ↔ eval w p = 0 := fun p ↦ by
    rw [hw, mem_vanishingIdeal_singleton_iff]
    exact Iff.rfl
  refine ⟨w, fun p hp ↦ (key p).1 ?_, ?_, ?_⟩
  · show algebraMap R' L (Ideal.Quotient.mk M.ideal p) ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    exact P.zero_mem
  · funext i
    have h1 : X i - C (q i) ∈ m := by
      show eval q (X i - C (q i)) = 0
      rw [map_sub, eval_X, eval_C, sub_self]
    rw [← hQ'm, ← hQeq] at h1
    have h2 := (key (rename Sum.inl (X i - C (q i)))).1 h1
    simp only [map_sub, rename_X, rename_C, eval_X, eval_C] at h2
    exact sub_eq_zero.1 h2
  · ext p
    rw [RingHom.mem_ker]
    exact key p
end ModelLocalizationMaximalPoint
end GroundTheory.Heights₂.Heights
