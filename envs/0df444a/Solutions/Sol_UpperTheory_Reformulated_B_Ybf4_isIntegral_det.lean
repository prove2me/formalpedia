-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Ybf4.isIntegral_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:31.231924+00:00
-- url     : https://prove2.me/submissions/2c218863-e38e-47ac-93cb-ab6bb605fa94

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsIntegralDetOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial in
private theorem UpperTheory.Reformulated.B.Ybf4.isIntegral_det_of_isIntegral {R E : Type} [CommRing R] [Field E]
    [Algebra R E] {N : ℕ} (γ : Matrix (Fin N) (Fin N) E) (h : IsIntegral R γ) :
    IsIntegral R γ.det := by
  let K := AlgebraicClosure E
  let φ : Matrix (Fin N) (Fin N) E →ₐ[R] Matrix (Fin N) (Fin N) K :=
    (IsScalarTower.toAlgHom R E K).mapMatrix
  have hφ : IsIntegral R (φ γ) := h.map φ
  have hdet : algebraMap E K γ.det = (φ γ).det := RingHom.map_det (algebraMap E K) γ
  rw [← isIntegral_algebraMap_iff (B := K) (algebraMap E K).injective, hdet,
    Matrix.det_eq_prod_roots_charpoly]
  refine IsIntegral.multiset_prod fun μ hμ => ?_
  have hspec : μ ∈ spectrum K (φ γ) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hμ)
  obtain ⟨p, hp, hp0⟩ := hφ
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (φ γ) (p.map (algebraMap R K)) ⟨μ, hspec, rfl⟩
  rw [aeval_map_algebraMap, aeval_def, hp0] at h1
  simp only [eval_map] at h1
  by_contra hne
  apply h1
  rw [spectrum.mem_resolventSet_iff, sub_zero]
  exact (IsUnit.mk0 _ hne).map _
end

set_option autoImplicit false

open Polynomial
namespace UpperTheory.Reformulated.B.Ybf4
theorem _root_.solution :
    ∀ {E : Type} [inst : Field E] [NumberField E] {N : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)),
      L.FG →
        Submodule.span E (↑L : Set (Fin N → E)) = ⊤ →
          ∀ (γ : Matrix (Fin N) (Fin N) E), (∀ v ∈ L, γ.mulVec v ∈ L) → IsIntegral ℤ γ.det := by
  intro E _ _ N L hfg hspan γ hγ
  refine isIntegral_trans (A := NumberField.RingOfIntegers E) _
    (UpperTheory.Reformulated.B.Ybf4.isIntegral_det_of_isIntegral γ ?_)
  haveI : Module.Finite (NumberField.RingOfIntegers E) L := Module.Finite.iff_fg.2 hfg
  let g : (Fin N → E) →ₗ[NumberField.RingOfIntegers E] (Fin N → E) :=
    (Matrix.mulVecLin γ).restrictScalars _
  let f : Module.End (NumberField.RingOfIntegers E) L := g.restrict (p := L) (q := L) hγ
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (NumberField.RingOfIntegers E) f
  refine ⟨p, hp, ?_⟩
  have hpow : ∀ (n : ℕ) (v : L), ((f ^ n) v : Fin N → E) = (γ ^ n).mulVec v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih, ← Matrix.mulVec_mulVec]
      rfl
  have key : ∀ (q : (NumberField.RingOfIntegers E)[X]) (v : L),
      ((aeval f q) v : Fin N → E) = (aeval γ q).mulVec v := by
    intro q v
    induction q using Polynomial.induction_on' with
    | add a b ha hb => simp [ha, hb, Matrix.add_mulVec]
    | monomial n a =>
      rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        LinearMap.smul_apply, Submodule.coe_smul, hpow]
      ext i
      change a • (∑ j, (γ ^ n) i j * (v : Fin N → E) j) = ∑ j, (a • (γ ^ n) i j) * (v : Fin N → E) j
      simp only [Algebra.smul_def, mul_assoc, Finset.mul_sum]
  have hz : Matrix.mulVecLin (aeval γ p) = 0 := by
    refine LinearMap.ext_on hspan fun v hv => ?_
    have := key p ⟨v, hv⟩
    rw [hp0] at this
    simpa using this.symm
  rw [← aeval_def]
  apply Matrix.toLin'.injective
  rw [map_zero]
  exact hz
end UpperTheory.Reformulated.B.Ybf4
