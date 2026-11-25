-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_extend_ff791a453812
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:32:00.303688+00:00
-- url     : https://prove2.me/submissions/c0ad6f73-311a-4830-b390-319f660fac20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothPartialLifts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothExtensionStep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PartialLiftLE_trans_b74671c00bb0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial IntermediateField
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] [CharP K p] {N : Ideal B}
    {u : K →ₐ[F] B ⧸ N} {ψ : K →+* B} (hψ : ∀ (z : K) (c : B), Ideal.Quotient.mk N c = u z → ψ z = c ^ p)
    {L : IntermediateField F K} {φ : L →ₐ[F] B} (hgood : IsGoodPartialLift p N u ψ ⟨L, φ⟩) {x : K}
    (hx : x ∉ L) :
    ∃ σ : Σ L : IntermediateField F K, L →ₐ[F] B,
      IsGoodPartialLift p N u ψ σ ∧ PartialLiftLE ⟨L, φ⟩ σ ∧ x ∈ σ.1 := by
  let _ : Algebra L B := φ.toRingHom.toAlgebra
  have : IsScalarTower F L B := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨hxp, hφx⟩ := hgood.1 x
  let a : L := ⟨x ^ p, hxp⟩
  have hirr : Irreducible (X ^ p - Polynomial.C a) := X_pow_sub_C_irreducible_of_prime hp.out fun b hb => hx (by
    have hb' : (b : K) ^ p = x ^ p := congrArg Subtype.val hb
    have hbx := frobenius_inj K p (show frobenius K p (b : K) = frobenius K p x by
      rw [frobenius_def, frobenius_def]; exact hb')
    rw [← hbx]
    exact b.2)
  have hmonic : (X ^ p - Polynomial.C a).Monic := monic_X_pow_sub_C a hp.out.ne_zero
  have hxroot : aeval x (X ^ p - Polynomial.C a) = 0 := by simp [a]
  have hmin : minpoly L x = X ^ p - Polynomial.C a :=
    (minpoly.eq_of_irreducible_of_monic hirr hxroot hmonic).symm
  have hint : IsIntegral L x := ⟨_, hmonic, hxroot⟩
  let pb := IntermediateField.adjoin.powerBasis hint
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u x)
  have hroot : aeval c (minpoly L pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin, map_sub, map_pow,
      aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
    show c ^ p - φ a = 0
    rw [hφx, hψ x c hc, sub_self]
  let σ₁ := pb.lift c hroot
  let L' : IntermediateField F K := IntermediateField.restrictScalars F (L⟮x⟯)
  let σ : L' →ₐ[F] B := σ₁.restrictScalars F
  have hLL' : L ≤ L' := fun y hy => (L⟮x⟯).algebraMap_mem ⟨y, hy⟩
  have hext : ∀ y : L, σ (IntermediateField.inclusion hLL' y) = φ y := fun y => σ₁.commutes y
  have hring : (Ideal.Quotient.mk N).comp (algebraMap L B) = (u : K →+* B ⧸ N).comp (algebraMap L K) :=
    RingHom.ext fun l => hgood.2 l
  refine ⟨⟨L', σ⟩, ⟨fun z => ?_, fun y => ?_⟩, ⟨hLL', hext⟩, IntermediateField.mem_adjoin_simple_self L x⟩
  · obtain ⟨h, h'⟩ := hgood.1 z
    exact ⟨hLL' h, (hext ⟨_, h⟩).trans h'⟩
  · obtain ⟨f, hf⟩ := pb.exists_eq_aeval' ⟨y.1, y.2⟩
    have hy : (y : K) = aeval x f := by
      have h' := congrArg (algebraMap (L⟮x⟯) K) hf
      rw [← Polynomial.aeval_algebraMap_apply, IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.AdjoinSimple.algebraMap_gen] at h'
      exact h'
    show Ideal.Quotient.mk N (σ₁ ⟨y.1, y.2⟩) = u y
    rw [hf, PowerBasis.lift_aeval, hy, aeval_def, aeval_def, Polynomial.hom_eval₂, hring, hc]
    exact (Polynomial.hom_eval₂ _ _ _ _).symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
