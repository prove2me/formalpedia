-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.gFam_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:34.629872+00:00
-- url     : https://prove2.me/submissions/3fce3277-44db-40c7-a655-798ff11d6e1a

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_coeffDer_C
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_coeffDer_X
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_algebraicIndependent_of_derivations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
namespace DerivationAlgebraicIndependence
open MvPolynomial
section CoeffDer
variable {K Ω σ : Type*} [CommRing K] [CommRing Ω] [Algebra K Ω]
end CoeffDer
private theorem coeffDer_linearCombinationPoly_apply {K Ω : Type*} [CommRing K] [CommRing Ω]
    [Algebra K Ω] {D m : ℕ} (δ : Derivation K Ω Ω) (x : Fin m → Ω) (b : Fin D) :
    coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) δ (yPoly x b) =
      -∑ k, X (Sum.inr (b.succ, k)) * C (δ (x k)) := by
  simp only [yPoly, map_neg, map_sum, Derivation.leibniz, coeffDer_X,
    coeffDer_C, smul_eq_mul, mul_zero, add_zero]
private theorem restrictScalars_pderiv_apply {K Ω σ : Type*} [CommRing K] [CommRing Ω]
    [Algebra K Ω] (w : σ) (f : MvPolynomial σ Ω) :
    ((pderiv w : Derivation Ω (MvPolynomial σ Ω) (MvPolynomial σ Ω)).restrictScalars K) f =
      pderiv w f := by
  exact congrFun (Derivation.coe_restrictScalars K _) f
set_option maxHeartbeats 800000 in

private theorem det_sum_X_mul_C_ne_zero_of_dual_family {Ω : Type*} [Field Ω] {D m : ℕ} (y : Fin D → Fin m → Ω)
    (J : Fin D → Fin m) (hy : ∀ a b, y a (J b) = if a = b then 1 else 0) :
    (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k)).det ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : ReciprocityTheory.MultiplicativeHeights.SVars D m → Ω, ∀ (b : Fin D) (k : Fin m),
      p (Sum.inr (b.succ, k)) = if k = J b then 1 else 0 :=
    ⟨Sum.elim (fun _ => 0)
      (fun q => Fin.cases (motive := fun _ => Ω) 0 (fun b => if q.2 = J b then 1 else 0) q.1),
      fun b k => by simp⟩
  intro h0
  have hmap : (eval p).mapMatrix (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k)) = 1 := by
    ext a b
    simp [RingHom.mapMatrix_apply, hp, hy, Matrix.one_apply]
  have h1 := RingHom.map_det (eval p) (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k))
  rw [h0, map_zero, hmap, Matrix.det_one] at h1
  exact zero_ne_one h1
end DerivationAlgebraicIndependence
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial
set_option maxHeartbeats 800000
namespace ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
theorem _root_.solution {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (x : Fin m → Ω) (J : Fin D → Fin m) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0) :
    AlgebraicIndependent K (gFam (D := D) x) := by
  classical
  have hz_inl : ∀ w, gFam (D := D) x (Sum.inl w) = X w := fun _ => rfl
  have hz_inr : ∀ b, gFam (D := D) x (Sum.inr b) = yPoly x b :=
    fun _ => rfl
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin D) (Fin D) (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω),
      N = Matrix.of fun a b : Fin D =>
        ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (δ a (x k)) :=
    ⟨_, rfl⟩
  have hNe : ∀ a b, N a b =
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (δ a (x k)) := by
    intro a b
    rw [hN]
    rfl
  have hcd : ∀ a b, coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) (δ a) (yPoly x b) =
      -N a b := by
    intro a b
    rw [hNe, coeffDer_linearCombinationPoly_apply]
  have hdet : N.det ≠ 0 := by
    rw [hN]
    exact det_sum_X_mul_C_ne_zero_of_dual_family (fun a k => δ a (x k)) J hδ
  refine algebraicIndependent_of_derivations (gFam (D := D) x)
    (Sum.elim (fun w : ReciprocityTheory.MultiplicativeHeights.SVars D m => (pderiv w : Derivation Ω (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω)
        (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω)).restrictScalars K)
      (fun a : Fin D => coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) (δ a))) ?_
  intro c hc
  have hmv : Matrix.mulVec N (fun b => c (Sum.inr b)) = 0 := by
    funext a
    have h1 := hc (Sum.inr a)
    simp only [Sum.elim_inr, Fintype.sum_sum_type, hz_inl, hz_inr, coeffDer_X, mul_zero,
      Finset.sum_const_zero, zero_add, hcd, mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at h1
    show ∑ b, N a b * c (Sum.inr b) = 0
    exact (Finset.sum_congr rfl fun b _ => mul_comm (N a b) (c (Sum.inr b))).trans h1
  have hinr : ∀ b, c (Sum.inr b) = 0 := fun b =>
    congr_fun (Matrix.eq_zero_of_mulVec_eq_zero hdet hmv) b
  intro i
  rcases i with w | b
  · have h2 := hc (Sum.inl w)
    rw [Fintype.sum_sum_type] at h2
    simp only [Sum.elim_inl, hinr, zero_mul, Finset.sum_const_zero, add_zero,
      restrictScalars_pderiv_apply, hz_inl] at h2
    rw [Finset.sum_eq_single w] at h2
    · rw [pderiv_X_self, mul_one] at h2
      exact h2
    · intro w' _ hw'
      rw [pderiv_X_of_ne hw', mul_zero]
    · intro h
      exact absurd (Finset.mem_univ w) h
  · exact hinr b
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
