-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_of_derivation_det_not_mem_28a934ea20c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:21.718134+00:00
-- url     : https://prove2.me/submissions/41fa38c8-5b65-428e-94c4-f4c117d9faae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationCotangentIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDerivationCotangentIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_derivation_mem_of_mem_sq_cb7946785f2b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {T : Type} [CommRing T] (P : Ideal T) [P.IsPrime] {h : ℕ}
    (D : Fin h → Derivation ℤ T T) (f : Fin h → T) (hf : ∀ i, f i ∈ P)
    (hdet : (Matrix.of fun i j => D j (f i)).det ∉ P) (b : Fin h → T) (t : T) (ht : t ∉ P)
    (hsum : t * ∑ i, b i * f i ∈ P ^ 2) (i : Fin h) : b i ∈ P := by
  set A : Matrix (Fin h) (Fin h) T := Matrix.of fun i j => D j (f i) with hA

  have hv : ∀ j, (b ᵥ* A) j ∈ P := by
    intro j
    have h1 := derivation_mem_of_mem_sq P (D j) hsum
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_sum] at h1
    have h2 : (∑ i, b i * f i) * D j t ∈ P :=
      P.mul_mem_right _ (P.sum_mem fun i _ => P.mul_mem_left _ (hf i))
    have h3 : t * ∑ i, D j (b i * f i) ∈ P := by
      have := P.sub_mem h1 h2; simpa using this
    have h4 : ∑ i, D j (b i * f i) ∈ P :=
      ((Ideal.IsPrime.mem_or_mem inferInstance h3).resolve_left ht)
    have h5 : ∑ i, D j (b i * f i) - ∑ i, f i * D j (b i) = (b ᵥ* A) j := by
      rw [← Finset.sum_sub_distrib]
      simp only [Matrix.vecMul, dotProduct, hA, Matrix.of_apply, Derivation.leibniz, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [← h5]
    exact P.sub_mem h4 (P.sum_mem fun i _ => P.mul_mem_right _ (hf i))

  have hw : (b ᵥ* A ᵥ* A.adjugate) i = A.det * b i := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
      Pi.smul_apply, smul_eq_mul]
  have hmem : (b ᵥ* A ᵥ* A.adjugate) i ∈ P := by
    simp only [Matrix.vecMul, dotProduct]
    exact P.sum_mem fun j _ => P.mul_mem_right _ (hv j)
  rw [hw] at hmem
  exact (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_left hdet
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
