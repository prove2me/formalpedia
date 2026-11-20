-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P24.mueller_jones_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:05:44.656182+00:00
-- url     : https://prove2.me/submissions/621b315f-1df9-4021-bbcc-dcb73a1b040b

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩
open scoped MatrixOrder

theorem AuxMJ_expand (Φ : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) (X : PolarizationMatrix) :
    Φ X = ∑ a, ∑ b, X a b • Φ (Matrix.single a b 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem AuxMJ_dual_apply (T : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) (M : PolarizationMatrix)
    (i j : Fin 2) :
    traceDual T M i j = ∑ x, ∑ y, T (Matrix.single j i 1) y x * M x y := rfl

theorem AuxMJ_dual_comp (P Q : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) :
    traceDual (P.comp Q) = (traceDual Q).comp (traceDual P) := by
  apply LinearMap.ext; intro M; ext i j
  rw [LinearMap.comp_apply, AuxMJ_dual_apply, AuxMJ_dual_apply]
  simp only [AuxMJ_dual_apply, LinearMap.comp_apply]
  conv_lhs => enter [2, x, 2, y]; rw [AuxMJ_expand P (Q _)]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  simp only [Fin.sum_univ_two]
  ring

theorem AuxMJ_cp_pos (Φ : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix)
    (h : QAlgorithms.Entanglement.IsCompletelyPositive Φ) : IsPositiveMap Φ := by
  intro X hX
  have hY := hX.submatrix (Prod.snd : Fin 1 × Fin 2 → Fin 2)
  have h1 := (h 1 _ hY).submatrix (fun j : Fin 2 => ((0 : Fin 1), j))
  convert h1 using 1
  ext i j; rfl

theorem AuxMJ_cp_comp (P Q : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix)
    (hP : QAlgorithms.Entanglement.IsCompletelyPositive P)
    (hQ : QAlgorithms.Entanglement.IsCompletelyPositive Q) :
    QAlgorithms.Entanglement.IsCompletelyPositive (P.comp Q) := by
  intro r X hX
  exact hP r _ (hQ r X hX)

theorem AuxMJ_trace_nonneg {A B : PolarizationMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have := (hB.mul_mul_conjTranspose_same C).trace_nonneg
  simpa [Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using this

theorem AuxMJ_dual_pos (T : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) (hT : IsPositiveMap T) :
    IsPositiveMap (traceDual T) := by
  intro M hM
  have key : ∀ v : Fin 2 → ℂ, star v ⬝ᵥ (traceDual T M *ᵥ v) =
      (M * T (Matrix.vecMulVec v (star v))).trace := by
    intro v
    rw [AuxMJ_expand T (Matrix.vecMulVec v (star v))]
    simp only [dotProduct, Matrix.mulVec, AuxMJ_dual_apply, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
      Fin.sum_univ_two, Pi.star_apply, Matrix.add_apply]
    ring
  have hnn : ∀ v : Fin 2 → ℂ, 0 ≤ star v ⬝ᵥ (traceDual T M *ᵥ v) := fun v => by
    rw [key]; exact AuxMJ_trace_nonneg hM (hT _ (Matrix.posSemidef_vecMulVec_self_star v))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ hnn
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have h := hnn (WithLp.ofLp v)
  have hre : (starRingEnd ℂ) (star (WithLp.ofLp v) ⬝ᵥ (traceDual T M *ᵥ WithLp.ofLp v)) =
      star (WithLp.ofLp v) ⬝ᵥ (traceDual T M *ᵥ WithLp.ofLp v) :=
    Complex.conj_eq_iff_im.mpr (Complex.nonneg_iff.mp h).2.symm
  have hin : inner ℂ ((traceDual T M).toEuclideanLin v) v =
      (starRingEnd ℂ) (star (WithLp.ofLp v) ⬝ᵥ (traceDual T M *ᵥ WithLp.ofLp v)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
      Matrix.dotProduct_star, dotProduct_comm]; rfl
  rw [hin, hre]; exact hre

theorem _root_.solution (P Q R : MuellerJonesPair)
    (hP : IsMuellerJones P) (hQ : IsMuellerJones Q) (hR : IsMuellerJones R) :
    IsMuellerJones (muellerJonesCompose P Q) ∧
      muellerJonesCompose (muellerJonesCompose P Q) R =
        muellerJonesCompose P (muellerJonesCompose Q R) := by
  obtain ⟨⟨hPcp, hP1, hPd⟩, hPj, hPpos⟩ := hP
  obtain ⟨⟨hQcp, hQ1, hQd⟩, hQj, hQpos⟩ := hQ
  have hPp := AuxMJ_cp_pos _ hPcp
  have hQp := AuxMJ_cp_pos _ hQcp
  refine ⟨⟨⟨AuxMJ_cp_comp _ _ hPcp hQcp, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · show (1 - P.1 (Q.1 1)).PosSemidef
    have : 1 - P.1 (Q.1 1) = (1 - P.1 1) + P.1 (1 - Q.1 1) := by
      rw [map_sub]; abel
    rw [this]; exact hP1.add (hPp _ hQ1)
  · show (1 - traceDual (P.1.comp Q.1) 1).PosSemidef
    rw [AuxMJ_dual_comp, LinearMap.comp_apply]
    have : 1 - traceDual Q.1 (traceDual P.1 1) =
        (1 - traceDual Q.1 1) + traceDual Q.1 (1 - traceDual P.1 1) := by
      rw [map_sub]; abel
    rw [this]; exact hQd.add (AuxMJ_dual_pos _ hQp _ hPd)
  · show (1 - P.2 * Q.2 * (P.2 * Q.2)ᴴ).PosSemidef
    have : 1 - P.2 * Q.2 * (P.2 * Q.2)ᴴ =
        (1 - P.2 * P.2ᴴ) + P.2 * (1 - Q.2 * Q.2ᴴ) * P.2ᴴ := by
      rw [Matrix.conjTranspose_mul]; noncomm_ring
    rw [this]; exact hPj.add (hQj.mul_mul_conjTranspose_same _)
  · intro X hX
    show (P.1 (Q.1 X) - P.2 * Q.2 * X * (P.2 * Q.2)ᴴ).PosSemidef
    have hJ : (Q.2 * X * Q.2ᴴ).PosSemidef := hX.mul_mul_conjTranspose_same _
    have h1 := hPp _ (hQpos X hX)
    have h2 := hPpos _ hJ
    change (P.1 (Q.1 X - Q.2 * X * Q.2ᴴ)).PosSemidef at h1
    change (P.1 (Q.2 * X * Q.2ᴴ) - P.2 * (Q.2 * X * Q.2ᴴ) * P.2ᴴ).PosSemidef at h2
    have : P.1 (Q.1 X) - P.2 * Q.2 * X * (P.2 * Q.2)ᴴ =
        P.1 (Q.1 X - Q.2 * X * Q.2ᴴ) +
          (P.1 (Q.2 * X * Q.2ᴴ) - P.2 * (Q.2 * X * Q.2ᴴ) * P.2ᴴ) := by
      rw [map_sub, Matrix.conjTranspose_mul]; noncomm_ring
    rw [this]; exact h1.add h2
  · simp [muellerJonesCompose, LinearMap.comp_assoc, Matrix.mul_assoc]

end QAlgorithms.Papers.Independent.Intake100.P24

end
