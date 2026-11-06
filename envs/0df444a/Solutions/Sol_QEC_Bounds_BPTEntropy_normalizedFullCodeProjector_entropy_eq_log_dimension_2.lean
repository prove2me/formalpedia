-- Prove2me | solution 2 for QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_entropy_eq_log_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:13.668496+00:00
-- url     : https://prove2.me/submissions/af5fdf84-d3ce-4ecf-8400-db3c8638ac2e

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u

namespace QBAux

theorem ptr_map_dualTensorHom {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (f : Module.Dual Complex H) (x : H) (g : Module.Dual Complex K) (y : K) :
    Semantics.partialTraceRightRaw H K
      (TensorProduct.map (dualTensorHom Complex H H (f ⊗ₜ[Complex] x))
        (dualTensorHom Complex K K (g ⊗ₜ[Complex] y))) =
      g y • dualTensorHom Complex H H (f ⊗ₜ[Complex] x) := by
  have h1 : TensorProduct.map (dualTensorHom Complex H H (f ⊗ₜ[Complex] x))
        (dualTensorHom Complex K K (g ⊗ₜ[Complex] y)) =
      dualTensorHom Complex (H ⊗[Complex] K) (H ⊗[Complex] K)
        (TensorProduct.dualDistrib Complex H K (f ⊗ₜ[Complex] g) ⊗ₜ[Complex] (x ⊗ₜ[Complex] y)) := by
    apply TensorProduct.ext'
    intro h k
    simp [dualTensorHom_apply, TensorProduct.smul_tmul', smul_smul, mul_comm]
  rw [h1]
  have hu : (dualTensorHomEquiv Complex (H ⊗[Complex] K) (H ⊗[Complex] K)).symm
      (dualTensorHom Complex (H ⊗[Complex] K) (H ⊗[Complex] K)
        (TensorProduct.dualDistrib Complex H K (f ⊗ₜ[Complex] g) ⊗ₜ[Complex] (x ⊗ₜ[Complex] y))) =
      TensorProduct.dualDistrib Complex H K (f ⊗ₜ[Complex] g) ⊗ₜ[Complex] (x ⊗ₜ[Complex] y) :=
    (dualTensorHomEquiv Complex (H ⊗[Complex] K) (H ⊗[Complex] K)).symm_apply_apply _
  have hd : (TensorProduct.dualDistribEquiv Complex H K).symm
      (TensorProduct.dualDistrib Complex H K (f ⊗ₜ[Complex] g)) = f ⊗ₜ[Complex] g :=
    (TensorProduct.dualDistribEquiv Complex H K).symm_apply_apply _
  unfold Semantics.partialTraceRightRaw
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hu]
  simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe, hd, TensorProduct.tensorTensorTensorComm_tmul,
    LinearMap.id_apply, contractLeft_apply, TensorProduct.rid_tmul]
  simp

theorem rankOne_eq_dualTensorHom {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (x x' : H) :
    (InnerProductSpace.rankOne Complex x x').toLinearMap =
      dualTensorHom Complex H H (innerₛₗ Complex x' ⊗ₜ[Complex] x) := by
  apply LinearMap.ext
  intro z
  simp [dualTensorHom_apply, InnerProductSpace.rankOne_apply]

theorem ptr_rankOne_tmul {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (x x' : H) (y y' : K) :
    Semantics.partialTraceRightRaw H K
        (InnerProductSpace.rankOne Complex (x ⊗ₜ[Complex] y) (x' ⊗ₜ[Complex] y')).toLinearMap =
      inner Complex y' y • (InnerProductSpace.rankOne Complex x x').toLinearMap := by
  have h : (InnerProductSpace.rankOne Complex (x ⊗ₜ[Complex] y) (x' ⊗ₜ[Complex] y')).toLinearMap =
      TensorProduct.map (InnerProductSpace.rankOne Complex x x').toLinearMap
        (InnerProductSpace.rankOne Complex y y').toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    simp [InnerProductSpace.rankOne_apply, TensorProduct.inner_tmul, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_smul, mul_comm]
  rw [h, rankOne_eq_dualTensorHom x x', rankOne_eq_dualTensorHom y y', ptr_map_dualTensorHom]
  simp

theorem rankOne_sum_sum {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    {ι : Type*} [Fintype ι] (c : Complex) (u : ι → H) :
    InnerProductSpace.rankOne Complex (∑ i, c • u i) (∑ j, c • u j) =
      ∑ i, ∑ j, (c * (starRingEnd Complex) c) • InnerProductSpace.rankOne Complex (u i) (u j) := by
  simp only [map_sum, ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul, map_smulₛₗ,
    ContinuousLinearMap.smul_apply]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem normalizedFullCodeProjector_toOperator
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedFullCodeProjector M parameter).toOperator =
      ((M.codeSpace.dimension : Real)⁻¹ : Complex) • M.fullCodeProjector := by
  have hdim : 0 < M.codeSpace.dimension := bptCodeDimension_pos M parameter
  change Semantics.partialTraceRightRaw _ _
    (InnerProductSpace.rankOne Complex (codeReferenceVector M.codeSpace)
      (codeReferenceVector M.codeSpace)).toLinearMap = _
  let b : OrthonormalBasis (Fin M.codeSpace.dimension) Complex M.codeSpace.carrier :=
    stdOrthonormalBasis Complex M.codeSpace.carrier
  let c : Complex := ((Real.sqrt ((M.codeSpace.dimension : Real)⁻¹) : Real) : Complex)
  have hv : codeReferenceVector M.codeSpace =
      ∑ i, c • ((b i : L.Register) ⊗ₜ[Complex] (b i : L.Register)) := rfl
  have hCLM := QBAux.rankOne_sum_sum (H := TensorProduct Complex L.Register L.Register) c
    (fun i => (b i : L.Register) ⊗ₜ[Complex] (b i : L.Register))
  rw [← hv] at hCLM
  have hexp : (InnerProductSpace.rankOne Complex (codeReferenceVector M.codeSpace)
      (codeReferenceVector M.codeSpace)).toLinearMap =
      ∑ i, ∑ j, (c * (starRingEnd Complex) c) •
        (InnerProductSpace.rankOne Complex ((b i : L.Register) ⊗ₜ[Complex] (b i : L.Register))
          ((b j : L.Register) ⊗ₜ[Complex] (b j : L.Register))).toLinearMap := by
    rw [hCLM]
    simp
  have hcc : c * (starRingEnd Complex) c = ((M.codeSpace.dimension : Real)⁻¹ : Complex) := by
    simp only [c, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    exact Complex.ofReal_inv _
  rw [hexp]
  simp only [map_sum, map_smul, QBAux.ptr_rankOne_tmul]
  have horth : ∀ x x' : Fin M.codeSpace.dimension,
      inner Complex (b x' : L.Register) (b x : L.Register) = if x' = x then (1 : Complex) else 0 := by
    intro x x'
    rw [← Submodule.coe_inner]
    exact b.inner_eq_ite x' x
  simp only [horth, ite_smul, one_smul, zero_smul, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hcc]
  rw [← Finset.smul_sum]
  congr 1
  have hproj := OrthonormalBasis.starProjection_eq_sum_rankOne b
  have hproj' := congrArg (fun T : L.Register →L[Complex] L.Register => (T : L.Register →ₗ[Complex] L.Register)) hproj
  simp only [ContinuousLinearMap.coe_sum] at hproj'
  exact hproj'.symm

theorem multiset_re_sum (s : Multiset Complex) : (s.map Complex.re).sum = s.sum.re := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

end QBAux

theorem solution
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy =
      Real.logb 2 (M.codeSpace.dimension : Real) := by
  have hT := QBAux.normalizedFullCodeProjector_toOperator M parameter
  have hdim : 0 < M.codeSpace.dimension := bptCodeDimension_pos M parameter
  have hdpos : (0 : Real) < (M.codeSpace.dimension : Real) := by exact_mod_cast hdim
  set rho := normalizedFullCodeProjector M parameter with hrho
  set d : Real := (M.codeSpace.dimension : Real) with hd
  have hP : M.fullCodeProjector * M.fullCodeProjector = M.fullCodeProjector := by
    have h := (Submodule.isIdempotentElem_starProjection M.codeSpace.carrier).eq
    have h' := congrArg
      (fun T : L.Register →L[Complex] L.Register => (T : L.Register →ₗ[Complex] L.Register)) h
    exact h'
  have hsq : rho.toOperator * rho.toOperator = ((d : Complex)⁻¹) • rho.toOperator := by
    rw [hT, smul_mul_assoc, mul_smul_comm, hP]
  have hroots : ∀ r ∈ rho.toOperator.charpoly.roots, r = 0 ∨ r = ((d : Complex)⁻¹) := by
    intro r hr
    have hrt : rho.toOperator.charpoly.IsRoot r :=
      (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hr
    have hev : Module.End.HasEigenvalue rho.toOperator r :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hrt
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 : rho.toOperator v = r • v := hv.apply_eq_smul
    have h2 := congrArg (fun A => A v) hsq
    simp only [Module.End.mul_apply, h1, map_smul, LinearMap.smul_apply] at h2
    have h3 : (r * r - ((d : Complex)⁻¹) * r) • v = 0 := by
      rw [sub_smul, mul_smul, mul_smul, h2]
      simp
    have h4 := (smul_eq_zero.mp h3).resolve_right hv.2
    have h5 : r * (r - ((d : Complex)⁻¹)) = 0 := by
      rw [mul_sub]; rw [mul_comm ((d : Complex)⁻¹) r] at h4; exact h4
    rcases mul_eq_zero.mp h5 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hsum : rho.toOperator.charpoly.roots.sum = 1 := by
    rw [← Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    exact rho.trace_one
  have key : ∀ r ∈ rho.toOperator.charpoly.roots,
      DensityOperator.entropyTerm r.re = r.re * Real.logb 2 d := by
    intro r hr
    rcases hroots r hr with h | h
    · rw [h]; simp
    · rw [h, ← Complex.ofReal_inv, Complex.ofReal_re]
      have hne : d⁻¹ ≠ 0 := inv_ne_zero hdpos.ne'
      rw [DensityOperator.entropyTerm, if_neg hne, Real.logb_inv]
      ring
  unfold DensityOperator.vonNeumannEntropy DensityOperator.finiteSpectrum
  have h6 : (rho.toOperator.charpoly.roots.map (DensityOperator.entropyTerm ∘ Complex.re)).sum =
      (rho.toOperator.charpoly.roots.map (fun r => r.re * Real.logb 2 d)).sum :=
    congrArg Multiset.sum (Multiset.map_congr rfl key)
  rw [Multiset.map_map, h6, Multiset.sum_map_mul_right, QBAux.multiset_re_sum, hsum]
  simp
