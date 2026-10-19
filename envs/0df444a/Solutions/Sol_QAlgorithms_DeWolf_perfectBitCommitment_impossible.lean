-- Prove2me | solution 1 for QAlgorithms.DeWolf.perfectBitCommitment_impossible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:59:27.750709+00:00
-- url     : https://prove2.me/submissions/c91c740d-b4f9-4408-96ce-0253b79b1ee7

import Definitions.Def_QAlgorithms_Defs_Information
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
open QAlgorithms
open scoped ComplexConjugate

private theorem gram_unitary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] (v w : ι → E)
    (h : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) :
    ∃ T : E ≃ₗᵢ[ℂ] E, ∀ i, T (v i) = w i := by
  classical
  let F := Fintype.linearCombination ℂ v
  let G := Fintype.linearCombination ℂ w
  have hinner (a b : ι → ℂ) : inner ℂ (F a) (F b) = inner ℂ (G a) (G b) := by
    simp only [F, G, Fintype.linearCombination_apply, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, h]
  have hnorm (a : ι → ℂ) : ‖G a‖ = ‖F a‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (G a), norm_eq_sqrt_re_inner (𝕜 := ℂ) (F a), hinner]
  have hker : LinearMap.ker F ≤ LinearMap.ker G := by
    intro a ha
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    rw [hnorm, LinearMap.mem_ker.mp ha, norm_zero]
  let H : LinearMap.range F →ₗ[ℂ] E :=
    ((LinearMap.ker F).liftQ G hker).comp F.quotKerEquivRange.symm.toLinearMap
  have hH (a : ι → ℂ) : H ⟨F a, LinearMap.mem_range_self F a⟩ = G a := by
    simp [H]
  have hHnorm (a : LinearMap.range F) : ‖H a‖ = ‖a‖ := by
    obtain ⟨b, hb⟩ := a.property
    have he : a = ⟨F b, LinearMap.mem_range_self F b⟩ := Subtype.ext hb.symm
    rw [he, hH]
    exact hnorm b
  let L : LinearMap.range F →ₗᵢ[ℂ] E := ⟨H, hHnorm⟩
  let T := L.extend
  have hT (a : ι → ℂ) : T (F a) = G a := by
    exact (L.extend_apply ⟨F a, LinearMap.mem_range_self F a⟩).trans (hH a)
  let U : E ≃ₗᵢ[ℂ] E := LinearIsometryEquiv.ofSurjective T
    (LinearMap.surjective_of_injective T.injective)
  refine ⟨U, fun i => ?_⟩
  have hh := hT (Pi.single i 1)
  simpa [U, F, G, Fintype.linearCombination_apply] using hh

theorem solution (dA dB : ℕ)
    (phi0 phi1 : EuclideanSpace ℂ (Fin dA × Fin dB)) (h0 : IsState phi0) (h1 : IsState phi1)
    (hconceal : traceLeft (pureDensity phi0) = traceLeft (pureDensity phi1)) :
    ∃ U ∈ Matrix.unitaryGroup (Fin dA) ℂ,
      act (Matrix.kronecker U (1 : Matrix (Fin dB) (Fin dB) ℂ)) phi0 = phi1 := by
  classical
  let v : Fin dB → EuclideanSpace ℂ (Fin dA) := fun b => WithLp.toLp 2 (fun a => phi0 (a,b))
  let w : Fin dB → EuclideanSpace ℂ (Fin dA) := fun b => WithLp.toLp 2 (fun a => phi1 (a,b))
  have hgram (b c : Fin dB) : inner ℂ (v b) (v c) = inner ℂ (w b) (w c) := by
    have hh := congrArg (fun M => M c b) hconceal
    simpa [v, w, PiLp.inner_apply, traceLeft, pureDensity, mul_comm] using hh
  obtain ⟨T, hT⟩ := gram_unitary v w hgram
  let B := EuclideanSpace.basisFun (Fin dA) ℂ
  let U := T.toMatrix B.toBasis B.toBasis
  refine ⟨U, T.toMatrix_mem_unitaryGroup B B, ?_⟩
  have hUv (b : Fin dB) : U.mulVec (fun a => phi0 (a,b)) = fun a => phi1 (a,b) := by
    have hh := T.toLinearEquiv.toLinearMap.toMatrix_mulVec_repr B.toBasis B.toBasis (v b)
    have hr (z : EuclideanSpace ℂ (Fin dA)) :
        (fun i => B.toBasis.repr z i) = (fun i => z i) := by
      funext i
      exact B.coe_toBasis_repr_apply z i
    change U.mulVec (fun i => B.toBasis.repr (v b) i) =
      (fun i => B.toBasis.repr (T (v b)) i) at hh
    rw [hr, hr, hT] at hh
    exact hh
  ext p
  rcases p with ⟨a,b⟩
  have hh := congrFun (hUv b) a
  simpa [act, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.one_apply,
    Fintype.sum_prod_type] using hh
