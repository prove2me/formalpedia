-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P35.gaussianPreservation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:20:29.616397+00:00
-- url     : https://prove2.me/submissions/3a8571a3-9d36-4774-84cc-13854d627ba6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

namespace X7D15GP

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33

lemma memℓp_comp {α β : Type} (e : α ≃ β) (u : Hilbert β) :
    Memℓp (fun p => u (e p)) 2 := by
  have hu := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp u)
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  exact e.summable_iff.mpr hu

def tr {α β : Type} (e : α ≃ β) (u : Hilbert β) : Hilbert α := ⟨fun p => u (e p), memℓp_comp e u⟩

lemma tr_apply {α β : Type} (e : α ≃ β) (u : Hilbert β) (p : α) : tr e u p = u (e p) := rfl

lemma tr_norm {α β : Type} (e : α ≃ β) (u : Hilbert β) : ‖tr e u‖ = ‖u‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact e.tsum_eq (fun i => ‖u i‖ ^ (2 : ℝ≥0∞).toReal)

lemma dens_transport {α β : Type} (e : α ≃ β) (X : Matrix β β ℂ) (h : IsDensity X) :
    IsDensity (fun p q => X (e p) (e q)) := by
  obtain ⟨⟨E⟩, hq, hs, hsum⟩ := h
  refine ⟨⟨{ left := fun n => tr e (E.left n)
             right := fun n => tr e (E.right n)
             summable := by simpa [tr_norm] using E.summable
             coefficients := fun i j => E.coefficients (e i) (e j) }⟩, ?_, ?_, ?_⟩
  · intro s z
    have := hq (s.map e.toEmbedding) (fun i => z (e.symm i))
    simp only [Finset.sum_map, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] at this
    exact this
  · exact e.summable_iff.mpr hs
  · rw [← hsum]; exact e.tsum_eq (fun i => (X i i).re)

end X7D15GP

end

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open X7D15GP in
theorem solution {I J : Type} [Nonempty I] [Nonempty J]
    {s t : ℕ} {hbar : ℝ} (W : ScaledWeylRepresentation I s hbar) (Wout : ScaledWeylRepresentation J t hbar)
    (T : Operation I J) (hT : IsTraceClassChannel T)
    (K : Matrix (Fin t × Fin 2) (Fin s × Fin 2) ℝ)
    (d : InterleavedPhase t) (B : Matrix (Fin t × Fin 2) (Fin t × Fin 2) ℝ)
    (hB : B.transpose = B) (hlaw : LinearBosonic W Wout T K (gaussianFunction d B))
    (rho : State I) (m : InterleavedPhase s)
    (alpha : Matrix (Fin s × Fin 2) (Fin s × Fin 2) ℝ)
    (halpha : alpha.transpose = alpha)
    (hrho : ∀ z, weylTraceCharacteristic W rho.coefficients z = gaussianFunction m alpha z) :
    MultimodeGaussianDensity Wout (T rho.coefficients) ∧
    ∀ z, weylTraceCharacteristic Wout (T rho.coefficients) z =
      gaussianFunction (K.mulVec m + d) (K * alpha * K.transpose + B) z := by
  have hchar : ∀ z, weylTraceCharacteristic Wout (T rho.coefficients) z =
      gaussianFunction (K.mulVec m + d) (K * alpha * K.transpose + B) z := by
    intro z
    rw [hlaw rho.coefficients rho.density.1 z, hrho]
    unfold gaussianFunction
    rw [← Complex.exp_add]
    congr 1
    have h1 : dotProduct m (K.transpose.mulVec z) = dotProduct (K.mulVec m) z := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
    have h2 : dotProduct (K.transpose.mulVec z) (alpha.mulVec (K.transpose.mulVec z)) =
        dotProduct z ((K * alpha * K.transpose).mulVec z) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z K,
        Matrix.mulVec_transpose]
    rw [Matrix.add_mulVec, dotProduct_add, add_dotProduct, h1, h2]
    push_cast
    ring
  refine ⟨⟨?_, K.mulVec m + d, K * alpha * K.transpose + B, ?_, hchar⟩, hchar⟩
  · let e : J × Fin 1 ≃ J := Equiv.prodUnique J (Fin 1)
    let e' : I × Fin 1 ≃ I := Equiv.prodUnique I (Fin 1)
    let X : State (I × Fin 1) := ⟨_, dens_transport e' _ rho.density⟩
    have hY := hT.2.2.2 1 X
    have := dens_transport e.symm _ hY
    exact this
  · rw [Matrix.transpose_add, hB, Matrix.transpose_mul, Matrix.transpose_mul, halpha,
      Matrix.transpose_transpose, Matrix.mul_assoc]
