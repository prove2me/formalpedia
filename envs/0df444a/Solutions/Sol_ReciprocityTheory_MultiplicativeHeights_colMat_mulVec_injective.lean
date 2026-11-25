-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.colMat_mulVec_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:29.157474+00:00
-- url     : https://prove2.me/submissions/f9037b88-b586-41fe-a5b6-7879e9ca9d7d

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) :
    Function.Injective (colMat σ b).mulVec := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin r) (Fin k) K, B = Matrix.of fun a i => b i a := ⟨_, rfl⟩
  have hker : LinearMap.ker B.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∑ i, g i • b i = 0 := by
      funext a
      have h1 := congrFun hg a
      simp only [hB, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Pi.zero_apply] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    funext i
    exact Fintype.linearIndependent_iff.mp hb g h0 i
  obtain ⟨L, hL⟩ := B.mulVecLin.exists_leftInverse_of_injective hker
  have hLB : LinearMap.toMatrix' L * B = 1 := by
    have h2 := congrArg LinearMap.toMatrix' hL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h2
    have h4 : LinearMap.toMatrix' B.mulVecLin = B := LinearMap.toMatrix'_toLin' B
    rwa [h4] at h2
  have hc : colMat σ b = B.map σ := by
    ext a i
    rw [hB]
    rfl
  intro v w hvw
  have h3 : ((LinearMap.toMatrix' L).map σ * colMat σ b).mulVec v =
      ((LinearMap.toMatrix' L).map σ * colMat σ b).mulVec w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvw]
  rwa [hc, ← Matrix.map_mul, hLB, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.one_mulVec,
    Matrix.one_mulVec] at h3
end ReciprocityTheory.MultiplicativeHeights
