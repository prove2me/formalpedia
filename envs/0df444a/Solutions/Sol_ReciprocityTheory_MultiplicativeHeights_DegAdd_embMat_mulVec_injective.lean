-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.embMat_mulVec_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:45:12.544115+00:00
-- url     : https://prove2.me/submissions/14e7934e-7719-46a5-95d7-be1622634425

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_EmbMatMulVecInjective

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
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    {v : Fin k → Fin r → K} (hv : LinearIndependent K v) :
    Function.Injective (embMat σ v).mulVec := by
  set B : Matrix (Fin r) (Fin k) K := Matrix.of fun a j => v j a
  have hcol : B.col = v := by
    funext j a
    rfl
  have hB : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hv
  have hker : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact hB (by simpa [Matrix.toLin'_apply] using h)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) hker
  have hNB : LinearMap.toMatrix' g * B = 1 := by
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hE : embMat σ v = B.map σ := rfl
  have h1 : (LinearMap.toMatrix' g).map σ * embMat σ v = 1 := by
    rw [hE, ← Matrix.map_mul, hNB, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have h := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, h1] using h
end ReciprocityTheory.MultiplicativeHeights.DegAdd
