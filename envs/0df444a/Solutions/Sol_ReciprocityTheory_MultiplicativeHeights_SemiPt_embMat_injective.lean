-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.embMat_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:55.143782+00:00
-- url     : https://prove2.me/submissions/40df99a1-6148-45ba-bb79-4c53b4d55da2

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (hli : LinearIndependent K b) :
    Function.Injective (embMat σ b).mulVec := by
  classical
  let A : Matrix (Fin r) (Fin k) K := Matrix.of fun a i => b i a
  have hA : Function.Injective (Matrix.toLin' A) := by
    intro x y hxy
    have hinj : Function.Injective A.mulVec := by
      rw [Matrix.mulVec_injective_iff]
      exact hli
    exact hinj (by simpa [Matrix.toLin'_apply] using hxy)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A)
    (LinearMap.ker_eq_bot.mpr hA)
  have hBA : LinearMap.toMatrix' g * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h
  have hE : embMat σ b = A.map σ := by
    ext a i
    rfl
  have hBA' : (LinearMap.toMatrix' g).map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one σ (map_zero σ) (map_one σ)]
  intro x y hxy
  rw [hE] at hxy
  have := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, hBA'] using this
end ReciprocityTheory.MultiplicativeHeights.SemiPt
