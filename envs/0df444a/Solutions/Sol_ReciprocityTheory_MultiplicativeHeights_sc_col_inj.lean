-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_col_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:50.112505+00:00
-- url     : https://prove2.me/submissions/4bf37f41-ab3e-49aa-996f-35c349fed41a

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
    [DecidableEq ι] (σ : K →+* ℂ) {v : ι → Fin r → K} (hv : LinearIndependent K v) :
    Function.Injective (embCols σ v).mulVec := by
  classical
  let V : Matrix (Fin r) ι K := Matrix.of fun a i => v i a
  have hinj : Function.Injective (Matrix.toLin' V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∑ i, x i • v i = 0 := by
      funext a
      have := congrFun hx a
      simpa [V, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm] using this
    funext i
    exact Fintype.linearIndependent_iff.mp hv x h0 i
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' V) (LinearMap.ker_eq_bot.mpr hinj)
  let W : Matrix ι (Fin r) K := LinearMap.toMatrix' h
  have hWV : W * V = 1 := by
    have := congrArg LinearMap.toMatrix' hh
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hV : embCols σ v = V.map σ := by ext a i; rfl
  have hWV' : W.map σ * V.map σ = 1 := by
    rw [← Matrix.map_mul, hWV, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro x y hxy
  have h2 := congrArg (fun z => (W.map σ) *ᵥ z) hxy
  simp only [hV, Matrix.mulVec_mulVec, hWV', Matrix.one_mulVec] at h2
  exact h2
end ReciprocityTheory.MultiplicativeHeights
