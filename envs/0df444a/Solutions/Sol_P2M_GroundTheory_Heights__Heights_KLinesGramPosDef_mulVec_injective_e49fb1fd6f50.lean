-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_mulVec_injective_e49fb1fd6f50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:50.218429+00:00
-- url     : https://prove2.me/submissions/25f087f7-821b-42f5-be9b-1b0861632207

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KLinesGramPosDef
open Matrix
variable {K : Type*} [Field K] {n : ℕ} {ι : Type*}
namespace GroundTheory.Heights₂.Heights.KLinesGramPosDef
theorem _root_.solution [Fintype ι] (σ : K →+* ℂ) (u : ι → Fin n → K) (hu : LinearIndependent K u) :
    Function.Injective ((Matrix.of fun j a => u a j).map σ).mulVec := by
  classical
  set Uk : Matrix (Fin n) ι K := Matrix.of fun j a => u a j with hUk
  have hinj : LinearMap.ker Uk.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Fintype.linearIndependent_iff] at hu
    funext a
    refine hu c ?_ a
    funext j
    have := congrFun hc j
    simpa [Uk, Matrix.mulVec, dotProduct, mul_comm] using this
  obtain ⟨g, hg⟩ := Uk.mulVecLin.exists_leftInverse_of_injective hinj
  set Lk : Matrix ι (Fin n) K := LinearMap.toMatrix' g
  have hL : Lk * Uk = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin'] at this
  have hLσ : Lk.map σ * Uk.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have := congrArg (fun v => (Lk.map σ) *ᵥ v) hxy
  simpa [Matrix.mulVec_mulVec, hLσ] using this
end GroundTheory.Heights₂.Heights.KLinesGramPosDef
