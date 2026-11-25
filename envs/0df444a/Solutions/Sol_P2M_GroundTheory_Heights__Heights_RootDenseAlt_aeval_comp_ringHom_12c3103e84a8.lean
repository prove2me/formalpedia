-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_comp_ringHom_12c3103e84a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:13:20.036322+00:00
-- url     : https://prove2.me/submissions/3713d8bf-5dc9-4645-b468-dd94ed907be7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDense

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootDenseAlt
namespace GroundTheory.Heights₂.Heights.RootDenseAlt
theorem _root_.solution {σ τ Ω : Type*} [Field Ω] (φ : MvPolynomial σ ℚ →+* Ω)
    (P : τ → MvPolynomial σ ℚ) (g : MvPolynomial τ ℤ) :
    aeval (fun i => φ (P i)) g = φ (aeval P g) := by
  have : (aeval (fun i => φ (P i)) : MvPolynomial τ ℤ →ₐ[ℤ] Ω).toRingHom =
      φ.comp (aeval P).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  exact congrArg (fun ψ : MvPolynomial τ ℤ →+* Ω => ψ g) this
end GroundTheory.Heights₂.Heights.RootDenseAlt
