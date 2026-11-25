-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_formMatrix_isUnit_7170a1850900
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:35.022426+00:00
-- url     : https://prove2.me/submissions/013805ed-4d04-4f99-a562-1efabfe39eed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeLinesIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeLinesIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace PairConeLinesIndep
theorem _root_.solution {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {N : ℕ}
    (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E) (hψ : LinearIndependent Ω ψ) :
    IsUnit (Matrix.of fun i j => ψ i (e j)) := by
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  have h := hψ.map' e.dualBasis.equivFun.toLinearMap e.dualBasis.equivFun.ker
  have hrows : (Matrix.of fun i j => ψ i (e j)).row = ⇑e.dualBasis.equivFun ∘ ψ := by
    funext i
    funext j
    simp [Matrix.row, Module.Basis.equivFun_apply]
  rw [hrows]
  exact h
end PairConeLinesIndep
end GroundTheory.Heights₂.Heights.NumbersDVR
