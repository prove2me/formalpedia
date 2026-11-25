-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_eqOn_of_exp_eq_35ecbbb8e43f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:53.557642+00:00
-- url     : https://prove2.me/submissions/8c94fa55-dca9-4fb8-ac92-915d40b740c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set E}
    (hW : IsOpen W) (hc : Convex ℝ W) {g₁ g₂ : E → ℂ} (h₁ : ContinuousOn g₁ W)
    (h₂ : ContinuousOn g₂ W) (he : ∀ w ∈ W, Complex.exp (g₁ w) = Complex.exp (g₂ w)) {w₀ : E}
    (hw₀ : w₀ ∈ W) (h₀ : g₁ w₀ = g₂ w₀) : ∀ w ∈ W, g₁ w = g₂ w := by
  have : ContractibleSpace W := hc.contractibleSpace ⟨w₀, hw₀⟩
  have : LocallyPathConnectedSpace W := hW.locallyPathConnectedSpace
  let f : C(W, ℂ) := ⟨fun x => Complex.exp (g₁ x), Complex.continuous_exp.comp h₁.domRestrict⟩
  obtain ⟨F, -, huniq⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (a₀ := ⟨w₀, hw₀⟩) (e₀ := g₁ w₀) rfl (fun x => Complex.exp_ne_zero _)
  have e₁ := huniq ⟨W.domRestrict g₁, h₁.domRestrict⟩ ⟨rfl, rfl⟩
  have e₂ := huniq ⟨W.domRestrict g₂, h₂.domRestrict⟩
    ⟨h₀.symm, funext fun x => (he x x.2).symm⟩
  intro w hw
  exact congrArg (fun F : C(W, ℂ) => F ⟨w, hw⟩) (e₁.trans e₂.symm)
end GroundTheory.Heights₂.Heights.Regular
