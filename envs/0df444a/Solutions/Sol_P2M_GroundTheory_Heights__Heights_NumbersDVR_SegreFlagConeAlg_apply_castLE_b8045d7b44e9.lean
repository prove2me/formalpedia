-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_apply_castLE_b8045d7b44e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:31:52.420702+00:00
-- url     : https://prove2.me/submissions/d5f9283c-9726-4207-a89f-856206060eb1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagConeAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_sum_castLE_755031291b04
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg
theorem _root_.solution {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N k : ℕ} (hkN : k ≤ N)
    (w : Module.Basis (Fin N) Ω E) (v : E) (hv : ∀ j : Fin N, k ≤ (j : ℕ) → w.repr v j = 0)
    (ψ : Module.Dual Ω E) :
    ψ v = ∑ j : Fin k, w.repr v (Fin.castLE hkN j) * ψ (w (Fin.castLE hkN j)) := by
  conv_lhs => rw [← w.sum_repr v]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact sum_castLE hkN _ fun j hj => by rw [hv j hj, zero_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg
