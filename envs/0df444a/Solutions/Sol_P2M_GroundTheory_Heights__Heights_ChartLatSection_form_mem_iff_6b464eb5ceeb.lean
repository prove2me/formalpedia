-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatSection_form_mem_iff_6b464eb5ceeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:13.62095+00:00
-- url     : https://prove2.me/submissions/676814ef-a974-47a2-8ecb-fe3dd4ec62ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_mConeMap_form_f169be4db4e3

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.ChartLatSection
theorem _root_.solution (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y f = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_form y hf]
  constructor
  · intro h
    have hM : (∏ k, (X k : MvPolynomial ι Ω) ^ δ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)
  · intro h
    rw [h, C_0, zero_mul]
end GroundTheory.Heights₂.Heights.ChartLatSection
