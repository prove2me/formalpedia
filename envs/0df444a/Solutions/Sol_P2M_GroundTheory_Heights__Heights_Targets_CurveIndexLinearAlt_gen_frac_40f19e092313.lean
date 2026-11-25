-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_frac_40f19e092313
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:35.366893+00:00
-- url     : https://prove2.me/submissions/bd8c8fa6-0b82-4d4e-b22c-b9a66f777fd4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_div_e53e99228c31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_gen_ne_zero_4ffc22541bb7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
theorem _root_.solution {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {m : Ideal (curveRing y)}
    {c0 : ∀ k, ι k} (hc0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0)
    (hr : ∀ p : Σ k, ι k, ∃ α β : curveRing y, β ∉ m ∧ (β : Ω) * (y p / y ⟨p.1, c0 p.1⟩) = α)
    (c' : ∀ k, ι k) (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a : K → ℤ) :
    ∃ d ∈ curveRing y, d ≠ 0 ∧ d * gen y c a c' ∈ curveRing y := by
  set S := Subfield.closure (curveRing y : Set Ω) with hSdef
  have hB : ∀ b ∈ curveRing y, b ∈ S := fun b hb => Subfield.subset_closure hb
  have hrat : ∀ p : Σ k, ι k, y p / y ⟨p.1, c0 p.1⟩ ∈ S := by
    intro p
    obtain ⟨α, β, hβ, e⟩ := hr p
    have hβ0 : (β : Ω) ≠ 0 := fun h0 => hβ (by
      have : β = 0 := Subtype.ext h0
      rw [this]; exact m.zero_mem)
    have : y p / y ⟨p.1, c0 p.1⟩ = α / β := by rw [← e]; field_simp
    rw [this]
    exact S.div_mem (hB _ α.2) (hB _ β.2)
  have hx : gen y c a c' ∈ S := by
    rw [gen, cu_div]
    refine prod_mem fun k _ => S.zpow_mem ?_ _
    have e : y ⟨k, c' k⟩ / y ⟨k, c k⟩ =
        (y ⟨k, c' k⟩ / y ⟨k, c0 k⟩) / (y ⟨k, c k⟩ / y ⟨k, c0 k⟩) :=
      (div_div_div_cancel_right₀ (hc0 k) _ _).symm
    rw [e]
    exact S.div_mem (hrat ⟨k, c' k⟩) (hrat ⟨k, c k⟩)
  obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.mp hx
  rw [Subring.closure_eq] at hu hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [div_zero] at huv
    exact gen_ne_zero hc hc' a huv.symm
  refine ⟨v, hv, hv0, ?_⟩
  rw [← huv, mul_div_cancel₀ _ hv0]
  exact hu
end GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
