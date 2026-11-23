-- Prove2me | solution 1 for PI.CntNotIntW.div_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:58.866312+00:00
-- url     : https://prove2.me/submissions/e1426d3a-e3b3-4300-92a5-2bab1c9e4644

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_ValOneOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open NumberField IsDedekindDomain ValuativeRel
variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [ValuativeRel K]
namespace PI.CntNotIntW
theorem _root_.solution (σ : E →+* K) (q m : 𝒪[K]) (j n : ℕ) (c x : E) (o : 𝓞 E)
    (hc : valuation K (σ c) = 1) (hn : (n : K) = (q : K) ^ j * m) (h : c * x = (n : E) * o) :
    ∃ t : 𝒪[K], σ x = (q : K) ^ j * t := by
  have hc0 : σ c ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hc
    exact zero_ne_one hc
  have hσ : σ c * σ x = (n : K) * σ (o : E) := by
    have := congrArg σ h
    simpa [map_mul, map_natCast] using this
  have hm : valuation K (m : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 m.2
  have ho : valuation K (σ (o : E)) ≤ 1 := sig_le_one σ o
  refine ⟨⟨(m : K) * σ (o : E) * (σ c)⁻¹, ?_⟩, ?_⟩
  · rw [Valuation.mem_integer_iff, Valuation.map_mul, Valuation.map_mul, Valuation.map_inv, hc, inv_one, mul_one]
    exact mul_le_one' hm ho
  · simp only
    rw [hn] at hσ
    field_simp
    linear_combination hσ
end PI.CntNotIntW
