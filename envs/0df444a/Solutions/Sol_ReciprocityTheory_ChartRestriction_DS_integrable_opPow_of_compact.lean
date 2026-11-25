-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.integrable_opPow_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:50.639883+00:00
-- url     : https://prove2.me/submissions/f8c5fd69-ce38-4404-bc5c-16f653d1e0b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrVGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefIntCpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefIntCpt_toE_continuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefIntCpt_hs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_continuous_toM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exists_signVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_integrable_of_decayVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefOp_le_sqrt_hs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hq : S7.q0 ε = 0) (Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hcont : ContinuousOn Ψ {g | inUJ ε g}) (hle : ∀ g, inUJ ε g → ‖Ψ g‖ ≤ 1)
    {N : ℝ} (hN : 0 ≤ N) (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] :
    Integrable (fun g : S7.UJ ε =>
      ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N) ν := by
  obtain ⟨s, hsc⟩ := S7.exists_signVG ε
  have hfc : Continuous (fun g : S7.UJ ε =>
      ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N) := by
    have h1 : Continuous fun g : S7.UJ ε => Ψ (S7.toM g) :=
      hcont.comp_continuous (S7.continuous_toM ε) (fun g => g.2)
    have h2 : Continuous fun g : S7.UJ ε => Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g) :=
      (coefIntCpt_toE_continuous n).comp (S7.continuous_toM ε)
    exact h1.norm.mul (h2.norm.rpow_const fun _ => Or.inr hN)
  refine S7.integrable_of_decayVG ε s ν _ hfc.aestronglyMeasurable (Real.sqrt n ^ N)
    (fun g _ => ?_) 1 ?_ (fun g hg => ?_)
  · have hop := coefOp_le_sqrt_hs (S7.toM g)
    rw [coefIntCpt_hs hq g] at hop
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc _ ≤ 1 * Real.sqrt n ^ N :=
          mul_le_mul (hle _ g.2) (Real.rpow_le_rpow (norm_nonneg _) hop hN) (by positivity) zero_le_one
      _ = _ := one_mul _
  · rw [hsc, hq]; norm_num
  · exfalso
    rw [coefIntCpt_hs hq g] at hg
    have e1 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    have e0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
end ReciprocityTheory.ChartRestriction.DS
