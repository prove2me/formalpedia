-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.ta_rdV_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:43.973611+00:00
-- url     : https://prove2.me/submissions/ea15af92-3b49-4023-9600-3e4775503c29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_curve_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_inUJ_mul_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {W : Set (Matrix (Fin n) (Fin n) ℂ)} {m g X : Matrix (Fin n) (Fin n) ℂ}
    (hW : IsOpen W) (hg : g ∈ W) (hgu : inUJ ε g) (hX : inG ε X)
    (hF : DifferentiableAt ℂ F (g⁻¹ * m)) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ h ∈ W, inUJ ε h → f h = F (h⁻¹ * m)) :
    RdV X f g = fderiv ℂ F (g⁻¹ * m) (-X * (g⁻¹ * m)) := by
  have hc := ta_curve g X
  have hnear : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ W := by
    apply hc.continuousAt.preimage_mem_nhds
    have h0 : g * NormedSpace.exp ((((0 : ℝ) : ℂ)) • X) = g := by
      simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]
    rw [h0]
    exact hW.mem_nhds hg
  have hcn := ta_curve_neg X (g⁻¹ * m)
  have hcomp : HasDerivAt (fun t : ℝ => F (NormedSpace.exp (-((t : ℂ) • X)) * (g⁻¹ * m)))
      (fderiv ℂ F (g⁻¹ * m) (-X * (g⁻¹ * m))) 0 := by
    have := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hcn
      (by simp only [Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul])
    exact this
  have heq : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      (fun t : ℝ => F (NormedSpace.exp (-((t : ℂ) • X)) * (g⁻¹ * m))) := by
    filter_upwards [hnear] with t ht
    rw [hf _ ht (ta_inUJ_mul_exp ε hgu hX t), Matrix.mul_inv_rev, ← Matrix.exp_neg, mul_assoc]
  exact (hcomp.congr_of_eventuallyEq heq).deriv
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
