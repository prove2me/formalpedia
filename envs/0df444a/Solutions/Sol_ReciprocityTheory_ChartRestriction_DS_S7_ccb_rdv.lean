-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.ccb_rdv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:15.104737+00:00
-- url     : https://prove2.me/submissions/897b1120-c6a0-43f0-b77e-ab909d67374b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_exp_inUJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_inUJ_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_path_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ccb_path_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ g ∈ W, inUJ ε g → f g = F (g⁻¹ * m)) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X)))
      (-(fderiv ℂ F (g⁻¹ * m) (X * (g⁻¹ * m)))) 0 := by
  set y := g⁻¹ * m with hy
  have hyV : y ∈ V := (hWV g hg).2
  have hΦ : HasFDerivAt F (fderiv ℂ F y) y := (hF.differentiableAt (hV.mem_nhds hyV)).hasFDerivAt
  have h0 : y = NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)) * y := by simp
  have h1 : HasDerivAt (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • (-X)) * y))
      (fderiv ℂ F y (-X * y)) 0 :=
    (hΦ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (ccb_path_right (-X) y) h0
  have hcont : ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
    (ccb_path_left g X).continuousAt
  have hW0 : W ∈ nhds ((fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) := by
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact hW.mem_nhds hg
  have hev : ∀ᶠ t : ℝ in nhds 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ W :=
    hcont.preimage_mem_nhds hW0
  have hfin : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • (-X)) * y) := by
    filter_upwards [hev] with t ht
    rw [hf _ ht (ccb_inUJ_mul ε hgu (ccb_exp_inUJ ε hX t)), Matrix.mul_inv_rev, smul_neg,
      Matrix.exp_neg, Matrix.mul_assoc]
  have h2 := h1.congr_of_eventuallyEq hfin
  rwa [Matrix.neg_mul, map_neg] at h2
end ReciprocityTheory.ChartRestriction.DS.S7
