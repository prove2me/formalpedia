-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_hWord_phiP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:39.715498+00:00
-- url     : https://prove2.me/submissions/45ca1288-f17e-46c5-b405-2c14dc36a676

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_inv_hasFDerivAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_isUnit_of_omegaP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_contDiffOn_lWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_isOpen_omega


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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (μ : Fin n → ℤ) (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    ∀ x ∈ OmegaP n, hWord D (PhiP μ) x = lWord (D.map Neg.neg) (PhiM μ) x⁻¹ := by
  induction D with
  | nil => intro x _; rfl
  | cons Z D ih =>
    intro x hx
    have hxu := tb_isUnit_of_omegaP hx
    obtain ⟨L, hL, hLv⟩ := tb_inv_hasFDerivAt hxu
    have hnhds : OmegaP n ∈ nhds x :=
      hL.continuousAt.preimage_mem_nhds (isOpen_omega.mem_nhds (show x⁻¹ ∈ OmegaSet n from hx))
    have hev : hWord D (PhiP μ) =ᶠ[nhds x] fun z => lWord (D.map Neg.neg) (PhiM μ) z⁻¹ :=
      Filter.eventually_of_mem hnhds ih
    have hG : HasFDerivAt (lWord (D.map Neg.neg) (PhiM μ))
        (fderiv ℂ (lWord (D.map Neg.neg) (PhiM μ)) x⁻¹) x⁻¹ :=
      (((tb_contDiffOn_lWord μ _).differentiableOn (by simp)).differentiableAt
        (isOpen_omega.mem_nhds hx)).hasFDerivAt
    have hcomp : HasFDerivAt (fun z => lWord (D.map Neg.neg) (PhiM μ) z⁻¹)
        ((fderiv ℂ (lWord (D.map Neg.neg) (PhiM μ)) x⁻¹).comp L) x := hG.comp x hL
    show fderiv ℂ (hWord D (PhiP μ)) x (x * Z) = fderiv ℂ (lWord (D.map Neg.neg) (PhiM μ)) x⁻¹ (-Z * x⁻¹)
    rw [hev.fderiv_eq, hcomp.fderiv, ContinuousLinearMap.comp_apply, hLv]
    congr 1
    have hxd : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).mp hxu
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul x hxd, Matrix.one_mul, Matrix.neg_mul]
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
