-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.wt_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:17.160713+00:00
-- url     : https://prove2.me/submissions/133860c7-2bd4-4953-a56e-bfc39dd8f10f

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_ord_zpow_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_GLDoubling_nabs_unif
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_one
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_zero_iff
import Theorems.Thm_GlobalTheory_SplitFlip_apow_of_valuation_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (d : ℕ) {n : ℕ} {m : ℤ} {g : GL (Fin n) k}
    (hg : g ∈ dShell n m) : wt d ν g = cst d ϖ ν ^ m := by
  have hm : ord k (gdet g) = m := hg
  have hu : valuation k ((gdet g / ϖ ^ m : kˣ) : k) = 1 := by
    refine ord_eq_zero_iff.1 ?_
    have h := ord_mul k (gdet g / ϖ ^ m) (ϖ ^ m)
    rw [div_mul_cancel, ord_zpow_eq, ord_eq_one hϖ, hm] at h
    omega
  have hϖd : apow ϖ ((d : ℂ) / 2) = (resCard k : ℂ) ^ (-(d : ℂ) / 2) := by
    rw [apow, GlobalTheory.GLDoubling.nabs_unif hϖ, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg, neg_div]
  let w : kˣ →* ℂ :=
    { toFun := fun x => (ν x : ℂ) * apow x ((d : ℂ) / 2)
      map_one' := by simp
      map_mul' := fun x y => by rw [map_mul, apow_mul, Units.val_mul]; ring }
  have h1 : w (gdet g / ϖ ^ m) = 1 := by
    show (ν _ : ℂ) * apow _ _ = 1
    rw [hν _ hu, apow_of_valuation_eq_one hu]; simp
  have h2 : w ϖ = cst d ϖ ν := by
    show (ν _ : ℂ) * apow _ _ = _
    rw [hϖd, cst]
  show w (gdet g) = _
  rw [← div_mul_cancel (gdet g) (ϖ ^ m), map_mul, h1, one_mul, map_zpow, h2]
end PositivityTheory.ThK.SplitLoc.Unr
