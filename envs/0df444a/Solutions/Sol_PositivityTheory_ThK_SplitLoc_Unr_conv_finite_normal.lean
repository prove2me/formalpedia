-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.conv_finite_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:15:26.839063+00:00
-- url     : https://prove2.me/submissions/144e1707-f0d4-43e2-a041-ecd41ce0f770

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_gen_mem_polys
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zCoeff_eq
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_hnf
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_finite_of_polys
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_natDegree_invL_le
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_coe_invL
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
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
  [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (n d : ℕ)
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) (M : ℕ)
    (hp : ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) → φ (x + y) = φ x) :
    (Function.support (conv (invL n d ϖ ν) n (zCoeff n d ϖ ν φ))).Finite := by
  obtain ⟨T, hT, h0, hJ⟩ := Jm_hnf hϖ hφ hs M hp
  refine conv_finite_of_polys (natDegree_invL_le n d ϖ ν)
    (fun m hm => by rw [zCoeff_eq hϖ hν d hφ, h0 m hm, mul_zero]) ?_
  have key := gen_mem_polys (fun i : Fin n => cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - (i : ℕ))) M
    (fun a => cst d ϖ ν ^ (∑ i, a i) * T a) (fun a => by
      have e : ∑ i, a i = ∑ i, (a i - M) + ∑ i, min (a i) M := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by omega
      rw [hT a, e, pow_add]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring)
  rw [coe_invL]
  convert key using 3
  funext t
  rw [zCoeff_eq hϖ hν d hφ, hJ, zpow_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_piAntidiag.1 ha).1]
end PositivityTheory.ThK.SplitLoc.Unr
