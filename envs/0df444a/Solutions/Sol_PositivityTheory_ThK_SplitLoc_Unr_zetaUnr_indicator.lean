-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.zetaUnr_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:58.544518+00:00
-- url     : https://prove2.me/submissions/7512db06-22b2-4928-94fe-22ae59b9c5eb

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_gen_geom
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_natCast
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_neg
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zCoeff_eq
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_hnf
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_indicator
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_natDegree_invL_le
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_coe_invL
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sb_indicator_sq
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_eq_conv
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
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (n d : ℕ) :
    zetaUnr n d ϖ ν (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1) = 1 := by
  have hφ := sb_indicator_sq (k := k) n
  obtain ⟨_, -, h0, -⟩ := Jm_hnf hϖ hφ (fun x hx => by
      by_contra hc
      exact hx (Set.indicator_of_notMem (s := {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]}) hc _)) 0
    (fun x y hy => by
      have hy' : ∀ i j, y i j ∈ 𝒪[k] := fun i j => by simpa [Valuation.mem_integer_iff] using hy i j
      by_cases hx : x ∈ {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]}
      · have hxy : x + y ∈ {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} :=
          fun i j => add_mem (hx i j) (hy' i j)
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxy]
        rfl
      · have hxy : x + y ∉ {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} := fun h =>
          hx fun i j => by simpa using sub_mem (h i j) (hy' i j)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxy])
  have hf : ∀ m < 0, zCoeff n d ϖ ν (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1) m = 0 :=
    fun m hm => by rw [zCoeff_eq hϖ hν d hφ, h0 m hm, mul_zero]
  have key : (invL n d ϖ ν : PowerSeries ℂ) * PowerSeries.mk (fun s : ℕ =>
      zCoeff n d ϖ ν (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1) s) = 1 := by
    rw [coe_invL]
    convert gen_geom (fun i : Fin n => cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - (i : ℕ))) using 3
    funext t
    rw [zCoeff_eq hϖ hν d hφ, Jm_indicator, zpow_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [(Finset.mem_piAntidiag.1 ha).1]
  rw [zetaUnr_eq_conv, finsum_eq_single _ ((0 : ℕ) : ℤ), conv_natCast (natDegree_invL_le n d ϖ ν) hf, key]
  · simp
  · intro m hm
    rcases lt_or_ge m 0 with h | h
    · exact conv_neg hf h
    · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le h
      rw [conv_natCast (natDegree_invL_le n d ϖ ν) hf, key, PowerSeries.coeff_one, if_neg]
      exact fun ht => hm (by rw [ht])
end PositivityTheory.ThK.SplitLoc.Unr
