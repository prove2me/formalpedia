-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.zetaUnr_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:45.05386+00:00
-- url     : https://prove2.me/submissions/5dd7cb70-a67f-4f16-b493-7461bae078bf

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_hasSum_conv
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_measurableSet_dShell
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_wt_of_mem
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_integrableOn_dShell
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zCoeff_eq
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_natDegree_invL_le
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_finite
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_eq_conv
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_summable_Jm
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
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
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (hu : ‖(ν ϖ : ℂ)‖ = 1)
    {n d : ℕ} (hn : 2 * n < d + 2) {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) :
    Integrable (fun g : GL (Fin n) k => φ g.val * wt d ν g) (haarVol (KO k (Fin n))) ∧
      (invL n d ϖ ν).eval 1 * ∫ g, φ g.val * wt d ν g ∂haarVol (KO k (Fin n)) = zetaUnr n d ϖ ν φ := by
  set μ : Measure (GL (Fin n) k) := haarVol (KO k (Fin n)) with hμ
  set c := cst d ϖ ν with hc
  have hq : (1 : ℝ) < resCard k := by
    have : 1 < resCard k := Finite.one_lt_card
    exact_mod_cast this
  have hq0 : (0 : ℝ) < resCard k := zero_lt_one.trans hq
  have hcn : ‖c‖ = (resCard k : ℝ) ^ (-(d : ℝ) / 2) := by
    have h : (resCard k : ℂ) ^ (-(d : ℂ) / 2) = (((resCard k : ℝ) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hq0.le]; push_cast; rfl
    rw [hc, cst, norm_mul, hu, one_mul, h, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq0.le _)]
  have hc0 : 0 < ‖c‖ := hcn ▸ Real.rpow_pos_of_pos hq0 _
  have hrq : ∀ i : Fin n, ‖c‖ * (resCard k : ℝ) ^ (n - 1 - (i : ℕ)) < 1 := fun i => by
    rw [hcn, ← Real.rpow_natCast, ← Real.rpow_add hq0]
    refine Real.rpow_lt_one_of_one_lt_of_neg hq ?_
    have hi := i.2
    have : 2 * (n - 1 - (i : ℕ)) < d := by omega
    have : (2 : ℝ) * ((n - 1 - (i : ℕ) : ℕ) : ℝ) < d := by exact_mod_cast this
    linarith
  have hψ : (fun x => ((‖φ x‖ : ℝ) : ℂ)) ∈ SB _ :=
    ⟨hφ.1.comp (fun z : ℂ => ((‖z‖ : ℝ) : ℂ)), hφ.2.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp)⟩
  have hsum := summable_Jm hϖ hψ hc0 hrq
  have hmeas := measurableSet_dShell (k := k) n
  have heq : ∀ m : ℤ, Set.EqOn (fun g : GL (Fin n) k => φ g.val * wt d ν g) (fun g => c ^ m * φ g.val) (dShell n m) :=
    fun m g hg => by
      simp only [wt_of_mem hϖ hν d hg, hc, mul_comm]
  have hint : ∀ m : ℤ, IntegrableOn (fun g : GL (Fin n) k => φ g.val * wt d ν g) (dShell n m) μ := fun m =>
    IntegrableOn.congr_fun ((integrableOn_dShell hφ m).const_mul (c ^ m)) (heq m).symm (hmeas m)
  have hnorm : ∀ m : ℤ, ∫ g in dShell n m, ‖φ g.val * wt d ν g‖ ∂μ =
      ‖c‖ ^ m * ‖Jm n (fun x => ((‖φ x‖ : ℝ) : ℂ)) m‖ := fun m => by
    rw [setIntegral_congr_fun (g := fun g : GL (Fin n) k => ‖c‖ ^ m * ‖φ g.val‖) (hmeas m) (fun g hg => by
      have := heq m hg
      simp only at this ⊢
      rw [this, norm_mul, norm_zpow]), integral_const_mul, Jm, integral_complex_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hU : (⋃ m : ℤ, dShell (k := k) n m) = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨ord k (gdet g), rfl⟩
  have hI : IntegrableOn (fun g : GL (Fin n) k => φ g.val * wt d ν g) (⋃ m : ℤ, dShell n m) μ :=
    integrableOn_iUnion_of_summable_integral_norm hint (hsum.congr fun m => (hnorm m).symm)
  have hdisj : Pairwise (Function.onFun Disjoint (dShell (k := k) n)) := fun a b hab =>
    Set.disjoint_left.2 fun g ha hb => hab (Eq.trans (Eq.symm ha) hb)
  have hS := hasSum_integral_iUnion hmeas hdisj hI
  rw [hU] at hI hS
  rw [Measure.restrict_univ] at hS
  refine ⟨integrableOn_univ.1 hI, ?_⟩
  have hz : (fun m : ℤ => ∫ g in dShell n m, φ g.val * wt d ν g ∂μ) = zCoeff n d ϖ ν φ := by
    funext m
    rw [zCoeff_eq hϖ hν d hφ, setIntegral_congr_fun (hmeas m) (heq m), integral_const_mul, Jm]
  rw [hz] at hS
  rw [zetaUnr_eq_conv]
  exact (hasSum_conv (natDegree_invL_le n d ϖ ν) hS).tsum_eq.symm.trans (tsum_eq_finsum (conv_finite hϖ hν n d hφ))
end PositivityTheory.ThK.SplitLoc.Unr
