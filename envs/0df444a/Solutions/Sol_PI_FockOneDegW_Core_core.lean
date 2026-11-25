-- Prove2me | solution 1 for PI.FockOneDegW.Core.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:11.232358+00:00
-- url     : https://prove2.me/submissions/caf2a8fb-9267-4a01-909f-8714ebf0b0bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Core_side_lp
import Theorems.Thm_PI_FockOneDegW_Core_side_sb
import Theorems.Thm_PI_FockOneDegW_Core_sum_SS
import Theorems.Thm_PI_FockOneDegW_Core_SS_self_re
import Theorems.Thm_PI_FockOneDegW_Core_SS_nonneg
import Theorems.Thm_PI_FockOneDegW_Inner_eq_zero_of_fockInner_self_re
import Theorems.Thm_PI_FockOneDegW_Inner_fockInner_self_re_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Core
theorem _root_.solution (hK : OpsK) (hL : HarmIff) (μ : Ix p q → ℚ) (v : Pol p q r s)
    (hv : IsHW (fockAct1 p q r s) μ v) (hh : Harm2 v) (a : Ix p q) (c d : Ix r s)
    (hc : linePos ((a, c) : Ln p q r s) = false) (hd : linePos ((a, d) : Ln p q r s) = true) :
    pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) v) = 0 := by
  have hH := (hL p q r s v).1 hh
  have hsum := sum_SS v hH
  have hre : ∑ a : Ix p q, ∑ b : Ix p q, (SS v a b).re = 0 := by
    have := congrArg Complex.re hsum
    rw [Complex.re_sum] at this
    simpa [Complex.re_sum] using this
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    Finset.sum_nonneg fun b _ => SS_nonneg hK μ v hv a b)).1 hre a (Finset.mem_univ _)
  have haa := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => SS_nonneg hK μ v hv a b)).1 hrow a
    (Finset.mem_univ _)
  rw [SS_self_re] at haa
  have hc1 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => Finset.sum_nonneg fun d _ =>
    fockInner_self_re_nonneg (gg v a c d))).1 haa c (Finset.mem_univ _)
  have hcd := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ =>
    fockInner_self_re_nonneg (gg v a c d))).1 hc1 d (Finset.mem_univ _)
  have hg := eq_zero_of_fockInner_self_re _ hcd
  have hnsb : ¬ sameBlock c d := by
    intro h
    rw [side_sb] at h
    have h1 := (side_lp a d).1 hd
    have h2 : ¬ linePos ((a, c) : Ln p q r s) = true := by rw [hc]; simp
    exact h2 ((side_lp a c).2 (h1.trans h.symm))
  unfold gg at hg
  rwa [if_pos ⟨hnsb, hd⟩] at hg
end PI.FockOneDegW.Core
