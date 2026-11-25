-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.wd_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:34.673323+00:00
-- url     : https://prove2.me/submissions/fd7ac339-0ed7-4e06-8746-539aaaf048d0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_wd_smooth
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_diffAt
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_dd_congr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_dd_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_dd_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv
namespace PositivityTheory.Rg.Sw.WR.K.GB.Inv
theorem _root_.solution {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ∀ (m : ℕ) (v : Fin m → Mc n), ∀ x ∈ U, wd (List.ofFn v) F x =
      ∑ r : Fin m → Fin n × Fin n, (∏ t, v t (r t).1 (r t).2) * wd (List.ofFn fun t => E (r t)) F x := by
  intro m
  induction m with
  | zero => intro v x _; simp [wd]
  | succ m ih =>
    intro v x hx
    rw [List.ofFn_succ]
    show dd (v 0) (wd (List.ofFn fun i => v i.succ) F) x = _
    rw [dd_congr hU (fun y hy => ih (fun i => v i.succ) y hy) (v 0) hx]
    rw [dd_sum _ _ _ _ (fun r _ => diffAt hU (wd_smooth hU hF _) hx)]
    simp_rw [dd_expand (v 0), Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n × Fin n).sum_comp
      (fun r : Fin (m + 1) → Fin n × Fin n => (∏ t, v t (r t).1 (r t).2) * wd (List.ofFn fun t => E (r t)) F x),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r' _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ]
    show _ = _ * dd (E p) (wd (List.ofFn fun t => E (r' t)) F) x
    ring
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
