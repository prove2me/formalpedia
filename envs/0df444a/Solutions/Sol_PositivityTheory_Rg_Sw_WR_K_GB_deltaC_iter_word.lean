-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.deltaC_iter_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:22.155983+00:00
-- url     : https://prove2.me/submissions/86140baa-b23e-4ee0-8377-785aa3d8a60d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_eqOn_word
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_word_contDiffOn
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_word_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_word_append
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_deltaC_eq_word
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_flat_succ

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (N : ℕ) :
    Set.EqOn (DeltaC^[N] F) (fun b => ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => blk (τ j)) F b) U := by
  induction N with
  | zero => intro b _; simp [word]
  | succ N ih =>
    intro b hb
    rw [Function.iterate_succ_apply', deltaC_eq_word]
    dsimp only
    have step : ∀ σ : Equiv.Perm (Fin n), word (blk σ) (DeltaC^[N] F) b =
        ∑ τ : Fin N → Equiv.Perm (Fin n), ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
          word (blk σ ++ (List.finRange N).flatMap fun j => blk (τ j)) F b := by
      intro σ
      rw [eqOn_word (blk σ) hU ih hb]
      have hw := word_sum (Finset.univ : Finset (Fin N → Equiv.Perm (Fin n)))
        (fun τ => ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))
        (fun τ => word ((List.finRange N).flatMap fun j => blk (τ j)) F) (blk σ) hU
        (fun τ => word_contDiffOn _ hU hF) hb
      rw [hw]
      simp only [word_append]
    simp only [step, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ => Equiv.Perm (Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.consEquiv_apply, flat_succ, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
    push_cast
    ring
end PositivityTheory.Rg.Sw.WR.K.GB
