-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.ren_PhOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:28.104168+00:00
-- url     : https://prove2.me/submissions/13064c5f-ccb8-4f29-8e2e-c89d660570bd

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_psubst
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_cc_lin
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_lin
import Theorems.Thm_PI_FglPhSplit_Wk_cc_psubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
variable {σ τ : Type} [Finite σ] (r : σ → τ)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hl0 : PowerSeries.constantCoeff l = 0)
omit [Finite σ]
include hex0 hl0
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution {κ T : Type} [Fintype κ] [Fintype T] {n : ℕ} (E : T ≃ Fin n)
    (B : T → κ → ℂ_[p] × ℂ_[p]) :
    ren (p := p) E.symm (PhOn l ex ph (fun j => B (E.symm j))) = PhOn l ex ph B := by
  unfold PhOn phAt
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw : ∀ j : Fin n, constantCoeff (Xv j : MvPowerSeries (Fin n) ℂ_[p]) = 0 :=
    fun j => constantCoeff_X j
  have h0 : constantCoeff (lin l ex (fun j => (B (E.symm j) k).1)
      (fun j => (Xv j : MvPowerSeries (Fin n) ℂ_[p]))) = 0 := by
    unfold lin pt
    exact PI.FglPhSplit.Wk.cc_psubst _ hex0 (cc_lin hl0 _ _ hw)
  rw [ren_psubst _ _ h0, ren_lin _ hl0 _ _ hw]
  simp only [Xv, ren_X]
  congr 1
  unfold lin
  congr 1
  exact Equiv.sum_comp E.symm (fun e => C (B e k).1 * lg l (X e : MvPowerSeries T ℂ_[p]))
end PI.UnitaryGroupMassFormula.PhDualGram
