-- Prove2me | solution 1 for PI.AddIntG.Wk.thirdRoot_mem_coeffSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:41.652442+00:00
-- url     : https://prove2.me/submissions/93ad484c-9df6-4131-b385-ef47947a6337

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_Acf
import Theorems.Thm_PI_AddIntG_Wk_coeff_wSeriesVar_zero
import Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_lamA_wser_mem
import Theorems.Thm_PI_AddIntG_Wk_lam_mem
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_wq_mem


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
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    Z3 W wq ∈ SerS S (Fin 2) := by
  have hwq := wq_mem h1 h2 h3 h4 h6 h
  have hcc : ∀ a ∈ S, cc a ∈ SerS S (Fin 2) := fun a ha => (mem_SerS S _).2 fun e => by
    simp only [cc, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      MvPowerSeries.coeff_C]
    split_ifs
    · exact ha
    · exact S.zero_mem
  have hX : ∀ i, (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := fun i =>
    (mem_SerS S _).2 fun e => by
      rw [MvPowerSeries.coeff_X]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
  have hl : lam wq ∈ SerS S (Fin 2) := (mem_SerS S _).2 (lam_mem hwq)
  have hw0 : wv wq 0 ∈ SerS S (Fin 2) := (mem_SerS S _).2 fun e => by
    rw [coeff_wSeriesVar_zero]
    split_ifs
    · exact lamA_wser_mem hwq _
    · exact S.zero_mem
  have hn : nu wq ∈ SerS S (Fin 2) := sub_mem hw0 (mul_mem hl (hX 0))
  have h2' : (2 : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
    rw [show (2 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 + 1 from one_add_one_eq_two.symm]
    exact add_mem (SerS S (Fin 2)).one_mem (SerS S (Fin 2)).one_mem
  have h3' : (3 : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
    rw [show (3 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 + 1 + 1 by ring]
    exact add_mem (add_mem (SerS S (Fin 2)).one_mem (SerS S (Fin 2)).one_mem) (SerS S (Fin 2)).one_mem
  have hA : Acf W wq ∈ SerS S (Fin 2) := by
    unfold Acf
    exact add_mem (add_mem (add_mem (SerS S (Fin 2)).one_mem (mul_mem (hcc _ h2) hl)) (mul_mem (hcc _ h4) (pow_mem hl 2)))
      (mul_mem (hcc _ h6) (pow_mem hl 3))
  have hB : Bcf W wq ∈ SerS S (Fin 2) := by
    unfold Bcf
    exact add_mem (add_mem (add_mem (add_mem (mul_mem (hcc _ h1) hl) (mul_mem (hcc _ h2) hn))
      (mul_mem (hcc _ h3) (pow_mem hl 2))) (mul_mem (mul_mem (mul_mem h2' (hcc _ h4)) hl) hn))
      (mul_mem (mul_mem (mul_mem h3' (hcc _ h6)) (pow_mem hl 2)) hn)
  unfold Z3
  exact sub_mem (sub_mem (neg_mem (hX 0)) (hX 1)) (mul_mem hB (inv_mem_SerS S (constantCoeff_Acf W wq) hA))
end PI.AddIntG.Wk
