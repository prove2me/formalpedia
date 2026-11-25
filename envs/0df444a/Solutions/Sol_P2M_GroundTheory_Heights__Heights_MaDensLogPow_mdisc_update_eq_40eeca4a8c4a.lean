-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_update_eq_40eeca4a8c4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:40.287424+00:00
-- url     : https://prove2.me/submissions/e2d05f7a-92c9-4b41-a062-e13a45daf366

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_const_apply_5310b6bbe09d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_cons_const_apply_6e8bc6b37f22
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_comp_perm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLogPow
theorem _root_.solution {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (i : Fin (n + 1 + 1))
    (hi : i ≠ 0) :
    mdisc (Function.update (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) i G) =
      mdisc (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) := by
  rw [← mdisc_comp_perm (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _)
    ((Equiv.swap 1 i).trans (Equiv.swap 0 1))]
  congr 1
  funext k
  simp only [Function.comp_apply, cons_cons_const_apply, Function.update_apply, cons_const_apply,
    Equiv.trans_apply, Equiv.swap_apply_def]
  have h01 : (0 : Fin (n + 1 + 1)) ≠ 1 := by
    rw [← Fin.succ_zero_eq_one]; exact (Fin.succ_ne_zero 0).symm
  by_cases hki : k = i
  · subst hki
    by_cases hk1 : k = 1
    · subst hk1; simp [Ne.symm h01]
    · simp [hk1]
  · by_cases hk0 : k = 0
    · subst hk0; simp [Ne.symm hi, h01]
    · by_cases hk1 : k = 1
      · subst hk1; simp [hki, Ne.symm hki, hi, Ne.symm h01]
      · simp [hki, hk0, hk1]
end GroundTheory.Heights₂.Heights.MaDensLogPow
