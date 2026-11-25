-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sg_raise_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:20.142927+00:00
-- url     : https://prove2.me/submissions/415f5054-6108-492d-994d-7a9bdc0d293c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isCAR_fock
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sgE_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) {a b : Fin n} (hab : a ≠ b) (hε : ε a = ε b) {ν : Fin n → ℝ}
    {f : Fock n} (hf : ∀ c, sgE ε cpFock cmFock c c f = ((ν c : ℝ) : ℂ) • f) (c : Fin n) :
    sgE ε cpFock cmFock c c (sgE ε cpFock cmFock a b f) =
      (((ν + root a b) c : ℝ) : ℂ) • sgE ε cpFock cmFock a b f := by
  classical
  have hcomm := sgE_comm isCAR_fock ε c c a b rfl hε
  have key : sgE ε cpFock cmFock c c * sgE ε cpFock cmFock a b -
      sgE ε cpFock cmFock a b * sgE ε cpFock cmFock c c =
        ((root a b c : ℝ) : ℂ) • sgE ε cpFock cmFock a b := by
    rw [hcomm]
    by_cases hca : c = a
    · subst hca
      have hbc : b ≠ c := fun h => hab h.symm
      simp [root, Pi.single_apply, hbc, hab]
    · by_cases hbc : b = c
      · subst hbc
        simp [root, Pi.single_apply, hca, Ne.symm hca]
      · simp [root, Pi.single_apply, hca, Ne.symm hca, hbc, Ne.symm hbc]
  have h1 : sgE ε cpFock cmFock c c (sgE ε cpFock cmFock a b f) -
      sgE ε cpFock cmFock a b (sgE ε cpFock cmFock c c f) =
        ((root a b c : ℝ) : ℂ) • sgE ε cpFock cmFock a b f := by
    have h2 := congrArg (fun T : Module.End ℂ (Fock n) => T f) key
    simpa using h2
  rw [hf c, map_smul, sub_eq_iff_eq_add] at h1
  rw [h1, Pi.add_apply, Complex.ofReal_add, add_smul]
  abel
end ReciprocityTheory.ChartRestriction.DS
