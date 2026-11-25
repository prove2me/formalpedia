-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.eeVd_nnMinus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:26:58.680363+00:00
-- url     : https://prove2.me/submissions/b588bd8e-9e3e-4ce5-8ddb-28c430149bb6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Tensor
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_eeVd_apply__ec28e3696ecf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelli_expand_minus


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : IsGlRep E)
    (β : Fin (m + 1) → ℂ) (om : ℂ) (v : M) (hv : capelliC E om v = 0) :
    eeVd E (nnMinus E β om v) = (om - (m : ℂ)) • nnMinus E β om v := by
  have hE' : GlRelR E := hE
  funext a
  have key : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
      E a d (cminor E c.succAbove d.succAbove om v) =
      (-((om - (m : ℂ)) * (-1 : ℂ) ^ ((a : ℕ) + (c : ℕ)))) • cminor E c.succAbove a.succAbove om v := by
    intro c
    have h := LinearMap.congr_fun (capelli_expand_minus E hE' om a c) v
    have hr : (if a = c then capelliC E om else 0) v = 0 := by split_ifs <;> simp [hv]
    rw [hr, LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, Module.End.mul_apply, capEntry, LinearMap.add_apply, smul_add,
      Finset.sum_add_distrib] at h
    have h2 : ∑ x : Fin (m + 1), ((-1 : ℂ) ^ ((x : ℕ) + (c : ℕ))) •
        (if a = x then algebraMap ℂ (Module.End ℂ M) (om - (m : ℂ)) else 0) (cminor E c.succAbove x.succAbove om v) =
        ((om - (m : ℂ)) * (-1 : ℂ) ^ ((a : ℕ) + (c : ℕ))) • cminor E c.succAbove a.succAbove om v := by
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl, Module.algebraMap_end_apply, smul_smul, mul_comm]
      · intro d _ hd; simp [Ne.symm hd]
      · simp
    rw [h2] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h
  rw [eeVd_apply', Pi.smul_apply]
  simp only [nnMinus, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  calc _ = -(β c • ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        E a d (cminor E c.succAbove d.succAbove om v)) := by
        rw [Finset.smul_sum]; simp only [smul_smul]
    _ = _ := by rw [key c, smul_smul, smul_smul, ← neg_smul]; congr 1; ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
