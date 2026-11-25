-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.eeV_nnPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:09:55.436067+00:00
-- url     : https://prove2.me/submissions/d31a0c63-3697-482f-bfe8-65c741a3e072

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Tensor
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_eeV_apply__dfa6054e04b2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelli_expand_plus


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
    (y : Fin (m + 1) → ℂ) (om : ℂ) (v : M) (hv : capelliC E om v = 0) :
    eeV E (nnPlus E y om v) = (-om) • nnPlus E y om v := by
  have hE' : GlRelR E := hE
  funext b
  have key : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
      E d b (cminor E d.succAbove c.succAbove (om - 1) v) =
      (-(om * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ)))) • cminor E b.succAbove c.succAbove (om - 1) v := by
    intro c
    have h := LinearMap.congr_fun (capelli_expand_plus E hE' om b c) v
    have hr : (if b = c then capelliC E om else 0) v = 0 := by split_ifs <;> simp [hv]
    rw [hr, LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, Module.End.mul_apply, capEntry, LinearMap.add_apply, smul_add,
      Finset.sum_add_distrib] at h
    have h2 : ∑ x : Fin (m + 1), ((-1 : ℂ) ^ ((x : ℕ) + (c : ℕ))) •
        (if x = b then algebraMap ℂ (Module.End ℂ M) om else 0) (cminor E x.succAbove c.succAbove (om - 1) v) =
        (om * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor E b.succAbove c.succAbove (om - 1) v := by
      rw [Finset.sum_eq_single b]
      · simp [Module.algebraMap_end_apply, smul_smul, mul_comm]
      · intro d _ hd; simp [hd]
      · simp
    rw [h2] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h
  rw [eeV_apply', Pi.smul_apply]
  simp only [nnPlus, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  calc _ = y c • ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (c : ℕ))) •
        E a b (cminor E a.succAbove c.succAbove (om - 1) v) := by
        rw [Finset.smul_sum]; simp only [smul_smul]
    _ = _ := by rw [key c, smul_smul, smul_smul]; congr 1; ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
