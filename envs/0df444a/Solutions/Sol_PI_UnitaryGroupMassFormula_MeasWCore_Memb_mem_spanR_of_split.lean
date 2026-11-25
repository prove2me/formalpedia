-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.Memb.mem_spanR_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:44.542807+00:00
-- url     : https://prove2.me/submissions/53356d61-3c9a-4797-bea0-39825f10dac9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_ratV
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_eq_iff_split
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.MeasWCore.Memb.mapV_apply

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.MeasWCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct
open PI.UnitaryGroupMassFormula.MeasWCore.Memb
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.MeasWCore.Memb
theorem _root_.solution (hbij : Function.Bijective (splT (F := F) (E := E))) {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) (w : Fin n → AF F ⊗[F] E)
    (h1 : mapV (E := E) (fstA F) w ∈ spanR (F := F) (Ainf F) Y s)
    (h2 : mapV (E := E) (sndA F) w ∈ spanR (F := F) (Af F) Y s) :
    w ∈ spanR (F := F) (AF F) Y s := by
  classical
  simp only [spanR, Set.image_eq_range] at h1 h2 ⊢
  rw [Submodule.mem_span_range_iff_exists_fun] at h1 h2
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  choose c hc using fun a => hbij.2 (c1 a, c2 a)
  have hw : w = ∑ a, c a • ratV (F := F) (AF F) (Y a) := by
    rw [eq_iff_split hbij.1]
    constructor
    · rw [← hc1, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mapV_smul, mapV_ratV]
      congr 1
      exact (congrArg Prod.fst (hc a)).symm
    · rw [← hc2, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mapV_smul, mapV_ratV]
      congr 1
      exact (congrArg Prod.snd (hc a)).symm
  rw [hw, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨c, rfl⟩
end PI.UnitaryGroupMassFormula.MeasWCore.Memb
