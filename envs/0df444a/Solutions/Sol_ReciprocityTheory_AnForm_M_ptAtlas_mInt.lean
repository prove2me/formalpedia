-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.ptAtlas_mInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:22:49.969341+00:00
-- url     : https://prove2.me/submissions/e63de407-29da-448e-afab-0af0df99f2a2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (Y : Type*) [TopologicalSpace Y] [Unique Y] (g : Y → ℝ) :
    mInt (ptAtlas Y) Fin.elim0 g = g default := by
  have hne : Nonempty (ChartPartition (ptAtlas Y)) := ⟨ptPart Y⟩
  have hχ : ∀ (Q : ChartPartition (ptAtlas Y)) (x : Y), Q.χ (0 : Fin 1) x = 1 := by
    intro Q x
    have h := Q.sum_eq_one x
    change ∑ j : Fin 1, Q.χ j x = 1 at h
    rwa [Fin.sum_univ_one] at h
  have hd : ∀ y : Fin 0 → ℂ, locDens (ptAtlas Y) Fin.elim0 (0 : Fin 1) y = 1 := by
    intro y
    simp [locDens, maDens, mdisc]
  have ht : ((ptAtlas Y).chart (0 : Fin 1)).target = Set.univ := rfl
  unfold mInt
  rw [dif_pos hne]
  unfold integralWith
  change ∑ j : Fin 1, _ = _
  rw [Fin.sum_univ_one]
  have e : ∀ y : Fin 0 → ℂ, hne.some.χ (0 : Fin 1) (((ptAtlas Y).chart (0 : Fin 1)).symm y) *
      g (((ptAtlas Y).chart (0 : Fin 1)).symm y) * locDens (ptAtlas Y) Fin.elim0 (0 : Fin 1) y =
      g default := by
    intro y
    rw [hχ, hd, Subsingleton.elim (((ptAtlas Y).chart (0 : Fin 1)).symm y) default]
    ring
  simp only [e, ht]
  simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ, MeasureTheory.measureReal_def]
end ReciprocityTheory.AnForm.M
