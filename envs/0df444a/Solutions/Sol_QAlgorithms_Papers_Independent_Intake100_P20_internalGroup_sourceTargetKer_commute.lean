-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.internalGroup_sourceTargetKer_commute
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:43:46.776997+00:00
-- url     : https://prove2.me/submissions/d75aa94a-beb4-4fbb-9a23-c8a854f15ec8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
import Mathlib.Tactic.Group

open QAlgorithms.Papers.Independent.Intake100.P20

universe u v
theorem solution {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) (a b : A)
    (ha : D.source a = 1) (hb : D.target b = 1) : a * b = b * a := by
  have hac : D.compose a 1 = a := by
    have hh := h.category.compose_identity a
    rw [ha,h.identity_one] at hh
    exact hh
  have hbc : D.compose 1 b = b := by
    have hh := h.category.identity_compose b
    rw [hb,h.identity_one] at hh
    exact hh
  have hab := h.interchange 1 a b 1 (h.target_one.trans ha.symm) (hb.trans h.source_one.symm)
  have hba := h.interchange b 1 1 a (hb.trans h.source_one.symm) (h.target_one.trans ha.symm)
  simp only [one_mul,mul_one,hac,hbc] at hab hba
  exact hab.symm.trans hba