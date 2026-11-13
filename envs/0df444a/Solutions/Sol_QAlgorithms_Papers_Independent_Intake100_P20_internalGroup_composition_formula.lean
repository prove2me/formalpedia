-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.internalGroup_composition_formula
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:37:26.484082+00:00
-- url     : https://prove2.me/submissions/1f20025b-32ab-4a16-aa37-0e7e039b6fd9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

open QAlgorithms.Papers.Independent.Intake100.P20

universe u v
 theorem solution {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) (h : InternalCategoryInGrp D) (f g : A)
    (hfg : D.target f = D.source g) :
    D.compose g f = g * (D.identity (D.source g))⁻¹ * f := by
  let b := (D.identity (D.source g))⁻¹ * f
  have hb : D.target b = 1 := by
    change (targetHom D h) ((D.identity (D.source g))⁻¹ * f) = 1
    rw [map_mul,map_inv]
    change (D.target (D.identity (D.source g)))⁻¹ * D.target f = 1
    rw [h.category.target_identity,← hfg,inv_mul_cancel]
  have hbc : D.compose 1 b = b := by
    have hh := h.category.identity_compose b
    rw [hb,h.identity_one] at hh
    exact hh
  have hh := h.interchange (D.identity (D.source g)) g b 1
    (h.category.target_identity (D.source g)) (hb.trans h.source_one.symm)
  have hab : D.identity (D.source g) * b = f := by
    dsimp [b]
    rw [mul_inv_cancel_left]
  rw [mul_one,hab,h.category.compose_identity,hbc] at hh
  exact hh.trans (mul_assoc _ _ _).symm