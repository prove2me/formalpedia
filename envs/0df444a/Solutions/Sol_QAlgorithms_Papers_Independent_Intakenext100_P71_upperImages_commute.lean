-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P71.upperImages_commute
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:45:16.441911+00:00
-- url     : https://prove2.me/submissions/ece8d63b-9ebe-4529-be05-858694d175ca

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P71

open CategoryTheory Opposite

universe u v w

open QAlgorithms.Papers.Independent.Intakenext100.P71 in
theorem solution {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [J.Subcanonical]
    {H G : RightCrossedModule.{u, v, w} J} (E : Butterfly H G) :
    ∀ (U : C) (h : H.one.sections U) (g : G.one.sections U),
      onSections E.kappa U h * onSections E.iota U g =
        onSections E.iota U g * onSections E.kappa U h := by
  intro U h g
  have h1 := E.iota_equivariant U g (onSections E.kappa U h)
  rw [E.j_kappa, G.act_id] at h1
  conv_lhs => rw [h1]
  simp [mul_assoc]
