-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.internalGrpAndGroupCat
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:33:59.045848+00:00
-- url     : https://prove2.me/submissions/2624a2e9-cfe0-4846-b733-2484da447d9a

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF p. 8: the explicit mutually inverse structure translations between
internal Grp categories and strict group objects in Cat. Under total-arrow
coordinates both translations retain the category and BOTH pointwise groups.
This claims no additional equivalence of categories of internal functors. -/
theorem solution {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) :
    InternalCategoryInGrp D ↔ GroupObjectInCat D := by
  constructor
  · intro h
    have hs (a : A) : D.source a⁻¹ = (D.source a)⁻¹ := (sourceHom D h).map_inv a
    have ht (a : A) : D.target a⁻¹ = (D.target a)⁻¹ := (targetHom D h).map_inv a
    refine ⟨h.category,?_,?_,?_⟩
    · refine ⟨fun a => ⟨h.source_mul a.1 a.2,h.target_mul a.1 a.2⟩,
        fun x => (h.identity_mul x.1 x.2).symm,?_⟩
      intro f g hfg
      exact (h.interchange f.1 g.1 f.2 g.2 (congrArg Prod.fst hfg) (congrArg Prod.snd hfg)).symm
    · exact ⟨fun _ => ⟨h.source_one,h.target_one⟩,
        fun _ => h.identity_one.symm,fun _ _ _ => h.compose_one.symm⟩
    · refine ⟨fun a => ⟨hs a,ht a⟩,fun x => ((identityHom D h).map_inv x).symm,?_⟩
      intro f g hfg
      have hinv : D.target f⁻¹ = D.source g⁻¹ := by rw [ht,hs,hfg]
      have hc := h.interchange f⁻¹ g⁻¹ f g hinv hfg
      simp only [inv_mul_cancel,h.compose_one] at hc
      exact (eq_inv_of_mul_eq_one_left hc.symm).symm
  · rintro ⟨hc,hm,hu,hi⟩
    refine ⟨hc,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (hu.1 PUnit.unit).1
    · intro a b
      exact (hm.1 (a,b)).1
    · exact (hu.1 PUnit.unit).2
    · intro a b
      exact (hm.1 (a,b)).2
    · exact (hu.2.1 PUnit.unit).symm
    · intro x y
      exact (hm.2.1 (x,y)).symm
    · exact (hu.2.2 PUnit.unit PUnit.unit rfl).symm
    · intro f g a b hfg hab
      exact (hm.2.2 (f,a) (g,b) (Prod.ext hfg hab)).symm
