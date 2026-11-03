-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_face_structure_core__p2m_49320d7c_d315_47bf_bd18_a40df71c3333_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:56:29.514266+00:00
-- url     : https://prove2.me/submissions/94bc166f-9a9e-4781-8d1d-d90a59f46e3a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (hcard : 3 ≤ Fintype.card V) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (F : Type) (hF : Fintype F) (hFdec : DecidableEq F) (face : K.Dart → F),
      (letI : Fintype F := hF
       letI : DecidableEq F := hFdec
       Fintype.card V + Fintype.card F = K.edgeFinset.card + 2 ∧
       (∀ f : F, 3 ≤ Fintype.card {d : K.Dart // face d = f})) := by
  classical
  obtain ⟨F, inst, len, heuler, hlen, hsum⟩ :=
    WilliamsonShmoys.face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5 K hK hconn hcard
  letI : Fintype F := inst
  have hedge : K.edgeSet.ncard = K.edgeFinset.card := by
    rw [← Set.fintypeCard_eq_ncard, K.edgeFinset_card]
  have hc : Fintype.card (Σ f : F, Fin (len f)) = Fintype.card K.Dart := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [hsum, hedge, K.dart_card_eq_twice_card_edges]
  let e : (Σ f : F, Fin (len f)) ≃ K.Dart := Fintype.equivOfCardEq hc
  let face : K.Dart → F := fun d => (e.symm d).1
  refine ⟨F, inst, Classical.decEq F, face, ?_, ?_⟩
  · simpa [hedge] using heuler
  · intro f
    have hinj : Function.Injective (fun i : Fin (len f) =>
        (⟨e ⟨f, i⟩, by simp [face]⟩ : {d : K.Dart // face d = f})) := by
      intro i j hij
      have h := congrArg Subtype.val hij
      have h' := e.injective h
      cases h'
      rfl
    have hle := Fintype.card_le_of_injective _ hinj
    simpa using (hlen f).trans (by simpa using hle)
