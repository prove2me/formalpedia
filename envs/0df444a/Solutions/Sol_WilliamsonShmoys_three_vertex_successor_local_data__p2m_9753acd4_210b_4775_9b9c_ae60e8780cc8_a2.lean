-- Prove2me | solution 1 for WilliamsonShmoys.three_vertex_successor_local_data__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T22:47:21.474481+00:00
-- url     : https://prove2.me/submissions/d63df272-118d-4790-8aab-57afd5f584c5

import Theorems.Thm_WilliamsonShmoys_three_vertex_outgoing_dart_fiber_card__p2m_551112cf_8b4c_4517_8603_726684976d71_a4
import Theorems.Thm_fintype_card_two_elim__p2m_551112cf_8b4c_4517_8603_726684976d71_a4
import Theorems.Thm_WilliamsonShmoys_three_vertex_successor_is_other_outgoing_dart__p2m_551112cf_8b4c_4517_8603_726684976d71_a4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : Fintype.card V = 3)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f))
    (hCovered : ∀ v, ∃ f i, corner f i = v)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v) :
    let succ : H.Dart → H.Dart := fun a =>
      dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)
    ∀ d e : H.Dart, d.fst = e.fst → d = e ∨ succ d = e := by
  classical
  dsimp only
  intro d e hde
  let s := dart ((dart.symm d.symm).1, (dart.symm d.symm).2 + 1)
  have hs := WilliamsonShmoys.three_vertex_successor_is_other_outgoing_dart__p2m_551112cf_8b4c_4517_8603_726684976d71_a4 H F corner dart hTail hHead hInjective d
  have hcard : Fintype.card {a : H.Dart // a.fst = d.fst} = 2 :=
    WilliamsonShmoys.three_vertex_outgoing_dart_fiber_card__p2m_551112cf_8b4c_4517_8603_726684976d71_a4 H hV hcomplete d.fst
  let x : {a : H.Dart // a.fst = d.fst} := ⟨d, rfl⟩
  let y : {a : H.Dart // a.fst = d.fst} := ⟨s, hs.1⟩
  let z : {a : H.Dart // a.fst = d.fst} := ⟨e, hde.symm⟩
  have hxy : x ≠ y := by
    intro h
    apply hs.2
    exact (congrArg Subtype.val h).symm
  have hz := fintype_card_two_elim__p2m_551112cf_8b4c_4517_8603_726684976d71_a4 hcard x y hxy z
  rcases hz with h | h
  · left
    exact (congrArg Subtype.val h).symm
  · right
    exact (congrArg Subtype.val h).symm

