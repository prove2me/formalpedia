-- Prove2me | solution 1 for WilliamsonShmoys.three_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:16:00.590971+00:00
-- url     : https://prove2.me/submissions/be6709ce-2c17-4f81-89a1-e28540a50861

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Theorems.Thm_WilliamsonShmoys_three_vertex_successor_local_data__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

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
    ∀ d e : H.Dart, d.fst = e.fst →
      ∃ k : Nat,
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e := by
  let succ : H.Dart → H.Dart := fun a =>
    dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)
  have hlocal := WilliamsonShmoys.three_vertex_successor_local_data__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a2
    H hV F corner dart hTail hHead hInjective hCovered hcomplete
  intro d e hde
  rcases hlocal d e hde with heq | hstep
  · exact ⟨0, by simpa using heq⟩
  · exact ⟨1, by simpa [succ] using hstep⟩