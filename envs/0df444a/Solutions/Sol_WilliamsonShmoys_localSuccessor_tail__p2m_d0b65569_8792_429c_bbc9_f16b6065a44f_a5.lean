-- Prove2me | solution 1 for WilliamsonShmoys.localSuccessor_tail__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:30:20.688602+00:00
-- url     : https://prove2.me/submissions/76f45fdc-ec53-4e6d-9206-4d42a5a70620

-- ID: 1674a10a-7413-464c-95a7-ca7e73c084c5 | NAME: WilliamsonShmoys.localSuccessor_tail__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (corner : F → Fin 3 → V) (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (a : H.Dart) :
    (dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)).fst = a.fst := by
  rw [hTail]
  rw [← hHead (dart.symm a.symm).1 (dart.symm a.symm).2]
  simpa [SimpleGraph.Dart.symm]
