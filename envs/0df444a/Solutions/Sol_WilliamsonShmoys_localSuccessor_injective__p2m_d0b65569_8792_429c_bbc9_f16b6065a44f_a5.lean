-- Prove2me | solution 1 for WilliamsonShmoys.localSuccessor_injective__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:57:04.743578+00:00
-- url     : https://prove2.me/submissions/f762cba7-e98f-48b3-a9e8-20d89776d0a1

-- ID: 86948773-153a-4452-8924-09ae7fd7b44a | NAME: WilliamsonShmoys.localSuccessor_injective__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5 | 未本地编译验证
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (dart : (F × Fin 3) ≃ H.Dart) :
    Function.Injective (fun a : H.Dart =>
      dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) := by
  intro a b h
  have h1 : ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1) =
      ((dart.symm b.symm).1, (dart.symm b.symm).2 + 1) := dart.injective h
  have hinj1 : Function.Injective (fun i : Fin 3 => i + 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hfst := congrArg (fun p : F × Fin 3 => p.1) h1
  have hsnd' := congrArg (fun p : F × Fin 3 => p.2) h1
  have hsnd : (dart.symm a.symm).2 = (dart.symm b.symm).2 := hinj1 hsnd'
  have h2 : dart.symm a.symm = dart.symm b.symm := Prod.ext hfst hsnd
  have h3 : a.symm = b.symm := dart.symm.injective h2
  have h4 := congrArg (fun d : H.Dart => d.symm) h3
  simpa only [SimpleGraph.Dart.symm_symm] using h4
