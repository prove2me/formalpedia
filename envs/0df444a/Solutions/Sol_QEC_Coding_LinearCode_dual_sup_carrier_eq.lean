-- Prove2me | solution 1 for QEC.Coding.LinearCode.dual_sup_carrier_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:22.707413+00:00
-- url     : https://prove2.me/submissions/a7700534-6941-4100-9fc3-a00b442b7e4f

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C D : LinearCode F ι) :
    ({ carrier := C.carrier ⊔ D.carrier } : LinearCode F ι).dual.carrier =
      C.dual.carrier ⊓ D.dual.carrier := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    exact ⟨(C.mem_dual x).2 (fun c hc =>
        (mem_dual _ x).1 hx c (Submodule.mem_sup_left hc)),
      (D.mem_dual x).2 (fun d hd =>
        (mem_dual _ x).1 hx d (Submodule.mem_sup_right hd))⟩
  · rintro ⟨hC, hD⟩
    refine (mem_dual _ x).2 ?_
    intro y hy
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add, C.orthogonal_of_mem_dual hC hc, D.orthogonal_of_mem_dual hD hd,
      add_zero]
end QEC.Coding.LinearCode
