-- Prove2me | solution 1 for R03SP06.p3_factor_leaf_forced_center
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:04:00.984295+00:00
-- url     : https://prove2.me/submissions/aefb65c4-fe5c-4492-b664-b046754cb7cf

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only extraction lemma for leaf-bearing P3-factors.  It is a generic
fact about the project's ordered-triple factor model: a degree-one vertex can
occur only at an end of its factor block, and the unique neighbor is the
block center.
-/

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]


end R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {G : SimpleGraph V} {u x : V}
    (hleaf : ∀ v, G.Adj u v ↔ v = x)
    (hfactor : Nonempty (P3Factor G)) :
    ∃ (p : P3Factor G) (i : Fin p.blockCount),
      (p.place (i, (0 : Fin 3)) = u ∧
          p.place (i, (1 : Fin 3)) = x) ∨
        (p.place (i, (2 : Fin 3)) = u ∧
          p.place (i, (1 : Fin 3)) = x) := by
  obtain ⟨p⟩ := hfactor
  let q := p.place.symm u
  have hq : p.place q = u := p.place.apply_symm_apply u
  have hqpos : q.2.val = 0 ∨ q.2.val = 1 ∨ q.2.val = 2 := by
    have hlt := q.2.isLt
    omega
  rcases hqpos with hzero | hone | htwo
  · have hz : q.2 = (0 : Fin 3) := by
      apply Fin.ext
      exact hzero
    have hzq : q = (q.1, (0 : Fin 3)) := by
      apply Prod.ext
      · rfl
      · exact hz
    have hu : p.place (q.1, (0 : Fin 3)) = u := by
      rw [← hzq]
      exact hq
    have hadj := p.edge01 q.1
    have hx : p.place (q.1, (1 : Fin 3)) = x := by
      apply (hleaf _).mp
      rw [← hu]
      exact hadj
    exact ⟨p, q.1, Or.inl ⟨hu, hx⟩⟩
  · have hz : q.2 = (1 : Fin 3) := by
      apply Fin.ext
      exact hone
    have hzq : q = (q.1, (1 : Fin 3)) := by
      apply Prod.ext
      · rfl
      · exact hz
    have hu : p.place (q.1, (1 : Fin 3)) = u := by
      rw [← hzq]
      exact hq
    have hadj_left := p.edge01 q.1
    have hleft : p.place (q.1, (0 : Fin 3)) = x := by
      apply (hleaf _).mp
      rw [← hu]
      exact hadj_left.symm
    have hadj_right := p.edge12 q.1
    have hright : p.place (q.1, (2 : Fin 3)) = x := by
      apply (hleaf _).mp
      rw [← hu]
      exact hadj_right
    have hplaces : p.place (q.1, (0 : Fin 3)) =
        p.place (q.1, (2 : Fin 3)) := hleft.trans hright.symm
    have hindices : (q.1, (0 : Fin 3)) = (q.1, (2 : Fin 3)) :=
      p.place.injective hplaces
    have hsecond := congrArg Prod.snd hindices
    have hsecond' : (0 : Fin 3) = 2 := by simpa using hsecond
    have hne : (0 : Fin 3) ≠ 2 := by decide
    exact (hne hsecond').elim
  · have hz : q.2 = (2 : Fin 3) := by
      apply Fin.ext
      exact htwo
    have hzq : q = (q.1, (2 : Fin 3)) := by
      apply Prod.ext
      · rfl
      · exact hz
    have hu : p.place (q.1, (2 : Fin 3)) = u := by
      rw [← hzq]
      exact hq
    have hadj := p.edge12 q.1
    have hx : p.place (q.1, (1 : Fin 3)) = x := by
      apply (hleaf _).mp
      rw [← hu]
      exact hadj.symm
    exact ⟨p, q.1, Or.inr ⟨hu, hx⟩⟩

