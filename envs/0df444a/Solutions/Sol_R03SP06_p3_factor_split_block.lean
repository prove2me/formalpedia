-- Prove2me | solution 1 for R03SP06.p3_factor_split_block
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:04:02.634558+00:00
-- url     : https://prove2.me/submissions/224ac383-8ecb-43c2-be8c-899a1dd9a572

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]


end R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {G : SimpleGraph V} (p : P3Factor G) (i : Fin p.blockCount) :
    ∃ L : P3Path G,
      L.left = p.place (i, 0) ∧
      L.center = p.place (i, 1) ∧
      L.right = p.place (i, 2) ∧
      Nonempty (P3Factor (eraseP3 G L)) := by
    let a : V := p.place (i, 0)
    let b : V := p.place (i, 1)
    let c : V := p.place (i, 2)
    let L : P3Path G := {
      left := a
      center := b
      right := c
      left_ne_center := by
        intro hab
        have hp : (i, (0 : Fin 3)) = (i, (1 : Fin 3)) :=
          p.place.injective hab
        exact Fin.zero_ne_one (congrArg Prod.snd hp)
      center_ne_right := by
        intro hbc
        have hp : (i, (1 : Fin 3)) = (i, (2 : Fin 3)) :=
          p.place.injective hbc
        exact (by decide : (1 : Fin 3) ≠ 2) (congrArg Prod.snd hp)
      left_ne_right := by
        intro hac
        have hp : (i, (0 : Fin 3)) = (i, (2 : Fin 3)) :=
          p.place.injective hac
        exact (by decide : (0 : Fin 3) ≠ 2) (congrArg Prod.snd hp)
      edge_left := p.edge01 i
      edge_right := p.edge12 i
    }
    let J := {j : Fin p.blockCount // j ≠ i}
    have hJcard : Fintype.card J = p.blockCount - 1 := by
      classical
      rw [Fintype.card_subtype]
      change (Finset.univ.filter (fun x : Fin p.blockCount => x ≠ i)).card =
        p.blockCount - 1
      rw [show Finset.univ.filter (fun x : Fin p.blockCount => x ≠ i) =
          Finset.univ.erase i by
        ext x
        simp]
      simp
    let skip : Fin (p.blockCount - 1) ≃ J :=
      (Equiv.cast (congrArg Fin hJcard.symm)).trans (Fintype.equivFin J).symm
    have hnot0 (j : Fin (p.blockCount - 1)) :
        p.place ((skip j).1, (0 : Fin 3)) ≠ p.place (i, 0) := by
      intro h
      apply (skip j).property
      exact congrArg Prod.fst (p.place.injective h)
    have hnot1 (j : Fin (p.blockCount - 1)) :
        p.place ((skip j).1, (1 : Fin 3)) ≠ p.place (i, 1) := by
      intro h
      apply (skip j).property
      exact congrArg Prod.fst (p.place.injective h)
    have hnot2 (j : Fin (p.blockCount - 1)) :
        p.place ((skip j).1, (2 : Fin 3)) ≠ p.place (i, 2) := by
      intro h
      apply (skip j).property
      exact congrArg Prod.fst (p.place.injective h)
    let W := {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c}
    let oldPlace : (Fin (p.blockCount - 1) × Fin 3) → W := fun z =>
      ⟨p.place ((skip z.1).1, z.2), by
        have hfirst : (skip z.1).1 ≠ i := (skip z.1).property
        have h0 : p.place ((skip z.1).1, z.2) ≠ a := by
          intro h
          apply hfirst
          exact congrArg Prod.fst (p.place.injective h)
        have h1 : p.place ((skip z.1).1, z.2) ≠ b := by
          intro h
          apply hfirst
          exact congrArg Prod.fst (p.place.injective h)
        have h2 : p.place ((skip z.1).1, z.2) ≠ c := by
          intro h
          apply hfirst
          exact congrArg Prod.fst (p.place.injective h)
        exact ⟨h0, h1, h2⟩⟩
    have old_inj : Function.Injective oldPlace := by
      intro z z' hzz'
      have hp : p.place ((skip z.1).1, z.2) =
          p.place ((skip z'.1).1, z'.2) := congrArg Subtype.val hzz'
      have hpair : ((skip z.1).1, z.2) = ((skip z'.1).1, z'.2) :=
        p.place.injective hp
      have hskip : skip z.1 = skip z'.1 :=
        Subtype.ext (congrArg Prod.fst hpair)
      have hz1 : z.1 = z'.1 := skip.injective hskip
      have hz2 : z.2 = z'.2 :=
        congrArg (fun q : Fin p.blockCount × Fin 3 => q.2) hpair
      exact Prod.ext hz1 hz2
    have old_surj : Function.Surjective oldPlace := by
      intro w
      obtain ⟨z, hz⟩ := p.place.surjective w.1
      obtain ⟨j, k⟩ := z
      have hj : j ≠ i := by
        intro hji
        subst j
        fin_cases k
        · exact w.2.1 hz.symm
        · exact w.2.2.1 hz.symm
        · exact w.2.2.2 hz.symm
      let q : J := ⟨j, hj⟩
      let r : Fin (p.blockCount - 1) := skip.symm q
      refine ⟨(r, k), ?_⟩
      apply Subtype.ext
      have hskip : skip r = q := skip.apply_symm_apply q
      have hval : (skip r).1 = j := congrArg Subtype.val hskip
      simpa [oldPlace, r, q, hval] using hz
    let rplace : (Fin (p.blockCount - 1) × Fin 3) ≃ W := Equiv.ofBijective oldPlace
      ⟨old_inj, old_surj⟩
    have hfactor : Nonempty (P3Factor (eraseP3 G L)) := by
      refine ⟨{
        blockCount := p.blockCount - 1
        place := rplace
        edge01 := ?_
        edge12 := ?_
      }⟩
      · intro j
        change G.Adj (p.place ((skip j).1, 0)) (p.place ((skip j).1, 1))
        exact p.edge01 (skip j).1
      · intro j
        change G.Adj (p.place ((skip j).1, 1)) (p.place ((skip j).1, 2))
        exact p.edge12 (skip j).1
    refine ⟨L, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · simpa [L, a, b, c, W] using hfactor

