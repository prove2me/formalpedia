-- Prove2me | solution 1 for R03SP06.p3_factor_glue
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:03:59.121207+00:00
-- url     : https://prove2.me/submissions/cd8bb9f0-c4f2-443a-b0f7-fb2caf083ca6

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
    {G : SimpleGraph V} (L : P3Path G)
    (hfactor : Nonempty (P3Factor (eraseP3 G L))) :
    Nonempty (P3Factor G) := by
  obtain ⟨p⟩ := hfactor
  let W := {v : V // v ≠ L.left ∧ v ≠ L.center ∧ v ≠ L.right}
  let t : Fin 3 → V := ![L.left, L.center, L.right]
  have htinj : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [t, eq_comm, L.left_ne_center, L.center_ne_right, L.left_ne_right]
  let g : W ⊕ Fin 3 → V :=
    Sum.elim (fun w : W => w.1) t
  have ginj : Function.Injective g := by
    apply Function.Injective.sumElim
    · intro w w' h
      exact Subtype.ext h
    · exact htinj
    · intro w i h
      fin_cases i
      · exact w.2.1 h
      · exact w.2.2.1 h
      · exact w.2.2.2 h
  have gsurj : Function.Surjective g := by
    intro v
    by_cases hleft : v = L.left
    · exact ⟨Sum.inr (0 : Fin 3), by simp [g, t, hleft]⟩
    by_cases hcenter : v = L.center
    · exact ⟨Sum.inr (1 : Fin 3), by simp [g, t, hcenter]⟩
    by_cases hright : v = L.right
    · exact ⟨Sum.inr (2 : Fin 3), by simp [g, t, hright]⟩
    · let w : W := ⟨v, hleft, hcenter, hright⟩
      exact ⟨Sum.inl w, by rfl⟩
  let ge : W ⊕ Fin 3 ≃ V := Equiv.ofBijective g ⟨ginj, gsurj⟩
  have hge_inl (w : W) : ge (Sum.inl w) = w.1 := by rfl
  have hge_inr (j : Fin 3) : ge (Sum.inr j) = t j := by rfl
  let oldToW : (Fin p.blockCount × Fin 3) ⊕ Fin 3 ≃ W ⊕ Fin 3 :=
    Equiv.sumCongr p.place (Equiv.refl (Fin 3))
  let indexSplit : (Fin (p.blockCount + 1) × Fin 3) ≃
      (Fin p.blockCount × Fin 3) ⊕ Fin 3 := by
    let e1 : (Fin (p.blockCount + 1) × Fin 3) ≃
        ((Fin p.blockCount ⊕ Fin 1) × Fin 3) :=
      Equiv.prodCongr finSumFinEquiv.symm (Equiv.refl (Fin 3))
    let e2 : ((Fin p.blockCount ⊕ Fin 1) × Fin 3) ≃
        ((Fin p.blockCount × Fin 3) ⊕ (Fin 1 × Fin 3)) :=
      Equiv.sumProdDistrib (Fin p.blockCount) (Fin 1) (Fin 3)
    let e3 : ((Fin p.blockCount × Fin 3) ⊕ (Fin 1 × Fin 3)) ≃
        ((Fin p.blockCount × Fin 3) ⊕ Fin 3) :=
      Equiv.sumCongr (Equiv.refl _) (Equiv.uniqueProd (Fin 3) (Fin 1))
    exact e1.trans (e2.trans e3)
  let place : (Fin (p.blockCount + 1) × Fin 3) ≃ V :=
    indexSplit.trans (oldToW.trans ge)
  have hplace_old (i : Fin p.blockCount) (j : Fin 3) :
      place (i.castSucc, j) = (p.place (i, j)).1 := by
    simp [place, indexSplit, oldToW, ge, g, t, hge_inl, hge_inr,
      Equiv.trans_apply, Equiv.prodCongr, Equiv.sumProdDistrib,
      Equiv.sumCongr, Equiv.uniqueProd]
  have hplace_new (j : Fin 3) : place (Fin.last p.blockCount, j) = t j := by
    simp [place, indexSplit, oldToW, ge, g, t, hge_inl, hge_inr,
      Equiv.trans_apply, Equiv.prodCongr, Equiv.sumProdDistrib,
      Equiv.sumCongr, Equiv.uniqueProd]
  refine ⟨{
    blockCount := p.blockCount + 1
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [hplace_new, t] using L.edge_left
    · simpa [hplace_old, eraseP3] using p.edge01 j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [hplace_new, t] using L.edge_right
    · simpa [hplace_old, eraseP3] using p.edge12 j

