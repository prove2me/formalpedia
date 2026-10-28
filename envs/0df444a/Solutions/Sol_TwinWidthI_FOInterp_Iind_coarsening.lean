-- Prove2me | solution 1 for TwinWidthI.FOInterp.Iind_coarsening
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:14:13.358739+00:00
-- url     : https://prove2.me/submissions/1600d727-f4fa-4b4b-ba94-021933e599f7

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

open Finset

namespace Aux_TWI_coarse
open TwinWidthI.FOInterp

lemma part_mono {V : Type*} [Fintype V] [DecidableEq V] (P P' : Finpartition (univ : Finset V))
    (h : P ≤ P') (x y : V) (hxy : P.part x = P.part y) : P'.part x = P'.part y := by
  obtain ⟨c, hc, hbc⟩ := h (P.part_mem.mpr (mem_univ x))
  have hx : x ∈ c := hbc (P.mem_part_self.mpr (mem_univ x))
  have hy : y ∈ c := by
    apply hbc
    rw [hxy]
    exact P.mem_part_self.mpr (mem_univ y)
  rw [P'.part_eq_of_mem hc hx, P'.part_eq_of_mem hc hy]

lemma auto_mono {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P P' : Finpartition (univ : Finset V)) (h : P ≤ P') (T : Set (List V)) (f : List V → List V)
    (hf : IsAuto G P T f) : IsAuto G P' T f := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨h1, h2, ?_⟩
  intro s hs a b x y x' y' ha hb ha' hb'
  obtain ⟨e1, e2, e3⟩ := h3 s hs a b x y x' y' ha hb ha' hb'
  exact ⟨e1, e2, part_mono P P' h x x' e3⟩

lemma sib_mono {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P P' : Finpartition (univ : Finset V)) (h : P ≤ P') (T : Set (List V)) (s : List V)
    (v v' : V) (hs : EquivSiblings G P T s v v') : EquivSiblings G P' T s v v' := by
  obtain ⟨h1, h2, h3, f, hf, hf1, hf2⟩ := hs
  exact ⟨h1, h2, h3, f, auto_mono G P P' h T f hf, hf1, hf2⟩

end Aux_TWI_coarse

open TwinWidthI.FOInterp in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P P' : Finpartition (univ : Finset V)) (ℓ : ℕ) :
    (∀ u u' : V, (Eind G P (ℓ + 2)).Reachable u u' → P.part u = P.part u') ∧
    (P ≤ P' → ∀ u u' : V, (Eind G P (ℓ + 2)).Adj u u' → (Eind G P' (ℓ + 2)).Adj u u') ∧
    (P ≤ P' → ∀ u u' : V, (Eind G P (ℓ + 2)).Reachable u u' →
      (Eind G P' (ℓ + 2)).Reachable u u') := by
  have hadj : ∀ u u' : V, (Eind G P (ℓ + 2)).Adj u u' → P.part u = P.part u' := by
    rintro u u' ⟨T, -, h1, -, -, f, hf, hf1, -⟩
    have hs : ([] ++ [u] : List V) ∈ T := h1
    have := (hf.2.2 ([] ++ [u]) hs 0 0 u u u' u' (by simp) (by simp)
      (by rw [hf1]; simp) (by rw [hf1]; simp)).2.2
    exact this
  have hadj2 : P ≤ P' → ∀ u u' : V, (Eind G P (ℓ + 2)).Adj u u' →
      (Eind G P' (ℓ + 2)).Adj u u' := by
    intro hle u u' ⟨T, hT, hsib⟩
    refine ⟨T, ?_, Aux_TWI_coarse.sib_mono G P P' hle T [] u u' hsib⟩
    unfold IsReduction at hT ⊢
    clear hsib
    induction hT with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      obtain ⟨s, v, v', hs, hB⟩ := hstep
      exact ih.tail ⟨s, v, v', Aux_TWI_coarse.sib_mono G P P' hle _ s v v' hs, hB⟩
  refine ⟨?_, hadj2, ?_⟩
  · intro u u' ⟨w⟩
    induction w with
    | nil => rfl
    | cons ha _ ih => exact (hadj _ _ ha).trans ih
  · intro hle u u' h
    exact h.mono (fun a b hab => hadj2 hle a b hab)
