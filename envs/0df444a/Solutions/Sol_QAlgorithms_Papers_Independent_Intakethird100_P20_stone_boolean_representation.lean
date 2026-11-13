-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.stone_boolean_representation
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:57:07.6562+00:00
-- url     : https://prove2.me/submissions/3323c2a0-254f-41c5-a1b8-60b26b035e9f

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_heyting_stone_compact
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthomodular_basic_sets_injective
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_distributive_basic_unions
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- stone-boolean-representation; de Groote, Observables I, PDF pp. 8, 39.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem solution {L : Type u} [BooleanAlgebra L] :
    CompactSpace (StoneSpectrum L) ∧ T2Space (StoneSpectrum L) ∧
    TopologicalSpace.IsTopologicalBasis {s : Set (StoneSpectrum L) | IsClopen s} ∧
    ∃ e : L ≃o Clopens (StoneSpectrum L),
      ∀ a : L, (e a : Set (StoneSpectrum L)) = stoneBasic a := by
  classical
  letI : CompactSpace (StoneSpectrum L) := heyting_stone_compact
  have ht := stone_topology_properties (L := L)
  have hperp : IsOrthocomplement (compl : L → L) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; simp
    · intro a b; simp
    · intro a; simp
  have horth : IsOrthomodular (compl : L → L) :=
    ⟨hperp, fun a b c _ _ => inf_sup_left a b c⟩
  have hinj : Function.Injective (stoneBasic : L → Set (StoneSpectrum L)) :=
    fun a b h => orthomodular_basic_sets_injective compl horth h
  have hdist : IsDistributive (L := L) :=
    ⟨fun a b c => inf_sup_left a b c, fun a b c => sup_inf_left a b c⟩
  have hsup := (distributive_basic_unions (L := L)).1 hdist
  have hfinite (s : Set L) (hs : s.Finite) :
      ∃ a : L, stoneBasic a = ⋃ b ∈ s, stoneBasic b := by
    induction s, hs using Set.Finite.induction_on with
    | empty =>
      exact ⟨⊥, by simpa using ht.2.1⟩
    | @insert b s hb hs ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨b ⊔ a, ?_⟩
      rw [← hsup, ha]
      ext C
      simp
  let f : L → Clopens (StoneSpectrum L) := fun a => ⟨stoneBasic a, ht.2.2.2.1 a⟩
  have hfi : Function.Injective f := by
    intro a b h
    exact hinj (congrArg (fun C : Clopens (StoneSpectrum L) => (C : Set (StoneSpectrum L))) h)
  have hfs : Function.Surjective f := by
    intro C
    obtain ⟨s, hs, hC⟩ := eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open
      (stoneBasic : L → Set (StoneSpectrum L)) ht.2.2.2.2.1 (C : Set (StoneSpectrum L))
      C.isClosed.isCompact C.isOpen
    obtain ⟨a, ha⟩ := hfinite s hs
    exact ⟨a, SetLike.coe_injective (ha.trans hC.symm)⟩
  have horder (a b : L) : f a ≤ f b ↔ a ≤ b := by
    constructor
    · intro h
      have hsub : stoneBasic a ⊆ stoneBasic b := h
      have heq : stoneBasic (a ⊔ b) = stoneBasic b :=
        (hsup a b).symm.trans (Set.union_eq_right.mpr hsub)
      exact sup_eq_right.mp (hinj heq)
    · intro h C hCa
      exact (quasipoint_upward_and_meet_closed C.val C.property).1 a hCa b h
  let g : L ↪o Clopens (StoneSpectrum L) :=
    { toFun := f, inj' := hfi, map_rel_iff' := fun {a b} => horder a b }
  let e : L ≃o Clopens (StoneSpectrum L) := OrderIso.ofSurjective g hfs
  exact ⟨inferInstance, ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.1, e, fun a => rfl⟩
