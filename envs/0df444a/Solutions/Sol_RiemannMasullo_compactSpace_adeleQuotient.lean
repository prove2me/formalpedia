-- Prove2me | solution 1 for RiemannMasullo.compactSpace_adeleQuotient
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:53:42.394836+00:00
-- url     : https://prove2.me/submissions/72df86c4-d80a-4f5c-abfb-016fc769412e

-- Alternative proof for the theorem from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L507-L548
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_precompact
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_cover
import Mathlib
open Function NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
local notation "Principal(" F ")" => AdeleRing.principalSubgroup (𝓞 F) F
local notation "AQuot(" F ")" => 𝔸[F] ⧸ Principal(F)

theorem solution : CompactSpace (AQuot(F)) := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 F)
  let D := RiemannMasullo.adeleFundamentalDomain F b
  let q := QuotientAddGroup.mk' (Principal(F))
  have hcover := RiemannMasullo.adeleFundamentalDomain_cover F b
  have hc := RiemannMasullo.adeleFundamentalDomain_precompact F b
  have hsur : q '' closure D = Set.univ := by
    apply Set.eq_univ_of_forall
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H a =>
      have ha : a ∈ ⋃ x : F, algebraMap F 𝔸[F] x +ᵥ D := by
        rw [show (⋃ x : F, algebraMap F 𝔸[F] x +ᵥ D) = Set.univ from hcover]
        exact Set.mem_univ a
      obtain ⟨x, y, hy, he⟩ := Set.mem_iUnion.mp ha
      refine ⟨y, subset_closure hy, QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
      refine ⟨-x, ?_⟩
      change algebraMap F 𝔸[F] x + y = a at he
      rw [map_neg, ← he]; abel
  rw [← isCompact_univ_iff, ← hsur]
  exact hc.image QuotientAddGroup.continuous_mk
