-- Prove2me | solution 1 for RiemannMasullo.regulator_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:10:00.712561+00:00
-- url     : https://prove2.me/submissions/fd2178b9-dd55-4ee1-bb1f-70c7f8a53489

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L141-L142
import Mathlib
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]

theorem solution : CompactSpace (logSpace F ⧸ (Units.logEmbedding F).range) := by
  classical
  let L := Units.unitLattice F
  let B := (Units.basisUnitLattice F).ofZLatticeBasis ℝ L
  let q := QuotientAddGroup.mk' (Units.logEmbedding F).range
  have hsp : Submodule.span ℤ (Set.range B) = L := Module.Basis.ofZLatticeBasis_span ..
  have hs : q '' B.parallelepiped = Set.univ := by
    apply Set.eq_univ_of_forall
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B x
      refine ⟨v +ᵥ x, ZSpan.fundamentalDomain_subset_parallelepiped B hv, ?_⟩
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change (v.val + x - x) ∈ (Units.logEmbedding F).range
      rw [add_sub_cancel_right]
      have hvL : v.val ∈ L := by rw [← hsp]; exact v.property
      obtain ⟨u, _, hu⟩ := hvL
      exact ⟨u, hu⟩
  rw [← isCompact_univ_iff, ← hs]
  exact B.parallelepiped.isCompact.image QuotientAddGroup.continuous_mk
