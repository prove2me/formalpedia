-- Prove2me | solution 1 for RiemannMasullo.regulatorParallelotope_cover
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:12:35.986591+00:00
-- url     : https://prove2.me/submissions/204b0c2e-bad3-401d-a47a-6d2fd2ea8203

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L204-L206
import Mathlib
import Definitions.Def_RiemannMasullo_RegulatorParallelotope
open RiemannMasullo
set_option maxSynthPendingDepth 8
open scoped Classical
open scoped Pointwise
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

theorem solution :
    (⋃ x : (Units.logEmbedding F).range, x.val +ᵥ regulatorParallelotope F b) = Set.univ := by
  classical
  let B := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  have hs : Submodule.span ℤ (Set.range B) = Units.unitLattice F := Module.Basis.ofZLatticeBasis_span ..
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B y
  have hL : v.val ∈ Units.unitLattice F := by rw [← hs]; exact v.property
  obtain ⟨u, _, hu⟩ := hL
  have hmem : v.val ∈ (Units.logEmbedding F).range := ⟨u, hu⟩
  refine Set.mem_iUnion.mpr ⟨-⟨v.val, hmem⟩, v +ᵥ y, hv, ?_⟩
  change -v.val + (v.val + y) = y
  abel
