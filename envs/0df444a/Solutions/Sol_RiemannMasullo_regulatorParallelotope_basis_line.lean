-- Prove2me | solution 1 for RiemannMasullo.regulatorParallelotope_basis_line
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:12:33.684149+00:00
-- url     : https://prove2.me/submissions/b218c0af-87b0-4b9f-8fff-6da3b46d1a08

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L186-L188
import Mathlib
import Definitions.Def_RiemannMasullo_RegulatorParallelotope
open RiemannMasullo
set_option maxSynthPendingDepth 8
open scoped Classical
open scoped Pointwise
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

theorem solution (i : Fin (Units.rank F)) (t : ℝ) :
    t • Units.logEmbeddingQuot F (b i) ∈ regulatorParallelotope F b ↔ t ∈ Set.Ico 0 1 := by
  classical
  let B := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  have hi : B i = Units.logEmbeddingQuot F (b i) := by
    rw [show B i = ((b.map (Units.logEmbeddingEquiv F)) i : logSpace F) from
      Module.Basis.ofZLatticeBasis_apply ..]
    rfl
  change t • Units.logEmbeddingQuot F (b i) ∈ ZSpan.fundamentalDomain B ↔ _
  rw [← hi, ZSpan.mem_fundamentalDomain]
  constructor
  · intro h; simpa using h i
  · intro ht k
    by_cases h : i = k
    · subst k; simpa using ht
    · simp [Module.Basis.repr_self, Finsupp.single_apply, h, Ne.symm h]
