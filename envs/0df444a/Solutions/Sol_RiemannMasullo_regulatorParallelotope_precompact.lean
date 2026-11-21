-- Prove2me | solution 1 for RiemannMasullo.regulatorParallelotope_precompact
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:12:34.58725+00:00
-- url     : https://prove2.me/submissions/089df1b7-cc46-4b35-9562-23010f52db4b

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L196-L197
import Mathlib
import Definitions.Def_RiemannMasullo_RegulatorParallelotope
open RiemannMasullo
set_option maxSynthPendingDepth 8
open scoped Classical
open scoped Pointwise
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

theorem solution : IsCompact (closure (regulatorParallelotope F b)) := by
  classical
  let B := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure,
    (ZSpan.fundamentalDomain_isBounded B).closure⟩
