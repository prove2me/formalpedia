-- Prove2me | solution 1 for RiemannMasullo.regulatorParallelotope_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:14:29.417186+00:00
-- url     : https://prove2.me/submissions/7c85b2f1-5244-4a0b-8561-0ef8c1b927ff

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L209-L211
import Mathlib
import Definitions.Def_RiemannMasullo_RegulatorParallelotope
open RiemannMasullo
set_option maxSynthPendingDepth 8
open scoped Classical
open scoped Pointwise
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

theorem solution (x : (Units.logEmbedding F).range) (hx : x ≠ 0) :
    Disjoint (x.val +ᵥ regulatorParallelotope F b) (regulatorParallelotope F b) := by
  classical
  let B := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  have hs : Submodule.span ℤ (Set.range B) = Units.unitLattice F := Module.Basis.ofZLatticeBasis_span ..
  obtain ⟨u, hu⟩ := x.property
  have hv : x.val ∈ Submodule.span ℤ (Set.range B) := by
    rw [hs]; exact ⟨u, trivial, hu⟩
  let v : Submodule.span ℤ (Set.range B) := ⟨x.val, hv⟩
  apply Set.disjoint_left.mpr
  rintro _ ⟨y, hy, rfl⟩ ht
  have h0 : (0 : Submodule.span ℤ (Set.range B)) +ᵥ y ∈ ZSpan.fundamentalDomain B := by
    simpa only [zero_vadd] using (show y ∈ ZSpan.fundamentalDomain B from hy)
  have h₁ : v +ᵥ y ∈ ZSpan.fundamentalDomain B := ht
  have h := (ZSpan.exist_unique_vadd_mem_fundamentalDomain B y).unique h₁ h0
  have hval := congrArg (fun z : Submodule.span ℤ (Set.range B) ↦ z.val) h
  exact hx (Subtype.ext hval)
