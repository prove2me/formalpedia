-- Prove2me | solution 1 for RiemannMasullo.regulatorParallelotope_interior
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:12:35.235194+00:00
-- url     : https://prove2.me/submissions/5a6e8890-0524-4ec9-9506-d04eeb239e5e

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L200-L201
import Mathlib
import Definitions.Def_RiemannMasullo_RegulatorParallelotope
open RiemannMasullo
set_option maxSynthPendingDepth 8
open scoped Classical
open scoped Pointwise
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

theorem solution : (interior (regulatorParallelotope F b)).Nonempty := by
  classical
  let B := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  let e := B.equivFun.toContinuousLinearEquiv
  let U := e ⁻¹' (Set.univ.pi fun _ ↦ Set.Ioo (0 : ℝ) 1)
  have ho : IsOpen U := (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo).preimage e.continuous
  have hsub : U ⊆ regulatorParallelotope F b := fun x hx i ↦
    ⟨(hx i (Set.mem_univ i)).1.le, (hx i (Set.mem_univ i)).2⟩
  refine ⟨e.symm (fun _ ↦ 1/2), interior_maximal hsub ho ?_⟩
  change e (e.symm _) ∈ Set.univ.pi _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  intro i _
  constructor <;> norm_num
