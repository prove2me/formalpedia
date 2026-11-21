-- Prove2me | solution 1 for RiemannMasullo.regulator_coordinates_unique
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:16:16.810444+00:00
-- url     : https://prove2.me/submissions/c760b59f-aa39-4173-942a-0b604c7f5d24

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L174-L177
import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

open NumberField.Units.dirichletUnitTheorem
set_option maxSynthPendingDepth 8
variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

theorem solution (g : N∞) :
    ∃! t : Fin (Units.rank F) → ℝ, ∀ w : {w : InfinitePlace F // w ≠ w₀},
      infiniteIdeleLog F g.val w.val = ∑ i, t i * Units.logEmbeddingQuot F (b i) w := by
  classical
  let B := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  let y : logSpace F := fun w ↦ infiniteIdeleLog F g.val w.val
  have hi (i) : B i = Units.logEmbeddingQuot F (b i) := by
    rw [show B i = ((b.map (Units.logEmbeddingEquiv F)) i : logSpace F) from
      Module.Basis.ofZLatticeBasis_apply ..]
    rfl
  have hex (t : Fin (Units.rank F) → ℝ) (w : {w : InfinitePlace F // w ≠ w₀}) :
      (B.equivFun.symm t) w = ∑ i, t i * Units.logEmbeddingQuot F (b i) w := by
    simp only [Module.Basis.equivFun_symm_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, hi]
  refine ⟨B.equivFun y, ?_, ?_⟩
  · intro w
    simpa only [LinearEquiv.symm_apply_apply] using hex (B.equivFun y) w
  · intro t ht
    apply B.equivFun.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    funext w
    exact (hex t w).trans (ht w).symm
