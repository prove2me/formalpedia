-- Prove2me | solution 1 for Projectivization.momentMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:15.590596+00:00
-- url     : https://prove2.me/submissions/88d84d1d-2bf7-4d89-b167-b01d1a9786e6

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MomentMap
public import Theorems.Thm_Projectivization_momentRatio_smul

set_option autoImplicit false
@[expose] public section
public section
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace Projectivization
theorem _root_.solution (ψ : EuclideanSpace ℂ ι) (hψ : ψ ≠ 0) (i : ι) :
    momentMap (mk ℂ ψ hψ) i = ‖ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by
  obtain ⟨a, ha⟩ :=
    (mk_eq_mk_iff ℂ (mk ℂ ψ hψ).rep ψ (rep_nonzero _) hψ).mp (mk_rep _)
  unfold momentMap
  rw [← ha]
  simp only [Units.smul_def]
  exact momentRatio_smul (↑a) (Units.ne_zero a) ψ i
end Projectivization
