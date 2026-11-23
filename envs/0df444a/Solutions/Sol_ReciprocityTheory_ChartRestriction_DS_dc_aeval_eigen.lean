-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_aeval_eigen
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:15:27.699798+00:00
-- url     : https://prove2.me/submissions/8af32150-b426-46e9-a3ae-e2af25eb89df

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
theorem AuxDE_pow {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {T : Module.End ℂ Y} {z : ℂ} {f : Y}
    (hf : T f = z • f) : ∀ k : ℕ, (T ^ k) f = z ^ k • f := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hf, smul_smul, ← pow_succ]


theorem ReciprocityTheory.ChartRestriction.DS.dc_aeval_eigen {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (p : ℂ[X]) :
    aeval T p f = p.eval z • f := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, Module.End.mul_apply, AuxDE_pow hf, Module.algebraMap_end_apply,
      eval_monomial, smul_smul]


end

theorem solution {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {T : Module.End ℂ Y} {z : ℂ} {f : Y}
    (hf : T f = z • f) (p : Polynomial ℂ) :
    Polynomial.aeval T p f = p.eval z • f := ReciprocityTheory.ChartRestriction.DS.dc_aeval_eigen hf p
