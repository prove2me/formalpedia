-- Prove2me | solution 1 for SpectralRepresentation.cfcHom_comm_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:47.14365+00:00
-- url     : https://prove2.me/submissions/c1cb2e0a-f2d7-4684-99f4-65cb3cdab20c

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Definitions.Def_BasicResults_Spectral_Projection
public import Theorems.Thm_SpectralRepresentation_stepDown_continuous
attribute [local fun_prop] SpectralRepresentation.stepDown_continuous

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
open SpectralRepresentation
open Filter Topology
open scoped InnerProductSpace
variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
namespace SpectralRepresentation
theorem _root_.solution {P : H₁ →L[ℂ] H₁} (hP : IsSelfAdjoint P)
    (J : H₁ →L[ℝ] H₁) (hJP : ∀ x, J (P x) = P (J x)) (f : C(spectrum ℝ P, ℝ)) :
    ∀ x, J (cfcHom hP f x) = cfcHom hP f (J x) := by
  open scoped ContinuousFunctionalCalculus in
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
      intro x
      rw [show (ContinuousMap.const (spectrum ℝ P) r) = algebraMap ℝ C(spectrum ℝ P, ℝ) r from rfl,
        AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]
      simp only [smul_apply, one_apply_eq_self, map_smul]
  | id => intro x; rw [cfcHom_id hP]; exact hJP x
  | star_id => intro x; rw [map_star, cfcHom_id hP, hP.star_eq]; exact hJP x
  | add f g hf hg =>
      intro x
      rw [map_add, add_apply, add_apply, map_add, hf x, hg x]
  | mul f g hf hg =>
      intro x
      rw [map_mul, mul_apply_eq_comp, mul_apply_eq_comp,
        hf (cfcHom hP g x), hg x]
  | frequently f hf =>
      have hSclosed : IsClosed {g : C(spectrum ℝ P, ℝ) |
          ∀ x, J (cfcHom hP g x) = cfcHom hP g (J x)} := by
        rw [Set.ofPred_forall]
        exact isClosed_iInter fun x => isClosed_eq
          (J.continuous.comp ((cfcHom_continuous hP).clm_apply continuous_const))
          ((cfcHom_continuous hP).clm_apply continuous_const)
      have hmem : f ∈ closure {g : C(spectrum ℝ P, ℝ) |
          ∀ x, J (cfcHom hP g x) = cfcHom hP g (J x)} := mem_closure_iff_frequently.mpr hf
      rwa [hSclosed.closure_eq] at hmem
end SpectralRepresentation
