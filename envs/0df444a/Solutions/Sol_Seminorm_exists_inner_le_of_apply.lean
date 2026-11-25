-- Prove2me | solution 1 for Seminorm.exists_inner_le_of_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:11.004512+00:00
-- url     : https://prove2.me/submissions/5b468aa5-2378-40a2-81d8-71c499dfd241

module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Definitions.Def_BasicResults_JohnIngredients

set_option autoImplicit true
@[expose] public section
public section
open scoped InnerProductSpace ComplexConjugate
open RCLike
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
namespace Seminorm
theorem _root_.solution (q : Seminorm 𝕜 E) (u : E) :
    ∃ v : E, (∀ x, re ⟪x, v⟫_𝕜 ≤ q x) ∧ re ⟪u, v⟫_𝕜 = q u := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, fun x => by simp, by simp⟩
  -- `f : c • u ↦ c * q u` on the span of `u`; at `z = c • u` both sides are `‖c‖ * q u`
  set f : Module.Dual 𝕜 (𝕜 ∙ u) :=
    (q u : 𝕜) • (ContinuousLinearEquiv.coord 𝕜 u hu).toLinearMap with hf
  have hcoord : ∀ z : (𝕜 ∙ u), (ContinuousLinearEquiv.coord 𝕜 u hu z) • u = (z : E) :=
    fun z => LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul 𝕜 E u hu z
  have hdom : ∀ z : (𝕜 ∙ u), ‖f z‖ ≤ q z := by
    intro z
    have hq : q (z : E) = ‖ContinuousLinearEquiv.coord 𝕜 u hu z‖ * q u := by
      rw [← hcoord z, map_smul_eq_mul]
    rw [hf]
    simp only [LinearMap.smul_apply, smul_eq_mul, norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg (apply_nonneg q u), hq]
    exact le_of_eq (mul_comm _ _)
  -- extend to all of `E`, still dominated by `q`
  obtain ⟨g, hg_eq, hg_le⟩ := Module.Dual.exists_extension_of_le_seminorm (𝕜 ∙ u) f hdom
  have hgu : g u = (q u : 𝕜) := by
    rw [hg_eq ⟨u, Submodule.mem_span_singleton_self u⟩, hf]
    simp [RCLike.real_smul_eq_coe_mul]
  -- represent the extension by a vector via Riesz
  set v : E := (InnerProductSpace.toDual 𝕜 E).symm (LinearMap.toContinuousLinearMap g) with hv
  have hre : ∀ x, re ⟪x, v⟫_𝕜 = re (g x) := fun x => by
    rw [← inner_conj_symm x v, RCLike.conj_re, hv, InnerProductSpace.toDual_symm_apply]
    rfl
  exact ⟨v, fun x => (hre x).le.trans ((re_le_norm (g x)).trans (hg_le x)),
    by rw [hre u, hgu, RCLike.ofReal_re]⟩
end Seminorm
