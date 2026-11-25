-- Prove2me | solution 1 for SNumbers.Lifting.kolmogorovNumber_le_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:12:33.266693+00:00
-- url     : https://prove2.me/submissions/921f57cc-d45b-4487-aeb8-7eb5f23e5596

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_norm_le_norm_comp_Q
public import Theorems.Thm_SNumbers_Lifting_liftA_apply
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_approximationSet_nonempty
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_deviation
public import Theorems.Thm_Submodule_liftQL_mkQL
public import Theorems.Thm_Submodule_norm_mkQL_le
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.Lifting.liftA_apply

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
omit [CompleteSpace 𝕜]
namespace SNumbers.Lifting
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    SNumbers.kolmogorovNumber S n
      ≤ approximationNumber (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) n := by
  refine le_csInf (approximationSet_nonempty _ _) ?_
  rintro _ ⟨L, hL, rfl⟩
  -- `V := range L` has rank ≤ n and is admissible for `dₙ`.
  set V : Submodule 𝕜 Y := LinearMap.range (L : BallLp 𝕜 X →ₗ[𝕜] Y) with hV
  have hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal) := hL
  refine (SNumbers.kolmogorovNumber_le_deviation hV_rank).trans ?_
  show ‖V.mkQL.comp S‖ ≤ ‖S.comp (Q : BallLp 𝕜 X →L[𝕜] X) - L‖
  -- `π_V ∘ L = 0` since `range L = V`.
  have hL0 : V.mkQL.comp L = 0 := by
    ext α
    simp only [coe_comp, Function.comp_apply, zero_apply,
      Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self (L : BallLp 𝕜 X →ₗ[𝕜] Y) α
  calc ‖V.mkQL.comp S‖
      ≤ ‖(V.mkQL.comp S).comp (Q : BallLp 𝕜 X →L[𝕜] X)‖ := norm_le_norm_comp_Q _
    _ = ‖V.mkQL.comp (S.comp (Q : BallLp 𝕜 X →L[𝕜] X) - L)‖ := by
        rw [ContinuousLinearMap.comp_sub, hL0, sub_zero, ContinuousLinearMap.comp_assoc]
    _ ≤ ‖V.mkQL‖ * ‖S.comp (Q : BallLp 𝕜 X →L[𝕜] X) - L‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖S.comp (Q : BallLp 𝕜 X →L[𝕜] X) - L‖ := by
        gcongr; exact V.norm_mkQL_le
    _ = ‖S.comp (Q : BallLp 𝕜 X →L[𝕜] X) - L‖ := one_mul _
end SNumbers.Lifting
