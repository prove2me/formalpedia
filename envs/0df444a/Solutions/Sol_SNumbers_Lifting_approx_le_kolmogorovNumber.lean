-- Prove2me | solution 1 for SNumbers.Lifting.approx_le_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:12:35.325331+00:00
-- url     : https://prove2.me/submissions/c11167cd-b980-4713-8486-25bbbdea9124

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_liftA_apply
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_deviationFromSubspace_nonneg
public import Theorems.Thm_Submodule_liftQL_mkQL
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
namespace SNumbers.Lifting
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) n
      ≤ SNumbers.kolmogorovNumber S n := by
  unfold SNumbers.kolmogorovNumber
  refine le_csInf ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩ ?_
  rintro _ ⟨V, hV, rfl⟩
  set d : ℝ := deviationFromSubspace S V with hd_def
  have hd_nn : 0 ≤ d := deviationFromSubspace_nonneg S V
  -- `V` is finite-dimensional (rank `≤ n < ℵ₀`), hence complete.
  have hVfin : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hV (Cardinal.natCast_lt_aleph0))
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Choose, for each `x ∈ B_X`, a point `w x ∈ V` with `‖S x − w x‖ < d + ε`.
  have hchoice : ∀ x : Ball X, ∃ w : V, ‖S (x : X) - (w : Y)‖ < d + ε := by
    intro x
    have hmk_le : ‖(V.mkQL (S (x : X)))‖ ≤ d := by
      calc ‖V.mkQL (S (x : X))‖
          = ‖(V.mkQL.comp S) (x : X)‖ := rfl
        _ ≤ ‖V.mkQL.comp S‖ * ‖(x : X)‖ := le_opNorm _ _
        _ ≤ ‖V.mkQL.comp S‖ * 1 := by gcongr; exact x.2
        _ = d := by rw [hd_def]; exact mul_one _
    obtain ⟨y', hy'_mk, hy'_lt⟩ :=
      Submodule.Quotient.norm_mk_lt (V.mkQL (S (x : X))) hε
    refine ⟨⟨S (x : X) - y', ?_⟩, ?_⟩
    · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hy'_mk,
        Submodule.mkQL_apply, Submodule.mkQ_apply, sub_self]
    · rw [sub_sub_cancel]
      exact hy'_lt.trans_le (by linarith [hmk_le])
  choose w hw using hchoice
  -- Uniform bound `‖w x‖ ≤ C` on the chosen points.
  set C : ℝ := ‖S‖ + (d + ε) with hC_def
  have hwC : ∀ x : Ball X, ‖(w x : Y)‖ ≤ C := fun x => by
    have hSx : ‖S (x : X)‖ ≤ ‖S‖ :=
      (S.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg S) x.2)
    calc ‖(w x : Y)‖
        = ‖S (x : X) - (S (x : X) - (w x : Y))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖S (x : X)‖ + ‖S (x : X) - (w x : Y)‖ := norm_sub_le _ _
      _ ≤ ‖S‖ + (d + ε) := by gcongr; exact (hw x).le
      _ = C := hC_def.symm
  -- Summability of `x ↦ ‖α x • w x‖` (hence of `x ↦ α x • w x`, using `V` complete).
  have hsumnorm : ∀ α : BallLp 𝕜 X, Summable (fun x : Ball X => ‖α x • w x‖) := fun α =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hwC x) (norm_nonneg _))
      ((summable_norm_α α).mul_right C)
  have hsum : ∀ α : BallLp 𝕜 X, Summable (fun x : Ball X => α x • w x) := fun α =>
    (hsumnorm α).of_norm
  -- The approximant `L' : ℓ¹(B_X) →L[𝕜] V`, then `L := ι_V ∘ L'`.
  let L' : BallLp 𝕜 X →L[𝕜] V := LinearMap.mkContinuous
    { toFun := fun α => ∑' x : Ball X, α x • w x
      map_add' := fun α β => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (hsum α).tsum_add (hsum β)
      map_smul' := fun k α => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul]
        exact (hsum α).tsum_const_smul k }
    C (fun α => by
      refine (norm_tsum_le_tsum_norm (hsumnorm α)).trans ?_
      refine (Summable.tsum_le_tsum (fun x => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hwC x) (norm_nonneg _))
        (hsumnorm α) ((summable_norm_α α).mul_right C)).trans_eq ?_
      rw [tsum_mul_right]
      have hp1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
      rw [lp.norm_eq_tsum_rpow hp1 α, show (1 : ℝ≥0∞).toReal = 1 from by norm_num]
      simp [Real.rpow_one, mul_comm])
  set L : BallLp 𝕜 X →L[𝕜] Y := V.subtypeL.comp L' with hL_def
  have hL'_apply : ∀ α, L' α = ∑' x : Ball X, α x • w x := fun α => rfl
  -- `range L ⊆ V`, so `rank L ≤ rank V ≤ n`.
  have hrank : L.rank ≤ (n : Cardinal) := by
    refine le_trans (Submodule.rank_mono ?_) hV
    rintro y ⟨α, rfl⟩
    exact (L' α).2
  -- The residual `S∘Q − L` is bounded by `d + ε`.
  have hres : ‖S.comp (Q : BallLp 𝕜 X →L[𝕜] X) - L‖ ≤ d + ε := by
    refine opNorm_le_bound _ (by positivity) fun α => ?_
    have hSsum : Summable (fun x : Ball X => α x • S (x : X)) :=
      ((summable_smul_val α).mapL S).congr (fun x => map_smul S (α x) _)
    have hLsum : Summable (fun x : Ball X => α x • (w x : Y)) :=
      ((hsum α).mapL V.subtypeL).congr (fun x => by rw [map_smul]; rfl)
    have hnormsum : Summable (fun x : Ball X => ‖α x • (S (x : X) - (w x : Y))‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hw x).le (norm_nonneg _))
        ((summable_norm_α α).mul_right (d + ε))
    have hval : (S.comp (Q : BallLp 𝕜 X →L[𝕜] X) - L) α
        = ∑' x : Ball X, α x • (S (x : X) - (w x : Y)) := by
      rw [sub_apply]
      have e1 : (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) α = ∑' x, α x • S (x : X) := by
        rw [coe_comp, Function.comp_apply, Q_apply, S.map_tsum (summable_smul_val α)]
        simp_rw [map_smul]
      have e2 : L α = ∑' x, α x • (w x : Y) := by
        rw [hL_def, coe_comp, Function.comp_apply, hL'_apply,
            V.subtypeL.map_tsum (hsum α)]
        simp_rw [map_smul]
        rfl
      rw [e1, e2, ← Summable.tsum_sub hSsum hLsum]
      simp_rw [← smul_sub]
    rw [hval]
    calc ‖∑' x : Ball X, α x • (S (x : X) - (w x : Y))‖
        ≤ ∑' x : Ball X, ‖α x • (S (x : X) - (w x : Y))‖ :=
          norm_tsum_le_tsum_norm hnormsum
      _ ≤ ∑' x : Ball X, ‖α x‖ * (d + ε) := by
          refine Summable.tsum_le_tsum (fun x => ?_) hnormsum
            ((summable_norm_α α).mul_right (d + ε))
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hw x).le (norm_nonneg _)
      _ = (d + ε) * ‖α‖ := by
          rw [tsum_mul_right]
          have hp1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
          rw [lp.norm_eq_tsum_rpow hp1 α, show (1 : ℝ≥0∞).toReal = 1 from by norm_num]
          simp [Real.rpow_one, mul_comm]
  calc approximationNumber (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) n
      ≤ ‖S.comp (Q : BallLp 𝕜 X →L[𝕜] X) - L‖ := approximationNumber_le_norm_sub hrank
    _ ≤ d + ε := hres
end SNumbers.Lifting
