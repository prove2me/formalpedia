-- Prove2me | solution 1 for TroppMatrixConcentration.trace_cgf_subadditivity
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:22:02.212989+00:00
-- url     : https://prove2.me/submissions/057c3d89-13ca-4f9d-8f7a-52512a41d2ce

import Definitions.Def_TroppMatrixConcentration_probability
import Theorems.Thm_TroppMatrixConcentration_ch3_cgf_independent_replacement
import Theorems.Thm_TroppMatrixConcentration_ch3_master_sum_exponential_integrable
import Theorems.Thm_TroppMatrixConcentration_ch3_lieb_regularity_shift_integrable

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
open TroppMatrixConcentration
set_option autoImplicit false

private lemma finite_tensorization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (X k ω)) μ)
    (s : Finset (Fin N)) (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    (∫ ω, traceExp (H + ∑ k ∈ s, X k ω) ∂μ) ≤
      traceExp (H + ∑ k ∈ s, matrixLog (∫ ω, matrixExp (X k ω) ∂μ)) := by
  classical
  have hm (s : Finset (Fin N)) : Measurable (fun ω => ∑ k ∈ s, X k ω) :=
    Finset.measurable_sum _ (fun k _ => hMeas k)
  have hh (s : Finset (Fin N)) : ∀ᵐ ω ∂μ, (∑ k ∈ s, X k ω).IsHermitian := by
    filter_upwards [ae_all_iff.2 hHerm] with ω hω
    exact isSelfAdjoint_sum _ (fun k _ => hω k)
  have he (s : Finset (Fin N)) : Integrable (fun ω => matrixExp (∑ k ∈ s, X k ω)) μ := by
    let Z : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ := fun k ω => if k ∈ s then X k ω else 0
    have hZm (k : Fin N) : Measurable (Z k) := by
      dsimp [Z]
      split_ifs
      · exact hMeas k
      · exact measurable_const
    have hZh (k : Fin N) : ∀ᵐ ω ∂μ, (Z k ω).IsHermitian := by
      dsimp [Z]
      split_ifs
      · exact hHerm k
      · exact Filter.Eventually.of_forall (fun _ => Matrix.isHermitian_zero)
    have hZe (k : Fin N) : Integrable (fun ω => matrixExp ((1 : ℝ) • Z k ω)) μ := by
      dsimp [Z]
      split_ifs
      · simpa using hExp k
      · simpa using integrable_const (matrixExp (0 : Matrix (Fin d) (Fin d) ℂ))
    have hZi : iIndepFun Z μ := by
      exact hIndep.comp (fun k A => if k ∈ s then A else 0) (fun k => by
        split_ifs <;> fun_prop)
    have h := ch3_master_sum_exponential_integrable μ Z 1 hZm hZh hZi hZe
    simpa [Z] using h
  have hshift (s : Finset (Fin N)) (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian) :
      Integrable (fun ω => traceExp (B + ∑ k ∈ s, X k ω)) μ :=
    (ch3_lieb_regularity_shift_integrable μ B hB _ (hm s) (hh s) (he s)).2
  induction s using Finset.induction_on generalizing H with
  | empty => simp
  | @insert a s ha ih =>
    let L := matrixLog (∫ ω, matrixExp (X a ω) ∂μ)
    have hL : L.IsHermitian := cfc_predicate Real.log _
    have hrm : Measurable (fun ω => H + ∑ k ∈ s, X k ω) := measurable_const.add (hm s)
    have hrh : ∀ᵐ ω ∂μ, (H + ∑ k ∈ s, X k ω).IsHermitian := by
      filter_upwards [hh s] with ω hω
      exact hH.add hω
    have hri : IndepFun (fun ω => H + ∑ k ∈ s, X k ω) (X a) μ := by
      have hi := hIndep.indepFun_finsetSum_of_notMem hMeas ha
      simpa only [Function.comp_def, Finset.sum_apply, id_eq] using
        hi.comp (φ := fun A => H + A) (ψ := id) (by fun_prop) measurable_id
    have htotal : Integrable (fun ω => traceExp ((H + ∑ k ∈ s, X k ω) + X a ω)) μ := by
      simpa only [Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using hshift (insert a s) H hH
    have hreplaced : Integrable (fun ω => traceExp ((H + ∑ k ∈ s, X k ω) + L)) μ := by
      simpa only [add_assoc, add_left_comm, add_comm] using hshift s (H + L) (hH.add hL)
    have step := ch3_cgf_independent_replacement μ (fun ω => H + ∑ k ∈ s, X k ω)
      (X a) hrm (hMeas a) hrh (hHerm a) hri (hExp a) htotal hreplaced
    have finish := ih (H + L) (hH.add hL)
    have step' : (∫ ω, traceExp (H + ∑ k ∈ insert a s, X k ω) ∂μ) ≤
        ∫ ω, traceExp (H + L + ∑ k ∈ s, X k ω) ∂μ := by
      simpa only [L, Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using step
    simpa only [L, Finset.sum_insert ha, add_assoc] using step'.trans finish

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (θ : ℝ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hIndep : iIndepFun X μ)
    (hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ) :
    (∫ ω, traceExp (∑ k, θ • X k ω) ∂μ) ≤
      traceExp (cumulantSum μ X θ) := by
  let Z := fun k ω => θ • X k ω
  have hZm (k : Fin N) : Measurable (Z k) := by
    dsimp [Z]
    exact (hMeas k).const_smul θ
  have hZh (k : Fin N) : ∀ᵐ ω ∂μ, (Z k ω).IsHermitian := by
    filter_upwards [hHerm k] with ω hω
    exact hω.smul (isSelfAdjoint_iff.mpr rfl)
  have hZi : iIndepFun Z μ := hIndep.comp (fun _ A => θ • A) (fun _ => by fun_prop)
  have h := finite_tensorization μ Z hZm hZh hZi hExp Finset.univ 0 Matrix.isHermitian_zero
  simpa only [zero_add, cumulantSum] using h
