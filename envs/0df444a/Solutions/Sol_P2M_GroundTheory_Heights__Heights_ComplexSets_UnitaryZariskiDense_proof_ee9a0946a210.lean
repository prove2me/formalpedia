-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_proof_ee9a0946a210
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:31.337551+00:00
-- url     : https://prove2.me/submissions/84479cd3-190d-4e08-ae68-9ca224033dcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_eval_aeval_subst_b79d4cd87e0f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_polyEval_aeval_subst_33ac81fff056
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_unit_circle_infinite_c0f460037610
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_conj_diagonal_mem_b7c8c32ec557

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix Complex
noncomputable section
open UnitaryZariskiDense
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace UnitaryZariskiDense
theorem _root_.solution : UnitaryZariskiDense.Statement := by
  intro n p hp
  by_contra hall
  push Not at hall
  apply hp

  have herm : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian →
      eval (fun ij : Fin n × Fin n => H ij.1 ij.2) p = 0 := by
    intro H hH
    have hspec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    set V : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hVdef
    have hV : V ∈ unitaryGroup (Fin n) ℂ := hH.eigenvectorUnitary.2
    have hentry : ∀ d : Fin n → ℂ,
        eval d (aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p) =
          eval (fun ij : Fin n × Fin n => (V * diagonal d * star V) ij.1 ij.2) p := by
      intro d
      rw [eval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      rw [Matrix.mul_apply]
      simp only [map_sum, map_mul, eval_C, eval_X, Matrix.mul_diagonal]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hr : aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p = 0 :=
      funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unit_circle_infinite) fun d hd => by
        rw [hentry, map_zero]
        exact hall _ (conj_diagonal_mem hV fun k => hd k trivial)
    have h0 := hentry (RCLike.ofReal ∘ hH.eigenvalues)
    rw [hr, map_zero] at h0
    rw [h0]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    exact congrFun (congrFun hspec ij.1) ij.2

  have all : ∀ A : Matrix (Fin n) (Fin n) ℂ, eval (fun ij : Fin n × Fin n => A ij.1 ij.2) p = 0 := by
    intro A
    set g : Polynomial ℂ := aeval (fun ij : Fin n × Fin n =>
      Polynomial.C (A ij.1 ij.2) * (Polynomial.C (1 / 2) - Polynomial.C (I / 2) * Polynomial.X) +
        Polynomial.C (Aᴴ ij.1 ij.2) * (Polynomial.C (1 / 2) + Polynomial.C (I / 2) * Polynomial.X)) p
      with hgdef
    have hg : ∀ z : ℂ, g.eval z = eval (fun ij : Fin n × Fin n =>
        A ij.1 ij.2 * (1 / 2 - I / 2 * z) + Aᴴ ij.1 ij.2 * (1 / 2 + I / 2 * z)) p := by
      intro z
      rw [hgdef, polyEval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      simp
    have g0 : g = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
      rintro _ ⟨t, rfl⟩
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hg]
      have hstar : star (1 / 2 - I / 2 * (t : ℂ)) = 1 / 2 + I / 2 * (t : ℂ) := by
        apply Complex.ext <;> (simp; try ring)
      have hM : ((1 / 2 - I / 2 * (t : ℂ)) • A + (1 / 2 + I / 2 * (t : ℂ)) • Aᴴ).IsHermitian := by
        unfold IsHermitian
        rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_conjTranspose,
          hstar, ← hstar, star_star, add_comm]
      have h := herm _ hM
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
      rw [← h]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      ring
    have h := hg I
    rw [g0, Polynomial.eval_zero] at h
    rw [h]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    have h1 : (1 / 2 - I / 2 * I : ℂ) = 1 := by
      ring_nf
      rw [I_sq]
      norm_num
    have h2 : (1 / 2 + I / 2 * I : ℂ) = 0 := by
      ring_nf
      rw [I_sq]
      norm_num
    rw [h1, h2]
    ring

  exact MvPolynomial.funext fun x => by
    simpa using all (Matrix.of fun i j => x (i, j))
end UnitaryZariskiDense
end GroundTheory.Heights₂.Heights.ComplexSets
