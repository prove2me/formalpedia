-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.CP.scalar_avoid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:51.863005+00:00
-- url     : https://prove2.me/submissions/e4c94578-a88d-4c8e-a599-f911f064bd6e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.CP
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.SiegelWeilFormula.Krd.CP
theorem _root_.solution {J h : Matrix ι ι ℂ} (hh : hᴴ * J * h = J) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) (hhV : h ∈ V) :
    ∃ μ : ℂ, star μ * μ = 1 ∧ μ • h ∈ V ∧ IsUnit (1 + μ • h).det := by
  obtain ⟨q, hqd⟩ : ∃ q : Polynomial ℂ, q = (1 + (Polynomial.X : Polynomial ℂ) • h.map Polynomial.C).det := ⟨_, rfl⟩
  have hq : ∀ μ : ℂ, q.eval μ = (1 + μ • h).det := by
    intro μ
    rw [hqd, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
  have hq0 : q ≠ 0 := fun h0 => by
    have := hq 0
    rw [h0, Polynomial.eval_zero, zero_smul, add_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hg : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) • h :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).smul continuous_const
  have hO : IsOpen ((fun θ : ℝ => Complex.exp (θ * Complex.I) • h) ⁻¹' V) := hV.preimage hg
  have h0O : (0 : ℝ) ∈ (fun θ : ℝ => Complex.exp (θ * Complex.I) • h) ⁻¹' V := by
    simp only [Set.mem_preimage, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    exact hhV
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO 0 h0O
  have hδ' : (0 : ℝ) < min δ 1 := lt_min hδ one_pos
  have hSinf : (Set.Ioo (0 : ℝ) (min δ 1)).Infinite := Set.Ioo_infinite hδ'
  have hinj : Set.InjOn (fun θ : ℝ => Complex.exp (θ * Complex.I)) (Set.Ioo (0 : ℝ) (min δ 1)) := by
    intro a ha b hb hab
    have hpi : (1 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
    have hIoc : ∀ t ∈ Set.Ioo (0 : ℝ) (min δ 1), t ∈ Set.Ioc (-Real.pi) Real.pi := fun t ht =>
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, min_le_right δ 1]⟩
    have e := congrArg Complex.arg hab
    simp only [Complex.exp_mul_I] at e
    rwa [Complex.arg_cos_add_sin_mul_I (hIoc a ha), Complex.arg_cos_add_sin_mul_I (hIoc b hb)] at e
  obtain ⟨μ, ⟨θ, hθ, rfl⟩, hμ⟩ := (hSinf.image hinj).exists_notMem_finset q.roots.toFinset
  refine ⟨Complex.exp (θ * Complex.I), ?_, ?_, ?_⟩
  · rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show (θ : ℂ) * -Complex.I + θ * Complex.I = 0 by ring, Complex.exp_zero]
  · refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ.1]
    exact lt_of_lt_of_le hθ.2 (min_le_left δ 1)
  · rw [isUnit_iff_ne_zero, ← hq]
    intro h0
    exact hμ (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hq0).2 h0))
end PositivityTheory.SiegelWeilFormula.Krd.CP
