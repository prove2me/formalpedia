-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:35:09.293318+00:00
-- url     : https://prove2.me/submissions/df75374a-3f62-4585-9300-f940c7405a62

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)


theorem g53a_trace_kraus {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (N : Superop I J) (hN : IsChannel N) (X : Matrix I I ℂ) : (N X).trace = X.trace := by
  obtain ⟨m, E, hE, hNE⟩ := hN
  rw [hNE, krausApply, Matrix.trace_sum]
  have : ∀ k, (E k * X * (E k)ᴴ).trace = ((E k)ᴴ * E k * X).trace := fun k => by
    rw [Matrix.trace_mul_cycle]
  simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show (∑ k, (E k)ᴴ * E k) = 1 from hE, one_mul]

theorem g53a_trace_choi {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (N : Superop I J) (hN : IsChannel N) : (choi N).trace = (Fintype.card I : ℂ) := by
  have h1 : (choi N).trace = ∑ i : I, (N (Matrix.single i i 1)).trace := by
    simp only [Matrix.trace, Matrix.diag, choi, Fintype.sum_prod_type]
  rw [h1]
  simp_rw [g53a_trace_kraus N hN]
  simp [Matrix.trace, Matrix.diag, Matrix.single_apply]

theorem g53a_re_trace_nonneg {I : Type} [Fintype I] {X : Matrix I I ℂ} (h : X.PosSemidef) :
    0 ≤ X.trace.re := by
  have := h.trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

theorem g53a_entry_le_specNorm {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) (i : I) :
    ‖M i i‖ ≤ specNorm M := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single i (1 : ℂ))
  have h2 : ‖M i i‖ ≤ ‖(WithLp.toLp 2 (M *ᵥ (WithLp.ofLp (EuclideanSpace.single i (1 : ℂ)))) :
      EuclideanSpace ℂ I)‖ := by
    have := PiLp.norm_apply_le (p := 2) (WithLp.toLp 2 (M *ᵥ (WithLp.ofLp (EuclideanSpace.single i (1 : ℂ)))) :
      EuclideanSpace ℂ I) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have h3 : ‖(EuclideanSpace.single i (1 : ℂ))‖ = 1 := by simp
  rw [h3, mul_one] at h
  exact le_trans h2 h

theorem g53a_re_trace_le {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) :
    M.trace.re ≤ (Fintype.card I : ℝ) * specNorm M := by
  rw [Matrix.trace, Complex.re_sum]
  calc ∑ i, (M.diag i).re ≤ ∑ _i : I, specNorm M := by
        apply Finset.sum_le_sum; intro i _
        exact le_trans (Complex.re_le_norm _) (g53a_entry_le_specNorm M i)
    _ = _ := by simp

theorem g53a_one_le_beta {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B]
    (N : Superop (A × B) (C × D)) (hN : IsChannel N) : (1 : EReal) ≤ bipartiteBeta N := by
  apply le_sInf
  rintro r ⟨S, V, hF, rfl⟩
  obtain ⟨_, _, _, hVm, _, hSm, _⟩ := hF
  have e1 := g53a_re_trace_nonneg hSm
  have e2 := g53a_re_trace_nonneg hVm
  have htb : ∀ X : Op ((A × B) × (C × D)), (transposeBobChoi X).trace = X.trace := fun X => rfl
  rw [htb, Matrix.trace_sub, Complex.sub_re, g53a_trace_choi N hN] at e2
  rw [Matrix.trace_sub, Complex.sub_re] at e1
  have e3 : (traceOutput S).trace = S.trace := by
    simp only [Matrix.trace, Matrix.diag, traceOutput, Fintype.sum_prod_type]
  have e4 := g53a_re_trace_le (traceOutput S)
  rw [e3] at e4
  simp only [Complex.natCast_re] at e2
  have hpos : (0 : ℝ) < (Fintype.card (A × B) : ℝ) := by exact_mod_cast Fintype.card_pos
  have : (1 : ℝ) ≤ specNorm (traceOutput S) := by
    by_contra hc
    push Not at hc
    nlinarith
  exact_mod_cast this

end QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P09
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)
open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)
open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)
open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Proposition 2 (Non-negativity), arXiv:2010.01058v3, PDF pp.5.
 -/
theorem solution {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (N : Superop (A × B) (C × D)) (hN : IsChannel N) :
    0 ≤ cBeta N := by
  have h1 := g53a_one_le_beta N hN
  unfold cBeta logExt
  split_ifs with ht hle
  · exact le_top
  · exact absurd (le_trans h1 hle) (by norm_num)
  · have hb : bipartiteBeta N ≠ ⊥ := fun h => by rw [h] at h1; exact absurd h1 (not_le.mpr (lt_of_lt_of_le EReal.bot_lt_zero zero_le_one))
    have hr : (1 : ℝ) ≤ (bipartiteBeta N).toReal := by
      have := EReal.coe_toReal ht hb
      rw [← this] at h1
      exact_mod_cast h1
    exact_mod_cast Real.logb_nonneg (by norm_num) hr


end

