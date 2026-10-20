-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_classicalFeedback
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:37:56.693804+00:00
-- url     : https://prove2.me/submissions/1a6eef54-e4ec-491d-a252-1fc82fee1dcb

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
    (N : Superop (A × B) (C × D)) (htr : (choi N).trace = (Fintype.card (A × B) : ℂ)) :
    (1 : EReal) ≤ bipartiteBeta N := by
  apply le_sInf
  rintro r ⟨S, V, hF, rfl⟩
  obtain ⟨_, _, _, hVm, _, hSm, _⟩ := hF
  have e1 := g53a_re_trace_nonneg hSm
  have e2 := g53a_re_trace_nonneg hVm
  have htb : ∀ X : Op ((A × B) × (C × D)), (transposeBobChoi X).trace = X.trace := fun X => rfl
  rw [htb, Matrix.trace_sub, Complex.sub_re, htr] at e2
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


def g53a_fbJ (d : ℕ) : Op ((Fin 1 × Fin d) × (Fin d × Fin 1)) :=
  Matrix.diagonal (fun p : (Fin 1 × Fin d) × (Fin d × Fin 1) =>
      if p.1.2 = p.2.1 then (1 : ℂ) else 0)

theorem g53a_fb_choi (d : ℕ) (inst : DecidableEq (Fin 1 × Fin d)) :
    @choi _ _ inst (feedbackMap d) = g53a_fbJ d := by
  ext p q
  obtain ⟨⟨p1, p2⟩, ⟨p3, p4⟩⟩ := p
  obtain ⟨⟨q1, q2⟩, ⟨q3, q4⟩⟩ := q
  have e1 : p1 = q1 := Subsingleton.elim _ _
  have e4 : p4 = q4 := Subsingleton.elim _ _
  have e1' : p1 = 0 := Subsingleton.elim _ _
  subst e1 e4 e1'
  simp only [g53a_fbJ, choi, feedbackMap, Matrix.single_apply, Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases h3 : p3 = q3
  · subst h3; by_cases h2 : p2 = q2
    · subst h2; simp
    · simp [h2]
      intro h h'; exact h2 (h.trans h'.symm)
  · simp [h3]

theorem g53a_fb_trace (d : ℕ) : (g53a_fbJ d).trace = (d : ℂ) := by
  simp only [g53a_fbJ, Matrix.trace_diagonal, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp [Finset.sum_ite_eq]

theorem g53a_fb_beta_le {d : ℕ} (hd : 0 < d) : bipartiteBeta (feedbackMap d) ≤ 1 := by
  let J := g53a_fbJ d
  have hdiag : ∀ c : ℂ, 0 ≤ c.re → c.im = 0 → (c • J).PosSemidef := by
    intro c hc hci
    show (c • g53a_fbJ d).PosSemidef
    rw [g53a_fbJ, ← Matrix.diagonal_smul]
    apply Matrix.PosSemidef.diagonal
    intro p
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; show (0:ℂ) ≤ c; rw [Complex.nonneg_iff]; exact ⟨hc, hci.symm⟩
    · simp
  have htb : transposeBobChoi J = J := by
    show transposeBobChoi (g53a_fbJ d) = g53a_fbJ d
    ext p q
    obtain ⟨⟨p1, p2⟩, ⟨p3, p4⟩⟩ := p
    obtain ⟨⟨q1, q2⟩, ⟨q3, q4⟩⟩ := q
    have e1 : p1 = q1 := Subsingleton.elim _ _
    have e4 : p4 = q4 := Subsingleton.elim _ _
    subst e1 e4
    simp only [g53a_fbJ, transposeBobChoi, Matrix.diagonal_apply, Prod.mk.injEq]
    by_cases h2 : p2 = q2 <;> by_cases h3 : p3 = q3 <;> simp [h2, h3]
    all_goals (intro h; exact absurd h.symm h2)
  have h2J : J + J = (2 : ℂ) • J := by rw [two_smul]
  have hz : (0 : Op ((Fin 1 × Fin d) × (Fin d × Fin 1))).PosSemidef := Matrix.PosSemidef.zero
  have hfeas : BetaFeasible (feedbackMap d) J J := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using (hdiag 1 (by norm_num) (by norm_num)).isHermitian
    · simpa using (hdiag 1 (by norm_num) (by norm_num)).isHermitian
    · rw [g53a_fb_choi d, h2J]
      have : transposeBobChoi ((2 : ℂ) • J) = (2 : ℂ) • transposeBobChoi J := by
        ext p q; rfl
      rw [this, htb]; exact hdiag 2 (by norm_num) (by norm_num)
    · rw [g53a_fb_choi d, sub_self]
      have : transposeBobChoi (0 : Op ((Fin 1 × Fin d) × (Fin d × Fin 1))) = 0 := by ext p q; rfl
      rw [this]; exact hz
    · rw [h2J]; exact hdiag 2 (by norm_num) (by norm_num)
    · rw [sub_self]; exact hz
    · intro a aa b bb dd ddd
      obtain rfl : a = 0 := Subsingleton.elim _ _
      obtain rfl : aa = 0 := Subsingleton.elim _ _
      simp
  have htr : traceOutput J = 1 := by
    show traceOutput (g53a_fbJ d) = 1
    ext i j
    simp only [g53a_fbJ, traceOutput, Matrix.diagonal_apply, Matrix.one_apply, Prod.mk.injEq]
    rw [Fintype.sum_prod_type]
    by_cases hij : i = j
    · subst hij
      simp
      rw [Finset.sum_eq_single i.2 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    · simp [hij]
  have hn : specNorm (traceOutput J) = 1 := by
    rw [htr]
    have : Nonempty (Fin 1 × Fin d) := ⟨(0, ⟨0, hd⟩)⟩
    unfold specNorm
    rw [← Matrix.diagonal_one]
    exact (Matrix.l2_opNorm_diagonal _).trans (by simp)
  apply sInf_le
  exact ⟨J, J, hfeas, by exact_mod_cast hn.symm⟩

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

/-- Proposition 4 (Zero on classical feedback channels), arXiv:2010.01058v3, PDF pp.6.
 -/
theorem solution {d : ℕ} (hd : 0 < d) :
    cBeta (feedbackMap d) = 0 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h1 := g53a_one_le_beta (feedbackMap d) (by
    rw [g53a_fb_choi d, g53a_fb_trace]; simp)
  have h2 := g53a_fb_beta_le hd
  have : bipartiteBeta (feedbackMap d) = 1 := le_antisymm h2 h1
  unfold cBeta logExt
  rw [this, if_neg (show (1:EReal) ≠ ⊤ from EReal.coe_ne_top 1),
    if_neg (show ¬ (1:EReal) ≤ 0 from not_le.mpr zero_lt_one)]
  simp

end
