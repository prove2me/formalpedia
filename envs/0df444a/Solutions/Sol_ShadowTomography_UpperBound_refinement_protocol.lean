-- Prove2me | solution 1 for ShadowTomography.UpperBound.refinement_protocol
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T07:30:04.333051+00:00
-- url     : https://prove2.me/submissions/418c4ad5-ffd2-439e-b14c-b28a481d9717
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
import Theorems.Thm_ShadowTomography_UpperBound_amp_tail
import Theorems.Thm_ShadowTomography_UpperBound_trace_mul_posSemidef_nonneg
import Theorems.Thm_ShadowTomography_UpperBound_povm_lift
import Theorems.Thm_ShadowTomography_UpperBound_povm_seq
import Theorems.Thm_ShadowTomography_UpperBound_tensorPow_isDensityOperator_le_one
import Theorems.Thm_ShadowTomography_UpperBound_avgMarginal_isDensityOperator
import Theorems.Thm_ShadowTomography_UpperBound_amp_isEffect
import Theorems.Thm_ShadowTomography_UpperBound_seqAccept_mono
import Theorems.Thm_ShadowTomography_UpperBound_seqAccept_snoc
import Theorems.Thm_ShadowTomography_UpperBound_adaptive_rounds
import Theorems.Thm_ShadowTomography_UpperBound_lemma_15
import Theorems.Thm_ShadowTomography_UpperBound_lemma_12
import Theorems.Thm_ShadowTomography_UpperBound_markov_bound
set_option autoImplicit false



/-! ### S2: sketch of `refinement_protocol` (K0) — Aaronson §5 with fixes G1, G2. -/

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound
namespace S2

/-! ## POVM utilities -/

section POVMutil
variable {n : Type} [Fintype n] [DecidableEq n] {Ω : Type} [Fintype Ω]

lemma prob_mono (P : POVM Ω n) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) {A B : Ω → Prop}
    (h : ∀ ω, A ω → B ω) : P.prob σ A ≤ P.prob σ B := by
  unfold POVM.prob
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω
  · intro ω _ _
    exact trace_mul_posSemidef_nonneg _ _ (P.psd ω) hσ

lemma prob_true (P : POVM Ω n) (σ : Matrix n n ℂ) :
    P.prob σ (fun _ => True) = σ.trace.re := by
  unfold POVM.prob
  rw [Finset.sum_filter]
  simp_rw [if_pos trivial]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, P.complete, Matrix.one_mul]

lemma prob_of_forall (P : POVM Ω n) (σ : Matrix n n ℂ) {A : Ω → Prop} (h : ∀ ω, A ω) :
    P.prob σ A = σ.trace.re := by
  have : A = fun _ => True := funext fun ω => propext ⟨fun _ => trivial, fun _ => h ω⟩
  subst this
  exact prob_true P σ

/-- The two-outcome measurement `{G, 1 - G}` of an effect. -/
noncomputable def ofEffect (G : Matrix n n ℂ) (hG : IsEffect G) : POVM Bool n where
  op b := if b then G else 1 - G
  psd b := by cases b <;> simp [hG.1, hG.2]
  complete := by simp [Fintype.sum_bool]

lemma ofEffect_prob_true (G : Matrix n n ℂ) (hG : IsEffect G) (σ : Matrix n n ℂ) :
    (ofEffect G hG).prob σ (fun b => b = true) = (G * σ).trace.re := by
  unfold POVM.prob
  rw [Finset.sum_filter, Fintype.sum_bool]
  simp [ofEffect]

lemma ofEffect_prob_false (G : Matrix n n ℂ) (hG : IsEffect G) (σ : Matrix n n ℂ)
    (hσ : σ.trace = 1) :
    (ofEffect G hG).prob σ (fun b => b = false) = 1 - (G * σ).trace.re := by
  unfold POVM.prob
  rw [Finset.sum_filter, Fintype.sum_bool]
  simp [ofEffect, Matrix.sub_mul, Matrix.trace_sub, hσ]

/-- A measurement with a fixed outcome. -/
noncomputable def constPOVM [DecidableEq Ω] (ω₀ : Ω) : POVM Ω n where
  op ω := if ω = ω₀ then 1 else 0
  psd ω := by
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  complete := by simp

lemma effect_trace_bounds (E A : Matrix n n ℂ) (hE : IsEffect E)
    (hA : WildeQIT.IsDensityOperator A) :
    0 ≤ (E * A).trace.re ∧ (E * A).trace.re ≤ 1 := by
  refine ⟨trace_mul_posSemidef_nonneg _ _ hE.1 hA.1, ?_⟩
  have h := trace_mul_posSemidef_nonneg _ _ hE.2 hA.1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hA.2] at h
  simp at h
  linarith

end POVMutil

/-! ## Tests of one round -/

section Tests
variable {n : Type} [Fintype n] [DecidableEq n] {M : ℕ}

/-- Test `j` of a round: `j = inl i` is "`Tr(E_i ρ)` is above `x_i + s`" and `j = inr i` is
"below `x_i - s`", amplified on `q` copies. -/
noncomputable def testOp (E : Fin M → Matrix n n ℂ) (q : ℕ) (x : Fin M → ℝ) (s : ℝ)
    (j : Fin (M + M)) : Matrix (Fin q → n) (Fin q → n) ℂ :=
  Sum.elim (fun i => ampAtLeast (E i) q (x i + s)) (fun i => ampAtMost (E i) q (x i - s))
    (finSumFinEquiv.symm j)

lemma testOp_isEffect (E : Fin M → Matrix n n ℂ) (hE : ∀ i, IsEffect (E i)) (q : ℕ)
    (x : Fin M → ℝ) (s : ℝ) (j : Fin (M + M)) : IsEffect (testOp E q x s j) := by
  unfold testOp
  cases finSumFinEquiv.symm j with
  | inl i => exact (amp_isEffect (E i) (hE i) q _).1
  | inr i => exact (amp_isEffect (E i) (hE i) q _).2

/-- The "good" event of one round with estimates `x`: on rejection all estimates are `ε`-close,
on acceptance the update measurement accepts `ρ^{⊗q}` with probability `≥ 1 - η`. -/
def roundGood (E : Fin M → Matrix n n ℂ) (q : ℕ) (ε : ℝ) (ρ : Matrix n n ℂ) (x : Fin M → ℝ)
    (j : Fin (M + M)) (acc : Bool) : Prop :=
  (acc = false → ∀ i, |x i - ((E i) * ρ).trace.re| ≤ ε) ∧
  (acc = true →
    1 - Real.exp (-2 * q * (ε / 8) ^ 2) ≤ (testOp E q x (ε / 4) j * tensorPow ρ q).trace.re)

variable (E : Fin M → Matrix n n ℂ) (hE : ∀ i, IsEffect (E i)) (ρ : Matrix n n ℂ)
  (hρ : WildeQIT.IsDensityOperator ρ) (q v : ℕ) (x : Fin M → ℝ) (ε : ℝ) (hε : 0 < ε)
  (hq6 : Real.exp (-2 * q * (ε / 4) ^ 2) ≤ 1 / 6)
include hE hρ hε hq6

/-- A search output that passes (`≥ 2/3`) is a real violation by `ε/2`: verification accepts
and the update measurement accepts `ρ^{⊗q}`. -/
lemma test_found (j : Fin (M + M))
    (hj : 5 / 6 - 1 / 6 ≤ (testOp E q x (3 * ε / 4) j * tensorPow ρ q).trace.re) :
    1 - Real.exp (-2 * v * (ε / 16) ^ 2) ≤
        (testOp E v x (7 * ε / 16) j * tensorPow ρ v).trace.re ∧
      1 - Real.exp (-2 * q * (ε / 8) ^ 2) ≤
        (testOp E q x (ε / 4) j * tensorPow ρ q).trace.re := by
  rcases hjj : finSumFinEquiv.symm j with i | i
  · simp only [testOp, hjj, Sum.elim_inl] at hj ⊢
    have T1 := amp_tail (E i) ρ (hE i) hρ q (x i + 3 * ε / 4) (ε / 4) (by positivity)
    have hp : x i + ε / 2 < ((E i) * ρ).trace.re := by
      by_contra hc
      push Not at hc
      have := T1.2.1 (by linarith)
      linarith
    exact ⟨(amp_tail (E i) ρ (hE i) hρ v (x i + 7 * ε / 16) (ε / 16) (by positivity)).1
        (by linarith),
      (amp_tail (E i) ρ (hE i) hρ q (x i + ε / 4) (ε / 8) (by positivity)).1 (by linarith)⟩
  · simp only [testOp, hjj, Sum.elim_inr] at hj ⊢
    have T1 := amp_tail (E i) ρ (hE i) hρ q (x i - 3 * ε / 4) (ε / 4) (by positivity)
    have hp : ((E i) * ρ).trace.re < x i - ε / 2 := by
      by_contra hc
      push Not at hc
      have := T1.2.2.2 (by linarith)
      linarith
    exact ⟨(amp_tail (E i) ρ (hE i) hρ v (x i - 7 * ε / 16) (ε / 16) (by positivity)).2.2.1
        (by linarith),
      (amp_tail (E i) ρ (hE i) hρ q (x i - ε / 4) (ε / 8) (by positivity)).2.2.1
        (by linarith)⟩

/-- If the update measurement of `j` would not accept `ρ^{⊗q}`, verification rejects. -/
lemma test_unsafe (j : Fin (M + M))
    (hj : ¬ 1 - Real.exp (-2 * q * (ε / 8) ^ 2) ≤
        (testOp E q x (ε / 4) j * tensorPow ρ q).trace.re) :
    (testOp E v x (7 * ε / 16) j * tensorPow ρ v).trace.re ≤
      Real.exp (-2 * v * (ε / 16) ^ 2) := by
  rcases hjj : finSumFinEquiv.symm j with i | i
  · simp only [testOp, hjj, Sum.elim_inl] at hj ⊢
    have hp : ((E i) * ρ).trace.re < x i + 3 * ε / 8 := by
      by_contra hc
      push Not at hc
      exact hj ((amp_tail (E i) ρ (hE i) hρ q (x i + ε / 4) (ε / 8) (by positivity)).1
        (by linarith))
    exact (amp_tail (E i) ρ (hE i) hρ v (x i + 7 * ε / 16) (ε / 16) (by positivity)).2.1
      (by linarith)
  · simp only [testOp, hjj, Sum.elim_inr] at hj ⊢
    have hp : x i - 3 * ε / 8 < ((E i) * ρ).trace.re := by
      by_contra hc
      push Not at hc
      exact hj ((amp_tail (E i) ρ (hE i) hρ q (x i - ε / 4) (ε / 8) (by positivity)).2.2.1
        (by linarith))
    exact (amp_tail (E i) ρ (hE i) hρ v (x i - 7 * ε / 16) (ε / 16) (by positivity)).2.2.2
      (by linarith)

/-- A wrong estimate makes some search test accept `ρ^{⊗q}` with probability `≥ 5/6`. -/
lemma test_promise (i : Fin M) (hi : ε < |x i - ((E i) * ρ).trace.re|) :
    ∃ j, 5 / 6 ≤ (testOp E q x (3 * ε / 4) j * tensorPow ρ q).trace.re := by
  rcases lt_abs.mp hi with h | h
  · refine ⟨finSumFinEquiv (Sum.inr i), ?_⟩
    simp only [testOp, Equiv.symm_apply_apply, Sum.elim_inr]
    have := (amp_tail (E i) ρ (hE i) hρ q (x i - 3 * ε / 4) (ε / 4) (by positivity)).2.2.1
      (by linarith)
    linarith
  · refine ⟨finSumFinEquiv (Sum.inl i), ?_⟩
    simp only [testOp, Equiv.symm_apply_apply, Sum.elim_inl]
    have := (amp_tail (E i) ρ (hE i) hρ q (x i + 3 * ε / 4) (ε / 4) (by positivity)).1
      (by linarith)
    linarith

end Tests

/-! ## One round -/

/-- The constant of Gentle Search (`lemma_15`). -/
noncomputable def C15 : ℝ := Classical.choose lemma_15

noncomputable def C15_spec := Classical.choose_spec lemma_15

/-- One round on `q ℓ + v` fresh copies, given the current estimates `x`: Gentle Search over the
`2M` amplified tests, then verification of the found test. -/
lemma round_exists {D M : ℕ} (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (hE : ∀ i, IsEffect (E i))
    (hM : 1 ≤ M) (q ℓ v : ℕ) (ε δ' : ℝ) (hε : 0 < ε) (hδ' : 0 < δ') (hδ'2 : δ' ≤ 1 / 2)
    (hℓ : C15 * (Real.log ((M + M : ℕ) : ℝ) ^ 4 / (1 / 6 : ℝ) ^ 2) *
        (Real.log (Real.log ((M + M : ℕ) : ℝ)) + Real.log (1 / δ')) ≤ ℓ)
    (hq6 : Real.exp (-2 * q * (ε / 4) ^ 2) ≤ 1 / 6)
    (hv : Real.exp (-2 * v * (ε / 16) ^ 2) ≤ δ') (x : Fin M → ℝ) :
    ∃ R : POVM (Fin (M + M) × Bool) (Fin (q * ℓ + v) → Fin D),
      ∀ ρ, WildeQIT.IsDensityOperator ρ →
        1 - (δ' + δ') ≤ R.prob (tensorPow ρ (q * ℓ + v))
          (fun ω => roundGood E q ε ρ x ω.1 ω.2) := by
  obtain ⟨k, hk, P, hP⟩ := C15_spec.2 (n := Fin q → Fin D) (M + M) (testOp E q x (3 * ε / 4))
    (5 / 6) (1 / 6) δ' (by omega) (testOp_isEffect E hE q x _) (by norm_num) hδ' hδ'2
  have hkℓ : k ≤ ℓ := by exact_mod_cast hk.trans hℓ
  obtain ⟨P', hP'⟩ := povm_lift q k ℓ hkℓ P
  obtain ⟨R, hR⟩ := povm_seq (q * ℓ) v P'
    (fun j => ofEffect (testOp E v x (7 * ε / 16) j) (testOp_isEffect E hE v x _ j))
  refine ⟨R, fun ρ hρ => ?_⟩
  have hρq := (tensorPow_isDensityOperator_le_one ρ hρ q).1
  have hρv := (tensorPow_isDensityOperator_le_one ρ hρ v).1
  have hρqℓ := (tensorPow_isDensityOperator_le_one ρ hρ (q * ℓ)).1
  have hδ'0 : 0 ≤ δ' := hδ'.le
  by_cases hall : ∀ i, |x i - ((E i) * ρ).trace.re| ≤ ε
  · have := hR ρ hρ (fun _ => True) (fun j b => roundGood E q ε ρ x j b) 0 δ' hδ'0
      (by rw [prob_true, hρqℓ.2]; simp) ?_
    · linarith
    · intro j _
      by_cases hu : 1 - Real.exp (-2 * q * (ε / 8) ^ 2) ≤
          (testOp E q x (ε / 4) j * tensorPow ρ q).trace.re
      · rw [prob_of_forall _ _ (fun b => ⟨fun _ => hall, fun _ => hu⟩), hρv.2]
        simp
        linarith
      · have hb := test_unsafe E hE ρ hρ q v x ε hε hq6 j hu
        calc 1 - δ' ≤ 1 - (testOp E v x (7 * ε / 16) j * tensorPow ρ v).trace.re := by linarith
          _ = _ := (ofEffect_prob_false _ _ _ hρv.2).symm
          _ ≤ _ := prob_mono _ hρv.1 (fun b hb => ⟨fun _ => hall, fun h => by simp [hb] at h⟩)
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hS : 1 - δ' ≤ P'.prob (tensorPow ρ (q * ℓ))
        (fun j => 5 / 6 - 1 / 6 ≤ (testOp E q x (3 * ε / 4) j * tensorPow ρ q).trace.re) := by
      rw [hP' ρ hρ]
      exact hP (tensorPow ρ q) hρq (test_promise E hE ρ hρ q x ε hε hq6 i hi)
    have := hR ρ hρ _ (fun j b => roundGood E q ε ρ x j b) δ' δ' hδ'0 hS ?_
    · linarith
    · intro j hj
      obtain ⟨h1, h2⟩ := test_found E hE ρ hρ q v x ε hε hq6 j hj
      calc 1 - δ' ≤ (testOp E v x (7 * ε / 16) j * tensorPow ρ v).trace.re := by linarith
        _ = _ := (ofEffect_prob_true _ _ _).symm
        _ ≤ _ := prob_mono _ hρv.1 (fun b hb => ⟨fun h => by simp [hb] at h, fun _ => h2⟩)

/-! ## The classical hypothesis and the potential argument -/

section Potential
variable {m : Type} [Fintype m] [DecidableEq m]

/-- Unnormalised post-selected hypothesis `A σ₀ A†`, `A = √F_{t-1} ⋯ √F_0`. -/
noncomputable def postN {t : ℕ} (F : Fin t → Matrix m m ℂ) (σ0 : Matrix m m ℂ) :
    Matrix m m ℂ :=
  ((List.finRange t).reverse.map (fun i => CFC.sqrt (F i))).prod * σ0 *
    (((List.finRange t).reverse.map (fun i => CFC.sqrt (F i))).prod).conjTranspose

/-- Normalised post-selected hypothesis. -/
noncomputable def hyp {t : ℕ} (F : Fin t → Matrix m m ℂ) (σ0 : Matrix m m ℂ) : Matrix m m ℂ :=
  ((seqAccept F σ0 : ℂ))⁻¹ • postN F σ0

lemma seqAccept_eq {t : ℕ} (F : Fin t → Matrix m m ℂ) (σ0 : Matrix m m ℂ) :
    seqAccept F σ0 = (postN F σ0).trace.re := rfl

lemma postN_psd {t : ℕ} (F : Fin t → Matrix m m ℂ) {σ0 : Matrix m m ℂ}
    (h : σ0.PosSemidef) : (postN F σ0).PosSemidef :=
  h.mul_mul_conjTranspose_same _

lemma trace_postN {t : ℕ} (F : Fin t → Matrix m m ℂ) {σ0 : Matrix m m ℂ}
    (h : σ0.PosSemidef) : (postN F σ0).trace = ((seqAccept F σ0 : ℝ) : ℂ) := by
  have h0 := (postN_psd F h).trace_nonneg
  rw [seqAccept_eq]
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    exact ((Complex.le_def.1 h0).2).symm

lemma postN_eq_smul {t : ℕ} (F : Fin t → Matrix m m ℂ) (σ0 : Matrix m m ℂ)
    (hp : seqAccept F σ0 ≠ 0) : postN F σ0 = ((seqAccept F σ0 : ℝ) : ℂ) • hyp F σ0 := by
  rw [hyp, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hp), one_smul]

lemma hyp_density {t : ℕ} (F : Fin t → Matrix m m ℂ) {σ0 : Matrix m m ℂ}
    (h : σ0.PosSemidef) (hp : 0 < seqAccept F σ0) : WildeQIT.IsDensityOperator (hyp F σ0) := by
  refine ⟨(postN_psd F h).smul ?_, ?_⟩
  · rw [← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr hp.le)
  · rw [hyp, Matrix.trace_smul, trace_postN F h, smul_eq_mul,
      inv_mul_cancel₀ (by exact_mod_cast hp.ne')]

lemma entry_eq (Fp : (t : ℕ) → Fin t → Matrix m m ℂ) (g : ℕ → Matrix m m ℂ)
    (hFp : ∀ t, Fp (t + 1) = Fin.snoc (α := fun _ => Matrix m m ℂ) (Fp t) (g t)) :
    ∀ t (i : Fin t), Fp t i = g i
  | 0, i => i.elim0
  | t + 1, i => by
    rw [hFp t]
    induction i using Fin.lastCases with
    | last => simp
    | cast j =>
      simp only [Fin.snoc_castSucc, Fin.val_castSucc]
      exact entry_eq Fp g hFp t j

/-- **Potential argument.** Along a sequence of effects each accepting `ρ` w.p. `≥ 1 - η`, the
acceptance of the prior `σ₀ ⪰ c ρ` is at least `c (1 - 2T√η)` (quantum union bound), while each
step multiplies it by at most `α` (Markov). -/
lemma potential (Fp : (t : ℕ) → Fin t → Matrix m m ℂ) (g : ℕ → Matrix m m ℂ)
    (hFp : ∀ t, Fp (t + 1) = Fin.snoc (α := fun _ => Matrix m m ℂ) (Fp t) (g t))
    (hg : ∀ t, IsEffect (g t)) (σ0 ρ : Matrix m m ℂ) (hσ0 : WildeQIT.IsDensityOperator σ0)
    (hρ : WildeQIT.IsDensityOperator ρ) (c : ℝ) (hc : (σ0 - (c : ℂ) • ρ).PosSemidef)
    (hc0 : 0 ≤ c) (T : ℕ) (η α : ℝ) (hα : 0 ≤ α)
    (hacc : ∀ t < T, 1 - η ≤ (g t * ρ).trace.re)
    (hmark : ∀ t < T, 0 < seqAccept (Fp t) σ0 →
      (g t * postN (Fp t) σ0).trace.re ≤ α * seqAccept (Fp t) σ0) :
    c * (1 - 2 * T * Real.sqrt η) ≤ α ^ T := by
  have hentry := entry_eq Fp g hFp
  have hlow : c * (1 - 2 * T * Real.sqrt η) ≤ seqAccept (Fp T) σ0 := by
    have h12 := lemma_12 T (Fp T) ρ η (fun i => by rw [hentry]; exact hg i) hρ
      (fun i => by rw [hentry]; exact hacc i i.isLt)
    calc c * (1 - 2 * T * Real.sqrt η) ≤ c * seqAccept (Fp T) ρ :=
          mul_le_mul_of_nonneg_left h12 hc0
      _ ≤ _ := seqAccept_mono (Fp T) σ0 ρ c hc
  have hup : ∀ t ≤ T, seqAccept (Fp t) σ0 ≤ α ^ t := by
    intro t
    induction t with
    | zero =>
      intro _
      have h0 : seqAccept (Fp 0) σ0 = 1 := by simp [seqAccept, hσ0.2]
      simp [h0]
    | succ t ih =>
      intro ht
      have ih := ih (by omega)
      have hsnoc : seqAccept (Fp (t + 1)) σ0 = (g t * postN (Fp t) σ0).trace.re := by
        rw [hFp t]
        exact seqAccept_snoc (Fp t) (g t) (hg t) σ0
      have hdec : (g t * postN (Fp t) σ0).trace.re ≤ seqAccept (Fp t) σ0 := by
        have := trace_mul_posSemidef_nonneg _ _ (hg t).2 (postN_psd (Fp t) hσ0.1)
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at this
        rw [seqAccept_eq]
        linarith
      rw [hsnoc]
      by_cases hp : 0 < seqAccept (Fp t) σ0
      · calc _ ≤ α * seqAccept (Fp t) σ0 := hmark t (by omega) hp
          _ ≤ α * α ^ t := mul_le_mul_of_nonneg_left ih hα
          _ = α ^ (t + 1) := by ring
      · push Not at hp
        calc _ ≤ seqAccept (Fp t) σ0 := hdec
          _ ≤ 0 := hp
          _ ≤ α ^ (t + 1) := pow_nonneg hα _
  linarith [hup T le_rfl]

end Potential

/-! ## The protocol -/

section Protocol
variable {n : Type} [Fintype n] [DecidableEq n] {M : ℕ}

/-- Estimates read off a hypothesis. -/
noncomputable def xOf (E : Fin M → Matrix n n ℂ) {q : ℕ}
    (σ : Matrix (Fin q → n) (Fin q → n) ℂ) (i : Fin M) : ℝ :=
  ((E i) * avgMarginal σ).trace.re

/-- Effects of the update steps, along an (extended) record `a`. -/
noncomputable def Fpref (E : Fin M → Matrix n n ℂ) (q : ℕ) (ε : ℝ)
    (σ0 : Matrix (Fin q → n) (Fin q → n) ℂ) (a : ℕ → Fin (M + M) × Bool) :
    (t : ℕ) → Fin t → Matrix (Fin q → n) (Fin q → n) ℂ
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (α := fun _ => Matrix (Fin q → n) (Fin q → n) ℂ) (Fpref E q ε σ0 a t)
      (testOp E q (xOf E (hyp (Fpref E q ε σ0 a t) σ0)) (ε / 4) (a t).1)

lemma Fpref_congr (E : Fin M → Matrix n n ℂ) (q : ℕ) (ε : ℝ)
    (σ0 : Matrix (Fin q → n) (Fin q → n) ℂ) (a b : ℕ → Fin (M + M) × Bool) :
    ∀ t, (∀ i < t, a i = b i) → Fpref E q ε σ0 a t = Fpref E q ε σ0 b t
  | 0, _ => rfl
  | t + 1, h => by
    simp only [Fpref]
    rw [Fpref_congr E q ε σ0 a b t (fun i hi => h i (by omega)), h t (by omega)]

/-- Extend a finite history by a default value. -/
def extH {α : Type} {r : ℕ} (h : Fin r → α) (d : α) (i : ℕ) : α :=
  if hi : i < r then h ⟨i, hi⟩ else d

end Protocol

lemma clamp_close (x p ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : |x - p| ≤ ε) :
    |max 0 (min 1 x) - p| ≤ ε := by
  rw [abs_le] at h ⊢
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

lemma log_lb (c : ℝ) (hc : 0 < c) : 1 - 1 / c ≤ Real.log c := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
  rw [Real.log_inv] at h
  rw [one_div]
  linarith

lemma markov_step {n : Type} [Fintype n] [DecidableEq n] {M : ℕ} (E : Fin M → Matrix n n ℂ)
    (hE : ∀ i, IsEffect (E i)) (q : ℕ) (hq : 1 ≤ q) (σ : Matrix (Fin q → n) (Fin q → n) ℂ)
    (hσ : WildeQIT.IsDensityOperator σ) (ε : ℝ) (hε : 0 < ε) (j : Fin (M + M)) :
    (testOp E q (xOf E σ) (ε / 4) j * σ).trace.re ≤ 1 / (1 + ε / 4) := by
  have hA := avgMarginal_isDensityOperator hq σ hσ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rcases hjj : finSumFinEquiv.symm j with i | i
  · simp only [testOp, hjj, Sum.elim_inl, xOf]
    have hb := effect_trace_bounds (E i) _ (hE i) hA
    refine (markov_bound (E i) q σ ε (hE i) hσ hq hε).1.trans ?_
    rw [div_le_div_iff₀ (mul_pos (by linarith [hb.1]) hq0) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hq0.le hε.le) (sub_nonneg.2 hb.2)]
  · simp only [testOp, hjj, Sum.elim_inr, xOf]
    have hb := effect_trace_bounds (E i) _ (hE i) hA
    refine (markov_bound (E i) q σ ε (hE i) hσ hq hε).2.trans ?_
    rw [div_le_div_iff₀ (mul_pos (by linarith [hb.2]) hq0) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hq0.le hε.le) hb.1]

lemma exp_neg_le {x c : ℝ} (hc : 0 < c) (h : c ≤ Real.exp x) : Real.exp (-x) ≤ 1 / c := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hc h

end S2

end ShadowTomography.UpperBound

open ShadowTomography.UpperBound

set_option maxHeartbeats 1600000 in
open ShadowTomography.UpperBound.S2 in
theorem solution :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (D M : ℕ) (ε δ : ℝ) (q ℓ v T : ℕ), 2 ≤ D → 2 ≤ M → 0 < ε → ε ≤ 1 / 2 → 0 < δ →
        δ ≤ 1 / 2 →
        C₀ * (1 + Real.log T) / ε ^ 2 ≤ (q : ℝ) →
        C₀ * q * Real.log D / ε ≤ (T : ℝ) →
        C₀ * Real.log M ^ 4 * (1 + Real.log (Real.log M) + Real.log (T / δ)) ≤ (ℓ : ℝ) →
        C₀ * (1 + Real.log (T / δ)) / ε ^ 2 ≤ (v : ℝ) →
        ∀ E : Fin M → Matrix (Fin D) (Fin D) ℂ, (∀ i, IsEffect (E i)) →
          ∃ (Ω : Type) (_ : Fintype Ω) (P : POVM Ω (Fin (T * (q * ℓ + v)) → Fin D))
            (b : Ω → Fin M → ℝ),
            (∀ ω i, b ω i ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ ρ : Matrix (Fin D) (Fin D) ℂ, WildeQIT.IsDensityOperator ρ →
              1 - δ ≤ P.prob (tensorPow ρ (T * (q * ℓ + v)))
                (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε) := by
  have hC15 : 0 < C15 := C15_spec.1
  refine ⟨1152 * C15 + 1280, by positivity, ?_⟩
  intro D M ε δ q ℓ v T hD hM hε hε2 hδ hδ2 hq hT hℓ hv E hE
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = 1152 * C15 + 1280 := ⟨_, rfl⟩
  rw [← hC₀] at hq hT hℓ hv
  have hC₀big : 1280 ≤ C₀ := by rw [hC₀]; linarith
  have hC₀15 : 1152 * C15 ≤ C₀ := by rw [hC₀]; linarith
  /- basic numeric facts -/
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hlogT0 : 0 ≤ Real.log T := Real.log_natCast_nonneg T
  have hε2pos : 0 < ε ^ 2 := by positivity
  have hqε : C₀ * (1 + Real.log T) ≤ q * ε ^ 2 := (div_le_iff₀ hε2pos).1 hq
  have hqε' : 1280 * (1 + Real.log T) ≤ q * ε ^ 2 := by
    linarith [mul_le_mul_of_nonneg_right hC₀big (by linarith : (0:ℝ) ≤ 1 + Real.log T)]
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      rw [Nat.cast_zero, zero_mul] at hqε'
      linarith
    · omega
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hlogD : Real.log 2 ≤ Real.log D := Real.log_le_log (by norm_num) (by exact_mod_cast hD)
  have hTε : C₀ * q * Real.log D ≤ T * ε := (div_le_iff₀ hε).1 hT
  have hT1 : 1 ≤ T := by
    have : 0 < C₀ * q * Real.log D :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    rcases Nat.eq_zero_or_pos T with h | h
    · subst h
      rw [Nat.cast_zero, zero_mul] at hTε
      linarith
    · omega
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hTpos : (0 : ℝ) < T := by linarith
  have hvε : C₀ * (1 + Real.log (T / δ)) ≤ v * ε ^ 2 := (div_le_iff₀ hε2pos).1 hv
  have hTδ : 2 ≤ (T : ℝ) / δ := by rw [le_div_iff₀ hδ]; linarith
  have hlogTδ : 0 ≤ Real.log (T / δ) := Real.log_nonneg (by linarith)
  have hvε' : 1280 * (1 + Real.log (T / δ)) ≤ v * ε ^ 2 := by
    linarith [mul_le_mul_of_nonneg_right hC₀big (by linarith : (0:ℝ) ≤ 1 + Real.log (T / δ))]
  /- (R1) promise and search thresholds -/
  have hq6 : Real.exp (-2 * q * (ε / 4) ^ 2) ≤ 1 / 6 := by
    rw [show -2 * (q : ℝ) * (ε / 4) ^ 2 = -(q * ε ^ 2 / 8) by ring]
    exact exp_neg_le (by norm_num) (by linarith [Real.add_one_le_exp (q * ε ^ 2 / 8)])
  /- (R2) verification failure -/
  obtain ⟨δ', hδ'def⟩ : ∃ δ' : ℝ, δ' = δ / (2 * T) := ⟨_, rfl⟩
  have hδ'pos : 0 < δ' := by rw [hδ'def]; positivity
  have hδ'half : δ' ≤ 1 / 2 := by
    rw [hδ'def, div_le_iff₀ (by positivity)]
    linarith
  have hvδ : Real.exp (-2 * v * (ε / 16) ^ 2) ≤ δ' := by
    have hR2 : Real.log (2 * (T / δ)) ≤ v * ε ^ 2 / 128 := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      linarith
    have he := Real.exp_le_exp.mpr hR2
    rw [Real.exp_log (by positivity)] at he
    rw [show -2 * (v : ℝ) * (ε / 16) ^ 2 = -(v * ε ^ 2 / 128) by ring]
    calc Real.exp (-(v * ε ^ 2 / 128)) ≤ 1 / (2 * (T / δ)) := exp_neg_le (by positivity) he
      _ = δ' := by rw [hδ'def]; field_simp
  /- (R3) Gentle Search fits in `ℓ` blocks -/
  have hℓ15 : C15 * (Real.log ((M + M : ℕ) : ℝ) ^ 4 / (1 / 6 : ℝ) ^ 2) *
      (Real.log (Real.log ((M + M : ℕ) : ℝ)) + Real.log (1 / δ')) ≤ ℓ := by
    have hL : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
    have hLpos : 0 < Real.log M := by linarith
    have hMM : Real.log ((M + M : ℕ) : ℝ) = Real.log 2 + Real.log M := by
      rw [show ((M + M : ℕ) : ℝ) = 2 * M by push_cast; ring,
        Real.log_mul (by norm_num) (by positivity)]
    have hP : Real.log ((M + M : ℕ) : ℝ) ^ 4 ≤ 16 * Real.log M ^ 4 := by
      rw [hMM]
      calc (Real.log 2 + Real.log M) ^ 4 ≤ (2 * Real.log M) ^ 4 :=
            pow_le_pow_left₀ (by linarith) (by linarith) 4
        _ = 16 * Real.log M ^ 4 := by ring
    have hll : Real.log (Real.log ((M + M : ℕ) : ℝ)) ≤ Real.log 2 + Real.log (Real.log M) := by
      rw [← Real.log_mul (by norm_num) hLpos.ne']
      exact Real.log_le_log (by rw [hMM]; linarith) (by rw [hMM]; linarith)
    have hlδ : Real.log (1 / δ') = Real.log 2 + Real.log (T / δ) := by
      rw [← Real.log_mul (by norm_num) (by positivity), hδ'def]
      congr 1
      field_simp
    have hlL : -0.45 ≤ Real.log (Real.log M) := by
      have h1 := log_lb (Real.log M) hLpos
      have h2 : 1 / Real.log M ≤ 1.45 := by
        rw [div_le_iff₀ hLpos]
        linarith
      linarith
    have hZ : Real.log (Real.log ((M + M : ℕ) : ℝ)) + Real.log (1 / δ') ≤
        2 * (1 + Real.log (Real.log M) + Real.log (T / δ)) := by
      rw [hlδ]
      linarith
    have hW : 0 ≤ 1 + Real.log (Real.log M) + Real.log (T / δ) := by linarith
    calc C15 * (Real.log ((M + M : ℕ) : ℝ) ^ 4 / (1 / 6 : ℝ) ^ 2) *
          (Real.log (Real.log ((M + M : ℕ) : ℝ)) + Real.log (1 / δ'))
        = 36 * C15 * Real.log ((M + M : ℕ) : ℝ) ^ 4 *
          (Real.log (Real.log ((M + M : ℕ) : ℝ)) + Real.log (1 / δ')) := by ring
      _ ≤ 36 * C15 * Real.log ((M + M : ℕ) : ℝ) ^ 4 *
          (2 * (1 + Real.log (Real.log M) + Real.log (T / δ))) :=
          mul_le_mul_of_nonneg_left hZ (by positivity)
      _ ≤ 36 * C15 * (16 * Real.log M ^ 4) *
          (2 * (1 + Real.log (Real.log M) + Real.log (T / δ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by positivity))
            (by linarith)
      _ = 1152 * C15 * (Real.log M ^ 4 * (1 + Real.log (Real.log M) + Real.log (T / δ))) := by
          ring
      _ ≤ C₀ * (Real.log M ^ 4 * (1 + Real.log (Real.log M) + Real.log (T / δ))) :=
          mul_le_mul_of_nonneg_right hC₀15 (mul_nonneg (by positivity) hW)
      _ = C₀ * Real.log M ^ 4 * (1 + Real.log (Real.log M) + Real.log (T / δ)) := by ring
      _ ≤ ℓ := hℓ
  /- the round measurements -/
  have hround := round_exists E hE (by omega) q ℓ v ε δ' hε hδ'pos hδ'half hℓ15 hq6 hvδ
  choose Rnd hRnd using hround
  /- the prior `σ₀ = D^{-q} · 1` -/
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (D : ℝ) ^ q := ⟨_, rfl⟩
  have hD0 : (0 : ℝ) < D := by
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  have hc0 : 0 < c := by rw [hcdef]; positivity
  obtain ⟨σ0, hσ0def⟩ : ∃ σ0 : Matrix (Fin q → Fin D) (Fin q → Fin D) ℂ,
      σ0 = (c : ℂ) • 1 := ⟨_, rfl⟩
  have hσ0 : WildeQIT.IsDensityOperator σ0 := by
    rw [hσ0def]
    refine ⟨Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hc0.le), ?_⟩
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, hcdef, smul_eq_mul]
    have : (D : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
    push_cast
    field_simp
  have hρq_le : ∀ ρ : Matrix (Fin D) (Fin D) ℂ, WildeQIT.IsDensityOperator ρ →
      (σ0 - (c : ℂ) • tensorPow ρ q).PosSemidef := by
    intro ρ hρ
    rw [hσ0def, ← smul_sub]
    exact (tensorPow_isDensityOperator_le_one ρ hρ q).2.smul (Complex.zero_le_real.mpr hc0.le)
  /- the protocol -/
  obtain ⟨j0⟩ : Nonempty (Fin (M + M)) := ⟨⟨0, by omega⟩⟩
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : ∀ r : Fin T, (Fin r → Fin (M + M) × Bool) →
      POVM (Fin (M + M) × Bool) (Fin (q * ℓ + v) → Fin D),
      P = fun (r : Fin T) (h : Fin r → Fin (M + M) × Bool) =>
        if ∃ i, (h i).2 = false then constPOVM (j0, false)
        else Rnd (xOf E (hyp (Fpref E q ε σ0 (extH h (j0, true)) (r : ℕ)) σ0)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ := adaptive_rounds T (q * ℓ + v) P
  obtain ⟨b, hbdef⟩ : ∃ b : (Fin T → Fin (M + M) × Bool) → Fin M → ℝ,
      b = fun ω i => if hh : ∃ r, (ω r).2 = false then
        max 0 (min 1 (xOf E (hyp (Fpref E q ε σ0 (extH ω (j0, true))
          (Fin.find (fun r => (ω r).2 = false) hh)) σ0) i)) else 0 := ⟨_, rfl⟩
  refine ⟨Fin T → Fin (M + M) × Bool, inferInstance, Q, b, ?_, ?_⟩
  · intro ω i
    rw [hbdef]
    dsimp only
    split_ifs
    · exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    · exact ⟨le_rfl, zero_le_one⟩
  intro ρ hρ
  have hρq := (tensorPow_isDensityOperator_le_one ρ hρ q).1
  obtain ⟨good, hgood⟩ : ∃ good : ∀ r : Fin T, (Fin r → Fin (M + M) × Bool) →
      Fin (M + M) × Bool → Prop,
      good = fun (r : Fin T) (h : Fin r → Fin (M + M) × Bool) (ω : Fin (M + M) × Bool) =>
        (∃ i, (h i).2 = false) ∨
        roundGood E q ε ρ (xOf E (hyp (Fpref E q ε σ0 (extH h (j0, true)) (r : ℕ)) σ0)) ω.1 ω.2 :=
    ⟨_, rfl⟩
  have hK := hQ ρ hρ good (fun _ => δ / T) ?_
  swap
  · intro r h
    rw [hPdef, hgood]
    dsimp only
    have hk := (tensorPow_isDensityOperator_le_one ρ hρ (q * ℓ + v)).1
    by_cases hh : ∃ i, (h i).2 = false
    · rw [if_pos hh, prob_of_forall _ _ (fun ω => Or.inl hh), hk.2]
      simp only [Complex.one_re]
      have : 0 ≤ δ / T := by positivity
      linarith
    · rw [if_neg hh]
      calc 1 - δ / T = 1 - (δ' + δ') := by rw [hδ'def]; field_simp; ring
        _ ≤ _ := hRnd _ ρ hρ
        _ ≤ _ := prob_mono _ hk.1 (fun ω hω => Or.inr hω)
  have hsum : ∑ _r : Fin T, δ / (T : ℝ) = δ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsum] at hK
  refine hK.trans (prob_mono _ (tensorPow_isDensityOperator_le_one ρ hρ _).1.1 ?_)
  intro ω hω
  rw [hgood] at hω
  have hpre : ∀ r : Fin T, Fpref E q ε σ0
      (extH (fun i : Fin r => ω (Fin.castLT i (lt_trans i.isLt r.isLt))) (j0, true)) r =
      Fpref E q ε σ0 (extH ω (j0, true)) r := by
    intro r
    apply Fpref_congr
    intro i hi
    simp only [extH, dif_pos hi, dif_pos (hi.trans r.isLt)]
    rfl
  by_cases hh : ∃ r, (ω r).2 = false
  · -- first rejecting round: its estimates are returned
    have hspec : (ω (Fin.find (fun r => (ω r).2 = false) hh)).2 = false := Fin.find_spec hh
    have hg := hω (Fin.find (fun r => (ω r).2 = false) hh)
    dsimp only at hg
    rcases hg with ⟨j, hj⟩ | hg
    · exact absurd hj (Fin.find_min hh (Fin.mk_lt_of_lt_val j.isLt))
    · have hall := hg.1 hspec
      rw [hpre] at hall
      intro i
      rw [hbdef]
      dsimp only
      rw [dif_pos hh]
      have hb := effect_trace_bounds (E i) ρ (hE i) hρ
      exact clamp_close _ _ ε hb.1 hb.2 (hall i)
  · -- no rejecting round: impossible by the potential argument
    exfalso
    push Not at hh
    have hall : ∀ r, (ω r).2 = true := fun r => by simpa using hh r
    obtain ⟨g, hgdef⟩ : ∃ g : ℕ → Matrix (Fin q → Fin D) (Fin q → Fin D) ℂ,
        g = fun t => testOp E q (xOf E (hyp (Fpref E q ε σ0 (extH ω (j0, true)) t) σ0)) (ε / 4)
          (extH ω (j0, true) t).1 := ⟨_, rfl⟩
    have hacc : ∀ t < T,
        1 - Real.exp (-2 * q * (ε / 8) ^ 2) ≤ (g t * tensorPow ρ q).trace.re := by
      intro t ht
      have hg := hω ⟨t, ht⟩
      dsimp only at hg
      rcases hg with ⟨j, hj⟩ | hg
      · simp [hall] at hj
      · have h2 := hg.2 (hall _)
        have h3 : Fpref E q ε σ0 (extH (fun i : Fin t => ω (Fin.castLT i (lt_trans i.isLt ht)))
            (j0, true)) t = Fpref E q ε σ0 (extH ω (j0, true)) t := hpre ⟨t, ht⟩
        rw [h3] at h2
        have hat : extH ω (j0, true) t = ω ⟨t, ht⟩ := by simp [extH, ht]
        rw [hgdef]
        dsimp only
        rw [hat]
        exact h2
    have hmark : ∀ t < T, 0 < seqAccept (Fpref E q ε σ0 (extH ω (j0, true)) t) σ0 →
        (g t * postN (Fpref E q ε σ0 (extH ω (j0, true)) t) σ0).trace.re ≤
          1 / (1 + ε / 4) * seqAccept (Fpref E q ε σ0 (extH ω (j0, true)) t) σ0 := by
      intro t _ hp
      have hσt := hyp_density _ hσ0.1 hp
      rw [postN_eq_smul _ σ0 hp.ne', Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        Complex.re_ofReal_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right _ hp.le
      rw [hgdef]
      exact markov_step E hE q hq1 _ hσt ε hε _
    have hpot := potential (Fpref E q ε σ0 (extH ω (j0, true))) g
      (fun t => by rw [hgdef]; rfl)
      (fun t => by rw [hgdef]; exact testOp_isEffect E hE q _ _ _) σ0 (tensorPow ρ q) hσ0 hρq c
      (hρq_le ρ hρ) hc0.le T _ (1 / (1 + ε / 4)) (by positivity) hacc hmark
    /- (R5) the union-bound loss is at most `1/10` -/
    have hη : 2 * T * Real.sqrt (Real.exp (-2 * q * (ε / 8) ^ 2)) ≤ 1 / 10 := by
      have hs : Real.sqrt (Real.exp (-2 * q * (ε / 8) ^ 2)) = Real.exp (-(q * ε ^ 2 / 64)) := by
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add]
        congr 1
        ring
      have hX : 19 + Real.log T ≤ q * ε ^ 2 / 64 := by linarith
      have h20 : 20 * (T : ℝ) ≤ Real.exp (q * ε ^ 2 / 64) := by
        calc 20 * (T : ℝ) ≤ Real.exp 19 * T :=
              mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp 19]) (by linarith)
          _ = Real.exp (19 + Real.log T) := by rw [Real.exp_add, Real.exp_log hTpos]
          _ ≤ _ := Real.exp_le_exp.mpr hX
      rw [hs, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      linarith
    /- (R6) `T` rounds drive the potential below `0.9 D^{-q}` -/
    have hlog1 : 2 * ε / 9 ≤ Real.log (1 + ε / 4) := by
      have h1 := log_lb (1 + ε / 4) (by positivity)
      have h2 : 1 / (1 + ε / 4) ≤ 1 - 2 * ε / 9 := by
        rw [div_le_iff₀ (by positivity)]
        linarith [mul_nonneg hε.le (by linarith : (0:ℝ) ≤ 1 - 2 * ε)]
      linarith
    have hqlogD : Real.log 2 ≤ q * Real.log D := by
      linarith [mul_le_mul hqr hlogD (by linarith) (by linarith)]
    have hlog109 : Real.log (10 / 9) ≤ 1 / 9 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 / 9 by norm_num)
      linarith
    have hTlog : Real.log (10 / 9) + q * Real.log D < T * Real.log (1 + ε / 4) := by
      have : T * (2 * ε / 9) ≤ T * Real.log (1 + ε / 4) :=
        mul_le_mul_of_nonneg_left hlog1 (by linarith)
      linarith [mul_le_mul_of_nonneg_right hC₀big (by linarith : (0:ℝ) ≤ q * Real.log D)]
    have hB : 10 / 9 * (D : ℝ) ^ q < (1 + ε / 4) ^ T := by
      rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_mul (by norm_num)
        (by positivity), Real.log_pow, Real.log_pow]
      exact hTlog
    have hfin : (1 / (1 + ε / 4)) ^ T < c * (9 / 10) := by
      rw [one_div_pow, hcdef, div_mul_eq_mul_div, one_mul,
        div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith [mul_nonneg hc0.le (by linarith : (0 : ℝ) ≤ 1 / 10 - 2 * T *
      Real.sqrt (Real.exp (-2 * q * (ε / 8) ^ 2)))]
