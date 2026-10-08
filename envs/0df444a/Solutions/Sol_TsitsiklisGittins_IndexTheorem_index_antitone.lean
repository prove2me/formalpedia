-- Prove2me | solution 1 for TsitsiklisGittins.IndexTheorem.index_antitone
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:43:54.406146+00:00
-- url     : https://prove2.me/submissions/e04d0d3a-d912-455c-8050-84b0502c8af5

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun
open TsitsiklisGittins.IndexTheorem

private lemma reduction_rate_bound {n : ℕ} {X : Fin n → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (S : Stage n X) (s q : Σ i, X i)
    (hwq : 0 < S.w q) (hws : 0 < S.w s)
    (hc : 0 ≤ S.D q s / (1 - S.D s s))
    (hmax : S.rate q ≤ S.rate s) :
    (S.reduce s).rate q ≤ S.rate s := by
  have hm : S.ρ q ≤ S.rate s * S.w q := (div_le_iff₀ hwq).mp hmax
  have he : S.ρ s = S.rate s * S.w s := by
    unfold Stage.rate
    field_simp
  have hw : 0 < S.w q + S.D q s / (1 - S.D s s) * S.w s :=
    add_pos_of_pos_of_nonneg hwq (mul_nonneg hc hws.le)
  change (S.ρ q + S.D q s / (1 - S.D s s) * S.ρ s) /
    (S.w q + S.D q s / (1 - S.D s s) * S.w s) ≤ S.rate s
  apply (div_le_iff₀ hw).mpr
  rw [he]
  nlinarith

#print axioms reduction_rate_bound

theorem index_antitone_of_stage_bounds {n : ℕ} {X : Fin n → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X) (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ)
    (hrun : B.IsIndexRun seq γ)
    (hpos : ∀ k q, 0 < (B.stageAfter (seq.take k)).w q)
    (hc : ∀ k q s, 0 ≤ (B.stageAfter (seq.take k)).D q s /
      (1 - (B.stageAfter (seq.take k)).D s s))
    (k : ℕ) (hk : k + 1 < seq.length) : γ seq[k + 1] ≤ γ seq[k] := by
  have hk0 : k < seq.length := by omega
  obtain ⟨hmem, hmax, hγ⟩ := hrun.2.2 k hk0
  obtain ⟨hmem', hmax', hγ'⟩ := hrun.2.2 (k+1) hk
  have he : B.stageAfter (seq.take (k+1)) =
      (B.stageAfter (seq.take k)).reduce seq[k] := by
    rw [List.take_succ_eq_append_getElem hk0]
    simp only [SemiMarkovBandit.stageAfter, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [he] at hmem' hγ'
  have hmem0 : seq[k+1] ∈ (B.stageAfter (seq.take k)).alive :=
    Finset.mem_of_mem_erase hmem'
  rw [hγ', hγ]
  exact reduction_rate_bound _ _ _ (hpos k _) (hpos k _) (hc k _ _) (hmax _ hmem0)

#print axioms index_antitone_of_stage_bounds

private def Good {n : ℕ} {X : Fin n → Type}
    [∀ i, Fintype (X i)] (S : Stage n X) : Prop :=
  (∀ q, 0 < S.w q) ∧ (∀ q p, 0 ≤ S.D q p) ∧ (∀ q, ∑ p, S.D q p < 1)

private lemma good_coeff {n : ℕ} {X : Fin n → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (S : Stage n X) (hS : Good S) (q s : Σ i, X i) :
    0 ≤ S.D q s / (1 - S.D s s) := by
  have hss : S.D s s < 1 :=
    lt_of_le_of_lt (Finset.single_le_sum (fun p _ => hS.2.1 s p) (Finset.mem_univ s)) (hS.2.2 s)
  exact div_nonneg (hS.2.1 q s) (by linarith)

private lemma good_reduce {n : ℕ} {X : Fin n → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (S : Stage n X) (hS : Good S) (s : Σ i, X i) : Good (S.reduce s) := by
  classical
  have hss : S.D s s < 1 :=
    lt_of_le_of_lt (Finset.single_le_sum (fun p _ => hS.2.1 s p) (Finset.mem_univ s)) (hS.2.2 s)
  have hden : 0 < 1 - S.D s s := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact add_pos_of_pos_of_nonneg (hS.1 q) (mul_nonneg (good_coeff S hS q s) (hS.1 s).le)
  · intro q p
    change 0 ≤ if p = s then 0 else S.D q p + S.D q s / (1 - S.D s s) * S.D s p
    split
    · rfl
    · exact add_nonneg (hS.2.1 q p) (mul_nonneg (good_coeff S hS q s) (hS.2.1 s p))
  · intro q
    let c := S.D q s / (1 - S.D s s)
    have hrow : ∑ p, (S.reduce s).D q p = ∑ p, S.D q p + c * (∑ p, S.D s p - 1) := by
      have he : ∑ p, (S.reduce s).D q p =
          ∑ p ∈ Finset.univ.erase s, (S.D q p + c * S.D s p) := by
        simp only [Stage.reduce]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
        simp only [ite_true, add_zero]
        apply Finset.sum_congr rfl
        intro p hp
        rw [if_neg (Finset.mem_erase.mp hp).1]
      rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hqsum := Finset.sum_erase_add (Finset.univ : Finset (Σ i, X i)) (S.D q) (Finset.mem_univ s)
      have hssum := Finset.sum_erase_add (Finset.univ : Finset (Σ i, X i)) (S.D s) (Finset.mem_univ s)
      have hcid : c * (1 - S.D s s) = S.D q s := by
        dsimp [c]; exact div_mul_cancel₀ _ hden.ne'
      have hscaled := congrArg (fun x : ℝ => c * x) hssum
      nlinarith
    rw [hrow]
    have hc : 0 ≤ c := good_coeff S hS q s
    have hneg : c * (∑ p, S.D s p - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc (by linarith [hS.2.2 s])
    linarith [hS.2.2 q]

#print axioms good_reduce

private lemma duration_formula (β T : ℝ) (hβ : 0 < β) :
    (∫ t in (0 : ℝ)..T, Real.exp (-(β * t))) = (1 - Real.exp (-(β * T))) / β := by
  have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.exp) (a := 0) (b := T) (-β)
  simp only [mul_zero, integral_exp, Real.exp_zero, neg_mul] at h
  apply (eq_div_iff hβ.ne').mpr
  nlinarith

#print axioms duration_formula

open MeasureTheory in
private lemma initial_good {n : ℕ} {X : Fin n → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X) : Good B.initStage := by
  classical
  have hdata (q : Σ i, X i) :
      0 < B.discDuration q ∧ (∀ p, 0 ≤ B.discKernel q p) ∧ ∑ p, B.discKernel q p < 1 := by
    let μ := B.law q.1 q.2
    letI : IsProbabilityMeasure μ := B.isProb q.1 q.2
    let e : ℝ × ℝ × X q.1 → ℝ := fun ω => Real.exp (-(B.β * ω.1))
    have hme : Measurable e := by dsimp [e]; fun_prop
    have he_le : ∀ᵐ ω ∂μ, e ω ≤ 1 := by
      filter_upwards [B.T_nonneg q.1 q.2] with ω hω
      dsimp [e]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg B.β_pos.le hω))
    have he_int : Integrable e μ := by
      apply (integrable_const (1 : ℝ)).mono' hme.aestronglyMeasurable
      filter_upwards [he_le] with ω hω
      simpa [e, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hω
    have hg_int : Integrable (fun ω => 1 - e ω) μ := (integrable_const 1).sub he_int
    have hg_nonneg : ∀ᵐ ω ∂μ, 0 ≤ 1 - e ω := by
      filter_upwards [he_le] with ω hω; linarith
    have hg_pos : 0 < ∫ ω, 1 - e ω ∂μ := by
      apply (integral_pos_iff_support_of_nonneg_ae hg_nonneg hg_int).mpr
      apply lt_of_lt_of_le (B.T_pos q.1 q.2)
      apply measure_mono
      intro ω hω
      have he : e ω < 1 := by
        dsimp [e]
        exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos B.β_pos hω))
      exact ne_of_gt (sub_pos.mpr he)
    have hk_int (p : Σ i, X i) :
        Integrable (fun ω : ℝ × ℝ × X q.1 => e ω * if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then 1 else 0) μ := by
      have hi : Measurable (fun ω : ℝ × ℝ × X q.1 =>
          if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then (1 : ℝ) else 0) := by
        exact (measurable_of_countable (f := fun x : X q.1 =>
          if (⟨q.1, x⟩ : Σ i, X i) = p then (1 : ℝ) else 0)).comp measurable_snd.snd
      apply he_int.mono' (hme.mul hi).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun ω => by
        change ‖e ω * (if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then 1 else 0)‖ ≤ e ω
        split
        · simp [e, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
        · simp only [mul_zero, norm_zero]
          exact (Real.exp_pos _).le
    refine ⟨?_, ?_, ?_⟩
    · unfold SemiMarkovBandit.discDuration
      simp_rw [duration_formula B.β _ B.β_pos]
      rw [integral_div]
      exact div_pos hg_pos B.β_pos
    · intro p
      unfold SemiMarkovBandit.discKernel
      apply integral_nonneg
      intro ω
      exact mul_nonneg (Real.exp_pos _).le (by split <;> norm_num)
    · unfold SemiMarkovBandit.discKernel
      change (∑ p, ∫ ω, e ω * (if (⟨q.1, ω.2.2⟩ : Σ i, X i) = p then 1 else 0) ∂μ) < 1
      rw [← integral_finset_sum _ (fun p _ => hk_int p)]
      simp_rw [← Finset.mul_sum]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_one]
      have hh := integral_sub (integrable_const (1 : ℝ) (μ := μ)) he_int
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
      linarith
  exact ⟨fun q => (hdata q).1, fun q => (hdata q).2.1, fun q => (hdata q).2.2⟩

#print axioms initial_good


/-- Proof of Theorem 2.2 of Tsitsiklis (1994), p. 198: along a run of the index algorithm the
indices do not increase; a state picked next never has a larger index than the state picked
before it, `γ(s*) ≥ γ(q*)`. -/
theorem solution {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (k : ℕ) (hk : k + 1 < seq.length) :
    γ seq[k + 1] ≤ γ seq[k] := by
  have hfold (S : Stage n X) (hS : Good S) (L : List (Σ i, X i)) :
      Good (L.foldl Stage.reduce S) := by
    induction L generalizing S with
    | nil => exact hS
    | cons s L ih => exact ih _ (good_reduce S hS s)
  have hg (j : ℕ) : Good (B.stageAfter (seq.take j)) :=
    hfold B.initStage (initial_good B) _
  apply index_antitone_of_stage_bounds B seq γ hrun
  · exact fun j q => (hg j).1 q
  · exact fun j q s => good_coeff _ (hg j) q s


#print axioms solution
