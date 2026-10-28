-- Prove2me | solution 1 for SeqRankAgg.Optimality.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T15:59:44.52604+00:00
-- url     : https://prove2.me/submissions/e62053fc-5ab5-4385-a39e-8f907b4fde79

import Mathlib

namespace Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology unitInterval

namespace AzumaAudit

lemma exp_affine_le_of_nonpos_nonneg
    {a b t : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (hab : a ≤ b) :
    (b / (b - a)) * Real.exp (t * a) + ((-a) / (b - a)) * Real.exp (t * b)
      ≤ Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · let p : I := ⟨(-a) / (b - a), by
      constructor
      · exact div_nonneg (neg_nonneg.mpr ha) (sub_nonneg.mpr hab)
      · rw [div_le_one (sub_pos.mpr hlt)]
        linarith⟩
    let X : Bool → ℝ := fun z => if z then b else a
    let μ : Measure Bool := Ber(true, false, p)
    have hX : AEMeasurable X μ := by fun_prop
    have hbX : ∀ᵐ z ∂μ, X z ∈ Set.Icc a b := by
      filter_upwards with z
      by_cases hz : z <;> simp [X, hz, hab]
    have hInt : ∫ z, X z ∂μ = 0 := by
      rw [integral_bernoulliMeasure]
      simp only [X, if_true, smul_eq_mul]
      change (p : ℝ) * b + (1 - (p : ℝ)) * a = 0
      have hpval : (p : ℝ) = (-a) / (b - a) := rfl
      rw [hpval]
      field_simp [sub_ne_zero.mpr hlt.ne']
      ring
    have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := X) (μ := μ) (a := a) (b := b) hX hbX hInt
    have hm := hsub.mgf_le t
    have hmgf : mgf X μ t =
        (b / (b - a)) * Real.exp (t * a) + ((-a) / (b - a)) * Real.exp (t * b) := by
      rw [mgf, integral_bernoulliMeasure]
      simp only [X, if_true, smul_eq_mul]
      change (p : ℝ) * Real.exp (t * b) +
        (1 - (p : ℝ)) * Real.exp (t * a) = _
      have hpval : (p : ℝ) = (-a) / (b - a) := rfl
      rw [hpval]
      field_simp [sub_ne_zero.mpr hlt.ne']
      ring
    rw [hmgf] at hm
    convert hm using 1
    congr 1
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
    ring
  · subst b
    have ha0 : a = 0 := le_antisymm ha hb
    subst a
    norm_num

lemma exp_chord_le {a b x t : ℝ} (hx : x ∈ Set.Icc a b) (hab : a < b) :
    Real.exp (t * x) ≤
      ((b - x) / (b - a)) * Real.exp (t * a) +
      ((x - a) / (b - a)) * Real.exp (t * b) := by
  have hα : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hab.le)
  have hβ : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le)
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  have harg : ((b - x) / (b - a)) * (t * a) + ((x - a) / (b - a)) * (t * b) = t * x := by
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  have h := convexOn_exp.2 (Set.mem_univ (t * a)) (Set.mem_univ (t * b)) hα hβ hsum
  simpa only [smul_eq_mul, harg] using h

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma condExp_exp_le_of_mem_Icc_of_condExp_eq_zero
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (X : Ω → ℝ) {a b t : ℝ}
    (hX : AEMeasurable X P) (hXint : Integrable X P)
    (hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc a b)
    (ha : a ≤ 0) (hbb : 0 ≤ b)
    (hmean : P[X | m] =ᵐ[P] 0) :
    P[(fun ω => Real.exp (t * X ω)) | m] ≤ᵐ[P]
      (fun _ => Real.exp (t ^ 2 * (b - a) ^ 2 / 8)) := by
  have hab : a ≤ b := le_trans ha hbb
  by_cases hlt : a < b
  · have hExpInt : Integrable (fun ω => Real.exp (t * X ω)) P :=
      integrable_exp_mul_of_mem_Icc hX hb
    let c : ℝ := (Real.exp (t * b) - Real.exp (t * a)) / (b - a)
    let d : ℝ := (b * Real.exp (t * a) - a * Real.exp (t * b)) / (b - a)
    have hRint : Integrable (c • X + fun _ => d) P :=
      (hXint.smul c).add (integrable_const d)
    have hchord : (fun ω => Real.exp (t * X ω)) ≤ᵐ[P] (c • X + fun _ => d) := by
      filter_upwards [hb] with ω hω
      have h := exp_chord_le (t := t) hω hlt
      convert h using 1
      · simp only [c, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp [sub_ne_zero.mpr hlt.ne']
        ring
    have hmono : P[(fun ω => Real.exp (t * X ω)) | m] ≤ᵐ[P]
        P[(c • X + fun _ => d) | m] :=
      condExp_mono hExpInt hRint hchord
    have hlin : P[(c • X + fun _ => d) | m] =ᵐ[P] (fun _ => d) := by
      calc
        P[(c • X + fun _ => d) | m]
            =ᵐ[P] P[c • X | m] + P[(fun _ => d) | m] :=
              condExp_add (hXint.smul c) (integrable_const d) m
        _ =ᵐ[P] c • P[X | m] + (fun _ => d) := by
              simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
                (condExp_smul c X m).add (EventuallyEq.of_eq (condExp_const hm d))
        _ =ᵐ[P] (fun _ => d) := by
              filter_upwards [hmean] with ω hω
              simp [hω]
    have hconst : d ≤ Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
      have hscalar := exp_affine_le_of_nonpos_nonneg ha hbb hab (t := t)
      convert hscalar using 1
      simp only [d]
      field_simp [sub_ne_zero.mpr hlt.ne']
      ring
    refine hmono.trans ?_
    filter_upwards [hlin] with ω hω
    rw [hω]
    exact hconst
  · have heq : a = b := le_antisymm hab (le_of_not_gt hlt)
    have ha0 : a = 0 := by
      apply le_antisymm ha
      simpa only [← heq] using hbb
    have hb0 : b = 0 := by
      rw [← heq, ha0]
    subst a
    subst b
    have hXzero : X =ᵐ[P] (fun _ => 0) := by
      filter_upwards [hb] with ω hω
      simpa using hω
    have hexp : (fun ω => Real.exp (t * X ω)) =ᵐ[P] (fun _ => 1) := by
      filter_upwards [hXzero] with ω hω
      simp [hω]
    have hEq : P[(fun ω => Real.exp (t * X ω)) | m] =ᵐ[P] (fun _ => 1) :=
      (condExp_congr_ae hexp).trans (EventuallyEq.of_eq (condExp_const hm (1 : ℝ)))
    simpa using hEq.le

lemma nonpos_nonneg_of_condExp_eq_zero
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (X : Ω → ℝ) {a b : ℝ}
    (hXint : Integrable X P) (hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc a b)
    (hmean : P[X | m] =ᵐ[P] 0) :
    a ≤ 0 ∧ 0 ≤ b := by
  have hIntZero : ∫ ω, X ω ∂P = 0 := by
    calc
      ∫ ω, X ω ∂P = ∫ ω, P[X | m] ω ∂P := (integral_condExp hm).symm
      _ = ∫ ω, (0 : ℝ) ∂P := integral_congr_ae hmean
      _ = 0 := by simp
  constructor
  · have hge : ∀ᵐ ω ∂P, a ≤ X ω := hb.mono fun ω hω => hω.1
    have h := integral_mono_ae (integrable_const a) hXint hge
    simpa [hIntZero] using h
  · have hle : ∀ᵐ ω ∂P, X ω ≤ b := hb.mono fun ω hω => hω.2
    have h := integral_mono_ae hXint (integrable_const b) hle
    simpa [hIntZero] using h

variable {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}

lemma condExp_increment_eq_zero (hM : Martingale M ℱ P) (k : ℕ) :
    P[M (k + 1) - M k | ℱ k] =ᵐ[P] 0 := by
  have hsub := condExp_sub (hM.integrable (k + 1)) (hM.integrable k) (ℱ k)
  have hMk : P[M k | ℱ k] = M k :=
    condExp_of_stronglyMeasurable (ℱ.le k) (hM.stronglyMeasurable k) (hM.integrable k)
  calc
    P[M (k + 1) - M k | ℱ k]
        =ᵐ[P] P[M (k + 1) | ℱ k] - P[M k | ℱ k] := hsub
    _ =ᵐ[P] M k - M k := (hM.condExp_ae_eq (Nat.le_succ k)).sub (EventuallyEq.of_eq hMk)
    _ =ᵐ[P] 0 := by
      filter_upwards with ω
      simp


-- integrability of exp(lam M k) and terminal mgf bound
lemma integral_exp_mul_le
    (hM : Martingale M ℱ P) (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (a b : ℕ → ℝ)
    (hinc : ∀ k : ℕ, ∀ᵐ ω ∂P, M (k + 1) ω - M k ω ∈ Set.Icc (a (k + 1)) (b (k + 1)))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ n : ℕ,
      Integrable (fun ω => Real.exp (lam * M n ω)) P ∧
      ∫ ω, Real.exp (lam * M n ω) ∂P ≤
        Real.exp ((lam ^ 2 / 8) * ∑ i ∈ Finset.Icc 1 n, (b i - a i) ^ 2) := by
  intro n
  induction n with
  | zero =>
      have hExp0 : (fun ω => Real.exp (lam * M 0 ω)) =ᵐ[P] (fun _ => 1) := by
        filter_upwards [hM0] with ω hω
        simp [hω]
      constructor
      · exact (integrable_const (1 : ℝ)).congr hExp0.symm
      · have hIntEq : ∫ ω, Real.exp (lam * M 0 ω) ∂P = 1 := by
          calc
            ∫ ω, Real.exp (lam * M 0 ω) ∂P = ∫ _ : Ω, (1 : ℝ) ∂P := integral_congr_ae hExp0
            _ = 1 := by simp
        rw [hIntEq]
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
        norm_num
  | succ n ih =>
      let Δ : Ω → ℝ := M (n + 1) - M n
      let D : ℝ := b (n + 1) - a (n + 1)
      have hbΔ : ∀ᵐ ω ∂P, Δ ω ∈ Set.Icc (a (n + 1)) (b (n + 1)) := by
        simpa [Δ] using hinc n
      have hΔint : Integrable Δ P := (hM.integrable (n + 1)).sub (hM.integrable n)
      have hΔmeas : AEMeasurable Δ P := by
        have h1 : StronglyMeasurable (M (n + 1)) :=
          (hM.stronglyMeasurable (n + 1)).mono (ℱ.le (n + 1))
        have h2 : StronglyMeasurable (M n) :=
          (hM.stronglyMeasurable n).mono (ℱ.le n)
        simpa [Δ] using (h1.sub h2).aemeasurable
      have hmean : P[Δ | ℱ n] =ᵐ[P] 0 := by
        simpa [Δ] using condExp_increment_eq_zero (P := P) hM n
      have hsign : a (n + 1) ≤ 0 ∧ 0 ≤ b (n + 1) :=
        nonpos_nonneg_of_condExp_eq_zero (P := P) (m := ℱ n) (ℱ.le n) Δ hΔint hbΔ hmean
      have hcond : P[(fun ω => Real.exp (lam * Δ ω)) | ℱ n] ≤ᵐ[P]
          (fun _ => Real.exp (lam ^ 2 * D ^ 2 / 8)) := by
        simpa [D] using condExp_exp_le_of_mem_Icc_of_condExp_eq_zero
          (P := P) (m := ℱ n) (ℱ.le n) Δ hΔmeas hΔint hbΔ hsign.1 hsign.2 hmean (t := lam)
      have hExpΔint : Integrable (fun ω => Real.exp (lam * Δ ω)) P :=
        integrable_exp_mul_of_mem_Icc hΔmeas hbΔ
      have hExpΔbound : ∀ᵐ ω ∂P, ‖Real.exp (lam * Δ ω)‖ ≤ Real.exp (lam * b (n + 1)) := by
        filter_upwards [hbΔ] with ω hω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.2 hlam)
      have hExpNextInt : Integrable (fun ω => Real.exp (lam * M (n + 1) ω)) P := by
        have hmul : Integrable (fun ω => Real.exp (lam * M n ω) * Real.exp (lam * Δ ω)) P :=
          ih.1.mul_bdd hExpΔint.1 hExpΔbound
        refine hmul.congr ?_
        filter_upwards with ω
        rw [← Real.exp_add]
        congr 1
        simp [Δ]
        ring
      have hf_sm : StronglyMeasurable[ℱ n] (fun ω => Real.exp (lam * M n ω)) :=
        Real.continuous_exp.comp_stronglyMeasurable ((hM.stronglyMeasurable n).const_mul lam)
      have hprodInt : Integrable (fun ω => Real.exp (lam * M n ω) * Real.exp (lam * Δ ω)) P :=
        ih.1.mul_bdd hExpΔint.1 hExpΔbound
      have hpull : P[(fun ω => Real.exp (lam * M n ω) * Real.exp (lam * Δ ω)) | ℱ n] =ᵐ[P]
          (fun ω => Real.exp (lam * M n ω) * P[(fun ω => Real.exp (lam * Δ ω)) | ℱ n] ω) :=
        condExp_mul_of_aestronglyMeasurable_left hf_sm.aestronglyMeasurable hprodInt hExpΔint
      have hcondNext : P[(fun ω => Real.exp (lam * M (n + 1) ω)) | ℱ n] ≤ᵐ[P]
          (fun ω => Real.exp (lam * M n ω) * Real.exp (lam ^ 2 * D ^ 2 / 8)) := by
        calc
          P[(fun ω => Real.exp (lam * M (n + 1) ω)) | ℱ n]
              =ᵐ[P] P[(fun ω => Real.exp (lam * M n ω) * Real.exp (lam * Δ ω)) | ℱ n] := by
                apply condExp_congr_ae
                filter_upwards with ω
                rw [← Real.exp_add]
                congr 1
                simp [Δ]
                ring
          _ =ᵐ[P] (fun ω => Real.exp (lam * M n ω) * P[(fun ω => Real.exp (lam * Δ ω)) | ℱ n] ω) := hpull
          _ ≤ᵐ[P] (fun ω => Real.exp (lam * M n ω) * Real.exp (lam ^ 2 * D ^ 2 / 8)) := by
                filter_upwards [hcond] with ω hω
                exact mul_le_mul_of_nonneg_left hω (Real.exp_pos _).le
      have hIntIneq : ∫ ω, Real.exp (lam * M (n + 1) ω) ∂P ≤
          ∫ ω, Real.exp (lam * M n ω) * Real.exp (lam ^ 2 * D ^ 2 / 8) ∂P := by
        calc
          ∫ ω, Real.exp (lam * M (n + 1) ω) ∂P
              = ∫ ω, P[(fun ω => Real.exp (lam * M (n + 1) ω)) | ℱ n] ω ∂P :=
                (integral_condExp (ℱ.le n)).symm
          _ ≤ ∫ ω, Real.exp (lam * M n ω) * Real.exp (lam ^ 2 * D ^ 2 / 8) ∂P :=
                integral_mono_ae integrable_condExp (ih.1.mul_const _) hcondNext
      have hsumstep : ∑ i ∈ Finset.Icc 1 (n + 1), (b i - a i) ^ 2 =
          (∑ i ∈ Finset.Icc 1 n, (b i - a i) ^ 2) + D ^ 2 := by
        rw [Finset.sum_Icc_succ_top (by omega)]
      constructor
      · exact hExpNextInt
      · calc
          ∫ ω, Real.exp (lam * M (n + 1) ω) ∂P
              ≤ ∫ ω, Real.exp (lam * M n ω) * Real.exp (lam ^ 2 * D ^ 2 / 8) ∂P := hIntIneq
          _ = (∫ ω, Real.exp (lam * M n ω) ∂P) * Real.exp (lam ^ 2 * D ^ 2 / 8) := by
                rw [integral_mul_const]
          _ ≤ Real.exp ((lam ^ 2 / 8) * ∑ i ∈ Finset.Icc 1 n, (b i - a i) ^ 2) *
                Real.exp (lam ^ 2 * D ^ 2 / 8) := by
                gcongr
                exact ih.2
          _ = Real.exp ((lam ^ 2 / 8) * ∑ i ∈ Finset.Icc 1 (n + 1), (b i - a i) ^ 2) := by
                rw [← Real.exp_add, hsumstep]
                congr 1
                ring

lemma submartingale_exp
    (hM : Martingale M ℱ P) (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (a b : ℕ → ℝ)
    (hinc : ∀ k : ℕ, ∀ᵐ ω ∂P, M (k + 1) ω - M k ω ∈ Set.Icc (a (k + 1)) (b (k + 1)))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Submartingale (fun k ω => Real.exp (lam * M k ω)) ℱ P := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact Real.continuous_exp.comp_stronglyMeasurable ((hM.stronglyMeasurable k).const_mul lam)
  · intro i j hij
    have hfj_int : Integrable (fun ω => lam * M j ω) P := (hM.integrable j).const_mul lam
    have hexp_int : Integrable (fun ω => Real.exp (lam * M j ω)) P :=
      (integral_exp_mul_le (P := P) hM hM0 a b hinc hlam j).1
    have hJ := convexOn_exp.map_condExp_le_univ (μ := P) (m := ℱ i) (ℱ.le i)
      Real.continuous_exp.lowerSemicontinuous hfj_int hexp_int
    have hsmul_eq : (lam • M j) =ᵐ[P] (fun ω => lam * M j ω) := by
      filter_upwards with ω
      simp [Pi.smul_apply, smul_eq_mul]
    have hcond_lam : P[(fun ω => lam * M j ω) | ℱ i] =ᵐ[P] (fun ω => lam * M i ω) := by
      calc
        P[(fun ω => lam * M j ω) | ℱ i] =ᵐ[P] P[lam • M j | ℱ i] :=
          (condExp_congr_ae hsmul_eq).symm
        _ =ᵐ[P] lam • P[M j | ℱ i] := condExp_smul (μ := P) lam (M j) (ℱ i)
        _ =ᵐ[P] lam • M i := (hM.condExp_ae_eq hij).const_smul lam
        _ =ᵐ[P] (fun ω => lam * M i ω) := by
          filter_upwards with ω
          simp [Pi.smul_apply, smul_eq_mul]
    calc
      (fun ω => Real.exp (lam * M i ω))
          =ᵐ[P] (fun ω => Real.exp (P[(fun ω => lam * M j ω) | ℱ i] ω)) := by
            filter_upwards [hcond_lam] with ω hω
            rw [hω]
      _ ≤ᵐ[P] P[(fun ω => Real.exp (lam * M j ω)) | ℱ i] := by
            have hJright : P[Real.exp ∘ (fun ω => lam * M j ω) | ℱ i] =ᵐ[P]
                P[(fun ω => Real.exp (lam * M j ω)) | ℱ i] := by
              apply condExp_congr_ae
              filter_upwards with ω
              rfl
            have hJ' : (fun ω => Real.exp (P[(fun ω => lam * M j ω) | ℱ i] ω)) ≤ᵐ[P]
                P[(fun ω => Real.exp (lam * M j ω)) | ℱ i] :=
              hJ.trans_eq hJright
            exact hJ' 
  · intro k
    exact (integral_exp_mul_le (P := P) hM hM0 a b hinc hlam k).1

omit [IsProbabilityMeasure P] in
lemma doob_event_ae_eq
    (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0) {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    {ω | Real.exp (lam * t) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => Real.exp (lam * M k ω))} =ᵐ[P]
      {ω | ∃ k ∈ Finset.Icc 1 n, t ≤ M k ω} := by
  filter_upwards [hM0] with ω hω0
  apply propext
  simp only [Finset.le_sup'_iff, Finset.mem_range]
  constructor
  · rintro ⟨k, hklt, hkexp⟩
    have hk_le : t ≤ M k ω := by
      rw [Real.exp_le_exp] at hkexp
      nlinarith [hlam, hkexp]
    by_cases hk0 : k = 0
    · subst k
      rw [hω0] at hk_le
      linarith
    · exact ⟨k, by rw [Finset.mem_Icc]; omega, hk_le⟩
  · rintro ⟨k, hkIcc, hk⟩
    refine ⟨k, ?_, ?_⟩
    · rw [Finset.mem_Icc] at hkIcc
      omega
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk hlam.le)

theorem lemma_8_scratch {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P)
    (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (a b : ℕ → ℝ)
    (hinc : ∀ k : ℕ, ∀ᵐ ω ∂P, M (k + 1) ω - M k ω ∈ Set.Icc (a (k + 1)) (b (k + 1)))
    (n : ℕ) (_hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    P {ω | ∃ k ∈ Finset.Icc 1 n, t ≤ M k ω} ≤
      ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / ∑ i ∈ Finset.Icc 1 n, (b i - a i) ^ 2))) := by
  let S : ℝ := ∑ i ∈ Finset.Icc 1 n, (b i - a i) ^ 2
  let T : Set Ω := {ω | ∃ k ∈ Finset.Icc 1 n, t ≤ M k ω}
  by_cases hS : S = 0
  · have hle1 : P T ≤ 1 := by
      calc
        P T ≤ P Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    simpa [T, S, hS] using hle1
  · have hSpos : 0 < S := lt_of_le_of_ne (by
      dsimp [S]
      exact Finset.sum_nonneg fun i hi => sq_nonneg _) (Ne.symm hS)
    let lam : ℝ := 4 * t / S
    have hlam : 0 < lam := by
      dsimp [lam]
      positivity
    let Y : ℕ → Ω → ℝ := fun k ω => Real.exp (lam * M k ω)
    have hsubY : Submartingale Y ℱ P := by
      simpa [Y] using submartingale_exp (P := P) hM hM0 a b hinc hlam.le
    have hnonneg : 0 ≤ Y := by
      intro k ω
      exact (Real.exp_pos _).le
    let ε : ℝ≥0 := ⟨Real.exp (lam * t), (Real.exp_pos _).le⟩
    let E : Set Ω := {ω | (ε : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => Y k ω)}
    have hdoob := maximal_ineq (μ := P) (f := Y) (𝒢 := ℱ) hsubY hnonneg (ε := ε) n
    have hEeqT : E =ᵐ[P] T := by
      change {ω | Real.exp (lam * t) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => Real.exp (lam * M k ω))} =ᵐ[P]
        {ω | ∃ k ∈ Finset.Icc 1 n, t ≤ M k ω}
      exact doob_event_ae_eq (P := P) (M := M) hM0 hlam ht n
    have hdoobE : (ε : ℝ≥0∞) * P E ≤
        ENNReal.ofReal (∫ ω in E, Y n ω ∂P) := by
      simpa only [E, Y] using hdoob
    have hdoobT : (ε : ℝ≥0∞) * P T ≤
        ENNReal.ofReal (∫ ω in E, Y n ω ∂P) := by
      rw [show P E = P T from measure_congr hEeqT] at hdoobE
      exact hdoobE
    have hYint : Integrable (fun ω => Y n ω) P := by
      simpa [Y] using (integral_exp_mul_le (P := P) hM hM0 a b hinc hlam.le n).1
    have hYnonneg : 0 ≤ᵐ[P] (fun ω => Y n ω) :=
      Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
    have hsetIntLe : ∫ ω in E, Y n ω ∂P ≤ ∫ ω, Y n ω ∂P :=
      setIntegral_le_integral hYint hYnonneg
    have hfullIntLe : ∫ ω, Y n ω ∂P ≤ Real.exp ((lam ^ 2 / 8) * S) := by
      simpa [Y, S] using (integral_exp_mul_le (P := P) hM hM0 a b hinc hlam.le n).2
    have hIntLe : ∫ ω in E, Y n ω ∂P ≤ Real.exp ((lam ^ 2 / 8) * S) :=
      hsetIntLe.trans hfullIntLe
    have hdoobBound : (ε : ℝ≥0∞) * P T ≤ ENNReal.ofReal (Real.exp ((lam ^ 2 / 8) * S)) := by
      calc
        (ε : ℝ≥0∞) * P T ≤ ENNReal.ofReal (∫ ω in E, Y n ω ∂P) := hdoobT
        _ ≤ ENNReal.ofReal (Real.exp ((lam ^ 2 / 8) * S)) :=
          ENNReal.ofReal_le_ofReal hIntLe
    have hεeq : (ε : ℝ≥0∞) = ENNReal.ofReal (Real.exp (lam * t)) :=
      (ENNReal.ofReal_coe_nnreal (p := ε)).symm
    rw [hεeq] at hdoobBound
    have hεne0 : ENNReal.ofReal (Real.exp (lam * t)) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      positivity
    have hεnetop : ENNReal.ofReal (Real.exp (lam * t)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hPTle : P T ≤
        ENNReal.ofReal (Real.exp ((lam ^ 2 / 8) * S)) /
          ENNReal.ofReal (Real.exp (lam * t)) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hεne0) (Or.inl hεnetop)]
      simpa [mul_comm] using hdoobBound
    have hdiv : ENNReal.ofReal (Real.exp ((lam ^ 2 / 8) * S)) /
          ENNReal.ofReal (Real.exp (lam * t)) =
        ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / S))) := by
      rw [← ENNReal.ofReal_div_of_pos (x := Real.exp ((lam ^ 2 / 8) * S))
        (y := Real.exp (lam * t)) (Real.exp_pos _)]
      congr 1
      rw [← Real.exp_sub]
      congr 1
      dsimp [lam]
      field_simp [hSpos.ne']
      ring
    rw [hdiv] at hPTle
    simpa [T, S] using hPTle

end AzumaAudit

namespace SeqRankAgg.Optimality

theorem lemma_8 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P)
    (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (a b : ℕ → ℝ)
    (hinc : ∀ k : ℕ, ∀ᵐ ω ∂P, M (k + 1) ω - M k ω ∈ Set.Icc (a (k + 1)) (b (k + 1)))
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    P {ω | ∃ k ∈ Finset.Icc 1 n, t ≤ M k ω} ≤
      ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / ∑ i ∈ Finset.Icc 1 n, (b i - a i) ^ 2))) := by
  exact AzumaAudit.lemma_8_scratch P ℱ M hM hM0 a b hinc n hn t ht

end SeqRankAgg.Optimality

end Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P)
    (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (a b : ℕ → ℝ)
    (hinc : ∀ k : ℕ, ∀ᵐ ω ∂P, M (k + 1) ω - M k ω ∈ Set.Icc (a (k + 1)) (b (k + 1)))
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    P {ω | ∃ k ∈ Finset.Icc 1 n, t ≤ M k ω} ≤
      ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / ∑ i ∈ Finset.Icc 1 n, (b i - a i) ^ 2))) := by
  exact Prove2SwarmSubmission.SeqRankAgg.Optimality.lemma_8 P ℱ M hM hM0 a b hinc n hn t ht
