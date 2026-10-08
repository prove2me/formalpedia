-- Prove2me | solution 1 for TalagrandConc.SKModel.second_moment
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:49:19.380865+00:00
-- url     : https://prove2.me/submissions/8fd533f5-4886-4dd4-ae48-16e9efe72d9f

import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic



namespace TalagrandConc.SKModel

open MeasureTheory

/-- cubic Taylor lower bound for exp, valid for all reals -/
lemma exp_ge_cubic (u : ℝ) : 1 + u + u ^ 2 / 2 + u ^ 3 / 6 ≤ Real.exp u := by
  rcases le_or_gt 0 u with hu | hu
  · have := Real.sum_le_exp_of_nonneg hu 4
    simp [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  · -- g v = exp v * (1 - v + v^2/2 - v^3/6) is antitone on [0, ∞)
    set g : ℝ → ℝ := fun v => Real.exp v * (1 - v + v ^ 2 / 2 - v ^ 3 / 6) with hg
    have hderiv : ∀ v, HasDerivAt g (-(Real.exp v * v ^ 3 / 6)) v := by
      intro v
      have h1 : HasDerivAt (fun v => Real.exp v * (1 - v + v ^ 2 / 2 - v ^ 3 / 6))
          (Real.exp v * (1 - v + v ^ 2 / 2 - v ^ 3 / 6) +
            Real.exp v * (-1 + ((2:ℕ) : ℝ) * v ^ (2 - 1) / 2 - ((3:ℕ) : ℝ) * v ^ (3 - 1) / 6)) v :=
        (Real.hasDerivAt_exp v).mul
          (((((hasDerivAt_id v).const_sub 1).add ((hasDerivAt_pow 2 v).div_const 2)).sub
            ((hasDerivAt_pow 3 v).div_const 6)))
      rw [hg]
      exact h1.congr_deriv (by norm_num; ring)
    have hanti : AntitoneOn g (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · exact (continuous_iff_continuousAt.mpr fun v => (hderiv v).continuousAt).continuousOn
      · intro v _; exact (hderiv v).differentiableAt.differentiableWithinAt
      · intro v hv
        rw [(hderiv v).deriv]
        simp only [interior_Ici, Set.mem_Ioi] at hv
        have he := Real.exp_pos v
        have hv3 : 0 ≤ v ^ 3 := by positivity
        nlinarith [mul_nonneg he.le hv3]
    have h0 : g (-u) ≤ g 0 := hanti (by simp) (by simp; linarith) (by linarith)
    simp only [hg, Real.exp_zero] at h0
    have hpos := Real.exp_pos (-u)
    have hexp : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    -- h0 : exp(-u) * (1 + u + u^2/2 + u^3/6) ≤ 1
    have h2 : Real.exp (-u) * (1 + u + u ^ 2 / 2 + u ^ 3 / 6) ≤ 1 := by
      have : (1 - -u + (-u) ^ 2 / 2 - (-u) ^ 3 / 6) = 1 + u + u ^ 2 / 2 + u ^ 3 / 6 := by ring
      rw [this] at h0; linarith
    have h3 : Real.exp (-u) * (1 + u + u ^ 2 / 2 + u ^ 3 / 6) * Real.exp u ≤ 1 * Real.exp u :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_pos u).le
    calc 1 + u + u ^ 2 / 2 + u ^ 3 / 6
        = Real.exp (-u) * (1 + u + u ^ 2 / 2 + u ^ 3 / 6) * Real.exp u := by
          rw [mul_comm (Real.exp (-u)), mul_assoc, hexp, mul_one]
      _ ≤ Real.exp u := by linarith

/-- cubic Taylor upper bound with crude remainder, valid for all reals -/
lemma exp_le_cubic (u : ℝ) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 * Real.exp |u| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (u : ℂ) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Complex.norm_real,
    Real.norm_eq_abs] at h
  have h' : ‖((Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6) : ℝ) : ℂ)‖ ≤
      |u| ^ 4 * Real.exp |u| := by
    convert h using 2
    push_cast
    simp [Nat.factorial]
  rw [Complex.norm_real, Real.norm_eq_abs] at h'
  have := (abs_le.mp h').2
  have h4 : |u| ^ 4 = u ^ 4 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h4] at this
  linarith

lemma pow_four_le (x : ℝ) : x ^ 4 ≤ 6144 * Real.exp (|x| / 4) := by
  have := Real.pow_div_factorial_le_exp (x := |x| / 4) (by positivity) 4
  have h4 : |x| ^ 4 = x ^ 4 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  simp [Nat.factorial] at this
  rw [div_pow] at this
  nlinarith

lemma card_interaction (N : ℕ) : (Fintype.card (Interaction N) : ℝ) = N * (N - 1) / 2 := by
  classical
  have hA : Fintype.card (Interaction N) =
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)).card :=
    Fintype.card_subtype _
  have hB : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)).card =
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1)).card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp; simpa using hp
    · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq; refine ⟨(q.2, q.1), ?_, ?_⟩ <;> simpa using hq
  have hU : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)) ∪
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1)) =
      (Finset.univ : Finset (Fin N)).offDiag := by
    ext p; simp [Finset.mem_offDiag]
  have hD : Disjoint ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2))
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_filter]; intro p _ h1 h2; exact absurd (h1.trans h2) (lt_irrefl _)
  have hc := Finset.card_union_of_disjoint hD
  rw [hU, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hc
  have hN : N ≤ N * N := Nat.le_mul_self N
  have : 2 * Fintype.card (Interaction N) = N * N - N := by rw [hA]; omega
  have h2 : (2 : ℝ) * Fintype.card (Interaction N) = N * N - N := by
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, this, Nat.cast_sub hN, Nat.cast_mul]
  linarith

lemma exp_abs_le (x : ℝ) : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-x)]
  · rw [abs_of_neg hx]; linarith [Real.exp_pos x]

/-- the sign of the pair interaction -/
def sgn {N : ℕ} (ε : Fin N → Bool) (p : Interaction N) : ℝ := spin ε p.1.1 * spin ε p.1.2

lemma abs_spin' {N : ℕ} (ε : Fin N → Bool) (i : Fin N) : |spin ε i| = 1 := by
  unfold spin; split_ifs <;> simp

lemma abs_sgn {N : ℕ} (ε : Fin N → Bool) (p : Interaction N) : |sgn ε p| = 1 := by
  unfold sgn; rw [abs_mul, abs_spin', abs_spin', one_mul]

lemma sgn_sq {N : ℕ} (ε : Fin N → Bool) (p : Interaction N) : sgn ε p ^ 2 = 1 := by
  rw [← sq_abs, abs_sgn, one_pow]

lemma two_le_of_interaction {N : ℕ} (p : Interaction N) : 2 ≤ N := by
  have h1 := p.2
  have h2 := p.1.2.isLt
  have h3 := p.1.1.isLt
  omega

/-- the moment generating function of ν -/
noncomputable def phi (ν : Measure ℝ) (c : ℝ) : ℝ := ∫ x, Real.exp (c * x) ∂ν

lemma integrable_E (ν : Measure ℝ) (ht : LightTails ν) :
    Integrable (fun x => Real.exp x + Real.exp (-x)) ν := ht.1.add ht.2.1

lemma integrable_exp_mul (ν : Measure ℝ) (ht : LightTails ν) (c : ℝ) (hc : |c| ≤ 1) :
    Integrable (fun x => Real.exp (c * x)) ν := by
  refine (integrable_E ν ht).mono' ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : c * x ≤ |x| := by
      calc c * x ≤ |c * x| := le_abs_self _
        _ = |c| * |x| := abs_mul _ _
        _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        _ = |x| := one_mul _
    exact (Real.exp_le_exp.mpr h1).trans (exp_abs_le x)

lemma integrable_P (ν : Measure ℝ) [IsProbabilityMeasure ν] (hA : AdmissibleLaw ν) (c : ℝ) :
    Integrable (fun x => 1 + c * x + c ^ 2 * x ^ 2 / 2 + c ^ 3 * x ^ 3 / 6) ν := by
  have h1 : Integrable (fun _ : ℝ => (1:ℝ)) ν := integrable_const _
  have h2 : Integrable (fun x : ℝ => c * x) ν := hA.1.const_mul c
  have h3 : Integrable (fun x : ℝ => c ^ 2 * x ^ 2 / 2) ν := (hA.2.1.const_mul (c ^ 2)).div_const 2
  have h4 : Integrable (fun x : ℝ => c ^ 3 * x ^ 3 / 6) ν :=
    (hA.2.2.1.const_mul (c ^ 3)).div_const 6
  have h12 : Integrable (fun x : ℝ => 1 + c * x) ν := h1.add h2
  have h123 : Integrable (fun x : ℝ => 1 + c * x + c ^ 2 * x ^ 2 / 2) ν := h12.add h3
  exact h123.add h4

lemma integral_P (ν : Measure ℝ) [IsProbabilityMeasure ν] (hA : AdmissibleLaw ν) (c : ℝ) :
    ∫ x, (1 + c * x + c ^ 2 * x ^ 2 / 2 + c ^ 3 * x ^ 3 / 6) ∂ν = 1 + c ^ 2 / 2 := by
  have h1 : Integrable (fun _ : ℝ => (1:ℝ)) ν := integrable_const _
  have h2 : Integrable (fun x : ℝ => c * x) ν := hA.1.const_mul c
  have h3 : Integrable (fun x : ℝ => c ^ 2 * x ^ 2 / 2) ν := (hA.2.1.const_mul (c ^ 2)).div_const 2
  have h4 : Integrable (fun x : ℝ => c ^ 3 * x ^ 3 / 6) ν :=
    (hA.2.2.1.const_mul (c ^ 3)).div_const 6
  have h12 : Integrable (fun x : ℝ => 1 + c * x) ν := h1.add h2
  have h123 : Integrable (fun x : ℝ => 1 + c * x + c ^ 2 * x ^ 2 / 2) ν := h12.add h3
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2,
    integral_const, integral_const_mul, integral_div, integral_const_mul, integral_div,
    integral_const_mul, hA.2.2.2.1, hA.2.2.2.2.1, hA.2.2.2.2.2.1]
  simp

lemma phi_lower (ν : Measure ℝ) [IsProbabilityMeasure ν] (hA : AdmissibleLaw ν)
    (ht : LightTails ν) (c : ℝ) (hc : |c| ≤ 1) : 1 + c ^ 2 / 2 ≤ phi ν c := by
  rw [← integral_P ν hA c]
  apply integral_mono (integrable_P ν hA c) (integrable_exp_mul ν ht c hc)
  intro x
  have := exp_ge_cubic (c * x)
  simp only [mul_pow] at this
  simpa using this

lemma phi_upper (ν : Measure ℝ) [IsProbabilityMeasure ν] (hA : AdmissibleLaw ν)
    (ht : LightTails ν) (c : ℝ) (hc : |c| ≤ 3 / 4) :
    phi ν c ≤ 1 + c ^ 2 / 2 + 24576 * c ^ 4 := by
  have hc1 : |c| ≤ 1 := hc.trans (by norm_num)
  have hE : Integrable (fun x => 6144 * c ^ 4 * (Real.exp x + Real.exp (-x))) ν :=
    (integrable_E ν ht).const_mul _
  have hR : Integrable (fun x => (1 + c * x + c ^ 2 * x ^ 2 / 2 + c ^ 3 * x ^ 3 / 6) +
      6144 * c ^ 4 * (Real.exp x + Real.exp (-x))) ν :=
    (integrable_P ν hA c).add hE
  have hc4 : 0 ≤ c ^ 4 := by positivity
  calc phi ν c ≤ ∫ x, ((1 + c * x + c ^ 2 * x ^ 2 / 2 + c ^ 3 * x ^ 3 / 6) +
      6144 * c ^ 4 * (Real.exp x + Real.exp (-x))) ∂ν := by
        apply integral_mono (integrable_exp_mul ν ht c hc1) hR
        intro x
        have h1 := exp_le_cubic (c * x)
        simp only [mul_pow] at h1
        have h2 : x ^ 4 * Real.exp |c * x| ≤ 6144 * (Real.exp x + Real.exp (-x)) := by
          have h3 : Real.exp |c * x| ≤ Real.exp (3 / 4 * |x|) := by
            apply Real.exp_le_exp.mpr
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
          have h4 := pow_four_le x
          have h5 : 0 ≤ x ^ 4 := by positivity
          calc x ^ 4 * Real.exp |c * x| ≤ (6144 * Real.exp (|x| / 4)) * Real.exp (3 / 4 * |x|) :=
                mul_le_mul h4 h3 (Real.exp_pos _).le (by positivity)
            _ = 6144 * Real.exp |x| := by
                rw [mul_assoc, ← Real.exp_add]; congr 2; ring
            _ ≤ 6144 * (Real.exp x + Real.exp (-x)) :=
                mul_le_mul_of_nonneg_left (exp_abs_le x) (by norm_num)
        have h6 : c ^ 4 * x ^ 4 * Real.exp |c * x| ≤ c ^ 4 * (6144 * (Real.exp x + Real.exp (-x))) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hc4
        simp only
        linarith
    _ = 1 + c ^ 2 / 2 + 6144 * c ^ 4 * ((∫ x, Real.exp x ∂ν) + ∫ x, Real.exp (-x) ∂ν) := by
        rw [integral_add (integrable_P ν hA c) hE, integral_P ν hA c,
          integral_const_mul, integral_add ht.1 ht.2.1]
    _ ≤ 1 + c ^ 2 / 2 + 24576 * c ^ 4 := by
        have := ht.2.2.1
        have := ht.2.2.2
        nlinarith

lemma Z_eq (N : ℕ) (β : ℝ) (h : Interaction N → ℝ) :
    partitionFunction N β h =
      ((2 : ℝ) ^ N)⁻¹ * ∑ ε : Fin N → Bool, ∏ p : Interaction N,
        Real.exp (β / Real.sqrt N * sgn ε p * h p) := by
  unfold partitionFunction
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro p _
  congr 1
  unfold sgn; ring

lemma lam_abs_le (N : ℕ) (β : ℝ) (hN : 1 ≤ N) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    |β / Real.sqrt N| ≤ 1 := by
  have hs : 1 ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; norm_num; exact_mod_cast hN
  rw [abs_of_pos (by positivity), div_le_one (by linarith)]
  linarith

lemma lam_le_34 (N : ℕ) (β : ℝ) (hN : 2 ≤ N) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    |β / Real.sqrt N| ≤ 3 / 4 := by
  have hs : 4 / 3 ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have : (2:ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  rw [abs_of_pos (by positivity), div_le_iff₀ (by linarith)]
  nlinarith

lemma integrable_Z (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (β : ℝ)
    (hN : 1 ≤ N) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : LightTails ν) :
    Integrable (partitionFunction N β) (couplingLaw N ν) := by
  have hZ : partitionFunction N β = fun h => ((2 : ℝ) ^ N)⁻¹ * ∑ ε : Fin N → Bool,
      ∏ p : Interaction N, Real.exp (β / Real.sqrt N * sgn ε p * h p) := funext (Z_eq N β)
  rw [hZ]
  unfold couplingLaw
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro ε _
  apply Integrable.fintype_prod (f := fun p x => Real.exp (β / Real.sqrt N * sgn ε p * x))
  intro p
  apply integrable_exp_mul ν ht
  rw [abs_mul, abs_sgn, mul_one]
  exact lam_abs_le N β hN hβ hβ1

lemma integral_Z (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (β : ℝ)
    (hN : 1 ≤ N) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : LightTails ν) :
    ∫ h, partitionFunction N β h ∂(couplingLaw N ν) =
      ((2 : ℝ) ^ N)⁻¹ * ∑ ε : Fin N → Bool, ∏ p : Interaction N,
        phi ν (β / Real.sqrt N * sgn ε p) := by
  have hZ : partitionFunction N β = fun h => ((2 : ℝ) ^ N)⁻¹ * ∑ ε : Fin N → Bool,
      ∏ p : Interaction N, Real.exp (β / Real.sqrt N * sgn ε p * h p) := funext (Z_eq N β)
  rw [hZ]
  unfold couplingLaw
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro ε _
    exact integral_fintype_prod_eq_prod (fun p x => Real.exp (β / Real.sqrt N * sgn ε p * x))
  · intro ε _
    apply Integrable.fintype_prod (f := fun p x => Real.exp (β / Real.sqrt N * sgn ε p * x))
    intro p
    apply integrable_exp_mul ν ht
    rw [abs_mul, abs_sgn, mul_one]
    exact lam_abs_le N β hN hβ hβ1

lemma prod_bounds (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (β : ℝ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hA : AdmissibleLaw ν) (ht : LightTails ν) (ε : Fin N → Bool) :
    (1 + (β / Real.sqrt N) ^ 2 / 2) ^ Fintype.card (Interaction N) ≤
        ∏ p : Interaction N, phi ν (β / Real.sqrt N * sgn ε p) ∧
      ∏ p : Interaction N, phi ν (β / Real.sqrt N * sgn ε p) ≤
        (1 + (β / Real.sqrt N) ^ 2 / 2 + 24576 * (β / Real.sqrt N) ^ 4) ^
          Fintype.card (Interaction N) := by
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const]
  have hc : ∀ p : Interaction N, |β / Real.sqrt N * sgn ε p| ≤ 3 / 4 := by
    intro p
    rw [abs_mul, abs_sgn, mul_one]
    exact lam_le_34 N β (two_le_of_interaction p) hβ hβ1
  have hc2 : ∀ p : Interaction N, (β / Real.sqrt N * sgn ε p) ^ 2 = (β / Real.sqrt N) ^ 2 := by
    intro p; rw [mul_pow, sgn_sq, mul_one]
  have hc4 : ∀ p : Interaction N, (β / Real.sqrt N * sgn ε p) ^ 4 = (β / Real.sqrt N) ^ 4 := by
    intro p
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hc2, ← pow_mul]
  constructor
  · apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p _
      have := phi_lower ν hA ht _ ((hc p).trans (by norm_num))
      rw [hc2] at this; exact this
  · apply Finset.prod_le_prod
    · intro p _
      have := phi_lower ν hA ht _ ((hc p).trans (by norm_num))
      have h0 : (0:ℝ) ≤ 1 + (β / Real.sqrt N * sgn ε p) ^ 2 / 2 := by positivity
      linarith
    · intro p _
      have := phi_upper ν hA ht _ (hc p)
      rw [hc2, hc4] at this; exact this

lemma first_moment_core :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (ν : MeasureTheory.Measure ℝ)
      [MeasureTheory.IsProbabilityMeasure ν] (β : ℝ),
      1 ≤ N → 0 < β → β ≤ 1 → AdmissibleLaw ν → LightTails ν →
      MeasureTheory.Integrable (partitionFunction N β) (couplingLaw N ν) ∧
      K⁻¹ * Real.exp (β ^ 2 * N / 4) ≤
        ∫ h, partitionFunction N β h ∂(couplingLaw N ν) ∧
      (∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ≤
        K * Real.exp (β ^ 2 * N / 4) := by
  refine ⟨Real.exp 12288, Real.exp_pos _, ?_⟩
  intro N ν _ β hN hβ hβ1 hA ht
  refine ⟨integrable_Z N ν β hN hβ hβ1 ht, ?_⟩
  rw [integral_Z N ν β hN hβ hβ1 ht]
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : (β / Real.sqrt N) ^ 2 = β ^ 2 / N := by
    rw [div_pow, Real.sq_sqrt hNpos.le]
  have hl4 : (β / Real.sqrt N) ^ 4 = (β ^ 2 / N) ^ 2 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hl2]
  have hM := card_interaction N
  set M := Fintype.card (Interaction N) with hMdef
  have hcard : ((Finset.univ : Finset (Fin N → Bool)).card : ℝ) = 2 ^ N := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; rfl
  have h2N : (0:ℝ) < 2 ^ N := by positivity
  set a := β ^ 2 / N / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hβ4 : β ^ 4 ≤ 1 := pow_le_one₀ hβ.le hβ1
  have hfrac : ((N:ℝ) - 1) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
  have hfrac0 : 0 ≤ ((N:ℝ) - 1) / N := by apply div_nonneg <;> linarith
  have hMa : (M:ℝ) * a = β ^ 2 * (N - 1) / 4 := by
    rw [hM, ha]; field_simp; ring
  have hMa2 : (M:ℝ) * a ^ 2 ≤ 1 / 8 := by
    have : (M:ℝ) * a ^ 2 = ((N:ℝ) - 1) / N * β ^ 4 / 8 := by
      rw [hM, ha]; field_simp; ring
    rw [this]
    have := mul_le_mul hfrac hβ4 (by positivity) (by norm_num)
    linarith
  have hMl : (M:ℝ) * (β ^ 2 / N) ^ 2 ≤ 1 / 2 := by
    have : (M:ℝ) * (β ^ 2 / N) ^ 2 = ((N:ℝ) - 1) / N * β ^ 4 / 2 := by
      rw [hM]; field_simp
    rw [this]
    have := mul_le_mul hfrac hβ4 (by positivity) (by norm_num)
    linarith
  constructor
  · -- lower bound
    have hsum : ∑ ε : Fin N → Bool, (1 + (β / Real.sqrt N) ^ 2 / 2) ^ M ≤
        ∑ ε : Fin N → Bool, ∏ p : Interaction N, phi ν (β / Real.sqrt N * sgn ε p) :=
      Finset.sum_le_sum (fun ε _ => (prod_bounds N ν β hβ hβ1 hA ht ε).1)
    rw [Finset.sum_const, nsmul_eq_mul, hcard, hl2] at hsum
    have h1 : (1 + a) ^ M ≤ ((2:ℝ) ^ N)⁻¹ *
        ∑ ε : Fin N → Bool, ∏ p : Interaction N, phi ν (β / Real.sqrt N * sgn ε p) := by
      rw [le_inv_mul_iff₀ h2N]; exact hsum
    refine le_trans ?_ h1
    have hlog : a - a ^ 2 ≤ Real.log (1 + a) := by
      have h1 := Real.one_sub_inv_le_log_of_pos (x := 1 + a) (by linarith)
      have h2 : (1 + a)⁻¹ ≤ 1 - a + a ^ 2 := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]
        nlinarith [pow_nonneg ha0 3]
      linarith
    have hexp : Real.exp (a - a ^ 2) ≤ 1 + a := by
      calc Real.exp (a - a ^ 2) ≤ Real.exp (Real.log (1 + a)) := Real.exp_le_exp.mpr hlog
        _ = 1 + a := Real.exp_log (by linarith)
    calc (Real.exp 12288)⁻¹ * Real.exp (β ^ 2 * N / 4)
        = Real.exp (M * (a - a ^ 2) - (M * (a - a ^ 2) - (β ^ 2 * N / 4 - 12288))) := by
          rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (M * (a - a ^ 2)) := by
          apply Real.exp_le_exp.mpr
          have : (M:ℝ) * (a - a ^ 2) = M * a - M * a ^ 2 := by ring
          rw [this, hMa]
          nlinarith
      _ = Real.exp (a - a ^ 2) ^ M := Real.exp_nat_mul _ _
      _ ≤ (1 + a) ^ M := pow_le_pow_left₀ (Real.exp_pos _).le hexp M
  · -- upper bound
    have hsum : ∑ ε : Fin N → Bool, ∏ p : Interaction N, phi ν (β / Real.sqrt N * sgn ε p) ≤
        ∑ ε : Fin N → Bool,
          (1 + (β / Real.sqrt N) ^ 2 / 2 + 24576 * (β / Real.sqrt N) ^ 4) ^ M :=
      Finset.sum_le_sum (fun ε _ => (prod_bounds N ν β hβ hβ1 hA ht ε).2)
    rw [Finset.sum_const, nsmul_eq_mul, hcard, hl2, hl4] at hsum
    have h1 : ((2:ℝ) ^ N)⁻¹ *
        ∑ ε : Fin N → Bool, ∏ p : Interaction N, phi ν (β / Real.sqrt N * sgn ε p) ≤
        (1 + a + 24576 * (β ^ 2 / N) ^ 2) ^ M := by
      rw [inv_mul_le_iff₀ h2N]; exact hsum
    refine h1.trans ?_
    have hexp : 1 + a + 24576 * (β ^ 2 / N) ^ 2 ≤ Real.exp (a + 24576 * (β ^ 2 / N) ^ 2) := by
      have := Real.add_one_le_exp (a + 24576 * (β ^ 2 / N) ^ 2)
      linarith
    calc (1 + a + 24576 * (β ^ 2 / N) ^ 2) ^ M
        ≤ Real.exp (a + 24576 * (β ^ 2 / N) ^ 2) ^ M :=
          pow_le_pow_left₀ (by positivity) hexp M
      _ = Real.exp (M * (a + 24576 * (β ^ 2 / N) ^ 2)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (12288 + β ^ 2 * N / 4) := by
          apply Real.exp_le_exp.mpr
          have : (M:ℝ) * (a + 24576 * (β ^ 2 / N) ^ 2) =
              M * a + 24576 * (M * (β ^ 2 / N) ^ 2) := by ring
          rw [this, hMa]
          nlinarith
      _ = Real.exp 12288 * Real.exp (β ^ 2 * N / 4) := Real.exp_add _ _

lemma spin_sq {N : ℕ} (ε : Fin N → Bool) (i : Fin N) : spin ε i ^ 2 = 1 := by
  rw [← sq_abs, abs_spin', one_pow]

/-- Gaussian moment generating function, purely real. -/
lemma integrable_gauss_shift (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2 + c * x)) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).comp_sub_right c
  have h2 := h.const_mul (Real.exp (c ^ 2 / 2))
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← Real.exp_add]; congr 1; ring

lemma integral_gauss_shift (c : ℝ) :
    ∫ x : ℝ, Real.exp (-x ^ 2 / 2 + c * x) = Real.sqrt (2 * Real.pi) * Real.exp (c ^ 2 / 2) := by
  have h1 : ∀ x : ℝ, Real.exp (-x ^ 2 / 2 + c * x) =
      Real.exp (c ^ 2 / 2) * Real.exp (-(1 / 2) * (x - c) ^ 2) := by
    intro x; rw [← Real.exp_add]; congr 1; ring
  simp_rw [h1]
  rw [integral_const_mul,
    integral_sub_right_eq_self (μ := volume) (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) c,
    integral_gaussian]
  rw [mul_comm]; congr 1; congr 1; ring

/-- the pointwise product of two spin configurations is again a spin configuration -/
def xorb {N : ℕ} (ε ε' : Fin N → Bool) : Fin N → Bool := fun i => ε i == ε' i

lemma spin_xorb {N : ℕ} (ε ε' : Fin N → Bool) (i : Fin N) :
    spin ε i * spin ε' i = spin (xorb ε ε') i := by
  unfold spin xorb
  cases ε i <;> cases ε' i <;> simp

lemma sgn_mul_sgn {N : ℕ} (ε ε' : Fin N → Bool) (p : Interaction N) :
    sgn ε p * sgn ε' p = sgn (xorb ε ε') p := by
  unfold sgn; rw [← spin_xorb, ← spin_xorb]; ring

lemma xorb_involutive {N : ℕ} (ε : Fin N → Bool) : Function.Involutive (xorb ε) := by
  intro ε'; funext i; unfold xorb; cases ε i <;> cases ε' i <;> rfl

lemma sum_xorb {N : ℕ} (ε : Fin N → Bool) (F : (Fin N → Bool) → ℝ) :
    ∑ ε' : Fin N → Bool, F (xorb ε ε') = ∑ τ : Fin N → Bool, F τ :=
  Fintype.sum_bijective (xorb ε) (xorb_involutive ε).bijective _ _ (fun _ => rfl)

/-- `∑_{i<j} σ_i σ_j = ((∑ σ_i)^2 - N) / 2` for spins. -/
lemma sum_sgn_eq {N : ℕ} (τ : Fin N → Bool) :
    ∑ p : Interaction N, sgn τ p = ((∑ i : Fin N, spin τ i) ^ 2 - N) / 2 := by
  classical
  set σ := spin τ with hσ
  have hsq : (∑ i : Fin N, σ i) ^ 2 = ∑ x : Fin N × Fin N, σ x.1 * σ x.2 := by
    rw [pow_two, Finset.sum_mul_sum]
    exact (Fintype.sum_prod_type' (fun i j => σ i * σ j)).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin N × Fin N))
    (fun x => x.1 < x.2) (fun x => σ x.1 * σ x.2)
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun x => ¬ x.1 < x.2))
    (fun x => x.2 < x.1) (fun x => σ x.1 * σ x.2)
  have hA : ∑ x ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun x => x.1 < x.2),
      σ x.1 * σ x.2 = ∑ p : Interaction N, sgn τ p := by
    rw [Finset.sum_subtype (p := fun x : Fin N × Fin N => x.1 < x.2) _ (by simp)]
    rfl
  have hB : ∑ x ∈ ((Finset.univ : Finset (Fin N × Fin N)).filter (fun x => ¬ x.1 < x.2)).filter
      (fun x => x.2 < x.1), σ x.1 * σ x.2 =
      ∑ x ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun x => x.1 < x.2), σ x.1 * σ x.2 := by
    apply Finset.sum_equiv (Equiv.prodComm _ _)
    · intro x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodComm_apply,
        Prod.fst_swap, Prod.snd_swap]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨not_lt.mpr h.le, h⟩
    · intro x _; simp [mul_comm]
  have hC : ∑ x ∈ ((Finset.univ : Finset (Fin N × Fin N)).filter (fun x => ¬ x.1 < x.2)).filter
      (fun x => ¬ x.2 < x.1), σ x.1 * σ x.2 = N := by
    have hset : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun x => ¬ x.1 < x.2)).filter
        (fun x => ¬ x.2 < x.1) = (Finset.univ : Finset (Fin N)).image (fun i => (i, i)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨x.1, ?_⟩
        have : x.1 = x.2 := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        ext <;> simp [this]
      · rintro ⟨i, hi⟩; rw [← hi]; simp
    rw [hset, Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).1)]
    simp only [← pow_two, hσ, spin_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  rw [hsq, ← hsplit, ← hsplit2, hB, hC, hA]
  ring

/-- the Gaussian (Hubbard–Stratonovich) bound for the exponential square moment of a
Rademacher sum -/
lemma rademacher_sq_exp_bound (N : ℕ) (t : ℝ) (ht : N * t ^ 2 < 1) :
    ∑ τ : Fin N → Bool, Real.exp (t ^ 2 * (∑ i : Fin N, spin τ i) ^ 2 / 2) ≤
      2 ^ N / Real.sqrt (1 - N * t ^ 2) := by
  classical
  have hpos : 0 < 1 - N * t ^ 2 := by linarith
  have hb : 0 < (1 - N * t ^ 2) / 2 := by positivity
  -- Step 1: represent each term as a Gaussian integral
  have h1 : ∀ τ : Fin N → Bool, Real.exp (t ^ 2 * (∑ i : Fin N, spin τ i) ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-x ^ 2 / 2 + (t * ∑ i : Fin N, spin τ i) * x) := by
    intro τ
    rw [integral_gauss_shift, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    congr 1; ring
  simp_rw [h1]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun τ _ => integrable_gauss_shift _)]
  -- Step 2: pointwise evaluation of the sum
  have h2 : ∀ x : ℝ, ∑ τ : Fin N → Bool, Real.exp (-x ^ 2 / 2 + (t * ∑ i : Fin N, spin τ i) * x)
      = Real.exp (-x ^ 2 / 2) * (Real.exp (t * x) + Real.exp (-(t * x))) ^ N := by
    intro x
    have : ∀ τ : Fin N → Bool, Real.exp (-x ^ 2 / 2 + (t * ∑ i : Fin N, spin τ i) * x) =
        Real.exp (-x ^ 2 / 2) * ∏ i : Fin N, Real.exp (t * x * spin τ i) := by
      intro τ
      rw [← Real.exp_sum, ← Real.exp_add, Finset.mul_sum]
      congr 1
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl; intro i _; ring
    simp_rw [this]
    rw [← Finset.mul_sum]
    congr 1
    have hprod : ∑ τ : Fin N → Bool, ∏ i, Real.exp (t * x * spin τ i) =
        ∏ i : Fin N, ∑ b : Bool, Real.exp (t * x * (if b then 1 else -1)) := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      rfl
    rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Fintype.sum_bool]
    simp
  have h3 : ∀ x : ℝ, ∑ τ : Fin N → Bool, Real.exp (-x ^ 2 / 2 + (t * ∑ i : Fin N, spin τ i) * x)
      ≤ 2 ^ N * Real.exp (-((1 - N * t ^ 2) / 2) * x ^ 2) := by
    intro x
    rw [h2]
    have hc : Real.exp (t * x) + Real.exp (-(t * x)) ≤ 2 * Real.exp ((t * x) ^ 2 / 2) := by
      have := Real.cosh_le_exp_half_sq (t * x)
      rw [Real.cosh_eq] at this
      linarith
    have h0 : 0 ≤ Real.exp (t * x) + Real.exp (-(t * x)) := by positivity
    calc Real.exp (-x ^ 2 / 2) * (Real.exp (t * x) + Real.exp (-(t * x))) ^ N
        ≤ Real.exp (-x ^ 2 / 2) * (2 * Real.exp ((t * x) ^ 2 / 2)) ^ N := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact pow_le_pow_left₀ h0 hc N
      _ = 2 ^ N * Real.exp (-((1 - N * t ^ 2) / 2) * x ^ 2) := by
          rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, mul_comm (Real.exp _) ((2:ℝ) ^ N),
            mul_assoc, ← Real.exp_add]
          congr 2; ring
  have hint1 : Integrable (fun x : ℝ => ∑ τ : Fin N → Bool,
      Real.exp (-x ^ 2 / 2 + (t * ∑ i : Fin N, spin τ i) * x)) :=
    integrable_finsetSum _ (fun τ _ => integrable_gauss_shift _)
  have hint2 : Integrable (fun x : ℝ => 2 ^ N * Real.exp (-((1 - N * t ^ 2) / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  have hsq : Real.sqrt (Real.pi / ((1 - N * t ^ 2) / 2)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt (1 - N * t ^ 2) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  calc (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, ∑ τ : Fin N → Bool,
        Real.exp (-x ^ 2 / 2 + (t * ∑ i : Fin N, spin τ i) * x)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, 2 ^ N * Real.exp (-((1 - N * t ^ 2) / 2) * x ^ 2) :=
        mul_le_mul_of_nonneg_left (integral_mono hint1 hint2 h3) (by positivity)
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (2 ^ N * (Real.sqrt (2 * Real.pi) / Real.sqrt (1 - N * t ^ 2))) := by
        rw [integral_const_mul, integral_gaussian, hsq]
    _ = 2 ^ N / Real.sqrt (1 - N * t ^ 2) := by
        have : 0 < Real.sqrt (2 * Real.pi) := by positivity
        field_simp


lemma Zsq_eq (N : ℕ) (β : ℝ) (h : Interaction N → ℝ) :
    partitionFunction N β h ^ 2 =
      (((2 : ℝ) ^ N)⁻¹) ^ 2 * ∑ ε : Fin N → Bool, ∑ ε' : Fin N → Bool, ∏ p : Interaction N,
        Real.exp (β / Real.sqrt N * (sgn ε p + sgn ε' p) * h p) := by
  rw [Z_eq, mul_pow]
  simp only [sq]
  rw [Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro ε _
  apply Finset.sum_congr rfl; intro ε' _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro p _
  rw [← Real.exp_add]; congr 1; ring

lemma abs_sgn_add (N : ℕ) (β : ℝ) (ε ε' : Fin N → Bool) (p : Interaction N) :
    |β / Real.sqrt N * (sgn ε p + sgn ε' p)| ≤ 2 * |β / Real.sqrt N| := by
  rw [abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc |sgn ε p + sgn ε' p| ≤ |sgn ε p| + |sgn ε' p| := abs_add_le _ _
    _ = 2 := by rw [abs_sgn, abs_sgn]; norm_num

lemma lam_facts (N : ℕ) (β : ℝ) (hN : 8 ≤ N) (hβ : 0 < β) (hβ1 : β < 1) :
    (β / Real.sqrt N) ^ 2 ≤ 1 / 8 ∧ |2 * (β / Real.sqrt N)| ≤ 3 / 4 := by
  have hN8 : (8:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  have hs : 8 / 3 ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hspos : 0 < Real.sqrt N := by linarith
  constructor
  · rw [div_pow, Real.sq_sqrt hNpos.le, div_le_iff₀ hNpos]
    nlinarith
  · rw [abs_of_pos (by positivity), mul_div_assoc', div_le_iff₀ hspos]
    nlinarith

lemma integrable_Zsq (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (β : ℝ)
    (hN : 8 ≤ N) (hβ : 0 < β) (hβ1 : β < 1) (ht : LightTails ν) :
    Integrable (fun h => partitionFunction N β h ^ 2) (couplingLaw N ν) := by
  have hZ : (fun h => partitionFunction N β h ^ 2) = fun h => (((2 : ℝ) ^ N)⁻¹) ^ 2 *
      ∑ ε : Fin N → Bool, ∑ ε' : Fin N → Bool, ∏ p : Interaction N,
        Real.exp (β / Real.sqrt N * (sgn ε p + sgn ε' p) * h p) := funext (Zsq_eq N β)
  rw [hZ]
  unfold couplingLaw
  apply Integrable.const_mul
  apply integrable_finsetSum; intro ε _
  apply integrable_finsetSum; intro ε' _
  apply Integrable.fintype_prod
    (f := fun p x => Real.exp (β / Real.sqrt N * (sgn ε p + sgn ε' p) * x))
  intro p
  apply integrable_exp_mul ν ht
  have := (lam_facts N β hN hβ hβ1).2
  rw [abs_mul] at this
  have h2 := abs_sgn_add N β ε ε' p
  norm_num at this
  linarith

lemma integral_Zsq (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (β : ℝ)
    (hN : 8 ≤ N) (hβ : 0 < β) (hβ1 : β < 1) (ht : LightTails ν) :
    ∫ h, partitionFunction N β h ^ 2 ∂(couplingLaw N ν) =
      (((2 : ℝ) ^ N)⁻¹) ^ 2 * ∑ ε : Fin N → Bool, ∑ ε' : Fin N → Bool, ∏ p : Interaction N,
        phi ν (β / Real.sqrt N * (sgn ε p + sgn ε' p)) := by
  have hZ : (fun h => partitionFunction N β h ^ 2) = fun h => (((2 : ℝ) ^ N)⁻¹) ^ 2 *
      ∑ ε : Fin N → Bool, ∑ ε' : Fin N → Bool, ∏ p : Interaction N,
        Real.exp (β / Real.sqrt N * (sgn ε p + sgn ε' p) * h p) := funext (Zsq_eq N β)
  have hint : ∀ ε ε' : Fin N → Bool, Integrable (fun h : Interaction N → ℝ =>
      ∏ p : Interaction N, Real.exp (β / Real.sqrt N * (sgn ε p + sgn ε' p) * h p))
      (Measure.pi fun _ => ν) := by
    intro ε ε'
    apply Integrable.fintype_prod
      (f := fun p x => Real.exp (β / Real.sqrt N * (sgn ε p + sgn ε' p) * x))
    intro p
    apply integrable_exp_mul ν ht
    have := (lam_facts N β hN hβ hβ1).2
    rw [abs_mul] at this
    have h2 := abs_sgn_add N β ε ε' p
    norm_num at this
    linarith
  rw [hZ]
  unfold couplingLaw
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun ε _ => integrable_finsetSum _ (fun ε' _ => hint ε ε'))]
  apply Finset.sum_congr rfl; intro ε _
  rw [integral_finsetSum _ (fun ε' _ => hint ε ε')]
  apply Finset.sum_congr rfl; intro ε' _
  exact integral_fintype_prod_eq_prod
    (fun p x => Real.exp (β / Real.sqrt N * (sgn ε p + sgn ε' p) * x))

lemma phi_zero (ν : Measure ℝ) [IsProbabilityMeasure ν] : phi ν 0 = 1 := by
  unfold phi; simp

lemma phi_nonneg (ν : Measure ℝ) (c : ℝ) : 0 ≤ phi ν c :=
  integral_nonneg (fun x => (Real.exp_pos _).le)

/-- the key pairwise estimate -/
lemma pair_bound (ν : Measure ℝ) [IsProbabilityMeasure ν] (hA : AdmissibleLaw ν)
    (ht : LightTails ν) (u s s' : ℝ) (hu : u ^ 2 ≤ 1 / 8) (hu2 : |2 * u| ≤ 3 / 4)
    (hs : |s| = 1) (hs' : |s'| = 1) :
    phi ν (u * (s + s')) ≤
      (1 + u ^ 2 / 2) ^ 2 * (1 + u ^ 2 * (s * s')) * (1 + 393216 * u ^ 4) := by
  have hw0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hu4 : u ^ 4 = (u ^ 2) ^ 2 := by ring
  have hsame : phi ν (2 * u) ≤ 1 + 2 * u ^ 2 + 393216 * u ^ 4 := by
    have := phi_upper ν hA ht (2 * u) hu2
    have e1 : (2 * u) ^ 2 / 2 = 2 * u ^ 2 := by ring
    have e2 : 24576 * (2 * u) ^ 4 = 393216 * u ^ 4 := by ring
    rw [e1, e2] at this; exact this
  have hsame' : phi ν (-(2 * u)) ≤ 1 + 2 * u ^ 2 + 393216 * u ^ 4 := by
    have := phi_upper ν hA ht (-(2 * u)) (by rw [abs_neg]; exact hu2)
    have e1 : (-(2 * u)) ^ 2 / 2 = 2 * u ^ 2 := by ring
    have e2 : 24576 * (-(2 * u)) ^ 4 = 393216 * u ^ 4 := by ring
    rw [e1, e2] at this; exact this
  have hR1 : 1 + 2 * u ^ 2 + 393216 * u ^ 4 ≤
      (1 + u ^ 2 / 2) ^ 2 * (1 + u ^ 2 * 1) * (1 + 393216 * u ^ 4) := by
    rw [hu4]
    nlinarith [mul_nonneg hw0 hw0, mul_nonneg (mul_nonneg hw0 hw0) hw0,
      mul_nonneg (mul_nonneg hw0 hw0) (mul_nonneg hw0 hw0)]
  have hR2 : (1:ℝ) ≤ (1 + u ^ 2 / 2) ^ 2 * (1 + u ^ 2 * (-1)) * (1 + 393216 * u ^ 4) := by
    rw [hu4]
    have hw1 : u ^ 2 ≤ 1 := by linarith
    have hw2 : (u ^ 2) ^ 2 ≤ 1 / 64 := by nlinarith
    nlinarith [mul_nonneg hw0 hw0, mul_nonneg (mul_nonneg hw0 hw0) hw0,
      mul_nonneg (mul_nonneg hw0 hw0) (mul_nonneg hw0 hw0)]
  rcases abs_eq (zero_le_one' ℝ) |>.mp hs with h1 | h1 <;>
    rcases abs_eq (zero_le_one' ℝ) |>.mp hs' with h2 | h2 <;> subst h1 h2
  · have : u * (1 + 1) = 2 * u := by ring
    rw [this]; norm_num; linarith
  · have : u * (1 + -1) = 0 := by ring
    rw [this, phi_zero]; norm_num; linarith
  · have : u * (-1 + 1) = 0 := by ring
    rw [this, phi_zero]; norm_num; linarith
  · have : u * (-1 + -1) = -(2 * u) := by ring
    rw [this]; norm_num; linarith

/-- lower bound on the first moment (extracted from the first-moment argument) -/
lemma integral_Z_ge (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (β : ℝ)
    (hN : 1 ≤ N) (hβ : 0 < β) (hβ1 : β ≤ 1) (hA : AdmissibleLaw ν) (ht : LightTails ν) :
    (1 + (β / Real.sqrt N) ^ 2 / 2) ^ Fintype.card (Interaction N) ≤
      ∫ h, partitionFunction N β h ∂(couplingLaw N ν) := by
  rw [integral_Z N ν β hN hβ hβ1 ht]
  have hcard : ((Finset.univ : Finset (Fin N → Bool)).card : ℝ) = 2 ^ N := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; rfl
  have h2N : (0:ℝ) < 2 ^ N := by positivity
  have hsum : ∑ ε : Fin N → Bool, (1 + (β / Real.sqrt N) ^ 2 / 2) ^ Fintype.card (Interaction N) ≤
      ∑ ε : Fin N → Bool, ∏ p : Interaction N, phi ν (β / Real.sqrt N * sgn ε p) :=
    Finset.sum_le_sum (fun ε _ => (prod_bounds N ν β hβ hβ1 hA ht ε).1)
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  rw [le_inv_mul_iff₀ h2N]; exact hsum

lemma second_moment_core :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (ν : MeasureTheory.Measure ℝ)
      [MeasureTheory.IsProbabilityMeasure ν] (β : ℝ),
      8 ≤ N → 0 < β → β < 1 → AdmissibleLaw ν → LightTails ν →
      MeasureTheory.Integrable (partitionFunction N β) (couplingLaw N ν) ∧
      MeasureTheory.Integrable (fun h => partitionFunction N β h ^ 2) (couplingLaw N ν) ∧
      (∫ h, partitionFunction N β h ^ 2 ∂(couplingLaw N ν)) ≤
        K / (1 - β ^ 2) *
          (∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ^ 2 := by
  refine ⟨Real.exp 196608, Real.exp_pos _, ?_⟩
  intro N ν _ β hN hβ hβ1 hA ht
  have hN1 : 1 ≤ N := by omega
  refine ⟨integrable_Z N ν β hN1 hβ hβ1.le ht, integrable_Zsq N ν β hN hβ hβ1 ht, ?_⟩
  rw [integral_Zsq N ν β hN hβ hβ1 ht]
  obtain ⟨hu, hu2⟩ := lam_facts N β hN hβ hβ1
  set u := β / Real.sqrt N with hudef
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hu2' : u ^ 2 = β ^ 2 / N := by rw [hudef, div_pow, Real.sq_sqrt hNpos.le]
  have hNu : (N:ℝ) * u ^ 2 = β ^ 2 := by rw [hu2']; field_simp
  have hβ2 : β ^ 2 < 1 := by nlinarith
  have hpos : 0 < 1 - β ^ 2 := by linarith
  set M := Fintype.card (Interaction N) with hMdef
  have hM := card_interaction N
  set A := (1 + u ^ 2 / 2) ^ 2 * (1 + 393216 * u ^ 4) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hw0 : 0 ≤ u ^ 2 := sq_nonneg u
  -- pairwise product bound
  have hprod : ∀ ε ε' : Fin N → Bool,
      ∏ p : Interaction N, phi ν (u * (sgn ε p + sgn ε' p)) ≤
        A ^ M * Real.exp (u ^ 2 * ((∑ i : Fin N, spin (xorb ε ε') i) ^ 2 - N) / 2) := by
    intro ε ε'
    calc ∏ p : Interaction N, phi ν (u * (sgn ε p + sgn ε' p))
        ≤ ∏ p : Interaction N, (A * (1 + u ^ 2 * (sgn ε p * sgn ε' p))) := by
          apply Finset.prod_le_prod (fun p _ => phi_nonneg ν _)
          intro p _
          have := pair_bound ν hA ht u (sgn ε p) (sgn ε' p) hu hu2 (abs_sgn ε p) (abs_sgn ε' p)
          rw [hAdef]; linarith [this]
      _ = A ^ M * ∏ p : Interaction N, (1 + u ^ 2 * (sgn ε p * sgn ε' p)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ ≤ A ^ M * Real.exp (∑ p : Interaction N, u ^ 2 * (sgn ε p * sgn ε' p)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA0 _)
          rw [Real.exp_sum]
          apply Finset.prod_le_prod
          · intro p _
            have h1 : |sgn ε p * sgn ε' p| = 1 := by rw [abs_mul, abs_sgn, abs_sgn, one_mul]
            have h2 := (abs_le.mp h1.le).1
            nlinarith
          · intro p _
            have := Real.add_one_le_exp (u ^ 2 * (sgn ε p * sgn ε' p))
            linarith
      _ = A ^ M * Real.exp (u ^ 2 * ((∑ i : Fin N, spin (xorb ε ε') i) ^ 2 - N) / 2) := by
          congr 2
          simp_rw [sgn_mul_sgn]
          rw [← Finset.mul_sum, sum_sgn_eq]
          ring
  -- summing
  have hcard : ((Finset.univ : Finset (Fin N → Bool)).card : ℝ) = 2 ^ N := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; rfl
  have h2N : (0:ℝ) < 2 ^ N := by positivity
  have hgauss := rademacher_sq_exp_bound N u (by rw [hNu]; exact hβ2)
  rw [hNu] at hgauss
  have hsum : ∑ ε : Fin N → Bool, ∑ ε' : Fin N → Bool,
      ∏ p : Interaction N, phi ν (u * (sgn ε p + sgn ε' p)) ≤
      2 ^ N * (A ^ M * (2 ^ N / Real.sqrt (1 - β ^ 2))) := by
    calc ∑ ε : Fin N → Bool, ∑ ε' : Fin N → Bool,
          ∏ p : Interaction N, phi ν (u * (sgn ε p + sgn ε' p))
        ≤ ∑ ε : Fin N → Bool, ∑ ε' : Fin N → Bool,
            A ^ M * Real.exp (u ^ 2 * ((∑ i : Fin N, spin (xorb ε ε') i) ^ 2 - N) / 2) :=
          Finset.sum_le_sum (fun ε _ => Finset.sum_le_sum (fun ε' _ => hprod ε ε'))
      _ = ∑ ε : Fin N → Bool, ∑ τ : Fin N → Bool,
            A ^ M * Real.exp (u ^ 2 * ((∑ i : Fin N, spin τ i) ^ 2 - N) / 2) := by
          apply Finset.sum_congr rfl; intro ε _
          exact sum_xorb ε (fun τ => A ^ M * Real.exp (u ^ 2 * ((∑ i : Fin N, spin τ i) ^ 2 - N) / 2))
      _ ≤ ∑ ε : Fin N → Bool, ∑ τ : Fin N → Bool,
            A ^ M * Real.exp (u ^ 2 * (∑ i : Fin N, spin τ i) ^ 2 / 2) := by
          apply Finset.sum_le_sum; intro ε _
          apply Finset.sum_le_sum; intro τ _
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA0 _)
          apply Real.exp_le_exp.mpr
          have : (0:ℝ) ≤ N := hNpos.le
          nlinarith
      _ = 2 ^ N * (A ^ M * ∑ τ : Fin N → Bool,
            Real.exp (u ^ 2 * (∑ i : Fin N, spin τ i) ^ 2 / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; simp only [Finset.mul_sum]
      _ ≤ 2 ^ N * (A ^ M * (2 ^ N / Real.sqrt (1 - β ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ h2N.le
          exact mul_le_mul_of_nonneg_left hgauss (pow_nonneg hA0 _)
  -- the first moment lower bound
  have hZ := integral_Z_ge N ν β hN1 hβ hβ1.le hA ht
  have hZ0 : 0 ≤ (1 + u ^ 2 / 2) ^ M := by positivity
  have hZsq : ((1 + u ^ 2 / 2) ^ M) ^ 2 ≤ (∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ^ 2 :=
    pow_le_pow_left₀ hZ0 hZ 2
  -- the constant
  have hMu : (M:ℝ) * u ^ 4 ≤ 1 / 2 := by
    have : (M:ℝ) * u ^ 4 = ((N:ℝ) - 1) / N * β ^ 4 / 2 := by
      rw [hM, show u ^ 4 = (u ^ 2) ^ 2 by ring, hu2']; field_simp
    rw [this]
    have hfrac : ((N:ℝ) - 1) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
    have hβ4 : β ^ 4 ≤ 1 := pow_le_one₀ hβ.le hβ1.le
    have := mul_le_mul hfrac hβ4 (by positivity) (by norm_num)
    linarith
  have hC : (1 + 393216 * u ^ 4) ^ M ≤ Real.exp 196608 := by
    calc (1 + 393216 * u ^ 4) ^ M ≤ Real.exp (393216 * u ^ 4) ^ M := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp (393216 * u ^ 4); linarith
      _ = Real.exp (M * (393216 * u ^ 4)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 196608 := by
          apply Real.exp_le_exp.mpr; nlinarith
  have hsqrt : 1 / Real.sqrt (1 - β ^ 2) ≤ 1 / (1 - β ^ 2) := by
    apply one_div_le_one_div_of_le hpos
    rw [Real.le_sqrt hpos.le hpos.le]
    nlinarith
  have hAM : A ^ M = ((1 + u ^ 2 / 2) ^ M) ^ 2 * (1 + 393216 * u ^ 4) ^ M := by
    rw [hAdef, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 M]
  calc (((2:ℝ) ^ N)⁻¹) ^ 2 * ∑ ε : Fin N → Bool, ∑ ε' : Fin N → Bool,
        ∏ p : Interaction N, phi ν (u * (sgn ε p + sgn ε' p))
      ≤ (((2:ℝ) ^ N)⁻¹) ^ 2 * (2 ^ N * (A ^ M * (2 ^ N / Real.sqrt (1 - β ^ 2)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = A ^ M * (1 / Real.sqrt (1 - β ^ 2)) := by
        field_simp
    _ ≤ (((1 + u ^ 2 / 2) ^ M) ^ 2 * Real.exp 196608) * (1 / (1 - β ^ 2)) := by
        rw [hAM]
        apply mul_le_mul _ hsqrt (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hC (by positivity)
    _ ≤ ((∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ^ 2 * Real.exp 196608) *
          (1 / (1 - β ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hZsq (Real.exp_pos _).le
    _ = Real.exp 196608 / (1 - β ^ 2) *
          (∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ^ 2 := by ring

end TalagrandConc.SKModel

open TalagrandConc.SKModel


theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (ν : MeasureTheory.Measure ℝ)
      [MeasureTheory.IsProbabilityMeasure ν] (β : ℝ),
      8 ≤ N → 0 < β → β < 1 → AdmissibleLaw ν → LightTails ν →
      MeasureTheory.Integrable (partitionFunction N β) (couplingLaw N ν) ∧
      MeasureTheory.Integrable (fun h => partitionFunction N β h ^ 2) (couplingLaw N ν) ∧
      (∫ h, partitionFunction N β h ^ 2 ∂(couplingLaw N ν)) ≤
        K / (1 - β ^ 2) *
          (∫ h, partitionFunction N β h ∂(couplingLaw N ν)) ^ 2 := by
  exact second_moment_core
