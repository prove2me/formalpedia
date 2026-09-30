-- Prove2me | solution 1 for UnderstandingML.dudley_chaining
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T17:38:26.643281+00:00
-- url     : https://prove2.me/submissions/c4238d73-14cc-4d7a-8200-a43f0e73f82b

import Definitions.Def_UnderstandingML_Covering
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Logic.Equiv.Bool

open MeasureTheory

namespace UnderstandingML.DudleyAux

/-- Flipping every sign is a bijection of `{±1}^m`, so the signs average to zero. -/
lemma sum_signVec_eq_zero {m : ℕ} (i : Fin m) :
    ∑ σ : Fin m → Bool, signVec σ i = 0 := by
  have h : ∑ σ : Fin m → Bool, signVec σ i =
      ∑ σ : Fin m → Bool, signVec (fun j ↦ !σ j) i :=
    (Fintype.sum_equiv (Equiv.piCongrRight fun (_ : Fin m) ↦ Equiv.boolNot) _ _
      (fun _ ↦ rfl)).symm
  have h2 : ∀ σ : Fin m → Bool, signVec (fun j ↦ !σ j) i = - signVec σ i := by
    intro σ; unfold signVec; cases h : σ i <;> simp [h]
  simp only [h2, Finset.sum_neg_distrib] at h
  linarith

/-- The sum of `exp (λ ⟨σ, u⟩)` over sign vectors is `2^m ∏ cosh (λ uᵢ)`. -/
lemma sum_exp_signVec {m : ℕ} (l : ℝ) (u : Fin m → ℝ) :
    ∑ σ : Fin m → Bool, Real.exp (l * ∑ i, signVec σ i * u i) =
      2 ^ m * ∏ i, Real.cosh (l * u i) := by
  have h := Fintype.prod_sum (fun (i : Fin m) (b : Bool) ↦
    Real.exp (l * ((if b then 1 else -1) * u i)))
  have e : ∀ σ : Fin m → Bool, Real.exp (l * ∑ i, signVec σ i * u i) =
      ∏ i, Real.exp (l * ((if σ i then 1 else -1) * u i)) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    rfl
  rw [Finset.sum_congr rfl (fun σ _ ↦ e σ), ← h]
  rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [Fintype.sum_bool, Real.cosh_eq]
  simp only [if_true, one_mul, Bool.false_eq_true, if_false, neg_mul, mul_neg]
  ring

lemma sum_exp_signVec_le {m : ℕ} (l : ℝ) (u : Fin m → ℝ) :
    ∑ σ : Fin m → Bool, Real.exp (l * ∑ i, signVec σ i * u i) ≤
      2 ^ m * Real.exp (l ^ 2 * (∑ i, u i ^ 2) / 2) := by
  rw [sum_exp_signVec]
  gcongr
  calc ∏ i, Real.cosh (l * u i) ≤ ∏ i, Real.exp ((l * u i) ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ ↦ (Real.cosh_pos _).le)
          (fun i _ ↦ Real.cosh_le_exp_half_sq _)
    _ = Real.exp (l ^ 2 * (∑ i, u i ^ 2) / 2) := by
        rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun i _ ↦ ?_); ring

/-- If `X ≤ a/λ + λ b` for every `λ > 0` with `a, b ≥ 0`, then `X ≤ 2 √(a b)`. -/
lemma le_of_forall_lambda {X a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ l : ℝ, 0 < l → X ≤ a / l + l * b) : X ≤ 2 * Real.sqrt (a * b) := by
  rcases ha.lt_or_eq with ha | ha
  · rcases hb.lt_or_eq with hb | hb
    · set s := Real.sqrt (a / b) with hs_def
      have hl : 0 < s := Real.sqrt_pos.2 (div_pos ha hb)
      have hs : s ^ 2 = a / b := Real.sq_sqrt (div_pos ha hb).le
      have e1 : a / s = s * b := by
        rw [div_eq_iff hl.ne']
        have : s * b * s = s ^ 2 * b := by ring
        rw [this, hs, div_mul_cancel₀ _ hb.ne']
      have e2 : s * b = Real.sqrt (a * b) := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ s * b)]
        congr 1
        rw [mul_pow, hs]; field_simp
      have := h _ hl
      rw [e1, e2] at this
      linarith
    · subst hb
      simp only [mul_zero, Real.sqrt_zero, add_zero] at h ⊢
      refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
      have := h (a / ε + 1) (by positivity)
      have h2 : a / (a / ε + 1) ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        have : ε * (a / ε + 1) = a + ε := by field_simp
        rw [this]; linarith
      linarith
  · subst ha
    simp only [zero_div, zero_add, zero_mul, Real.sqrt_zero, mul_zero] at h ⊢
    refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
    have := h (ε / (b + 1)) (by positivity)
    have h2 : ε / (b + 1) * b ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith

/-- **Massart's lemma about an arbitrary center.** For a finite nonempty `B ⊆ ℝ^m`, a vector `v`
and `r ≥ 0` with `‖b − v‖ ≤ r` on `B`, the average over sign vectors of `sup_{b ∈ B} ⟨σ, b⟩` is
at most `r √(2 log |B|)`. -/
lemma massart_avg {m : ℕ} (B : Finset (Fin m → ℝ)) (hB : B.Nonempty) (v : Fin m → ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hnorm : ∀ b ∈ B, ∑ i, (b i - v i) ^ 2 ≤ r ^ 2) :
    (1 / 2 ^ m : ℝ) * ∑ σ : Fin m → Bool,
        ⨆ b : (↑B : Set (Fin m → ℝ)), ∑ i, signVec σ i * (b : Fin m → ℝ) i ≤
      r * Real.sqrt (2 * Real.log B.card) := by
  classical
  set N : ℕ := B.card with hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hB.card_pos
  have : Nonempty (↑B : Set (Fin m → ℝ)) := hB.coe_sort
  set M : (Fin m → Bool) → ℝ := fun σ ↦
    ⨆ a : (↑B : Set (Fin m → ℝ)), ∑ i, signVec σ i * (a : Fin m → ℝ) i with hM
  have hsum_v : ∑ σ : Fin m → Bool, ∑ i, signVec σ i * v i = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ ↦ ?_)
    rw [← Finset.sum_mul, sum_signVec_eq_zero, zero_mul]
  have key : ∀ l : ℝ, 0 < l →
      (1 / 2 ^ m) * ∑ σ, M σ ≤ Real.log N / l + l * (r ^ 2 / 2) := by
    intro l hl
    set Y : (Fin m → Bool) → ℝ := fun σ ↦ M σ - ∑ i, signVec σ i * v i with hY
    have hYsum : ∑ σ, M σ = ∑ σ, Y σ := by
      simp only [hY, Finset.sum_sub_distrib, hsum_v, sub_zero]
    have hYexp : ∀ σ, Real.exp (l * Y σ) ≤
        ∑ a ∈ B, Real.exp (l * ∑ i, signVec σ i * (a i - v i)) := by
      intro σ
      obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite
        (f := fun a : (↑B : Set (Fin m → ℝ)) ↦ ∑ i, signVec σ i * (a : Fin m → ℝ) i)
      have : Y σ = ∑ i, signVec σ i * ((a : Fin m → ℝ) i - v i) := by
        simp only [hY, hM, ← ha, mul_sub, Finset.sum_sub_distrib]
      rw [this]
      exact Finset.single_le_sum (f := fun a ↦ Real.exp (l * ∑ i, signVec σ i * (a i - v i)))
        (fun _ _ ↦ (Real.exp_pos _).le) a.2
    have hjensen : Real.exp (l * ((1 / 2 ^ m) * ∑ σ, Y σ)) ≤
        (1 / 2 ^ m) * ∑ σ, Real.exp (l * Y σ) := by
      have := (convexOn_exp).map_sum_le (t := Finset.univ) (w := fun _ ↦ (1 / 2 ^ m : ℝ))
        (p := fun σ : Fin m → Bool ↦ l * Y σ) (fun _ _ ↦ by positivity)
        (by simp [Finset.card_univ, Fintype.card_bool, Fintype.card_fin])
        (fun _ _ ↦ Set.mem_univ _)
      simp only [smul_eq_mul] at this
      have e1 : l * ((1 / 2 ^ m) * ∑ σ, Y σ) = ∑ σ, (1 / 2 ^ m : ℝ) * (l * Y σ) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
      rw [e1, Finset.mul_sum]
      exact this
    have hbound : (1 / 2 ^ m) * ∑ σ, Real.exp (l * Y σ) ≤
        N * Real.exp (l ^ 2 * r ^ 2 / 2) := by
      calc (1 / 2 ^ m) * ∑ σ, Real.exp (l * Y σ)
          ≤ (1 / 2 ^ m) * ∑ σ, ∑ a ∈ B, Real.exp (l * ∑ i, signVec σ i * (a i - v i)) := by
            gcongr with σ; exact hYexp σ
        _ = ∑ a ∈ B, (1 / 2 ^ m) * ∑ σ, Real.exp (l * ∑ i, signVec σ i * (a i - v i)) := by
            rw [Finset.sum_comm, Finset.mul_sum]
        _ ≤ ∑ a ∈ B, (1 / 2 ^ m) * (2 ^ m * Real.exp (l ^ 2 * r ^ 2 / 2)) := by
            refine Finset.sum_le_sum (fun a ha ↦ ?_)
            gcongr
            refine (sum_exp_signVec_le l (fun i ↦ a i - v i)).trans ?_
            gcongr
            exact hnorm a ha
        _ = N * Real.exp (l ^ 2 * r ^ 2 / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← hN]; field_simp
    have hlog : l * ((1 / 2 ^ m) * ∑ σ, Y σ) ≤ Real.log N + l ^ 2 * r ^ 2 / 2 := by
      rw [← Real.log_exp (l * _), ← Real.log_exp (l ^ 2 * r ^ 2 / 2),
        ← Real.log_mul hNpos.ne' (Real.exp_pos _).ne']
      exact Real.log_le_log (Real.exp_pos _) (hjensen.trans hbound)
    rw [hYsum]
    rw [div_add' _ _ _ hl.ne', le_div_iff₀ hl]
    nlinarith [hlog]
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hB.card_pos)
  have hopt := le_of_forall_lambda hlogN (by positivity : 0 ≤ r ^ 2 / 2) key
  have hsq : 2 * Real.sqrt (Real.log N * (r ^ 2 / 2)) = r * Real.sqrt (2 * Real.log N) := by
    have : Real.log N * (r ^ 2 / 2) = (r / 2) ^ 2 * (2 * Real.log N) := by ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    ring
  rw [hsq] at hopt
  exact hopt

/-! ### The Euclidean norm -/

lemma eucNorm_eq_norm {m : ℕ} (v : Fin m → ℝ) : eucNorm v = ‖WithLp.toLp 2 v‖ := by
  rw [EuclideanSpace.norm_eq, eucNorm]
  simp [Real.norm_eq_abs, sq_abs]

lemma eucNorm_nonneg' {m : ℕ} (v : Fin m → ℝ) : 0 ≤ eucNorm v := Real.sqrt_nonneg _

lemma sum_sq_eq_eucNorm_sq {m : ℕ} (v : Fin m → ℝ) : ∑ i, v i ^ 2 = eucNorm v ^ 2 :=
  (Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i)))).symm

lemma eucNorm_sub_comm {m : ℕ} (x y : Fin m → ℝ) : eucNorm (x - y) = eucNorm (y - x) := by
  rw [eucNorm_eq_norm, eucNorm_eq_norm, WithLp.toLp_sub, WithLp.toLp_sub, norm_sub_rev]

lemma eucNorm_sub_le {m : ℕ} (x y z : Fin m → ℝ) :
    eucNorm (x - z) ≤ eucNorm (x - y) + eucNorm (y - z) := by
  simp only [eucNorm_eq_norm, WithLp.toLp_sub]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- `⟨σ, x⟩ ≤ √m ‖x‖` for a sign vector `σ` (Cauchy–Schwarz). -/
lemma signed_sum_le {m : ℕ} (σ : Fin m → Bool) (x : Fin m → ℝ) :
    ∑ i, signVec σ i * x i ≤ Real.sqrt m * eucNorm x := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (signVec σ) x
  have h2 : ∑ i, signVec σ i ^ 2 = m := by
    have : ∀ i, signVec σ i ^ 2 = 1 := fun i ↦ by unfold signVec; split_ifs <;> norm_num
    simp [this]
  rw [h2] at h1
  calc ∑ i, signVec σ i * x i ≤ |∑ i, signVec σ i * x i| := le_abs_self _
    _ ≤ Real.sqrt (m * ∑ i, x i ^ 2) := Real.abs_le_sqrt h1
    _ = Real.sqrt m * eucNorm x := by rw [Real.sqrt_mul (Nat.cast_nonneg _)]; rfl

lemma sum_signed_const {m : ℕ} (v : Fin m → ℝ) :
    ∑ σ : Fin m → Bool, ∑ i, signVec σ i * v i = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun i _ ↦ ?_)
  rw [← Finset.sum_mul, sum_signVec_eq_zero, zero_mul]

lemma signed_sum_sub {m : ℕ} (σ : Fin m → Bool) (x y : Fin m → ℝ) :
    ∑ i, signVec σ i * (x - y) i = ∑ i, signVec σ i * x i - ∑ i, signVec σ i * y i := by
  simp [mul_sub, Finset.sum_sub_distrib]

/-! ### Covers -/

lemma isCover_mono {m : ℕ} {r r' : ℝ} (h : r ≤ r') {A : Set (Fin m → ℝ)}
    {A' : Finset (Fin m → ℝ)} (hA' : IsCover r A A') : IsCover r' A A' := by
  intro a ha
  obtain ⟨b, hb, hd⟩ := hA' a ha
  exact ⟨b, hb, hd.trans h⟩

lemma coveringNumber_le_card {m : ℕ} {r : ℝ} {A : Set (Fin m → ℝ)}
    {A' : Finset (Fin m → ℝ)} (hA' : IsCover r A A') : coveringNumber r A ≤ A'.card :=
  iInf₂_le A' hA'

/-- A set lying in a Euclidean ball has a finite `r`-cover for every `r > 0`. -/
lemma exists_isCover {m : ℕ} (A : Set (Fin m → ℝ)) (abar : Fin m → ℝ) (c : ℝ)
    (hc : ∀ a ∈ A, eucNorm (a - abar) ≤ c) (r : ℝ) (hr : 0 < r) :
    ∃ A' : Finset (Fin m → ℝ), IsCover r A A' := by
  classical
  have hsub : (WithLp.toLp 2 '' A : Set (EuclideanSpace ℝ (Fin m))) ⊆
      Metric.closedBall (WithLp.toLp 2 abar) c := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, ← WithLp.toLp_sub, ← eucNorm_eq_norm]
    exact hc a ha
  have htb : TotallyBounded (WithLp.toLp 2 '' A : Set (EuclideanSpace ℝ (Fin m))) :=
    (isCompact_closedBall _ _).totallyBounded.subset hsub
  obtain ⟨t, htfin, hcov⟩ := Metric.totallyBounded_iff.1 htb r hr
  refine ⟨htfin.toFinset.image WithLp.ofLp, fun a ha ↦ ?_⟩
  have := hcov ⟨a, ha, rfl⟩
  simp only [Set.mem_iUnion, Metric.mem_ball] at this
  obtain ⟨y, hy, hdist⟩ := this
  refine ⟨y.ofLp, Finset.mem_image.2 ⟨y, htfin.mem_toFinset.2 hy, rfl⟩, ?_⟩
  rw [eucNorm_eq_norm, WithLp.toLp_sub, WithLp.toLp_ofLp, ← dist_eq_norm]
  exact hdist.le

/-- If some finite `r`-cover exists, a cover of size exactly `N(r, A)` exists. -/
lemma exists_min_cover {m : ℕ} {r : ℝ} {A : Set (Fin m → ℝ)}
    (h : ∃ A' : Finset (Fin m → ℝ), IsCover r A A') :
    ∃ A' : Finset (Fin m → ℝ), IsCover r A A' ∧ (A'.card : ℕ∞) = coveringNumber r A := by
  obtain ⟨A₀, hA₀⟩ := h
  have : Nonempty {A' : Finset (Fin m → ℝ) // IsCover r A A'} := ⟨⟨A₀, hA₀⟩⟩
  obtain ⟨⟨A', hA'⟩, he⟩ :=
    ENat.exists_eq_iInf (fun x : {A' : Finset (Fin m → ℝ) // IsCover r A A'} ↦ (x.1.card : ℕ∞))
  refine ⟨A', hA', ?_⟩
  rw [he, coveringNumber, iInf_subtype']

lemma sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, f k = ∑ k ∈ Finset.range M, f (k + 1) := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

end UnderstandingML.DudleyAux

open UnderstandingML UnderstandingML.DudleyAux in
theorem solution {m : ℕ} (hm : 0 < m) (A : Set (Fin m → ℝ)) (hA : A.Nonempty) (c : ℝ)
    (abar : Fin m → ℝ) (hc : ∀ a ∈ A, eucNorm (a - abar) ≤ c) (M : ℕ) (hM : 0 < M) :
    rademacher A ≤ c * (2 : ℝ)⁻¹ ^ M / Real.sqrt m +
      6 * c / m * ∑ k ∈ Finset.Icc 1 M,
        (2 : ℝ)⁻¹ ^ k * Real.sqrt (Real.log ((coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat)) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hA
  have hAne : Nonempty A := ⟨⟨a₀, ha₀⟩⟩
  have hc0 : 0 ≤ c := (eucNorm_nonneg' _).trans (hc a₀ ha₀)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set rad : ℕ → ℝ := fun k ↦ c * (2 : ℝ)⁻¹ ^ k with hrad
  have hrad0 : ∀ k, 0 ≤ rad k := fun k ↦ by positivity
  have hrad_succ : ∀ k, rad k = 2 * rad (k + 1) := fun k ↦ by
    simp only [hrad, pow_succ]; ring
  -- the chosen covers: `P 0 = {ā}` and `P k` a minimal `rad k`-cover for `k ≥ 1`
  have hmin : ∀ k : ℕ, ∃ A' : Finset (Fin m → ℝ),
      IsCover (rad k) A A' ∧ (k ≠ 0 → (A'.card : ℕ∞) = coveringNumber (rad k) A) ∧
        (k = 0 → A' = {abar}) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨{abar}, fun a ha ↦ ⟨abar, Finset.mem_singleton_self _, ?_⟩, fun h ↦ absurd rfl h,
        fun _ ↦ rfl⟩
      simpa [hrad] using hc a ha
    · have hex : ∃ A' : Finset (Fin m → ℝ), IsCover (rad k) A A' := by
        rcases hc0.eq_or_lt with h0 | hpos
        · refine ⟨{abar}, fun a ha ↦ ⟨abar, Finset.mem_singleton_self _, ?_⟩⟩
          have := hc a ha
          simp only [hrad, ← h0, zero_mul] at this ⊢
          exact this
        · exact exists_isCover A abar c hc _ (by positivity)
      obtain ⟨A', h1, h2⟩ := exists_min_cover hex
      exact ⟨A', h1, fun _ ↦ h2, fun h ↦ absurd h hk.ne'⟩
  choose P hPcov hPcard hP0 using hmin
  have hPcard' : ∀ k, k ≠ 0 → (P k).card = (coveringNumber (rad k) A).toNat := fun k hk ↦ by
    rw [← hPcard k hk, ENat.toNat_natCast]
  have hPne : ∀ k, (P k).Nonempty := fun k ↦ by
    obtain ⟨b, hb, _⟩ := hPcov k a₀ ha₀
    exact ⟨b, hb⟩
  -- successive covers grow
  have hPmono : ∀ k, (P k).card ≤ (P (k + 1)).card := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [hP0 0 rfl, Finset.card_singleton]
      exact (hPne 1).card_pos
    · have h1 : coveringNumber (rad k) A ≤ (P (k + 1)).card :=
        coveringNumber_le_card (isCover_mono (by rw [hrad_succ k]; linarith [hrad0 (k + 1)])
          (hPcov (k + 1)))
      rw [← hPcard k hk.ne'] at h1
      exact_mod_cast h1
  -- projections onto the covers
  choose! π hπmem hπd using hPcov
  have hπ0 : ∀ a ∈ A, π 0 a = abar := fun a ha ↦ by
    have := hπmem 0 a ha
    rwa [hP0 0 rfl, Finset.mem_singleton] at this
  -- the sets of increments
  set D : ℕ → Finset (Fin m → ℝ) := fun k ↦
    ((P (k + 1) ×ˢ P k).filter (fun p ↦ eucNorm (p.1 - p.2) ≤ 3 * rad (k + 1))).image
      (fun p ↦ p.1 - p.2) with hD
  have hDmem : ∀ k, ∀ a ∈ A, π (k + 1) a - π k a ∈ D k := by
    intro k a ha
    refine Finset.mem_image.2 ⟨(π (k + 1) a, π k a), Finset.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
    · exact Finset.mem_product.2 ⟨hπmem _ a ha, hπmem _ a ha⟩
    · calc eucNorm (π (k + 1) a - π k a)
          ≤ eucNorm (π (k + 1) a - a) + eucNorm (a - π k a) := eucNorm_sub_le _ _ _
        _ ≤ rad (k + 1) + rad k := by
          rw [eucNorm_sub_comm]; exact add_le_add (hπd _ a ha) (hπd _ a ha)
        _ = 3 * rad (k + 1) := by rw [hrad_succ k]; ring
  have hDne : ∀ k, (D k).Nonempty := fun k ↦ ⟨_, hDmem k a₀ ha₀⟩
  have hDnorm : ∀ k, ∀ d ∈ D k, eucNorm d ≤ 3 * rad (k + 1) := by
    intro k d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hd
    exact (Finset.mem_filter.1 hp).2
  have hDcard : ∀ k, (D k).card ≤ (P (k + 1)).card ^ 2 := by
    intro k
    calc (D k).card ≤ (P (k + 1) ×ˢ P k).card :=
          Finset.card_image_le.trans (Finset.card_filter_le _ _)
      _ = (P (k + 1)).card * (P k).card := Finset.card_product _ _
      _ ≤ (P (k + 1)).card * (P (k + 1)).card := Nat.mul_le_mul_left _ (hPmono k)
      _ = (P (k + 1)).card ^ 2 := (sq _).symm
  -- the per-level Rademacher sums of the increments
  set F : (Fin m → Bool) → ℕ → ℝ := fun σ k ↦
    ⨆ d : (↑(D k) : Set (Fin m → ℝ)), ∑ i, signVec σ i * (d : Fin m → ℝ) i with hF
  have hFle : ∀ σ k, ∀ a ∈ A, ∑ i, signVec σ i * (π (k + 1) a - π k a) i ≤ F σ k := by
    intro σ k a ha
    exact le_ciSup (f := fun d : (↑(D k) : Set (Fin m → ℝ)) ↦ ∑ i, signVec σ i * (d : Fin m → ℝ) i)
      (Set.finite_range _).bddAbove ⟨_, hDmem k a ha⟩
  -- the chaining decomposition, pointwise in `σ`
  have hpt : ∀ σ : Fin m → Bool, (⨆ a : A, ∑ i, signVec σ i * (a : Fin m → ℝ) i) ≤
      Real.sqrt m * rad M + ∑ k ∈ Finset.range M, F σ k + ∑ i, signVec σ i * abar i := by
    intro σ
    refine ciSup_le (fun ⟨a, ha⟩ ↦ ?_)
    have htele := Finset.sum_range_sub (fun k ↦ ∑ i, signVec σ i * π k a i) M
    have hdec : ∑ i, signVec σ i * a i =
        ∑ i, signVec σ i * (a - π M a) i +
          ∑ k ∈ Finset.range M, ∑ i, signVec σ i * (π (k + 1) a - π k a) i +
          ∑ i, signVec σ i * abar i := by
      simp only [signed_sum_sub] at htele ⊢
      rw [htele, hπ0 a ha]; ring
    show ∑ i, signVec σ i * a i ≤ _
    rw [hdec]
    gcongr with k hk
    · exact (signed_sum_le σ _).trans
        (mul_le_mul_of_nonneg_left (hπd M a ha) (Real.sqrt_nonneg _))
    · exact hFle σ k a ha
  -- Massart's lemma at each level
  have hlev : ∀ k, (1 / 2 ^ m : ℝ) * ∑ σ, F σ k ≤
      6 * rad (k + 1) * Real.sqrt (Real.log (P (k + 1)).card) := by
    intro k
    have h1 := massart_avg (D k) (hDne k) 0 (3 * rad (k + 1)) (by linarith [hrad0 (k + 1)])
      (fun b hb ↦ by
        simp only [Pi.zero_apply, sub_zero]
        rw [sum_sq_eq_eucNorm_sq]
        exact pow_le_pow_left₀ (eucNorm_nonneg' _) (hDnorm k b hb) 2)
    refine h1.trans ?_
    have hPpos : (0 : ℝ) < (P (k + 1)).card := by exact_mod_cast (hPne _).card_pos
    have hDpos : (0 : ℝ) < (D k).card := by exact_mod_cast (hDne _).card_pos
    have hlog : Real.log (D k).card ≤ 2 * Real.log (P (k + 1)).card := by
      calc Real.log (D k).card ≤ Real.log (((P (k + 1)).card : ℝ) ^ 2) :=
            Real.log_le_log hDpos (by exact_mod_cast hDcard k)
        _ = 2 * Real.log (P (k + 1)).card := by rw [Real.log_pow]; norm_num
    have hsq : Real.sqrt (2 * Real.log (D k).card) ≤
        2 * Real.sqrt (Real.log (P (k + 1)).card) := by
      calc Real.sqrt (2 * Real.log (D k).card)
          ≤ Real.sqrt (2 ^ 2 * Real.log (P (k + 1)).card) := Real.sqrt_le_sqrt (by linarith)
        _ = 2 * Real.sqrt (Real.log (P (k + 1)).card) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    calc 3 * rad (k + 1) * Real.sqrt (2 * Real.log (D k).card)
        ≤ 3 * rad (k + 1) * (2 * Real.sqrt (Real.log (P (k + 1)).card)) :=
          mul_le_mul_of_nonneg_left hsq (by linarith [hrad0 (k + 1)])
      _ = 6 * rad (k + 1) * Real.sqrt (Real.log (P (k + 1)).card) := by ring
  -- average over `σ`
  have havg : (1 / 2 ^ m : ℝ) * ∑ σ : Fin m → Bool, (⨆ a : A, ∑ i, signVec σ i * (a : Fin m → ℝ) i)
      ≤ Real.sqrt m * rad M +
        ∑ k ∈ Finset.range M, 6 * rad (k + 1) * Real.sqrt (Real.log (P (k + 1)).card) := by
    have hcard : (∑ _σ : Fin m → Bool, (1 : ℝ)) = 2 ^ m := by simp
    calc (1 / 2 ^ m : ℝ) * ∑ σ : Fin m → Bool, (⨆ a : A, ∑ i, signVec σ i * (a : Fin m → ℝ) i)
        ≤ (1 / 2 ^ m : ℝ) * ∑ σ : Fin m → Bool,
            (Real.sqrt m * rad M + ∑ k ∈ Finset.range M, F σ k + ∑ i, signVec σ i * abar i) := by
          gcongr with σ; exact hpt σ
      _ = Real.sqrt m * rad M + ∑ k ∈ Finset.range M, (1 / 2 ^ m : ℝ) * ∑ σ, F σ k := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_signed_const, Finset.sum_comm,
            Finset.sum_const, Finset.card_univ]
          simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_pow, Nat.cast_ofNat]
          rw [add_zero, mul_add, ← Finset.mul_sum]
          congr 1
          field_simp
      _ ≤ _ := add_le_add_right (Finset.sum_le_sum fun k _ ↦ hlev k) _
  -- conclude
  rw [sum_Icc_one_eq_sum_range]
  have hN : ∀ k ∈ Finset.range M,
      (2 : ℝ)⁻¹ ^ (k + 1) * Real.sqrt (Real.log ((coveringNumber (c * (2 : ℝ)⁻¹ ^ (k + 1)) A).toNat))
        = (2 : ℝ)⁻¹ ^ (k + 1) * Real.sqrt (Real.log (P (k + 1)).card) := by
    intro k _
    rw [hPcard' (k + 1) (Nat.succ_ne_zero k)]
  rw [Finset.sum_congr rfl hN]
  have hsqm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hmpos.le
  have hsqpos : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
  calc rademacher A
      = (1 / m) * ((1 / 2 ^ m : ℝ) * ∑ σ : Fin m → Bool,
          (⨆ a : A, ∑ i, signVec σ i * (a : Fin m → ℝ) i)) := rfl
    _ ≤ (1 / m) * (Real.sqrt m * rad M +
        ∑ k ∈ Finset.range M, 6 * rad (k + 1) * Real.sqrt (Real.log (P (k + 1)).card)) :=
        mul_le_mul_of_nonneg_left havg (by positivity)
    _ = c * (2 : ℝ)⁻¹ ^ M / Real.sqrt m + 6 * c / m * ∑ k ∈ Finset.range M,
        (2 : ℝ)⁻¹ ^ (k + 1) * Real.sqrt (Real.log (P (k + 1)).card) := by
        simp only [hrad]
        rw [mul_add]
        congr 1
        · field_simp
          rw [Real.sq_sqrt hmpos.le]
        · rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ ↦ ?_)
          ring
