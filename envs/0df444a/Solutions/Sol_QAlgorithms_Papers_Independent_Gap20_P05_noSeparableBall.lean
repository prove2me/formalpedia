-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P05.noSeparableBall
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T20:29:20.923757+00:00
-- url     : https://prove2.me/submissions/fa068952-a4d1-4302-9497-c4fb0b4b06dc

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P05
noncomputable section

open Filter

open scoped ENNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap20.P05

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity rankOne traceSize traceClosure IsSeparable)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (NuclearExpansion productStates productCoeff)

/-- entrywise bound by a nuclear expansion -/
lemma nsb_summable_entry {I : Type} (l r : ℕ → Hilbert I)
    (hs : Summable (fun n => ‖l n‖ * ‖r n‖)) (i j : I) :
    Summable (fun n => ‖l n i * star (r n j)‖) ∧
      ∀ n, ‖l n i * star (r n j)‖ ≤ ‖l n‖ * ‖r n‖ := by
  have hb : ∀ n, ‖l n i * star (r n j)‖ ≤ ‖l n‖ * ‖r n‖ := by
    intro n
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ _)
      (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _) (norm_nonneg _)
  exact ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs, hb⟩

lemma nsb_entry_le {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (i j : I) :
    ‖X i j‖ ≤ ∑' n, ‖e.left n‖ * ‖e.right n‖ := by
  obtain ⟨hs, hb⟩ := nsb_summable_entry e.left e.right e.summable i j
  rw [e.coefficients i j]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb e.summable)

lemma nsb_entry_lt {I : Type} {Z : Matrix I I ℂ} {δ : ℝ}
    (h : traceSize Z < ENNReal.ofReal δ) (i j : I) : ‖Z i j‖ < δ := by
  unfold traceSize at h
  obtain ⟨e, he⟩ := iInf_lt_iff.mp h
  have h0 : 0 ≤ ∑' n, ‖e.left n‖ * ‖e.right n‖ :=
    tsum_nonneg (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).mp he
  exact (nsb_entry_le e i j).trans_lt this

/-- combined expansion -/
def nsbExp {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (a b : ℂ)
    (p q : Hilbert I) :
    NuclearExpansion (fun i j => a * X i j + b * (p i * star (q j))) where
  left := fun n => match n with
    | 0 => b • p
    | m + 1 => a • e.left m
  right := fun n => match n with
    | 0 => q
    | m + 1 => e.right m
  summable := by
    rw [← summable_nat_add_iff 1]
    have := e.summable.mul_left ‖a‖
    simpa [norm_smul, mul_assoc] using this
  coefficients := by
    intro i j
    have hs0 : Summable (fun n => ‖(match n with
        | 0 => b • p
        | m + 1 => a • e.left m : Hilbert I)‖ * ‖(match n with
        | 0 => q
        | m + 1 => e.right m : Hilbert I)‖) := by
      rw [← summable_nat_add_iff 1]
      have := e.summable.mul_left ‖a‖
      simpa [norm_smul, mul_assoc] using this
    obtain ⟨hs, _⟩ := nsb_summable_entry _ _ hs0 i j
    have hs' := hs.of_norm
    rw [hs'.tsum_eq_zero_add]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [e.coefficients i j, ← tsum_mul_left]
    rw [tsum_congr (fun m => (mul_assoc a (e.left m i) (star (e.right m j))))]
    ring

lemma nsb_traceSize_le {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (a b : ℂ)
    (p q : Hilbert I) :
    traceSize (fun i j => a * X i j + b * (p i * star (q j))) ≤
      ENNReal.ofReal (‖b‖ * ‖p‖ * ‖q‖ + ‖a‖ * ∑' n, ‖e.left n‖ * ‖e.right n‖) := by
  refine (iInf_le _ (nsbExp e a b p q)).trans (le_of_eq ?_)
  congr 1
  have hs0 : Summable (fun n => ‖(nsbExp e a b p q).left n‖ * ‖(nsbExp e a b p q).right n‖) :=
    (nsbExp e a b p q).summable
  rw [hs0.tsum_eq_zero_add]
  simp only [nsbExp, norm_smul]
  rw [← tsum_mul_left]
  simp only [mul_assoc]

lemma nsb_psd_diag {I : Type} {X : Matrix I I ℂ}
    (hP : ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re) (p : I) :
    (X p p).im = 0 ∧ 0 ≤ (X p p).re := by
  have := hP {p} (fun _ => 1)
  simpa using this

lemma nsb_quad {I : Type} (X : Matrix I I ℂ) {p q : I} (hpq : p ≠ q) (a b : ℂ) :
    (∑ i ∈ ({p, q} : Finset I), ∑ j ∈ ({p, q} : Finset I),
      star ((fun k => if k = p then a else b) i) * X i j *
        (fun k => if k = p then a else b) j) =
    star a * X p p * a + star a * X p q * b + (star b * X q p * a + star b * X q q * b) := by
  rw [Finset.sum_pair hpq, Finset.sum_pair hpq, Finset.sum_pair hpq]
  simp [hpq.symm]

lemma nsb_psd_two {I : Type} {X : Matrix I I ℂ}
    (hP : ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re) {p q : I} (hpq : p ≠ q) :
    X q p = star (X p q) ∧ ‖X p q‖ ^ 2 ≤ (X p p).re * (X q q).re := by
  obtain ⟨hp1, hp2⟩ := nsb_psd_diag hP p
  obtain ⟨hq1, hq2⟩ := nsb_psd_diag hP q
  have Q : ∀ a b : ℂ, (star a * X p p * a + star a * X p q * b +
      (star b * X q p * a + star b * X q q * b)).im = 0 ∧
      0 ≤ (star a * X p p * a + star a * X p q * b +
      (star b * X q p * a + star b * X q q * b)).re := by
    intro a b
    rw [← nsb_quad X hpq a b]
    exact hP _ _
  have h1 := (Q 1 1).1
  have h2 := (Q 1 Complex.I).1
  simp [Complex.mul_im, Complex.mul_re, hp1, hq1] at h1 h2
  have herm : X q p = star (X p q) := by
    apply Complex.ext <;> simp <;> linarith
  refine ⟨herm, ?_⟩
  have k1 := (Q (-(X p q)) ((X p p).re : ℂ)).2
  have k2 := (Q ((X q q).re : ℂ) (-(star (X p q)))).2
  have k3 := (Q (-(X p q)) 1).2
  rw [herm] at k1 k2 k3
  simp [Complex.mul_im, Complex.mul_re, hp1, hq1] at k1 k2 k3
  rw [Complex.sq_norm, Complex.normSq_apply]
  set P := (X p p).re
  set R := (X q q).re
  set u := (X p q).re
  set v := (X p q).im
  rcases hp2.lt_or_eq with hP0 | hP0
  · by_contra hc
    push Not at hc
    nlinarith [mul_pos hP0 (sub_pos.2 hc)]
  · rcases hq2.lt_or_eq with hR0 | hR0
    · rw [← hP0] at k2 ⊢
      nlinarith [mul_pos hR0 hR0]
    · rw [← hP0, ← hR0] at k3 ⊢
      nlinarith

/-- the entanglement witness functional -/
def nsbW (N : ℕ) (x y : ℝ) (Y : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ) : ℝ :=
  x * (Y (0, N) (0, N)).re + y * (Y (N, 0) (N, 0)).re - (Y (0, 0) (N, N)).re -
    (Y (N, N) (0, 0)).re

lemma nsb_W_sub (N : ℕ) (x y : ℝ) (A B : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ) :
    nsbW N x y (A - B) = nsbW N x y A - nsbW N x y B := by
  simp only [nsbW, Matrix.sub_apply, Complex.sub_re]
  ring

lemma nsb_W_prod {N : ℕ} (hN : N ≠ 0) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x * y = 1)
    (A B : State ℕ) : 0 ≤ nsbW N x y (productCoeff A.coefficients B.coefficients) := by
  have h0N : (0 : ℕ) ≠ N := Ne.symm hN
  obtain ⟨hA, csA⟩ := nsb_psd_two A.density.2.1 h0N
  obtain ⟨hB, csB⟩ := nsb_psd_two B.density.2.1 h0N
  obtain ⟨a01, a02⟩ := nsb_psd_diag A.density.2.1 0
  obtain ⟨aN1, aN2⟩ := nsb_psd_diag A.density.2.1 N
  obtain ⟨b01, b02⟩ := nsb_psd_diag B.density.2.1 0
  obtain ⟨bN1, bN2⟩ := nsb_psd_diag B.density.2.1 N
  simp only [nsbW, productCoeff]
  rw [hA, hB]
  set z := A.coefficients 0 N * B.coefficients 0 N with hz
  have hzc : (star (A.coefficients 0 N) * star (B.coefficients 0 N)).re = z.re := by
    rw [hz]; simp [Complex.mul_re]
  rw [hzc]
  have hre : z.re ≤ ‖A.coefficients 0 N‖ * ‖B.coefficients 0 N‖ := by
    rw [← norm_mul]; exact Complex.re_le_norm _
  simp only [Complex.mul_re, a01, aN1, b01, bN1, mul_zero, sub_zero]
  set k := ‖A.coefficients 0 N‖ * ‖B.coefficients 0 N‖
  set P := (A.coefficients 0 0).re * (B.coefficients N N).re
  set Q := (A.coefficients N N).re * (B.coefficients 0 0).re
  have hk0 : 0 ≤ k := by positivity
  have hP0 : 0 ≤ P := mul_nonneg a02 bN2
  have hQ0 : 0 ≤ Q := mul_nonneg aN2 b02
  have hk2 : k ^ 2 ≤ P * Q := by
    have : k ^ 2 = ‖A.coefficients 0 N‖ ^ 2 * ‖B.coefficients 0 N‖ ^ 2 := by ring
    rw [this]
    calc _ ≤ ((A.coefficients 0 0).re * (A.coefficients N N).re) *
          ((B.coefficients 0 0).re * (B.coefficients N N).re) :=
          mul_le_mul csA csB (sq_nonneg _) (mul_nonneg a02 aN2)
      _ = P * Q := by ring
  have : 2 * k ≤ x * P + y * Q := by
    by_contra hc
    push Not at hc
    have hxP : 0 ≤ x * P + y * Q := by positivity
    have h1 : (x * P + y * Q) ^ 2 < (2 * k) ^ 2 := by
      exact pow_lt_pow_left₀ hc hxP two_ne_zero
    nlinarith [sq_nonneg (x * P - y * Q)]
  linarith

lemma nsb_W_hull {N : ℕ} (hN : N ≠ 0) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x * y = 1) :
    ∀ Y ∈ convexHull ℝ (productStates ℕ ℕ), 0 ≤ nsbW N x y Y := by
  intro Y hY
  have hsub : productStates ℕ ℕ ⊆ {Y | 0 ≤ nsbW N x y Y} := by
    rintro _ ⟨A, B, rfl⟩
    exact nsb_W_prod hN hx hy hxy A B
  have hconv : Convex ℝ {Y : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ | 0 ≤ nsbW N x y Y} := by
    intro Y1 h1 Y2 h2 a b ha hb _
    simp only [Set.mem_setOf_eq] at *
    have : nsbW N x y (a • Y1 + b • Y2) = a * nsbW N x y Y1 + b * nsbW N x y Y2 := by
      simp only [nsbW, Matrix.add_apply, Matrix.smul_apply, Complex.add_re, Complex.smul_re,
        smul_eq_mul]
      ring
    rw [this]
    positivity
  exact convexHull_min hsub hconv hY

lemma nsb_ev_A (h : HamiltonianData) : ∀ᶠ N in atTop, 1 ≤ h.energyA N - h.energyA 0 := by
  have hex : ∃ N, 1 ≤ h.energyA N - h.energyA 0 := by
    by_contra hne
    push Not at hne
    have hs := (h.gibbs 1 one_pos).comp_injective (i := fun n : ℕ => (n, (0 : ℕ)))
      (fun a b hab => by simpa using hab)
    have ht := hs.tendsto_atTop_zero
    have hc : 0 < Real.exp (-1 * (h.energyA 0 + 1 + h.energyB 0)) := Real.exp_pos _
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hc)).exists
    simp only [Function.comp] at hn
    have : Real.exp (-1 * (h.energyA 0 + 1 + h.energyB 0)) ≤
        Real.exp (-1 * (h.energyA n + h.energyB 0)) :=
      Real.exp_le_exp.2 (by linarith [hne n])
    linarith
  obtain ⟨N0, hN0⟩ := hex
  exact eventually_atTop.2 ⟨N0, fun n hn => le_trans hN0 (by linarith [h.orderedA hn])⟩

lemma nsb_ev_B (h : HamiltonianData) : ∀ᶠ N in atTop, 1 ≤ h.energyB N - h.energyB 0 := by
  have hex : ∃ N, 1 ≤ h.energyB N - h.energyB 0 := by
    by_contra hne
    push Not at hne
    have hs := (h.gibbs 1 one_pos).comp_injective (i := fun n : ℕ => ((0 : ℕ), n))
      (fun a b hab => by simpa using hab)
    have ht := hs.tendsto_atTop_zero
    have hc : 0 < Real.exp (-1 * (h.energyA 0 + (h.energyB 0 + 1))) := Real.exp_pos _
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hc)).exists
    simp only [Function.comp] at hn
    have : Real.exp (-1 * (h.energyA 0 + (h.energyB 0 + 1))) ≤
        Real.exp (-1 * (h.energyA 0 + h.energyB n)) :=
      Real.exp_le_exp.2 (by linarith [hne n])
    linarith
  obtain ⟨N0, hN0⟩ := hex
  exact eventually_atTop.2 ⟨N0, fun n hn => le_trans hN0 (by linarith [h.orderedB hn])⟩

lemma nsb_ar1 {a b u η : ℝ} (hA : 1 ≤ a) (hb : 0 ≤ b) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hbu : b * u < η) (hη1 : η ≤ 1) : b / a * u ^ 2 * (a + b) ≤ 2 * η := by
  have ha : 0 < a := by linarith
  have e : b / a * u ^ 2 * (a + b) = b * u * u + (b * u) ^ 2 / a := by
    field_simp
  rw [e]
  have h1 : (b * u) ^ 2 / a ≤ (b * u) ^ 2 := div_le_self (sq_nonneg _) hA
  have h2 : 0 ≤ b * u := mul_nonneg hb hu0
  have h3 : b * u * u ≤ b * u := mul_le_of_le_one_right h2 hu1
  have h4 : (b * u) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ h2 hbu.le 2
  have h5 : η ^ 2 ≤ η := by nlinarith
  linarith

lemma nsb_arL {p q r E η t c β : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hE : 0 < E)
    (h1 : p ^ 2 * E ≤ 2 * η) (h2 : q ^ 2 * E ≤ 2 * η) (h3 : r ^ 2 * E ≤ 4 * η)
    (hη : η = t ^ 2 * c / 72) (ht : 0 < t) (hc : 0 < c) (hβ0 : 0 < β) (hβ2 : β ^ 2 = c / E) :
    p + q + r < t * β := by
  have hsq : (p + q + r) ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) := by
    nlinarith [sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (q - r)]
  have htb : (t * β) ^ 2 * E = t ^ 2 * c := by
    rw [mul_pow, hβ2]; field_simp
  have hA : (p + q + r) ^ 2 * E ≤ 3 * (p ^ 2 * E + q ^ 2 * E + r ^ 2 * E) := by
    have := mul_le_mul_of_nonneg_right hsq hE.le
    linarith
  have htc : 0 < t ^ 2 * c := by positivity
  have hlt : (p + q + r) ^ 2 * E < (t * β) ^ 2 * E := by
    rw [htb]; rw [hη] at h1 h2 h3; linarith
  have hlt' : (p + q + r) ^ 2 < (t * β) ^ 2 := lt_of_mul_lt_mul_right hlt hE.le
  have htb0 : 0 ≤ t * β := by positivity
  exact lt_of_pow_lt_pow_left₀ 2 htb0 hlt'

set_option maxHeartbeats 2000000 in
theorem nsb_main (h : HamiltonianData) (epsilon M : ℝ)
    (hepsilon : 0 < epsilon) (hM : 0 < M) (sigma : State (ℕ × ℕ))
    (hsigma : sigma ∈ energyBound h M) :
    ∃ rho : State (ℕ × ℕ), rho ∈ energyBound h M ∧
      ¬ IsSeparable rho.coefficients ∧
      traceSize (sigma.coefficients - rho.coefficients) < ENNReal.ofReal epsilon := by
  have hD := sigma.density
  set X := sigma.coefficients with hXdef
  obtain ⟨⟨e⟩, hPSD, hSum, hTr⟩ := hD
  set S := ∑' n, ‖e.left n‖ * ‖e.right n‖ with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hdiag : ∀ p, (X p p).im = 0 ∧ 0 ≤ (X p p).re := fun p => nsb_psd_diag hPSD p
  have hd1 : ∀ p, (X p p).re ≤ 1 := fun p => by
    rw [← hTr]; exact hSum.le_tsum p (fun q _ => (hdiag q).2)
  set L0 := levelEnergy h (0, 0) with hL0
  have hen : ∀ p : ℕ × ℕ, 0 ≤ levelEnergy h p - L0 := fun p =>
    sub_nonneg.2 (add_le_add (h.orderedA (Nat.zero_le _)) (h.orderedB (Nat.zero_le _)))
  set g : ℕ × ℕ → ℝ := fun p => (levelEnergy h p - L0) * (X p p).re with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => mul_nonneg (hen p) (hdiag p).2
  have hmean : ((L0 : EReal) + ((∑' p, ENNReal.ofReal (g p) : ℝ≥0∞) : EReal)) < (M : EReal) :=
    hsigma
  have hT : (∑' p, ENNReal.ofReal (g p)) ≠ ⊤ := by
    intro hT
    rw [hT, EReal.coe_ennreal_top, EReal.coe_add_top] at hmean
    exact absurd hmean (not_lt.2 le_top)
  have hgs : Summable g :=
    (ENNReal.summable_toReal hT).congr (fun p => ENNReal.toReal_ofReal (hg0 p))
  set K := ∑' p, g p with hKdef
  have hK0 : 0 ≤ K := tsum_nonneg hg0
  have hTK : (∑' p, ENNReal.ofReal (g p)) = ENNReal.ofReal K :=
    (ENNReal.ofReal_tsum_of_nonneg hg0 hgs).symm
  have hKM : L0 + K < M := by
    rw [hTK, EReal.coe_ennreal_ofReal, max_eq_left hK0, ← EReal.coe_add,
      EReal.coe_lt_coe_iff] at hmean
    exact hmean
  have hgap : 0 < M - L0 - K := by linarith
  -- parameters
  set t := min (1 / 2 : ℝ) (epsilon / (2 * (S + 4))) with htdef
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hepsilon (by positivity))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have hte : t ≤ epsilon / (2 * (S + 4)) := min_le_right _ _
  set c := min (1 / 2 : ℝ) ((M - L0 - K) / 2) with hcdef
  have hc0 : 0 < c := lt_min (by norm_num) (by linarith)
  have hc1 : c ≤ 1 / 2 := min_le_left _ _
  have hcg : c ≤ (M - L0 - K) / 2 := min_le_right _ _
  set η := t ^ 2 * c / 72 with hηdef
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    have : t ^ 2 ≤ 1 := by nlinarith
    rw [hηdef, div_le_one (by norm_num)]
    nlinarith
  -- choose N
  have inj1 : Function.Injective (fun N : ℕ => ((0 : ℕ), N)) := fun a b hab => by simpa using hab
  have inj2 : Function.Injective (fun N : ℕ => (N, (0 : ℕ))) := fun a b hab => by simpa using hab
  have inj3 : Function.Injective (fun N : ℕ => (N, N)) := fun a b hab => by simpa using hab
  have hu : ∀ᶠ N in atTop, g (0, N) < η :=
    ((hgs.comp_injective inj1).tendsto_atTop_zero).eventually (gt_mem_nhds hη0)
  have hv : ∀ᶠ N in atTop, g (N, 0) < η :=
    ((hgs.comp_injective inj2).tendsto_atTop_zero).eventually (gt_mem_nhds hη0)
  have hw : ∀ᶠ N in atTop, g (N, N) < η :=
    ((hgs.comp_injective inj3).tendsto_atTop_zero).eventually (gt_mem_nhds hη0)
  obtain ⟨N, hN1, hA, hB, hu, hv, hw⟩ := ((eventually_ge_atTop 1).and
    ((nsb_ev_A h).and ((nsb_ev_B h).and (hu.and (hv.and hw))))).exists
  have hNz : N ≠ 0 := by omega
  set a := h.energyA N - h.energyA 0 with hadef
  set b := h.energyB N - h.energyB 0 with hbdef
  have heNN : levelEnergy h (N, N) - L0 = a + b := by
    simp only [hL0, levelEnergy, hadef, hbdef]; ring
  have he0N : levelEnergy h (0, N) - L0 = b := by
    simp only [hL0, levelEnergy, hbdef]; ring
  have heN0 : levelEnergy h (N, 0) - L0 = a := by
    simp only [hL0, levelEnergy, hadef]; ring
  have he00 : levelEnergy h (0, 0) - L0 = 0 := by simp [hL0]
  set E := a + b with hEdef
  have hE2 : 2 ≤ E := by linarith
  have hE0 : 0 < E := by linarith
  set u := (X (0, N) (0, N)).re with hudef
  set v := (X (N, 0) (N, 0)).re with hvdef
  set w := (X (N, N) (N, N)).re with hwdef
  have hbu : b * u < η := by
    have : g (0, N) = b * u := by simp only [hg, he0N, hudef]
    linarith
  have hav : a * v < η := by
    have : g (N, 0) = a * v := by simp only [hg, heN0, hvdef]
    linarith
  have hEw : E * w < η := by
    have : g (N, N) = E * w := by simp only [hg, heNN, hwdef]
    linarith
  have hu0 : 0 ≤ u := (hdiag _).2
  have hv0 : 0 ≤ v := (hdiag _).2
  have hw0 : 0 ≤ w := (hdiag _).2
  have hu1 : u ≤ 1 := hd1 _
  have hv1 : v ≤ 1 := hd1 _
  -- the entangled admixture
  have hcE : c / E ≤ 1 / 4 := by
    rw [div_le_iff₀ hE0]; nlinarith
  have hcE0 : 0 ≤ c / E := div_nonneg hc0.le hE0.le
  set β := Real.sqrt (c / E) with hβdef
  set α := Real.sqrt (1 - c / E) with hαdef
  have hβ2 : β ^ 2 = c / E := Real.sq_sqrt hcE0
  have hα2 : α ^ 2 = 1 - c / E := Real.sq_sqrt (by linarith)
  have hβ0 : 0 < β := Real.sqrt_pos.2 (div_pos hc0 hE0)
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hαh : 1 / 2 ≤ α := by
    have h14 : Real.sqrt (1 / 4) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [← h14]; exact Real.sqrt_le_sqrt (by linarith)
  have hα1 : α ≤ 1 := (Real.sqrt_le_sqrt (by linarith : 1 - c / E ≤ 1)).trans_eq Real.sqrt_one
  have hβ1 : β ≤ 1 := (Real.sqrt_le_sqrt (by linarith : c / E ≤ 1)).trans_eq Real.sqrt_one
  have hNN00 : ((N, N) : ℕ × ℕ) ≠ (0, 0) := by simp [hNz]
  have h0NN : ((0, 0) : ℕ × ℕ) ≠ (N, N) := fun h' => hNN00 h'.symm
  set ψ : ℕ × ℕ → ℝ := fun p => (if p = (0, 0) then α else 0) + (if p = (N, N) then β else 0)
    with hψdef
  have hψ00 : ψ (0, 0) = α := by simp [hψdef, h0NN]
  have hψNN : ψ (N, N) = β := by simp [hψdef, hNN00]
  have hψ0 : ∀ p, p ≠ (0, 0) → p ≠ (N, N) → ψ p = 0 := by
    intro p h1 h2; simp [hψdef, h1, h2]
  have hψ0N : ψ (0, N) = 0 := hψ0 _ (by simp; omega) (by simp; omega)
  have hψN0 : ψ (N, 0) = 0 := hψ0 _ (by simp; omega) (by simp; omega)
  set Φ : Hilbert (ℕ × ℕ) := (α : ℂ) • lp.single 2 ((0 : ℕ), (0 : ℕ)) (1 : ℂ) +
    (β : ℂ) • lp.single 2 (N, N) (1 : ℂ) with hΦdef
  have hΦ : ∀ p, Φ p = (ψ p : ℂ) := by
    intro p
    simp only [hΦdef, hψdef, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
      lp.single_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hΦn : ‖Φ‖ ≤ 2 := by
    calc ‖Φ‖ ≤ ‖((α : ℂ) • lp.single 2 ((0 : ℕ), (0 : ℕ)) (1 : ℂ) : Hilbert (ℕ × ℕ))‖ +
          ‖((β : ℂ) • lp.single 2 (N, N) (1 : ℂ) : Hilbert (ℕ × ℕ))‖ := by
          rw [hΦdef]; exact norm_add_le _ _
      _ = α + β := by
          have n1 : ‖((α : ℂ) • lp.single 2 ((0 : ℕ), (0 : ℕ)) (1 : ℂ) : Hilbert (ℕ × ℕ))‖ = α := by
            rw [norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
            simp [abs_of_nonneg hα0]
          have n2 : ‖((β : ℂ) • lp.single 2 (N, N) (1 : ℂ) : Hilbert (ℕ × ℕ))‖ = β := by
            rw [norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
            simp [abs_of_nonneg hβ0.le]
          rw [n1, n2]
      _ ≤ 2 := by linarith
  set R : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
    fun i j => ((1 - t : ℝ) : ℂ) * X i j + ((t : ℝ) : ℂ) * (Φ i * star (Φ j)) with hRdef
  have hRre : ∀ i j, (R i j).re = (1 - t) * (X i j).re + t * (ψ i * ψ j) := by
    intro i j
    simp only [hRdef, hΦ, Complex.add_re, Complex.re_ofReal_mul]
    simp
  have hψs : ∀ p, p ∉ ({(0, 0), (N, N)} : Finset (ℕ × ℕ)) → ψ p * ψ p = 0 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    rw [hψ0 p hp.1 hp.2]; ring
  have hψsum : Summable (fun p => ψ p * ψ p) := summable_of_ne_finset_zero hψs
  have hψtsum : ∑' p, ψ p * ψ p = 1 := by
    rw [tsum_eq_sum hψs, Finset.sum_pair h0NN, hψ00, hψNN]
    nlinarith
  have hRdens : IsDensity R := by
    refine ⟨⟨nsbExp e _ _ Φ Φ⟩, ?_, ?_, ?_⟩
    · intro s z
      have hq := hPSD s z
      set wv := ∑ i ∈ s, star (z i) * Φ i with hwv
      have key : (∑ i ∈ s, ∑ j ∈ s, star (z i) * R i j * z j) =
          ((1 - t : ℝ) : ℂ) * (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j) +
          ((t : ℝ) : ℂ) * (wv * star wv) := by
        rw [hwv, star_sum, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [hRdef, star_mul', star_star]
        ring
      have hn : wv * star wv = ((Complex.normSq wv : ℝ) : ℂ) := Complex.mul_conj wv
      rw [key, hn]
      constructor
      · rw [Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, hq.1,
          Complex.ofReal_im]
        ring
      · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re]
        exact add_nonneg (mul_nonneg (by linarith) hq.2)
          (mul_nonneg ht0.le (Complex.normSq_nonneg _))
    · exact ((hSum.mul_left (1 - t)).add (hψsum.mul_left t)).congr
        (fun p => (hRre p p).symm)
    · rw [tsum_congr (fun p => hRre p p), Summable.tsum_add (hSum.mul_left (1 - t))
        (hψsum.mul_left t), tsum_mul_left, tsum_mul_left, hTr, hψtsum]
      ring
  let rho : State (ℕ × ℕ) := ⟨R, hRdens⟩
  refine ⟨rho, ?_, ?_, ?_⟩
  · -- energy
    show (L0 : EReal) + ((∑' p, ENNReal.ofReal ((levelEnergy h p - L0) * (R p p).re) :
      ℝ≥0∞) : EReal) < (M : EReal)
    have hpt : ∀ p, ENNReal.ofReal ((levelEnergy h p - L0) * (R p p).re) ≤
        ENNReal.ofReal (g p) + ENNReal.ofReal ((levelEnergy h p - L0) * (t * (ψ p * ψ p))) := by
      intro p
      rw [hRre p p]
      refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
      have h1 := hen p
      have h2 := (hdiag p).2
      have h3 : 0 ≤ (levelEnergy h p - L0) * (X p p).re := mul_nonneg h1 h2
      have h4 : 0 ≤ t * ((levelEnergy h p - L0) * (X p p).re) := mul_nonneg ht0.le h3
      have e5 : (levelEnergy h p - L0) * ((1 - t) * (X p p).re + t * (ψ p * ψ p)) =
          (levelEnergy h p - L0) * (X p p).re + (levelEnergy h p - L0) * (t * (ψ p * ψ p)) -
          t * ((levelEnergy h p - L0) * (X p p).re) := by ring
      rw [e5]
      simp only [hg]
      linarith
    have hsecond : ∑' p, ENNReal.ofReal ((levelEnergy h p - L0) * (t * (ψ p * ψ p))) =
        ENNReal.ofReal (t * c) := by
      rw [tsum_eq_single (N, N)]
      · rw [heNN, hψNN]
        congr 1
        have : β * β = c / E := by rw [← hβ2]; ring
        rw [this]
        field_simp
      · intro p hp
        by_cases h0 : p = (0, 0)
        · subst h0; simp [he00]
        · rw [hψ0 p h0 hp]; simp
    have hle : (∑' p, ENNReal.ofReal ((levelEnergy h p - L0) * (R p p).re)) ≤
        ENNReal.ofReal (K + t * c) := by
      calc _ ≤ ∑' p, (ENNReal.ofReal (g p) +
            ENNReal.ofReal ((levelEnergy h p - L0) * (t * (ψ p * ψ p)))) :=
            ENNReal.tsum_le_tsum hpt
        _ = ENNReal.ofReal K + ENNReal.ofReal (t * c) := by
            rw [ENNReal.tsum_add, hsecond, hTK]
        _ = ENNReal.ofReal (K + t * c) := (ENNReal.ofReal_add hK0 (by positivity)).symm
    calc (L0 : EReal) + ((∑' p, ENNReal.ofReal ((levelEnergy h p - L0) * (R p p).re) :
          ℝ≥0∞) : EReal)
        ≤ (L0 : EReal) + ((ENNReal.ofReal (K + t * c) : ℝ≥0∞) : EReal) :=
          add_le_add le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.2 hle)
      _ = ((L0 + (K + t * c) : ℝ) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left (by have := mul_pos ht0 hc0; linarith), ← EReal.coe_add]
      _ < (M : EReal) := by
          rw [EReal.coe_lt_coe_iff]
          have := mul_le_mul ht1 hcg hc0.le (by norm_num)
          linarith
  · -- not separable
    intro hsep
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    set x := Real.sqrt (b / a) with hxdef
    set y := Real.sqrt (a / b) with hydef
    have hx0 : 0 < x := Real.sqrt_pos.2 (div_pos hb0 ha0)
    have hy0 : 0 < y := Real.sqrt_pos.2 (div_pos ha0 hb0)
    have hx2 : x ^ 2 = b / a := Real.sq_sqrt (div_nonneg hb0.le ha0.le)
    have hy2 : y ^ 2 = a / b := Real.sq_sqrt (div_nonneg ha0.le hb0.le)
    have hxy : x * y = 1 := by
      rw [hxdef, hydef, ← Real.sqrt_mul (div_nonneg hb0.le ha0.le)]
      rw [div_mul_div_comm, mul_comm b a, div_self (by positivity), Real.sqrt_one]
    have hWR : nsbW N x y R = (1 - t) * nsbW N x y X - 2 * t * α * β := by
      simp only [nsbW, hRre, hψ0N, hψN0, hψ00, hψNN]
      ring
    obtain ⟨hherm, hcs⟩ := nsb_psd_two hPSD h0NN
    set mm := ‖X (0, 0) (N, N)‖ with hmmdef
    have hmm0 : 0 ≤ mm := norm_nonneg _
    have hWX : nsbW N x y X ≤ x * u + y * v + 2 * mm := by
      simp only [nsbW]
      rw [hherm]
      have h1 : -(X (0, 0) (N, N)).re ≤ mm :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      have h2 : (star (X (0, 0) (N, N))).re = (X (0, 0) (N, N)).re := Complex.conj_re _
      rw [h2]
      linarith
    have hmm2 : mm ^ 2 ≤ w := hcs.trans (mul_le_of_le_one_left hw0 (hd1 _))
    have hτ1 : (x * u) ^ 2 * E ≤ 2 * η := by
      rw [mul_pow, hx2, hEdef]; exact nsb_ar1 hA hb0.le hu0 hu1 hbu hη1
    have hτ2 : (y * v) ^ 2 * E ≤ 2 * η := by
      rw [mul_pow, hy2, hEdef, add_comm a b]; exact nsb_ar1 hB ha0.le hv0 hv1 hav hη1
    have hτ3 : (2 * mm) ^ 2 * E ≤ 4 * η := by
      have h1 := mul_le_mul_of_nonneg_right hmm2 hE0.le
      have e : (2 * mm) ^ 2 * E = 4 * (mm ^ 2 * E) := by ring
      rw [e]; linarith
    have hL0 : 0 ≤ x * u + y * v + 2 * mm := by positivity
    have hLt : x * u + y * v + 2 * mm < t * β :=
      nsb_arL (by positivity) (by positivity) (by positivity) hE0 hτ1 hτ2 hτ3 hηdef ht0 hc0
        hβ0 hβ2
    have hWRneg : nsbW N x y R < 0 := by
      rw [hWR]
      have h1 : (1 - t) * nsbW N x y X ≤ (1 - t) * (x * u + y * v + 2 * mm) :=
        mul_le_mul_of_nonneg_left hWX (by linarith)
      have h2 : (1 - t) * (x * u + y * v + 2 * mm) ≤ x * u + y * v + 2 * mm :=
        mul_le_of_le_one_left hL0 (by linarith)
      have h3 : t * β ≤ 2 * t * α * β := by
        have e : 2 * t * α * β - t * β = t * β * (2 * α - 1) := by ring
        have := mul_nonneg (mul_pos ht0 hβ0).le (by linarith : (0:ℝ) ≤ 2 * α - 1)
        linarith
      linarith
    set δ := -(nsbW N x y R) / (x + y + 2) with hδdef
    have hxy2 : 0 < x + y + 2 := by positivity
    have hδ : 0 < δ := div_pos (by linarith) hxy2
    obtain ⟨Y, hYmem, hYd⟩ := hsep δ hδ
    have hYpos := nsb_W_hull hNz hx0 hy0 hxy Y hYmem
    have e1 := nsb_entry_lt hYd (0, N) (0, N)
    have e2 := nsb_entry_lt hYd (N, 0) (N, 0)
    have e3 := nsb_entry_lt hYd (0, 0) (N, N)
    have e4 := nsb_entry_lt hYd (N, N) (0, 0)
    have hlin := nsb_W_sub N x y R Y
    have hlow : -((x + y + 2) * δ) < nsbW N x y (R - Y) := by
      have q1 : -δ < ((R - Y) (0, N) (0, N)).re := by
        linarith [neg_abs_le ((R - Y) (0, N) (0, N)).re, Complex.abs_re_le_norm ((R - Y) (0, N) (0, N))]
      have q2 : -δ < ((R - Y) (N, 0) (N, 0)).re := by
        linarith [neg_abs_le ((R - Y) (N, 0) (N, 0)).re, Complex.abs_re_le_norm ((R - Y) (N, 0) (N, 0))]
      have q3 : ((R - Y) (0, 0) (N, N)).re < δ := by
        linarith [le_abs_self ((R - Y) (0, 0) (N, N)).re, Complex.abs_re_le_norm ((R - Y) (0, 0) (N, N))]
      have q4 : ((R - Y) (N, N) (0, 0)).re < δ := by
        linarith [le_abs_self ((R - Y) (N, N) (0, 0)).re, Complex.abs_re_le_norm ((R - Y) (N, N) (0, 0))]
      have r1 := mul_lt_mul_of_pos_left q1 hx0
      have r2 := mul_lt_mul_of_pos_left q2 hy0
      simp only [nsbW]
      linarith
    have hδeq : (x + y + 2) * δ = -(nsbW N x y R) := by
      rw [hδdef]; field_simp
    linarith
  · -- distance
    show traceSize (X - R) < ENNReal.ofReal epsilon
    have hXR : X - R = fun i j => ((t : ℝ) : ℂ) * X i j + (-((t : ℝ) : ℂ)) * (Φ i * star (Φ j)) := by
      funext i j
      show X i j - R i j = _
      simp only [hRdef]
      push_cast
      ring
    rw [hXR]
    refine (nsb_traceSize_le e _ _ Φ Φ).trans_lt ?_
    rw [ENNReal.ofReal_lt_ofReal_iff hepsilon]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have h4 : ‖Φ‖ * ‖Φ‖ ≤ 2 * 2 := mul_le_mul hΦn hΦn (norm_nonneg _) (by norm_num)
    have h5 : t * (2 * (S + 4)) ≤ epsilon := (le_div_iff₀ (by positivity)).1 hte
    have h6 : t * ‖Φ‖ * ‖Φ‖ ≤ t * (2 * 2) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h4 ht0.le
    have h7 : t * S ≥ 0 := mul_nonneg ht0.le hS0
    have h8 : t * ∑' (n : ℕ), ‖e.left n‖ * ‖e.right n‖ = t * S := by rw [hSdef]
    linarith

theorem noSeparableBall (h : HamiltonianData) (epsilon M : ℝ)
    (hepsilon : 0 < epsilon) (hM : 0 < M) (sigma : State (ℕ × ℕ))
    (hsigma : sigma ∈ energyBound h M) :
    ∃ rho : State (ℕ × ℕ), rho ∈ energyBound h M ∧
      ¬ IsSeparable rho.coefficients ∧
      traceSize (sigma.coefficients - rho.coefficients) < ENNReal.ofReal epsilon :=
  nsb_main h epsilon M hepsilon hM sigma hsigma

end QAlgorithms.Papers.Independent.Gap20.P05

end


-- Platform entry point: restates the target verbatim.
noncomputable section

open Filter

open scoped ENNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap20.P05

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity rankOne traceSize traceClosure IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (generalizedRelativeEntropy traceSecond)

open QAlgorithms.Entanglement (partialTransposeFirst)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartitePower)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

/-- Proposition 10, PDF pp.13--14 (advertised on p.1): entangled states are dense
inside every strict energy sublevel. Entangled means outside the trace-norm closed
convex hull D. The flawed stronger energy inequality in the proof is not asserted. -/
theorem _root_.solution (h : HamiltonianData) (epsilon M : ℝ)
    (hepsilon : 0 < epsilon) (hM : 0 < M) (sigma : State (ℕ × ℕ))
    (hsigma : sigma ∈ energyBound h M) :
    ∃ rho : State (ℕ × ℕ), rho ∈ energyBound h M ∧
      ¬ IsSeparable rho.coefficients ∧
      traceSize (sigma.coefficients - rho.coefficients) < ENNReal.ofReal epsilon := by
  apply @QAlgorithms.Papers.Independent.Gap20.P05.noSeparableBall <;> assumption

end QAlgorithms.Papers.Independent.Gap20.P05

end
