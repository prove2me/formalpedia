-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.stationaryResourceNonmonotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:08:03.518085+00:00
-- url     : https://prove2.me/submissions/1b45185d-72e6-47b0-9cd4-924378a304b7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace X7P32Stat

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32

lemma rho_herm (p : ℝ) (c : ℂ) : (rho p c).IsHermitian := by
  ext i j
  cases i <;> cases j <;> simp [rho, Matrix.conjTranspose_apply]

lemma cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma rho_trace (p : ℝ) (c : ℂ) : (rho p c).trace = 1 := by
  simp [Matrix.trace, rho]

lemma rho_det (p : ℝ) (c : ℂ) : (rho p c).det = ((p * (1 - p) - Complex.normSq c : ℝ) : ℂ) := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm, Matrix.det_fin_two]
  simp [rho, finTwoEquiv, Complex.normSq_eq_conj_mul_self]
  ring

lemma vn_rho (p : ℝ) (c : ℂ) :
    Real.log 2 * vnEntropy (rho p c) =
      Real.binEntropy ((1 + Real.sqrt ((2 * p - 1) ^ 2 + 4 * Complex.normSq c)) / 2) := by
  have hH := rho_herm p c
  have htr := hH.trace_eq_sum_eigenvalues
  have hdet := hH.det_eq_prod_eigenvalues
  rw [rho_trace] at htr
  rw [rho_det] at hdet
  simp only [Fintype.sum_bool, Fintype.prod_bool] at htr hdet
  have h1 : hH.eigenvalues true + hH.eigenvalues false = 1 := by
    have := congrArg Complex.re htr; simp at this; linarith
  have h2 : hH.eigenvalues true * hH.eigenvalues false = p * (1 - p) - Complex.normSq c := by
    have := congrArg Complex.re hdet; simp at this; linarith
  have hv : vnEntropy (rho p c) = -(hH.eigenvalues true * Real.logb 2 (hH.eigenvalues true) +
      hH.eigenvalues false * Real.logb 2 (hH.eigenvalues false)) := by
    unfold vnEntropy
    rw [cfc_trace hH]
    simp
  generalize hH.eigenvalues = e at h1 h2 hv
  have hl2 : Real.log 2 ≠ 0 := by positivity
  have hb : Real.log 2 * vnEntropy (rho p c) = Real.binEntropy (e true) := by
    rw [hv, Real.binEntropy]
    have : 1 - e true = e false := by linarith
    rw [this]
    simp only [Real.logb, Real.log_inv]
    field_simp
    ring
  rw [hb]
  set s := Real.sqrt ((2 * p - 1) ^ 2 + 4 * Complex.normSq c) with hs
  have hs2 : s ^ 2 = (2 * p - 1) ^ 2 + 4 * Complex.normSq c :=
    Real.sq_sqrt (by have := Complex.normSq_nonneg c; positivity)
  have hq : (e true - (1 + s) / 2) * (e true - (1 - (1 + s) / 2)) = 0 := by
    have : e false = 1 - e true := by linarith
    rw [this] at h2
    linear_combination (-1 : ℝ) * h2 - hs2 / 4
  rcases mul_eq_zero.1 hq with h | h
  · rw [show e true = (1 + s) / 2 by linarith]
  · rw [show e true = 1 - (1 + s) / 2 by linarith, Real.binEntropy_one_sub]

lemma diag_rho (p : ℝ) (c : ℂ) : diagonal (rho p c) = rho p 0 := by
  ext i j
  cases i <;> cases j <;> simp [diagonal, rho]

lemma vn_rho0 (p : ℝ) : Real.log 2 * vnEntropy (rho p 0) = Real.binEntropy p := by
  rw [vn_rho]
  simp only [map_zero, mul_zero, add_zero]
  rw [Real.sqrt_sq_eq_abs]
  rcases le_total 0 (2 * p - 1) with h | h
  · rw [abs_of_nonneg h]; congr 1; ring
  · rw [abs_of_nonpos h, show (1 + -(2 * p - 1)) / 2 = 1 - p by ring, Real.binEntropy_one_sub]

lemma resEnt_rho (p : ℝ) (c : ℂ) : resourceEntropy (rho p c) =
    Real.binEntropy p -
      Real.binEntropy ((1 + Real.sqrt ((2 * p - 1) ^ 2 + 4 * Complex.normSq c)) / 2) := by
  unfold resourceEntropy
  rw [mul_sub, diag_rho, vn_rho0, vn_rho]

lemma resL1_rho (p : ℝ) (c : ℂ) : resourceL1 (rho p c) = 2 * ‖c‖ := by
  simp [resourceL1, QAlgorithms.Coherence.l1Coherence, Fin.sum_univ_two, rho, Finset.sum_filter]
  ring

lemma four_point {h : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Icc 0 1) h) {x y d : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) (hd : 0 ≤ d) (hyd : y + d ≤ 1) : h x + h (y + d) ≤ h y + h (x + d) := by
  rcases eq_or_lt_of_le (show 0 ≤ y + d - x by linarith) with hL | hL
  · have hy : y = x := by linarith
    have hd0 : d = 0 := by linarith
    subst hy hd0; simp
  set L := y + d - x with hLdef
  have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx, by linarith⟩
  have hyI : y + d ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, hyd⟩
  have w1 : 0 ≤ (y - x) / L := div_nonneg (by linarith) hL.le
  have w2 : 0 ≤ d / L := div_nonneg hd hL.le
  have hsum : (y - x) / L + d / L = 1 := by field_simp; ring
  have hsum' : d / L + (y - x) / L = 1 := by linarith
  have k1 := hc.2 hxI hyI w1 w2 hsum
  have k2 := hc.2 hxI hyI w2 w1 hsum'
  have e1 : ((y - x) / L) • x + (d / L) • (y + d) = x + d := by
    simp only [smul_eq_mul]; field_simp; ring
  have e2 : (d / L) • x + ((y - x) / L) • (y + d) = y := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [e1] at k1
  rw [e2] at k2
  simp only [smul_eq_mul] at k1 k2
  have : (y - x) / L * h x + d / L * h (y + d) + (d / L * h x + (y - x) / L * h (y + d)) =
      h x + h (y + d) := by linear_combination (h x + h (y + d)) * hsum
  linarith

def J0 : ℝ := Real.arccos (-4 / 5) / 2

lemma phys (t : ℝ) (ht : t ^ 2 ≤ 3 / 16) : Physical (3 / 4) (t : ℂ) :=
  ⟨by norm_num, by norm_num, by rw [Complex.normSq_ofReal]; nlinarith⟩

def mk (t : ℝ) (ht : t ^ 2 ≤ 3 / 16) : Model :=
  ⟨J0, Real.pi, 1, 3 / 4, (t : ℂ), one_pos, phys t ht⟩

lemma angleC_mk (t : ℝ) (ht) : angleC (mk t ht) = -4 / 5 := by
  simp only [angleC, mk, J0]
  rw [show 2 * (Real.arccos (-4 / 5) / 2) * 1 = Real.arccos (-4 / 5) by ring,
    Real.cos_arccos (by norm_num) (by norm_num)]

lemma angleS_mk (t : ℝ) (ht) : angleS (mk t ht) = 3 / 5 := by
  simp only [angleS, mk, J0]
  rw [show 2 * (Real.arccos (-4 / 5) / 2) * 1 = Real.arccos (-4 / 5) by ring, Real.sin_arccos,
    show (1 : ℝ) - (-4 / 5) ^ 2 = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma sin_mk (t : ℝ) (ht) : Real.sin ((mk t ht).frequency * (mk t ht).duration) = 0 := by
  simp [mk]

lemma diffL_mk (t : ℝ) (ht) : differenceL (mk t ht) = 1 / 5 := by
  simp only [differenceL, angleC_mk]
  simp [mk]; norm_num

lemma K_mk (t : ℝ) (ht) : denominatorK (mk t ht) = (1 + 16 * t ^ 2) / 25 := by
  simp only [denominatorK, denominatorD, diffL_mk, angleC_mk, sin_mk]
  simp only [mk, Complex.normSq_ofReal]
  ring

lemma pop_mk (t : ℝ) (ht) : starPopulation (mk t ht) = 3 / 4 - 4 * t ^ 2 / (1 + 16 * t ^ 2) := by
  have hpos : (0 : ℝ) < 1 + 16 * t ^ 2 := by positivity
  simp only [starPopulation, K_mk, diffL_mk, angleC_mk]
  simp only [mk, Complex.normSq_ofReal]
  field_simp
  ring

lemma coh_mk (t : ℝ) (ht) : starCoherence (mk t ht) =
    -Complex.I * ((3 / 2 * t / (1 + 16 * t ^ 2) : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < 1 + 16 * t ^ 2 := by positivity
  have hpos' : ((1 + 16 * t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [starCoherence, K_mk, diffL_mk, angleS_mk, sin_mk]
  simp only [mk]
  push_cast at hpos' ⊢
  field_simp
  ring

lemma nsq_mk (t : ℝ) (ht) : Complex.normSq (starCoherence (mk t ht)) =
    (3 / 2 * t / (1 + 16 * t ^ 2)) ^ 2 := by
  rw [coh_mk, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I, Complex.normSq_ofReal]
  ring

lemma L1_mk (t : ℝ) (ht) : resourceL1 (starState (mk t ht)) =
    2 * Real.sqrt ((3 / 2 * t / (1 + 16 * t ^ 2)) ^ 2) := by
  rw [starState, resL1_rho, ← nsq_mk t ht, Complex.norm_def]

lemma ent_mk (t : ℝ) (ht) : resourceEntropy (starState (mk t ht)) =
    Real.binEntropy (3 / 4 - 4 * t ^ 2 / (1 + 16 * t ^ 2)) -
      Real.binEntropy ((1 + Real.sqrt ((2 * (3 / 4 - 4 * t ^ 2 / (1 + 16 * t ^ 2)) - 1) ^ 2 +
        4 * (3 / 2 * t / (1 + 16 * t ^ 2)) ^ 2)) / 2) := by
  rw [starState, resEnt_rho, nsq_mk, pop_mk]

end X7P32Stat

namespace X7P32Stat

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32

lemma ent_a (h) : resourceEntropy (starState (mk 0 h)) = 0 := by
  have hs : Real.sqrt ((2 * (3 / 4 - 4 * (0 : ℝ) ^ 2 / (1 + 16 * 0 ^ 2)) - 1) ^ 2 +
      4 * (3 / 2 * 0 / (1 + 16 * 0 ^ 2)) ^ 2) = 1 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num
  rw [ent_mk, hs]; norm_num

lemma ent_b (h) : resourceEntropy (starState (mk (2 / 5) h)) =
    Real.binEntropy (203 / 356) - Real.binEntropy (243 / 356) := by
  have hs : Real.sqrt ((2 * (3 / 4 - 4 * (2 / 5 : ℝ) ^ 2 / (1 + 16 * (2 / 5) ^ 2)) - 1) ^ 2 +
      4 * (3 / 2 * (2 / 5) / (1 + 16 * (2 / 5) ^ 2)) ^ 2) = 65 / 178 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num
  rw [ent_mk, hs]; norm_num

lemma ent_c (h) : resourceEntropy (starState (mk (217 / 520) h)) =
    Real.binEntropy (72439 / 127978) - Real.binEntropy (173543 / 255956) := by
  have hs : Real.sqrt ((2 * (3 / 4 - 4 * (217 / 520 : ℝ) ^ 2 / (1 + 16 * (217 / 520) ^ 2)) - 1) ^ 2 +
      4 * (3 / 2 * (217 / 520) / (1 + 16 * (217 / 520) ^ 2)) ^ 2) = 45565 / 127978 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num
  rw [ent_mk, hs]; norm_num

lemma ent_ab : (0 : ℝ) < Real.binEntropy (203 / 356) - Real.binEntropy (243 / 356) := by
  have := Real.binEntropy_strictAntiOn (a := 203 / 356) (b := 243 / 356)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
  linarith

lemma ent_cb : Real.binEntropy (72439 / 127978) - Real.binEntropy (173543 / 255956) <
    Real.binEntropy (203 / 356) - Real.binEntropy (243 / 356) := by
  have k := four_point Real.strictConcave_binEntropy.concaveOn (x := 72439 / 127978)
    (y := 203 / 356) (d := 28665 / 255956) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have k2 := Real.binEntropy_strictAntiOn (a := 203 / 356 + 28665 / 255956) (b := 243 / 356)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
  rw [show (72439 / 127978 : ℝ) + 28665 / 255956 = 173543 / 255956 by norm_num] at k
  linarith

end X7P32Stat

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 X7P32Stat in
theorem solution :
    ∃ a b c : Model,
      a.coupling = b.coupling ∧ b.coupling = c.coupling ∧
      a.frequency = b.frequency ∧ b.frequency = c.frequency ∧
      a.duration = b.duration ∧ b.duration = c.duration ∧ a.pA = b.pA ∧ b.pA = c.pA ∧
      1 / 2 < a.pA ∧ a.pA < 1 ∧ 0 < a.frequency ∧ angleS a ≠ 0 ∧
      0 < denominatorK a ∧ 0 < denominatorK b ∧ 0 < denominatorK c ∧
      a.cA.im = 0 ∧ b.cA.im = 0 ∧ c.cA.im = 0 ∧ 0 ≤ a.cA.re ∧
      a.cA.re < b.cA.re ∧ b.cA.re < c.cA.re ∧
      resourceL1 (starState a) < resourceL1 (starState b) ∧
      resourceL1 (starState c) < resourceL1 (starState b) ∧
      resourceEntropy (starState a) < resourceEntropy (starState b) ∧
      resourceEntropy (starState c) < resourceEntropy (starState b) := by
  have ha : (0 : ℝ) ^ 2 ≤ 3 / 16 := by norm_num
  have hb : (2 / 5 : ℝ) ^ 2 ≤ 3 / 16 := by norm_num
  have hc : (217 / 520 : ℝ) ^ 2 ≤ 3 / 16 := by norm_num
  refine ⟨X7P32Stat.mk 0 ha, X7P32Stat.mk (2 / 5) hb, X7P32Stat.mk (217 / 520) hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [X7P32Stat.mk]; norm_num
  · simp only [X7P32Stat.mk]; norm_num
  · simp only [X7P32Stat.mk]; exact Real.pi_pos
  · rw [angleS_mk]; norm_num
  · rw [K_mk]; positivity
  · rw [K_mk]; positivity
  · rw [K_mk]; positivity
  · simp [X7P32Stat.mk]
  · simp [X7P32Stat.mk]
  · simp [X7P32Stat.mk]
  · simp [X7P32Stat.mk]
  · simp only [X7P32Stat.mk, Complex.ofReal_re]; norm_num
  · simp only [X7P32Stat.mk, Complex.ofReal_re]; norm_num
  · rw [L1_mk, L1_mk, Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]; norm_num
  · rw [L1_mk, L1_mk, Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]; norm_num
  · rw [ent_a, ent_b]; exact ent_ab
  · rw [ent_c, ent_b]; exact ent_cb
