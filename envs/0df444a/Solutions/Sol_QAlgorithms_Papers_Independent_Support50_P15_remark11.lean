-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P15.remark11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:46:12.391991+00:00
-- url     : https://prove2.me/submissions/1e26ba1f-b373-4c20-b565-4374e2bc3c56

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

lemma S200M_scaled (d : ℕ) (τ : ℝ) :
    (-((τ : ℂ)⁻¹)) • optimalHamiltonian d =
      Matrix.diagonal (fun i : Fin d => if i.val = 0 then ((τ⁻¹ : ℝ) : ℂ) else 0) := by
  ext i j
  by_cases hij : i = j
  · subst hij; by_cases h0 : i.val = 0 <;> simp [optimalHamiltonian, h0]
  · simp [optimalHamiltonian, Matrix.diagonal_apply_ne _ hij]

lemma S200M_exp_diag {d : ℕ} (w : Fin d → ℂ) :
    NormedSpace.exp (Matrix.diagonal w) = Matrix.diagonal (fun i => Complex.exp (w i)) := by
  rw [Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]

/-- the Gibbs state at inverse temperature b -/
lemma S200M_gibbs (d : ℕ) (hd : 2 ≤ d) (τ : ℝ) :
    thermalFinite (optimalHamiltonian d) τ =
      family d (((d : ℝ) - 1) / (Real.exp τ⁻¹ + (d - 1))) := by
  unfold thermalFinite gibbsState
  rw [S200M_scaled, S200M_exp_diag]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hpos : 0 < Real.exp τ⁻¹ + ((d : ℝ) - 1) := by positivity
  have htr : (Matrix.diagonal (fun i : Fin d =>
      Complex.exp (if i.val = 0 then ((τ⁻¹ : ℝ) : ℂ) else 0))).trace
      = ((Real.exp τ⁻¹ + ((d : ℝ) - 1) : ℝ) : ℂ) := by
    rw [Matrix.trace_diagonal]
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rw [Fin.sum_univ_succ]
    simp [Complex.ofReal_exp]
  rw [htr]
  unfold family
  rw [← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, familyProb]
  by_cases h0 : i.val = 0
  · simp only [h0, if_true]
    rw [← Complex.ofReal_exp, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    field_simp
    ring
  · simp only [h0, if_false, Complex.exp_zero]
    rw [← Complex.ofReal_inv]
    field_simp


lemma S200M_herm (d : ℕ) : (optimalHamiltonian d).IsHermitian := by
  unfold optimalHamiltonian
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  ext i
  by_cases h0 : i.val = 0 <;> simp [h0]

lemma S200M_spec (d : ℕ) (hd : 2 ≤ d) (x : ℝ) :
    x ∈ spectrum ℝ (optimalHamiltonian d) ↔ x = -1 ∨ x = 0 := by
  rw [← spectrum.algebraMap_mem_iff ℂ, optimalHamiltonian, spectrum_diagonal]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h0 : i.val = 0
    · left; simp [h0] at hi; exact_mod_cast hi.symm
    · right; simp [h0] at hi; exact_mod_cast hi.symm
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by omega⟩, by simp⟩
    · exact ⟨⟨1, by omega⟩, by simp⟩

lemma S200M_ground (d : ℕ) (hd : 2 ≤ d) :
    groundSpaceDensity (optimalHamiltonian d) = family d 0 := by
  have hH := S200M_herm d
  have hd0 : 0 < d := by omega
  unfold groundSpaceDensity
  rw [dif_pos hd0]
  simp only []
  have he : ascEigenvalues (optimalHamiltonian d)
      ⟨0, by simpa only [Fintype.card_fin] using hd0⟩ = -1 := by
    unfold QAlgorithms.ascEigenvalues
    rw [dif_pos hH]
    have hmem : ∀ k, hH.eigenvalues₀ k = -1 ∨ hH.eigenvalues₀ k = 0 := by
      intro k
      rw [← S200M_spec d hd, hH.spectrum_real_eq_range_eigenvalues]
      refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) k, ?_⟩
      simp [Matrix.IsHermitian.eigenvalues]
    have hm1 : (-1 : ℝ) ∈ spectrum ℝ (optimalHamiltonian d) := (S200M_spec d hd _).2 (Or.inl rfl)
    rw [hH.spectrum_real_eq_range_eigenvalues] at hm1
    obtain ⟨j, hj⟩ := hm1
    set k0 : Fin (Fintype.card (Fin d)) := Fin.rev ⟨0, by simpa only [Fintype.card_fin] using hd0⟩
    have hle := hH.eigenvalues₀_antitone
      (show (Fintype.equivOfCardEq (Fintype.card_fin _)).symm j ≤ k0 by
        rw [Fin.le_def]; simp only [k0, Fin.val_rev]; omega)
    have : hH.eigenvalues j = hH.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j) := rfl
    rcases hmem k0 with h | h
    · exact h
    · linarith
  rw [he]
  have hp : cfc (fun x : ℝ => if x = -1 then (1 : ℝ) else 0) (optimalHamiltonian d)
      = - optimalHamiltonian d := by
    rw [← cfc_neg_id (R := ℝ) (optimalHamiltonian d) hH.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    rcases (S200M_spec d hd x).1 hx with rfl | rfl <;> norm_num
  rw [hp]
  have htr : (- optimalHamiltonian d).trace = 1 := by
    rw [Matrix.trace_neg, optimalHamiltonian, Matrix.trace_diagonal]
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rw [Fin.sum_univ_succ]
    simp
  rw [htr, inv_one, one_smul]
  ext i j
  by_cases hij : i = j
  · subst hij; by_cases h0 : i.val = 0 <;> simp [optimalHamiltonian, family, familyProb, h0]
  · simp [optimalHamiltonian, family, Matrix.diagonal_apply_ne _ hij]


lemma S200M_logsplit (d : ℕ) (hd : 2 ≤ d) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Real.log ((1 - r) / r * ((d : ℝ) - 1)) = Real.log ((1 - r) / r) + Real.log ((d : ℝ) - 1) := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.log_mul (div_pos (by linarith) h0).ne' (by linarith)]

lemma S200M_upper (d : ℕ) (hd : 2 ≤ d) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    varianceObjective d r ≤ (Real.log ((d : ℝ) - 1)) ^ 2 / 4 + 2 * Real.log ((d : ℝ) - 1) + 4 := by
  obtain ⟨h0, h1⟩ := hr
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold varianceObjective
  rw [S200M_logsplit d hd h0 (by linarith)]
  set A := Real.log ((d : ℝ) - 1) with hA
  have hA0 : 0 ≤ A := Real.log_nonneg (by linarith)
  set y := (1 - r) / r with hy
  have hy1 : 1 < y := by rw [hy, lt_div_iff₀ h0]; linarith
  have hry : r * y = 1 - r := by rw [hy]; field_simp
  set g := Real.log y with hg
  have hg0 : 0 ≤ g := Real.log_nonneg hy1.le
  have hg1 : g ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hsq : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith))
  rw [Real.log_sqrt (by linarith)] at hsq
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hss : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have hg2 : g ^ 2 ≤ 4 * y := by nlinarith
  have hrr : 0 ≤ r * (1 - r) := by nlinarith
  have e1 : r * (1 - r) * A ^ 2 ≤ A ^ 2 / 4 := by nlinarith [sq_nonneg (r - 1/2)]
  have e2 : r * (1 - r) * g ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hg1 hrr
    nlinarith
  have e3 : r * (1 - r) * g ^ 2 ≤ 4 := by
    have := mul_le_mul_of_nonneg_left hg2 hrr
    nlinarith
  have e2' : 2 * A * (r * (1 - r) * g) ≤ 2 * A := by nlinarith
  nlinarith

lemma S200M_beat (d : ℕ) (hd : 2 ≤ d) :
    ∃ r ∈ Set.Ioo (0 : ℝ) (1 / 2), (Real.log ((d : ℝ) - 1)) ^ 2 / 4 < varianceObjective d r := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set ε : ℝ := 1 / (2 * d + 4) with hε
  have hε0 : 0 < ε := by positivity
  have hε8 : ε ≤ 1 / 8 := by rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hεd : ε * ((d : ℝ) - 2) ≤ 1 / 2 := by
    rw [hε, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  refine ⟨1 / 2 - ε, ⟨by linarith, by linarith⟩, ?_⟩
  unfold varianceObjective
  rw [S200M_logsplit d hd (by linarith) (by linarith)]
  set A := Real.log ((d : ℝ) - 1) with hA
  have hA0 : 0 ≤ A := Real.log_nonneg (by linarith)
  have hAd : A ≤ (d : ℝ) - 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (d : ℝ) - 1 by linarith)
    linarith
  set y := (1 - (1 / 2 - ε)) / (1 / 2 - ε) with hy
  have hypos : 0 < y := by rw [hy]; apply div_pos <;> linarith
  have hg := Real.one_sub_inv_le_log_of_pos hypos
  have hinv : 1 - y⁻¹ = 2 * ε / (1 / 2 + ε) := by
    have hne : (1 / 2 + ε) ≠ 0 := by linarith
    have hy' : y = (1 / 2 + ε) / (1 / 2 - ε) := by rw [hy]; ring
    rw [hy', inv_div, eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]; ring
  have h2e : 2 * ε ≤ 2 * ε / (1 / 2 + ε) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  set g := Real.log y
  have hg2 : 2 * ε ≤ g := by linarith
  have hεA : ε * A ≤ 1 / 2 := by nlinarith
  have hk1 : 0 ≤ A * (1 - ε * A - 4 * ε ^ 2) := by
    apply mul_nonneg hA0; nlinarith
  have hk2 : 0 < ε * (1 - 4 * ε ^ 2) := by
    apply mul_pos hε0; nlinarith
  have key : A ^ 2 / 4 < (1 / 4 - ε ^ 2) * (A + 2 * ε) ^ 2 := by
    have : (1 / 4 - ε ^ 2) * (A + 2 * ε) ^ 2 - A ^ 2 / 4
        = ε * (A * (1 - ε * A - 4 * ε ^ 2)) + ε * (ε * (1 - 4 * ε ^ 2)) := by ring
    nlinarith [mul_nonneg hε0.le hk1, mul_pos hε0 hk2]
  have hsq : (A + 2 * ε) ^ 2 ≤ (g + A) ^ 2 := by nlinarith
  have hc : (1 / 2 - ε) * (1 - (1 / 2 - ε)) = 1 / 4 - ε ^ 2 := by ring
  rw [hc]
  have : 0 ≤ 1 / 4 - ε ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq this]


/-- continuous extension of the variance objective -/
def S200M_F (A r : ℝ) : ℝ :=
  r * (1 - r) * (Real.log (1 - r) + A) ^ 2 - 2 * (1 - r) * (Real.log (1 - r) + A) * (r * Real.log r)
    + (1 - r) * (2 * (Real.sqrt r * Real.log (Real.sqrt r))) ^ 2

lemma S200M_F_cont (A : ℝ) : ContinuousOn (S200M_F A) (Set.Icc 0 (1 / 2)) := by
  have hl : ContinuousOn (fun r : ℝ => Real.log (1 - r)) (Set.Icc 0 (1 / 2)) := by
    apply ContinuousOn.log (continuousOn_const.sub continuousOn_id)
    intro x hx; have := hx.2; show (1 : ℝ) - x ≠ 0; exact (sub_pos.2 (by linarith)).ne'
  have hm : Continuous (fun r : ℝ => r * Real.log r) := Real.continuous_mul_log
  have hs : Continuous (fun r : ℝ => Real.sqrt r * Real.log (Real.sqrt r)) :=
    Real.continuous_mul_log.comp Real.continuous_sqrt
  unfold S200M_F
  apply ContinuousOn.add
  · apply ContinuousOn.sub
    · exact ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul
        ((hl.add continuousOn_const).pow 2))
    · exact (((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).mul
        (hl.add continuousOn_const)).mul hm.continuousOn)
  · exact (continuousOn_const.sub continuousOn_id).mul ((continuousOn_const.mul hs.continuousOn).pow 2)

lemma S200M_F_eq (d : ℕ) (hd : 2 ≤ d) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    S200M_F (Real.log ((d : ℝ) - 1)) r = varianceObjective d r := by
  unfold S200M_F varianceObjective
  rw [S200M_logsplit d hd h0 h1, Real.log_div (by linarith) h0.ne', Real.log_sqrt h0.le]
  have : Real.sqrt r ^ 2 = r := Real.sq_sqrt h0.le
  have e : (2 * (Real.sqrt r * (Real.log r / 2))) ^ 2 = Real.sqrt r ^ 2 * Real.log r ^ 2 := by ring
  rw [e, this]
  ring

lemma S200M_attain (d : ℕ) (hd : 2 ≤ d) :
    ∃ x ∈ Set.Ioo (0 : ℝ) (1 / 2), maxVariance d = varianceObjective d x ∧
      ∀ r ∈ Set.Ioo (0 : ℝ) (1 / 2), varianceObjective d r ≤ varianceObjective d x := by
  set A := Real.log ((d : ℝ) - 1) with hA
  obtain ⟨x, hxI, hxmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by norm_num : (0 : ℝ) ≤ 1 / 2)) (S200M_F_cont A)
  obtain ⟨r1, hr1, hlt⟩ := S200M_beat d hd
  have hF0 : S200M_F A 0 = 0 := by simp [S200M_F]
  have hFh : S200M_F A (1 / 2) = A ^ 2 / 4 := by
    rw [S200M_F_eq d hd (by norm_num) (by norm_num)]
    unfold varianceObjective
    norm_num
    rw [hA]; ring
  have hr1F : S200M_F A r1 ≤ S200M_F A x :=
    hxmax ⟨hr1.1.le, hr1.2.le⟩
  rw [S200M_F_eq d hd hr1.1 (by linarith [hr1.2])] at hr1F
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [hF0] at hr1F; nlinarith [sq_nonneg A]
  have hxh : x ≠ 1 / 2 := by
    rintro rfl; rw [hFh] at hr1F; linarith
  have hxI' : x ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hxh⟩
  have hfx : S200M_F A x = varianceObjective d x :=
    S200M_F_eq d hd hxI'.1 (by linarith [hxI'.2])
  have hall : ∀ r ∈ Set.Ioo (0 : ℝ) (1 / 2), varianceObjective d r ≤ varianceObjective d x := by
    intro r hr
    rw [← hfx, ← S200M_F_eq d hd hr.1 (by linarith [hr.2])]
    exact hxmax ⟨hr.1.le, hr.2.le⟩
  refine ⟨x, hxI', ?_, hall⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hxI', rfl⟩, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact hall r hr

lemma S200M_optimalMass (d : ℕ) (hd : 2 ≤ d) :
    optimalMass d ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧ varianceObjective d (optimalMass d) = maxVariance d := by
  obtain ⟨x, hx, hmax, -⟩ := S200M_attain d hd
  exact Classical.epsilon_spec (p := fun r : ℝ => r ∈ Set.Ioo 0 (1 / 2) ∧
    varianceObjective d r = maxVariance d) ⟨x, hx, hmax.symm⟩


lemma S200M_param (d : ℕ) (hd : 2 ≤ d) {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    ((d : ℝ) - 1) / (Real.exp (Real.log ((1 - s) / s * ((d : ℝ) - 1))) + ((d : ℝ) - 1)) = s := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hz : 0 < (1 - s) / s * ((d : ℝ) - 1) := mul_pos (div_pos (by linarith) h0) (by linarith)
  rw [Real.exp_log hz]
  have : (d : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

lemma S200M_z_gt (d : ℕ) {s : ℝ} (h0 : 0 < s) (h : s * d < (d : ℝ) - 1) :
    1 < (1 - s) / s * ((d : ℝ) - 1) := by
  rw [div_mul_eq_mul_div, lt_div_iff₀ h0]; nlinarith

lemma S200M_trace (d : ℕ) (hd : 2 ≤ d) (s : ℝ) :
    (optimalHamiltonian d * family d s).trace.re = s - 1 := by
  unfold optimalHamiltonian family
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  simp [familyProb]

lemma S200M_energy (d : ℕ) (hd : 2 ≤ d) :
    thermalExpectedEnergy (optimalHamiltonian d) =
      fun τ => ((d : ℝ) - 1) / (Real.exp τ⁻¹ + ((d : ℝ) - 1)) - 1 := by
  funext τ
  unfold thermalExpectedEnergy
  rw [S200M_gibbs d hd, S200M_trace d hd]

lemma S200M_deriv (d : ℕ) (hd : 2 ≤ d) {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun τ => ((d : ℝ) - 1) / (Real.exp τ⁻¹ + ((d : ℝ) - 1)) - 1)
      (((d : ℝ) - 1) * Real.exp T⁻¹ * (T ^ 2)⁻¹ / (Real.exp T⁻¹ + ((d : ℝ) - 1)) ^ 2) T := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := ((hasDerivAt_inv hT.ne').exp).add_const ((d : ℝ) - 1)
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hne : Real.exp T⁻¹ + ((d : ℝ) - 1) ≠ 0 := by positivity
  have := ((h1.inv hne).const_mul ((d : ℝ) - 1)).sub_const 1
  have e1 : (fun τ : ℝ => ((d : ℝ) - 1) / (Real.exp τ⁻¹ + ((d : ℝ) - 1)) - 1) =
      (fun x => ((d : ℝ) - 1) * (fun x => Real.exp x⁻¹ + ((d : ℝ) - 1))⁻¹ x - 1) := by
    funext τ; simp [div_eq_mul_inv]
  rw [e1]
  exact this.congr_deriv (by ring)

lemma S200M_temp (d : ℕ) (hd : 2 ≤ d) {s : ℝ} (h0 : 0 < s) (h1 : s < 1)
    (h : s * d < (d : ℝ) - 1) :
    let β := Real.log ((1 - s) / s * ((d : ℝ) - 1))
    ENNReal.ofReal β⁻¹ ≠ 0 ∧ ENNReal.ofReal β⁻¹ ≠ ⊤ ∧
      gibbsAtTemperature (optimalHamiltonian d) (ENNReal.ofReal β⁻¹) = family d s ∧
      heatCapacity (optimalHamiltonian d) (ENNReal.ofReal β⁻¹) = varianceObjective d s := by
  intro β
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hz := S200M_z_gt d h0 h
  have hβ : 0 < β := Real.log_pos hz
  have hT : 0 < β⁻¹ := inv_pos.2 hβ
  have hne0 : ENNReal.ofReal β⁻¹ ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hT
  have hneT : ENNReal.ofReal β⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hreal : (ENNReal.ofReal β⁻¹).toReal = β⁻¹ := ENNReal.toReal_ofReal hT.le
  refine ⟨hne0, hneT, ?_, ?_⟩
  · unfold gibbsAtTemperature
    rw [if_neg hneT, if_neg hne0, hreal, S200M_gibbs d hd, inv_inv, S200M_param d hd h0 h1]
  · unfold heatCapacity
    rw [if_neg (by tauto), hreal, S200M_energy d hd, (S200M_deriv d hd hT).deriv, inv_inv]
    have hzpos : 0 < (1 - s) / s * ((d : ℝ) - 1) := by linarith
    rw [Real.exp_log hzpos]
    unfold varianceObjective
    change _ = s * (1 - s) * β ^ 2
    clear_value β
    have : (d : ℝ) - 1 ≠ 0 := by linarith
    have : (1 : ℝ) - s ≠ 0 := by linarith
    field_simp
    ring

lemma S200M_top (d : ℕ) (hd : 2 ≤ d) :
    gibbsAtTemperature (optimalHamiltonian d) ⊤ = family d (massLimit d) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hdr : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hp : ∀ i, familyProb d (massLimit d) i = 1 / (d : ℝ) := by
    intro i; unfold familyProb massLimit
    split_ifs
    · field_simp; ring
    · field_simp
  simp only [gibbsAtTemperature, if_true]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [family, hp]
  · simp [family, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]


lemma S200M_bounds (D : ℕ) (hD : 2 ≤ D) :
    (Real.log ((D : ℝ) - 1)) ^ 2 / 4 ≤ maxVariance D ∧
      maxVariance D ≤ (Real.log ((D : ℝ) - 1)) ^ 2 / 4 + 2 * Real.log ((D : ℝ) - 1) + 4 := by
  obtain ⟨x, hx, hmax, hall⟩ := S200M_attain D hD
  obtain ⟨r1, hr1, hlt⟩ := S200M_beat D hD
  rw [hmax]
  exact ⟨(hlt.trans_le (hall r1 hr1)).le, S200M_upper D hD hx⟩

lemma S200M_ratio (l : ℕ) (hl : 2 ≤ l) :
    Tendsto (fun n : ℕ => Real.log ((l : ℝ) ^ n - 1) / n) atTop (nhds (Real.log l)) := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hlow : Tendsto (fun n : ℕ => Real.log l - Real.log 2 * (1 / (n : ℝ))) atTop
      (nhds (Real.log l)) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (Real.log 2)
    simpa using (tendsto_const_nhds (x := Real.log l)).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (2 : ℝ) ≤ (l : ℝ) ^ n := by
      calc (2 : ℝ) ≤ (l : ℝ) ^ 1 := by simpa using hl'
        _ ≤ (l : ℝ) ^ n := pow_le_pow_right₀ (by linarith) hn
    have h2 : (l : ℝ) ^ n / 2 ≤ (l : ℝ) ^ n - 1 := by linarith
    have hlog := Real.log_le_log (by positivity) h2
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hlog
    rw [le_div_iff₀ (by linarith)]
    have : (Real.log l - Real.log 2 * (1 / (n : ℝ))) * n = n * Real.log l - Real.log 2 := by
      field_simp
    rw [this]; linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (2 : ℝ) ≤ (l : ℝ) ^ n := by
      calc (2 : ℝ) ≤ (l : ℝ) ^ 1 := by simpa using hl'
        _ ≤ (l : ℝ) ^ n := pow_le_pow_right₀ (by linarith) hn
    have hlog := Real.log_le_log (by linarith) (show (l : ℝ) ^ n - 1 ≤ (l : ℝ) ^ n by linarith)
    rw [Real.log_pow] at hlog
    rw [div_le_iff₀ (by linarith)]; linarith

lemma S200M_clause3 (l : ℕ) (hl : 2 ≤ l) :
    Tendsto (fun n : ℕ => maxVariance (l ^ n) / ((n : ℝ) ^ 2)) atTop
      (nhds ((Real.log l) ^ 2 / 4)) := by
  have ha := S200M_ratio l hl
  have hz : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hlo : Tendsto (fun n : ℕ => (Real.log ((l : ℝ) ^ n - 1) / n) ^ 2 / 4) atTop
      (nhds ((Real.log l) ^ 2 / 4)) := (ha.pow 2).div_const 4
  have hhi : Tendsto (fun n : ℕ => (Real.log ((l : ℝ) ^ n - 1) / n) ^ 2 / 4 +
      2 * (Real.log ((l : ℝ) ^ n - 1) / n) * (1 / (n : ℝ)) + 4 * (1 / (n : ℝ)) ^ 2) atTop
      (nhds ((Real.log l) ^ 2 / 4)) := by
    have := (hlo.add ((ha.const_mul 2).mul hz)).add ((hz.pow 2).const_mul 4)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hD : 2 ≤ l ^ n := le_trans (by simpa using hl) (Nat.pow_le_pow_right (by omega) hn)
    have hb := (S200M_bounds (l ^ n) hD).1
    push_cast at hb
    rw [le_div_iff₀ (by positivity)]
    have : (Real.log ((l : ℝ) ^ n - 1) / n) ^ 2 / 4 * (n : ℝ) ^ 2
        = Real.log ((l : ℝ) ^ n - 1) ^ 2 / 4 := by field_simp
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hD : 2 ≤ l ^ n := le_trans (by simpa using hl) (Nat.pow_le_pow_right (by omega) hn)
    have hb := (S200M_bounds (l ^ n) hD).2
    push_cast at hb
    rw [div_le_iff₀ (by positivity)]
    have : ((Real.log ((l : ℝ) ^ n - 1) / n) ^ 2 / 4 +
      2 * (Real.log ((l : ℝ) ^ n - 1) / n) * (1 / (n : ℝ)) + 4 * (1 / (n : ℝ)) ^ 2) * (n : ℝ) ^ 2
        = Real.log ((l : ℝ) ^ n - 1) ^ 2 / 4 + 2 * Real.log ((l : ℝ) ^ n - 1) + 4 := by
      field_simp
    linarith

lemma S200M_main :
    (∀ d : ℕ, 2 ≤ d →
      (∀ s ∈ Set.Icc (0 : ℝ) (massLimit d),
        ∃ t : ℝ≥0∞, gibbsAtTemperature (optimalHamiltonian d) t = family d s) ∧
      (∃ t : ℝ≥0∞, t ≠ 0 ∧ t ≠ ⊤ ∧
        gibbsAtTemperature (optimalHamiltonian d) t = family d (optimalMass d) ∧
        heatCapacity (optimalHamiltonian d) t = maxVariance d)) ∧
    (∀ l : ℕ, 2 ≤ l → Tendsto
      (fun n : ℕ => maxVariance (l ^ n) / ((n : ℝ) ^ 2)) atTop (nhds ((Real.log l) ^ 2 / 4))) := by
  refine ⟨fun d hd => ⟨?_, ?_⟩, S200M_clause3⟩
  · intro s hs
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hdpos : (0 : ℝ) < d := by linarith
    rcases hs.1.eq_or_lt with h0 | h0
    · subst h0
      refine ⟨0, ?_⟩
      simp only [gibbsAtTemperature, ENNReal.zero_ne_top, if_false, if_true]
      exact S200M_ground d hd
    rcases hs.2.eq_or_lt with h1 | h1
    · subst h1
      exact ⟨⊤, S200M_top d hd⟩
    have hsd : s * d < (d : ℝ) - 1 := by
      unfold massLimit at h1; rwa [lt_div_iff₀ hdpos] at h1
    have hs1 : s < 1 := by
      have : massLimit d < 1 := by
        unfold massLimit; rw [div_lt_one hdpos]; linarith
      linarith
    exact ⟨_, (S200M_temp d hd h0 hs1 hsd).2.2.1⟩
  · obtain ⟨⟨h0, h1⟩, hv⟩ := S200M_optimalMass d hd
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hsd : optimalMass d * d < (d : ℝ) - 1 := by nlinarith
    obtain ⟨a, b, c, e⟩ := S200M_temp d hd h0 (by linarith) hsd
    exact ⟨_, a, b, c, e.trans hv⟩

end QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Support50.P15 in
theorem solution :
    (∀ d : ℕ, 2 ≤ d →
      (∀ s ∈ Set.Icc (0 : ℝ) (massLimit d),
        ∃ t : ℝ≥0∞, gibbsAtTemperature (optimalHamiltonian d) t = family d s) ∧
      (∃ t : ℝ≥0∞, t ≠ 0 ∧ t ≠ ⊤ ∧
        gibbsAtTemperature (optimalHamiltonian d) t = family d (optimalMass d) ∧
        heatCapacity (optimalHamiltonian d) t = maxVariance d)) ∧
    (∀ l : ℕ, 2 ≤ l → Tendsto
      (fun n : ℕ => maxVariance (l ^ n) / ((n : ℝ) ^ 2)) atTop (nhds ((Real.log l) ^ 2 / 4))) :=
  S200M_main

end
