-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.simpleTensorsNumericalZero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:32:24.056599+00:00
-- url     : https://prove2.me/submissions/8e54ab13-309a-4fef-8a5c-a7708568ea7e

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_widthSdpAnnihilator
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_matrixTensorWidth
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker

namespace X6P75C6

open QAlgorithms.Papers.Independent.Information100.P75 MeasureTheory

lemma phase_mul (s t : ℝ) : phase s * phase t = phase (s + t) := by
  unfold phase; rw [← Complex.exp_add]; push_cast; ring_nf

lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma phase_add_pi (t : ℝ) : phase (t + Real.pi) = - phase t := by
  unfold phase
  rw [show ((t + Real.pi : ℝ) : ℂ) * Complex.I = t * Complex.I + Real.pi * Complex.I by
    push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma kron_eq {ι' κ' : Type*} (A : Matrix ι' ι' ℂ) (B : Matrix κ' κ' ℂ) :
    Matrix.kronecker A B = A ⊗ₖ B := rfl

lemma trace_kron (A : Mat ι) (B : Mat κ) :
    (Matrix.kronecker A B).trace = A.trace * B.trace := by
  rw [kron_eq, Matrix.trace_kronecker]

lemma trace_kron_mul (A C : Mat ι) (B D : Mat κ) :
    (Matrix.kronecker A B * Matrix.kronecker C D).trace = (A * C).trace * (B * D).trace := by
  rw [kron_eq, kron_eq, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

lemma single_psd (i : ι) : (Matrix.single i i (1 : ℂ)).PosSemidef := by
  have : Matrix.single i i (1 : ℂ) = Matrix.diagonal (Pi.single i 1) := by
    ext j k
    by_cases hj : j = k
    · subst hj; by_cases hi : i = j
      · subst hi; simp
      · simp [Matrix.single_apply, hi, Pi.single_apply, Ne.symm hi]
    · simp [Matrix.single_apply, hj, Matrix.diagonal_apply_ne _ hj]
      intro h1 h2; exact hj (h1 ▸ h2)
  rw [this]
  refine Matrix.PosSemidef.diagonal fun j => ?_
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

lemma exists_density [Nonempty ι] : ∃ D : Mat ι, QAlgorithms.IsDensityMatrix D := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨Matrix.single i i 1, single_psd i, by simp⟩

lemma mem_omega_zero (R : Mat ι) :
    R ∈ omega (ι := ι) 0 ↔ QAlgorithms.IsDensityMatrix R := by
  constructor
  · rintro ⟨-, -, P, Q, hP, hQ, htr, rfl⟩
    simp only [blend, zero_div, neg_zero, phase_zero, one_smul]
    exact ⟨hP.add hQ, by rw [Matrix.trace_add]; exact htr⟩
  · rintro ⟨hR, htr⟩
    refine ⟨le_rfl, Real.pi_pos, R, 0, hR, Matrix.PosSemidef.zero, by simpa using htr, ?_⟩
    simp [blend, phase_zero]

lemma psd_trace_re (P : Mat ι) (hP : P.PosSemidef) : P.trace = ((P.trace.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp [(Complex.nonneg_iff.mp hP.trace_nonneg).2.symm]

lemma width_lb (X : Mat ι) : -Real.pi ≤ width X := by
  unfold width
  split_ifs
  · linarith [Real.pi_pos]
  · have hsub : gammaSet X ⊆ Set.Ico (-Real.pi) Real.pi := fun t ht => ⟨ht.1, ht.2.1⟩
    have hle : volume (gammaSet X) ≤ ENNReal.ofReal (Real.pi - -Real.pi) := by
      calc volume (gammaSet X) ≤ volume (Set.Ico (-Real.pi) Real.pi) := measure_mono hsub
        _ = _ := Real.volume_Ico
    have : gammaLength X ≤ Real.pi - -Real.pi := by
      unfold gammaLength
      exact ENNReal.toReal_le_of_le_ofReal (by linarith [Real.pi_pos]) hle
    linarith

lemma infWidth_ge_iff (M : Submodule ℂ (Mat ι)) (c : ℝ) :
    c ≤ infWidth M ↔ ∀ X ∈ M, c ≤ width X := by
  unfold infWidth
  constructor
  · intro h X hX
    exact h.trans (csInf_le ⟨-Real.pi, by rintro _ ⟨Y, -, rfl⟩; exact width_lb Y⟩ ⟨X, hX, rfl⟩)
  · intro h
    exact le_csInf ⟨_, 0, M.zero_mem, rfl⟩ (by rintro _ ⟨Y, hY, rfl⟩; exact h Y hY)

lemma infWidth_le (M : Submodule ℂ (Mat ι)) (X : Mat ι) (hX : X ∈ M) : infWidth M ≤ width X :=
  csInf_le ⟨-Real.pi, by rintro _ ⟨Y, -, rfl⟩; exact width_lb Y⟩ ⟨X, hX, rfl⟩

/-- a matrix annihilating every simple tensor annihilates the tensor space -/
lemma ann_tensorSpace (Z : Mat (ι × κ)) (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ))
    (h : ∀ X ∈ M, ∀ Y ∈ L, (Z * Matrix.kronecker X Y).trace = 0) :
    ∀ T ∈ tensorSpace M L, (Z * T).trace = 0 := by
  let φ : Mat (ι × κ) →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (ι × κ) ℂ ℂ).comp (LinearMap.mulLeft ℂ Z)
  have hφ : ∀ T, φ T = (Z * T).trace := fun T => rfl
  have hle : tensorSpace M L ≤ LinearMap.ker φ := by
    unfold tensorSpace
    rw [Submodule.span_le]
    rintro T ⟨X, hX, Y, hY, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hφ]
    exact h X hX Y hY
  intro T hT
  have := hle hT
  rwa [LinearMap.mem_ker, hφ] at this

/-- subspace witnesses from Theorem 2 -/
lemma sub_witness [Nonempty ι] (M : Submodule ℂ (Mat ι)) (hM : infWidth M < Real.pi)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : Real.pi ≤ infWidth M + a) (hap : a < Real.pi) :
    ∃ P Q : Mat ι, P.PosSemidef ∧ Q.PosSemidef ∧ P.trace + Q.trace = 1 ∧
      0 < P.trace.re ∧ 0 < Q.trace.re ∧
      ∀ X ∈ M, (Q * X).trace = -(phase a * (P * X).trace) := by
  obtain ⟨R, ⟨-, -, P, Q, hP, hQ, htr, rfl⟩, hRM⟩ :=
    ((widthSdpAnnihilator M a ha0 hap).1.trans (widthSdpAnnihilator M a ha0 hap).2).1 ha
  have hrel : ∀ X ∈ M, (Q * X).trace = -(phase a * (P * X).trace) := by
    intro X hX
    have hRX := hRM X hX
    simp only [blend, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
      smul_eq_mul] at hRX
    have h1 : phase (a / 2) * phase (a / 2) = phase a := by rw [phase_mul]; ring_nf
    have h2 : phase (a / 2) * phase (-a / 2) = 1 := by
      rw [phase_mul, show a / 2 + -a / 2 = 0 by ring, phase_zero]
    linear_combination (phase (a / 2)) * hRX - (P * X).trace * h1 - (Q * X).trace * h2
  have hPr := psd_trace_re P hP
  have hQr := psd_trace_re Q hQ
  have hsum : P.trace.re + Q.trace.re = 1 := by
    have := congrArg Complex.re htr; simpa using this
  have hP0 : 0 ≤ P.trace.re := (Complex.nonneg_iff.mp hP.trace_nonneg).1
  have hQ0 : 0 ≤ Q.trace.re := (Complex.nonneg_iff.mp hQ.trace_nonneg).1
  -- a density annihilating all of `M` forces infimal width `π`
  have hfull : ∀ D : Mat ι, QAlgorithms.IsDensityMatrix D → (∀ X ∈ M, (D * X).trace = 0) →
      False := by
    intro D hD hDM
    have : Real.pi ≤ infWidth M := by
      rw [infWidth_ge_iff]
      intro X hX
      unfold width; rw [if_pos ⟨D, hD, hDM X hX⟩]
    linarith
  have hph : phase a ≠ 0 := by unfold phase; exact Complex.exp_ne_zero _
  refine ⟨P, Q, hP, hQ, htr, ?_, ?_, hrel⟩
  · rcases lt_or_eq_of_le hP0 with h | h
    · exact h
    exfalso
    have hP0' : P = 0 := (hP.trace_eq_zero_iff).1 (by rw [hPr, ← h]; simp)
    refine hfull Q ⟨hQ, ?_⟩ fun X hX => ?_
    · rw [hQr]; rw [← h] at hsum; simp at hsum; rw [hsum]; simp
    · rw [hrel X hX, hP0', Matrix.zero_mul, Matrix.trace_zero, mul_zero, neg_zero]
  · rcases lt_or_eq_of_le hQ0 with h | h
    · exact h
    exfalso
    have hQ0' : Q = 0 := (hQ.trace_eq_zero_iff).1 (by rw [hQr, ← h]; simp)
    refine hfull P ⟨hP, ?_⟩ fun X hX => ?_
    · rw [hPr]; rw [← h] at hsum; simp at hsum; rw [hsum]; simp
    · have h' := hrel X hX
      rw [hQ0', Matrix.zero_mul, Matrix.trace_zero] at h'
      exact (mul_eq_zero.1 (neg_eq_zero.1 h'.symm)).resolve_left hph

theorem main [Nonempty ι] [Nonempty κ] (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ)) :
    (∀ X ∈ M, ∀ Y ∈ L, (0 : ℂ) ∈ numericalRange (Matrix.kronecker X Y)) ↔
    (∀ T ∈ tensorSpace M L, (0 : ℂ) ∈ numericalRange T) := by
  constructor
  swap
  · intro h X hX Y hY
    exact h _ (Submodule.subset_span ⟨X, hX, Y, hY, rfl⟩)
  intro h
  -- the infimal widths add up to at least `π`
  have hpair : ∀ X ∈ M, ∀ Y ∈ L, Real.pi ≤ width X + width Y := by
    intro X hX Y hY
    have h1 : width (Matrix.kronecker X Y) = Real.pi := by
      unfold width; rw [if_pos (h X hX Y hY)]
    rw [matrixTensorWidth X Y] at h1
    by_contra hc; push Not at hc
    rw [min_eq_left hc.le] at h1; linarith
  have hsum : Real.pi ≤ infWidth M + infWidth L := by
    have h1 : ∀ X ∈ M, Real.pi - width X ≤ infWidth L := fun X hX =>
      (infWidth_ge_iff L _).2 fun Y hY => by linarith [hpair X hX Y hY]
    have h2 : Real.pi - infWidth L ≤ infWidth M :=
      (infWidth_ge_iff M _).2 fun X hX => by linarith [h1 X hX]
    linarith
  -- a common density annihilating every simple tensor
  suffices hZ : ∃ Z : Mat (ι × κ), QAlgorithms.IsDensityMatrix Z ∧
      ∀ X ∈ M, ∀ Y ∈ L, (Z * Matrix.kronecker X Y).trace = 0 by
    obtain ⟨Z, hZ, hZann⟩ := hZ
    intro T hT
    exact ⟨Z, hZ, ann_tensorSpace Z M L hZann T hT⟩
  by_cases hL : Real.pi ≤ infWidth L
  · obtain ⟨R0, hR0, hR0L⟩ := ((widthSdpAnnihilator L 0 le_rfl Real.pi_pos).1.trans
      (widthSdpAnnihilator L 0 le_rfl Real.pi_pos).2).1 (by linarith)
    obtain ⟨D, hD⟩ := exists_density (ι := ι)
    have hR0' := (mem_omega_zero R0).1 hR0
    refine ⟨Matrix.kronecker D R0, ⟨hD.1.kronecker hR0'.1, by rw [trace_kron, hD.2, hR0'.2,
      one_mul]⟩, fun X _ Y hY => ?_⟩
    rw [trace_kron_mul, hR0L Y hY, mul_zero]
  by_cases hM : Real.pi ≤ infWidth M
  · obtain ⟨R0, hR0, hR0M⟩ := ((widthSdpAnnihilator M 0 le_rfl Real.pi_pos).1.trans
      (widthSdpAnnihilator M 0 le_rfl Real.pi_pos).2).1 (by linarith)
    obtain ⟨D, hD⟩ := exists_density (ι := κ)
    have hR0' := (mem_omega_zero R0).1 hR0
    refine ⟨Matrix.kronecker R0 D, ⟨hR0'.1.kronecker hD.1, by rw [trace_kron, hD.2, hR0'.2,
      one_mul]⟩, fun X hX Y _ => ?_⟩
    rw [trace_kron_mul, hR0M X hX, zero_mul]
  push Not at hL hM
  have hLpos : 0 < infWidth L := by linarith
  set a := max (Real.pi - infWidth M) (min (infWidth L) (Real.pi / 2))
  have ha1 : Real.pi - infWidth M ≤ a := le_max_left _ _
  have hmin_pos : 0 < min (infWidth L) (Real.pi / 2) := lt_min hLpos (by positivity)
  have ha0 : 0 < a := lt_of_lt_of_le hmin_pos (le_max_right _ _)
  have hap : a < Real.pi := max_lt (by linarith [hsum]) (lt_of_le_of_lt (min_le_right _ _)
    (by linarith [Real.pi_pos]))
  have haL : a ≤ infWidth L := max_le (by linarith) (min_le_left _ _)
  obtain ⟨P, Q, hP, hQ, hPQ, hP0, hQ0, hrM⟩ := sub_witness M hM a ha0.le (by linarith) hap
  obtain ⟨R, S, hR, hS, hRS, hR0, hS0, hrL⟩ :=
    sub_witness L hL (Real.pi - a) (by linarith) (by linarith) (by linarith)
  set m : ℝ := P.trace.re * R.trace.re + Q.trace.re * S.trace.re
  have hm : 0 < m := by positivity
  have hm0 : (0 : ℂ) ≤ ((m⁻¹ : ℝ) : ℂ) := by exact_mod_cast (inv_pos.2 hm).le
  refine ⟨((m⁻¹ : ℝ) : ℂ) • (Matrix.kronecker P R + Matrix.kronecker Q S),
    ⟨((hP.kronecker hR).add (hQ.kronecker hS)).smul hm0, ?_⟩, fun X hX Y hY => ?_⟩
  · rw [Matrix.trace_smul, Matrix.trace_add, trace_kron, trace_kron, psd_trace_re P hP,
      psd_trace_re Q hQ, psd_trace_re R hR, psd_trace_re S hS, smul_eq_mul]
    have : (m : ℂ) = (P.trace.re : ℂ) * R.trace.re + Q.trace.re * S.trace.re := by
      simp only [m]; push_cast; ring
    rw [← this, ← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne']
    simp
  · rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, trace_kron_mul,
      trace_kron_mul, hrM X hX, hrL Y hY, smul_eq_mul]
    have e : phase a * phase (Real.pi - a) = -1 := by
      rw [phase_mul, show a + (Real.pi - a) = 0 + Real.pi by ring, phase_add_pi, phase_zero]
    linear_combination (((m⁻¹ : ℝ) : ℂ) * ((P * X).trace * (R * Y).trace)) * e

end X6P75C6

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ)) :
    (∀ X ∈ M, ∀ Y ∈ L, (0 : ℂ) ∈ numericalRange (Matrix.kronecker X Y)) ↔
    (∀ T ∈ tensorSpace M L, (0 : ℂ) ∈ numericalRange T) :=
  X6P75C6.main M L
