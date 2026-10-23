-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.finiteTensorWidths
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:39:31.628257+00:00
-- url     : https://prove2.me/submissions/fe41c963-ecdd-4c11-b88b-f22e8deced30

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_widthSdpAnnihilator
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_matrixTensorWidth
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_annihilatorObstruction
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker

namespace X6P75C4

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


lemma width_zero [Nonempty ι] : width (0 : Mat ι) = Real.pi := by
  unfold width
  rw [if_pos]
  obtain ⟨D, hD⟩ := exists_density (ι := ι)
  exact ⟨D, hD, by simp⟩

lemma width_nonneg [Nonempty ι] (X : Mat ι) : 0 ≤ width X := by
  by_cases h0 : X = 0
  · rw [h0, width_zero]; exact Real.pi_pos.le
  have := (annihilatorObstruction (0 : Mat ι)).1 X h0 (by simp)
  rw [width_zero, sub_self] at this
  unfold width
  split_ifs
  · exact Real.pi_pos.le
  · exact this

lemma width_le_pi [Nonempty ι] (X : Mat ι) : width X ≤ Real.pi := by
  unfold width; split_ifs
  · exact le_rfl
  · have : 0 ≤ gammaLength X := ENNReal.toReal_nonneg
    linarith

lemma infWidth_le_pi [Nonempty ι] (M : Submodule ℂ (Mat ι)) : infWidth M ≤ Real.pi :=
  (infWidth_le M 0 M.zero_mem).trans (width_zero (ι := ι)).le

lemma infWidth_nonneg [Nonempty ι] (M : Submodule ℂ (Mat ι)) : 0 ≤ infWidth M :=
  (infWidth_ge_iff M 0).2 fun X _ => width_nonneg X

lemma thm2_iff [Nonempty ι] (M : Submodule ℂ (Mat ι)) (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    (Real.pi ≤ infWidth M + a) ↔ ∃ R ∈ omega (ι := ι) a, ∀ X ∈ M, (R * X).trace = 0 :=
  (widthSdpAnnihilator M a ha hap).1.trans (widthSdpAnnihilator M a ha hap).2

/-- binary subspace formula (first claim of Theorem 3) -/
theorem tensor_infWidth [Nonempty ι] [Nonempty κ] (M : Submodule ℂ (Mat ι))
    (L : Submodule ℂ (Mat κ)) :
    infWidth (tensorSpace M L) = min (infWidth M + infWidth L) Real.pi := by
  have hM0 := infWidth_nonneg M
  have hL0 := infWidth_nonneg L
  apply le_antisymm
  · refine le_min ?_ (infWidth_le_pi _)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨_, ⟨X, hX, rfl⟩, hXlt⟩ := exists_lt_of_csInf_lt (s := width '' (M : Set (Mat ι)))
      ⟨_, 0, M.zero_mem, rfl⟩ (show infWidth M < infWidth M + ε / 2 by linarith)
    obtain ⟨_, ⟨Y, hY, rfl⟩, hYlt⟩ := exists_lt_of_csInf_lt (s := width '' (L : Set (Mat κ)))
      ⟨_, 0, L.zero_mem, rfl⟩ (show infWidth L < infWidth L + ε / 2 by linarith)
    have h1 := infWidth_le (tensorSpace M L) _ (Submodule.subset_span ⟨X, hX, Y, hY, rfl⟩)
    rw [matrixTensorWidth] at h1
    have h2 := min_le_left (width X + width Y) Real.pi
    unfold infWidth at hXlt hYlt h1 ⊢
    linarith
  -- lower bound through Theorem 2 on the tensor space
  have key : ∀ c : ℝ, 0 ≤ c → c < Real.pi → (∃ Z ∈ omega (ι := ι × κ) c,
      ∀ X ∈ M, ∀ Y ∈ L, (Z * Matrix.kronecker X Y).trace = 0) →
      Real.pi - c ≤ infWidth (tensorSpace M L) := by
    rintro c hc hcp ⟨Z, hZ, hZann⟩
    have := (thm2_iff (tensorSpace M L) c hc hcp).2 ⟨Z, hZ, ann_tensorSpace Z M L hZann⟩
    linarith
  by_cases hs : Real.pi ≤ infWidth M + infWidth L
  · rw [min_eq_right hs]
    -- the density construction of Corollary 6
    have hZ : ∃ Z ∈ omega (ι := ι × κ) 0,
        ∀ X ∈ M, ∀ Y ∈ L, (Z * Matrix.kronecker X Y).trace = 0 := by
      by_cases hL : Real.pi ≤ infWidth L
      · obtain ⟨R0, hR0, hR0L⟩ := (thm2_iff L 0 le_rfl Real.pi_pos).1 (by linarith)
        obtain ⟨D, hD⟩ := exists_density (ι := ι)
        have hR0' := (mem_omega_zero R0).1 hR0
        refine ⟨Matrix.kronecker D R0, (mem_omega_zero _).2 ⟨hD.1.kronecker hR0'.1,
          by rw [trace_kron, hD.2, hR0'.2, one_mul]⟩, fun X _ Y hY => ?_⟩
        rw [trace_kron_mul, hR0L Y hY, mul_zero]
      by_cases hM : Real.pi ≤ infWidth M
      · obtain ⟨R0, hR0, hR0M⟩ := (thm2_iff M 0 le_rfl Real.pi_pos).1 (by linarith)
        obtain ⟨D, hD⟩ := exists_density (ι := κ)
        have hR0' := (mem_omega_zero R0).1 hR0
        refine ⟨Matrix.kronecker R0 D, (mem_omega_zero _).2 ⟨hR0'.1.kronecker hD.1,
          by rw [trace_kron, hD.2, hR0'.2, one_mul]⟩, fun X hX Y _ => ?_⟩
        rw [trace_kron_mul, hR0M X hX, zero_mul]
      push Not at hL hM
      have hLpos : 0 < infWidth L := by linarith
      set a := max (Real.pi - infWidth M) (min (infWidth L) (Real.pi / 2))
      have ha1 : Real.pi - infWidth M ≤ a := le_max_left _ _
      have hmin_pos : 0 < min (infWidth L) (Real.pi / 2) := lt_min hLpos (by positivity)
      have ha0 : 0 < a := lt_of_lt_of_le hmin_pos (le_max_right _ _)
      have hap : a < Real.pi := max_lt (by linarith) (lt_of_le_of_lt (min_le_right _ _)
        (by linarith [Real.pi_pos]))
      have haL : a ≤ infWidth L := max_le (by linarith) (min_le_left _ _)
      obtain ⟨P, Q, hP, hQ, hPQ, hP0, hQ0, hrM⟩ := sub_witness M hM a ha0.le (by linarith) hap
      obtain ⟨R, S, hR, hS, hRS, hR0, hS0, hrL⟩ :=
        sub_witness L hL (Real.pi - a) (by linarith) (by linarith) (by linarith)
      set m : ℝ := P.trace.re * R.trace.re + Q.trace.re * S.trace.re
      have hm : 0 < m := by positivity
      have hm0 : (0 : ℂ) ≤ ((m⁻¹ : ℝ) : ℂ) := by exact_mod_cast (inv_pos.2 hm).le
      refine ⟨((m⁻¹ : ℝ) : ℂ) • (Matrix.kronecker P R + Matrix.kronecker Q S),
        (mem_omega_zero _).2 ⟨((hP.kronecker hR).add (hQ.kronecker hS)).smul hm0, ?_⟩,
        fun X hX Y hY => ?_⟩
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
    have := key 0 le_rfl Real.pi_pos hZ
    linarith
  push Not at hs
  rw [min_eq_left hs.le]
  rcases eq_or_lt_of_le hM0 with hM | hM
  · rcases eq_or_lt_of_le hL0 with hL | hL
    · rw [← hM, ← hL, add_zero]; exact infWidth_nonneg _
    -- only `L` has positive width
    obtain ⟨R, S, hR, hS, hRS, -, -, hrL⟩ :=
      sub_witness L (by linarith) (Real.pi - infWidth L) (by linarith) (by linarith) (by linarith)
    obtain ⟨D, hD⟩ := exists_density (ι := ι)
    have := key (Real.pi - infWidth L) (by linarith) (by linarith)
      ⟨blend (Real.pi - infWidth L) (Matrix.kronecker D R) (Matrix.kronecker D S),
        ⟨by linarith, by linarith, _, _, hD.1.kronecker hR, hD.1.kronecker hS,
          by rw [Matrix.trace_kronecker, Matrix.trace_kronecker, ← mul_add, hRS, hD.2, one_mul], rfl⟩,
        fun X _ Y hY => by
          simp only [blend, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
            Matrix.trace_smul, smul_eq_mul, trace_kron_mul, hrL Y hY]
          have e : phase (-(Real.pi - infWidth L) / 2) * phase (Real.pi - infWidth L) =
              phase ((Real.pi - infWidth L) / 2) := by rw [phase_mul]; ring_nf
          linear_combination (-((D * X).trace * (R * Y).trace)) * e⟩
    rw [← hM, zero_add]; linarith
  rcases eq_or_lt_of_le hL0 with hL | hL
  · obtain ⟨P, Q, hP, hQ, hPQ, -, -, hrM⟩ :=
      sub_witness M (by linarith) (Real.pi - infWidth M) (by linarith) (by linarith) (by linarith)
    obtain ⟨D, hD⟩ := exists_density (ι := κ)
    have := key (Real.pi - infWidth M) (by linarith) (by linarith)
      ⟨blend (Real.pi - infWidth M) (Matrix.kronecker P D) (Matrix.kronecker Q D),
        ⟨by linarith, by linarith, _, _, hP.kronecker hD.1, hQ.kronecker hD.1,
          by rw [Matrix.trace_kronecker, Matrix.trace_kronecker, ← add_mul, hPQ, hD.2, one_mul], rfl⟩,
        fun X hX Y _ => by
          simp only [blend, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
            Matrix.trace_smul, smul_eq_mul, trace_kron_mul, hrM X hX]
          have e : phase (-(Real.pi - infWidth M) / 2) * phase (Real.pi - infWidth M) =
              phase ((Real.pi - infWidth M) / 2) := by rw [phase_mul]; ring_nf
          linear_combination (-((P * X).trace * (D * Y).trace)) * e⟩
    rw [← hL, add_zero]; linarith
  -- both widths positive: the product probe
  obtain ⟨P, Q, hP, hQ, hPQ, hP0, hQ0, hrM⟩ :=
    sub_witness M (by linarith) (Real.pi - infWidth M) (by linarith) (by linarith) (by linarith)
  obtain ⟨R, S, hR, hS, hRS, hR0, hS0, hrL⟩ :=
    sub_witness L (by linarith) (Real.pi - infWidth L) (by linarith) (by linarith) (by linarith)
  set a := Real.pi - infWidth M
  set b := Real.pi - infWidth L
  set c := a + b - Real.pi
  set m : ℝ := P.trace.re * R.trace.re + Q.trace.re * S.trace.re
  have hm : 0 < m := by positivity
  have hm0 : (0 : ℂ) ≤ ((m⁻¹ : ℝ) : ℂ) := by exact_mod_cast (inv_pos.2 hm).le
  have := key c (by simp only [c, a, b]; linarith) (by simp only [c, a, b]; linarith)
    ⟨blend c (((m⁻¹ : ℝ) : ℂ) • Matrix.kronecker P R) (((m⁻¹ : ℝ) : ℂ) • Matrix.kronecker Q S),
      ⟨by simp only [c, a, b]; linarith, by simp only [c, a, b]; linarith, _, _,
        (hP.kronecker hR).smul hm0, (hQ.kronecker hS).smul hm0, ?_, rfl⟩, ?_⟩
  · simp only [c, a, b] at this; linarith
  · simp only [Matrix.trace_smul, Matrix.trace_kronecker, smul_eq_mul]
    rw [psd_trace_re P hP, psd_trace_re Q hQ, psd_trace_re R hR, psd_trace_re S hS, ← mul_add]
    have : (m : ℂ) = (P.trace.re : ℂ) * R.trace.re + Q.trace.re * S.trace.re := by
      simp only [m]; push_cast; ring
    rw [← this, ← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne']
    simp
  · intro X hX Y hY
    simp only [blend, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
      smul_eq_mul, trace_kron_mul, hrM X hX, hrL Y hY]
    have e : phase (-c / 2) * phase a * phase b = -phase (c / 2) := by
      rw [phase_mul, phase_mul, show -c / 2 + a + b = c / 2 + Real.pi by simp only [c]; ring,
        phase_add_pi]
    linear_combination (((m⁻¹ : ℝ) : ℂ) * ((P * X).trace * (R * Y).trace)) * e

/-! ### reindexing -/

section Reindex

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
lemma trace_submatrix_equiv (A : Mat β) (e : α ≃ β) : (A.submatrix e e).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun b => A b b)

omit [DecidableEq α] [DecidableEq β] in
lemma zero_mem_submatrix (A : Mat β) (e : α ≃ β) :
    (0 : ℂ) ∈ numericalRange (A.submatrix e e) ↔ (0 : ℂ) ∈ numericalRange A := by
  constructor
  · rintro ⟨R, ⟨hR, htr⟩, hRA⟩
    refine ⟨R.submatrix e.symm e.symm, ⟨hR.submatrix _, by
      rw [trace_submatrix_equiv]; exact htr⟩, ?_⟩
    rw [← hRA, ← trace_submatrix_equiv _ e, ← Matrix.submatrix_mul_equiv _ _ _ e]
    simp
  · rintro ⟨R, ⟨hR, htr⟩, hRA⟩
    refine ⟨R.submatrix e e, ⟨hR.submatrix _, by rw [trace_submatrix_equiv]; exact htr⟩, ?_⟩
    rw [Matrix.submatrix_mul_equiv _ _ _ e, trace_submatrix_equiv, hRA]

omit [DecidableEq α] [DecidableEq β] in
lemma width_submatrix (A : Mat β) (e : α ≃ β) : width (A.submatrix e e) = width A := by
  have hg : gammaSet (A.submatrix e e) = gammaSet A := by
    ext t
    simp only [gammaSet, Set.mem_setOf_eq]
    have : hermitianReal (phase t • A.submatrix e e) =
        (hermitianReal (phase t • A)).submatrix e e := by
      unfold hermitianReal
      ext i j
      simp [Matrix.conjTranspose_apply]
      ring
    rw [this, Matrix.posSemidef_submatrix_equiv]
  unfold width gammaLength
  rw [hg, zero_mem_submatrix]

/-- reindexing as a linear map -/
def reidx (e : α ≃ β) : Mat β →ₗ[ℂ] Mat α where
  toFun A := A.submatrix e e
  map_add' A B := by ext; simp
  map_smul' c A := by ext; simp

omit [DecidableEq α] [DecidableEq β] in
lemma infWidth_map (S : Submodule ℂ (Mat β)) (e : α ≃ β) :
    infWidth (S.map (reidx e)) = infWidth S := by
  unfold infWidth
  congr 1
  ext w
  simp only [Set.mem_image, Submodule.map_coe, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A, hA, (width_submatrix A e).symm⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨_, ⟨A, hA, rfl⟩, width_submatrix A e⟩

end Reindex

/-! ### splitting off the first factor -/

section Split

variable {n : ℕ} (d : Fin (n + 2) → ℕ)

/-- `Fin (d 0) × Register (tail) ≃ Register d` -/
def consE : (Fin (d 0) × Register (fun j : Fin (n + 1) => d j.succ)) ≃ Register d where
  toFun p := Fin.cons (α := fun i => Fin (d i)) p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by simp
  right_inv x := by simp

lemma listTensor_cons (X : (i : Fin (n + 2)) → Mat (Fin (d i))) :
    (listTensor d X).submatrix (consE d) (consE d) =
      Matrix.kronecker (X 0) (listTensor (fun j : Fin (n + 1) => d j.succ) (fun j => X j.succ)) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  simp only [Matrix.submatrix_apply, listTensor, consE, Equiv.coe_fn_mk, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma lts_cons (M : (i : Fin (n + 2)) → Submodule ℂ (Mat (Fin (d i)))) :
    tensorSpace (M 0) (listTensorSpace (fun j : Fin (n + 1) => d j.succ) (fun j => M j.succ)) =
      (listTensorSpace d M).map (reidx (consE d)) := by
  apply le_antisymm
  · unfold tensorSpace
    rw [Submodule.span_le]
    rintro T ⟨X0, hX0, T', hT', rfl⟩
    -- induct on `T'` in the span of list tensors
    let kL : Mat (Register (fun j : Fin (n + 1) => d j.succ)) →ₗ[ℂ]
        Mat (Fin (d 0) × Register (fun j : Fin (n + 1) => d j.succ)) :=
      { toFun := fun T' => Matrix.kronecker X0 T'
        map_add' := by
          intro A B; ext ⟨a, x⟩ ⟨b, y⟩
          simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_add]
        map_smul' := by
          intro c A; ext ⟨a, x⟩ ⟨b, y⟩
          simp [Matrix.kronecker, Matrix.kroneckerMap_apply]; ring }
    let P := ((listTensorSpace d M).map (reidx (consE d))).comap kL
    have hle : listTensorSpace (fun j : Fin (n + 1) => d j.succ) (fun j => M j.succ) ≤ P := by
      unfold listTensorSpace
      rw [Submodule.span_le]
      rintro _ ⟨X', hX', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show Matrix.kronecker X0 (listTensor _ X') ∈ _
      set X : (i : Fin (n + 2)) → Mat (Fin (d i)) := Fin.cons (α := fun i => Mat (Fin (d i))) X0 X'
      have hX : ∀ i, X i ∈ M i := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [X] using hX0
        · simpa [X] using hX' j
      have := listTensor_cons d X
      simp only [X, Fin.cons_zero, Fin.cons_succ] at this
      rw [← this]
      exact ⟨_, Submodule.subset_span ⟨X, hX, rfl⟩, rfl⟩
    have := hle hT'
    rwa [Submodule.mem_comap] at this
  · unfold listTensorSpace
    rw [Submodule.map_span_le]
    rintro _ ⟨X, hX, rfl⟩
    show (listTensor d X).submatrix (consE d) (consE d) ∈ _
    rw [listTensor_cons]
    exact Submodule.subset_span ⟨X 0, hX 0, _, Submodule.subset_span ⟨fun j => X j.succ,
      fun j => hX j.succ, rfl⟩, rfl⟩

end Split

section One

variable (d : Fin 1 → ℕ)

def oneE : Fin (d 0) ≃ Register d where
  toFun a := Fin.cons (α := fun i => Fin (d i)) a (fun i => Fin.elim0 i)
  invFun x := x 0
  left_inv a := by simp
  right_inv x := by
    funext i
    fin_cases i
    simp

lemma listTensor_one (X : (i : Fin 1) → Mat (Fin (d i))) :
    (listTensor d X).submatrix (oneE d) (oneE d) = X 0 := by
  ext a b
  simp [listTensor, oneE, Fin.prod_univ_one]

lemma lts_one (M : (i : Fin 1) → Submodule ℂ (Mat (Fin (d i)))) :
    M 0 = (listTensorSpace d M).map (reidx (oneE d)) := by
  apply le_antisymm
  · intro Y hY
    set X : (i : Fin 1) → Mat (Fin (d i)) :=
      Fin.cons (α := fun i => Mat (Fin (d i))) Y (fun i => Fin.elim0 i)
    have hX : ∀ i, X i ∈ M i := by
      intro i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      simpa [X] using hY
    have h := listTensor_one d X
    simp only [X, Fin.cons_zero] at h
    rw [← h]
    exact ⟨_, Submodule.subset_span ⟨X, hX, rfl⟩, rfl⟩
  · unfold listTensorSpace
    rw [Submodule.map_span_le]
    rintro _ ⟨X, hX, rfl⟩
    show (listTensor d X).submatrix (oneE d) (oneE d) ∈ _
    rw [listTensor_one]
    exact hX 0

end One

lemma min_nest (a b : ℝ) (ha : 0 ≤ a) :
    min (a + min b Real.pi) Real.pi = min (a + b) Real.pi := by
  rcases le_total b Real.pi with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, min_eq_right (by linarith), min_eq_right (by linarith)]

theorem main_ind : ∀ (n : ℕ) (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
    (∀ M : (i : Fin (n + 1)) → Submodule ℂ (Mat (Fin (d i))),
      infWidth (listTensorSpace d M) = min (∑ i, infWidth (M i)) Real.pi) ∧
    (∀ X : (i : Fin (n + 1)) → Mat (Fin (d i)),
      width (listTensor d X) = min (∑ i, width (X i)) Real.pi)
  | 0, d, hd => by
    haveI : Nonempty (Fin (d 0)) := ⟨⟨0, hd 0⟩⟩
    refine ⟨fun M => ?_, fun X => ?_⟩
    · rw [← infWidth_map _ (oneE d), ← lts_one d M, Fin.sum_univ_one,
        min_eq_left (infWidth_le_pi _)]
    · rw [← width_submatrix _ (oneE d), listTensor_one, Fin.sum_univ_one,
        min_eq_left (width_le_pi _)]
  | n + 1, d, hd => by
    haveI : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd i⟩⟩
    obtain ⟨IH1, IH2⟩ := main_ind n (fun j => d j.succ) (fun j => hd j.succ)
    refine ⟨fun M => ?_, fun X => ?_⟩
    · rw [← infWidth_map _ (consE d), ← lts_cons d M, tensor_infWidth, IH1,
        min_nest _ _ (infWidth_nonneg _)]
      conv_rhs => rw [Fin.sum_univ_succ]
    · rw [← width_submatrix _ (consE d), listTensor_cons, matrixTensorWidth, IH2,
        min_nest _ _ (width_nonneg _)]
      conv_rhs => rw [Fin.sum_univ_succ]

end X6P75C4

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution {N : ℕ} (hN : 1 ≤ N) (d : Fin N → ℕ) (hd : ∀ i, 0 < d i) :
    (∀ M : (i : Fin N) → Submodule ℂ (Mat (Fin (d i))),
      infWidth (listTensorSpace d M) = min (∑ i, infWidth (M i)) Real.pi) ∧
    (∀ X : (i : Fin N) → Mat (Fin (d i)),
      width (listTensor d X) = min (∑ i, width (X i)) Real.pi) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  exact X6P75C4.main_ind n d hd
