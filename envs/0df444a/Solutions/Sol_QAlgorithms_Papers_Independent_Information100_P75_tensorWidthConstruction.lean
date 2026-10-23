-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P75.tensorWidthConstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:48:52.966603+00:00
-- url     : https://prove2.me/submissions/81d99bc9-e0d1-4288-9da6-ee2672854152

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_widthSdpAnnihilator
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_matrixTensorWidth
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_annihilatorObstruction
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker

namespace X6P75T3

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


/-! ### Theorem 3 -/

lemma phase_eq (t : ℝ) : phase t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
  unfold phase
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma star_phase (s : ℝ) : star (phase s) = phase (-s) := by
  rw [phase_eq, phase_eq, Real.cos_neg, Real.sin_neg]
  apply Complex.ext <;> simp

lemma phase_add_neg (t : ℝ) : phase t + phase (-t) = ((2 * Real.cos t : ℝ) : ℂ) := by
  rw [phase_eq, phase_eq, Real.cos_neg, Real.sin_neg]; push_cast; ring

lemma witnessParts_exists [Nonempty ι] (M : Submodule ℂ (Mat ι)) : ∃ P Q, WitnessParts M P Q := by
  by_cases h : infWidth M = 0
  · exact ⟨0, 0, ⟨fun h' => absurd h (ne_of_gt h'), fun _ => ⟨rfl, rfl⟩⟩⟩
  have hpos : 0 < infWidth M := lt_of_le_of_ne (infWidth_nonneg M) (Ne.symm h)
  have hle := infWidth_le_pi M
  obtain ⟨R, ⟨-, -, P, Q, hP, hQ, htr, rfl⟩, hRM⟩ :=
    (thm2_iff M (witnessAngle M) (by unfold witnessAngle; linarith)
      (by unfold witnessAngle; linarith)).1 (by unfold witnessAngle; linarith)
  exact ⟨P, Q, ⟨fun _ => ⟨hP, hQ, htr, hRM⟩, fun h' => absurd h' h⟩⟩

lemma parts_rel (M : Submodule ℂ (Mat ι)) (P Q : Mat ι) (a : ℝ)
    (h : ∀ X ∈ M, (blend a P Q * X).trace = 0) :
    ∀ X ∈ M, (Q * X).trace = -(phase a * (P * X).trace) := by
  intro X hX
  have hRX := h X hX
  simp only [blend, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul] at hRX
  have h1 : phase (a / 2) * phase (a / 2) = phase a := by rw [phase_mul]; ring_nf
  have h2 : phase (a / 2) * phase (-a / 2) = 1 := by
    rw [phase_mul, show a / 2 + -a / 2 = 0 by ring, phase_zero]
  linear_combination (phase (a / 2)) * hRX - (P * X).trace * h1 - (Q * X).trace * h2

lemma parts_pos [Nonempty ι] (M : Submodule ℂ (Mat ι)) (P Q : Mat ι) (hW : WitnessParts M P Q)
    (h0 : 0 < infWidth M) (hπ : infWidth M < Real.pi) : 0 < P.trace.re ∧ 0 < Q.trace.re := by
  obtain ⟨hP, hQ, htr, hann⟩ := hW.1 h0
  have hrel := parts_rel M P Q _ hann
  have hPr := psd_trace_re P hP
  have hQr := psd_trace_re Q hQ
  have hsum : P.trace.re + Q.trace.re = 1 := by
    have := congrArg Complex.re htr; simpa using this
  have hP0 : 0 ≤ P.trace.re := (Complex.nonneg_iff.mp hP.trace_nonneg).1
  have hQ0 : 0 ≤ Q.trace.re := (Complex.nonneg_iff.mp hQ.trace_nonneg).1
  have hfull : ∀ D : Mat ι, QAlgorithms.IsDensityMatrix D → (∀ X ∈ M, (D * X).trace = 0) →
      False := by
    intro D hD hDM
    have : Real.pi ≤ infWidth M := by
      rw [infWidth_ge_iff]
      intro X hX
      unfold width; rw [if_pos ⟨D, hD, hDM X hX⟩]
    linarith
  have hph : phase (witnessAngle M) ≠ 0 := by unfold phase; exact Complex.exp_ne_zero _
  constructor
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

lemma mixedIdentity_density [Nonempty ι] : QAlgorithms.IsDensityMatrix (mixedIdentity ι) := by
  have hc : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨Matrix.PosSemidef.one.smul ?_, ?_⟩
  · have : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
    rw [show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact_mod_cast this
  · simp only [mixedIdentity, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    exact inv_mul_cancel₀ hc

lemma kron_mixed : Matrix.kronecker (mixedIdentity ι) (mixedIdentity κ) = mixedIdentity (ι × κ) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [mixedIdentity, kron_eq, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    Matrix.one_apply, Prod.mk.injEq, Fintype.card_prod, smul_eq_mul]
  push_cast
  rw [mul_inv]
  by_cases h1 : i = j <;> by_cases h2 : k = l <;> simp [h1, h2]

lemma kron_blend_left (D : Mat ι) (c : ℝ) (R S : Mat κ) :
    Matrix.kronecker D (blend c R S) = blend c (Matrix.kronecker D R) (Matrix.kronecker D S) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [blend, kron_eq, Matrix.kroneckerMap_apply]; ring

lemma kron_blend_right (c : ℝ) (P Q : Mat ι) (D : Mat κ) :
    Matrix.kronecker (blend c P Q) D = blend c (Matrix.kronecker P D) (Matrix.kronecker Q D) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [blend, kron_eq, Matrix.kroneckerMap_apply]; ring

lemma smul_blend (r : ℂ) (c : ℝ) (A B : Mat ι) : r • blend c A B = blend c (r • A) (r • B) := by
  simp only [blend, smul_add, smul_comm r]

lemma sat_facts [Nonempty ι] [Nonempty κ] (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ))
    (P Q : Mat ι) (R S : Mat κ) (hWM : WitnessParts M P Q) (hWL : WitnessParts L R S)
    (h1 : 0 < infWidth M) (h2 : 0 < infWidth L) (h3 : Real.pi ≤ infWidth M + infWidth L) :
    (saturatedNumerator (probe M P Q) (probe L R S)).PosSemidef ∧
      0 < (saturatedNumerator (probe M P Q) (probe L R S)).trace.re ∧
      ∀ X ∈ M, ∀ Y ∈ L,
        (saturatedNumerator (probe M P Q) (probe L R S) * Matrix.kronecker X Y).trace = 0 := by
  have hMπ := infWidth_le_pi M
  have hLπ := infWidth_le_pi L
  obtain ⟨hP, hQ, hPQ, hannM⟩ := hWM.1 h1
  obtain ⟨hR, hS, hRS, hannL⟩ := hWL.1 h2
  have hpM : probe M P Q = blend (witnessAngle M) P Q := by
    unfold probe; rw [if_neg h1.ne']
  have hpL : probe L R S = blend (witnessAngle L) R S := by
    unfold probe; rw [if_neg h2.ne']
  rw [hpM, hpL]
  set a := witnessAngle M
  set b := witnessAngle L
  have ha0 : 0 ≤ a := by simp only [a, witnessAngle]; linarith
  have hap : a < Real.pi := by simp only [a, witnessAngle]; linarith
  have hb0 : 0 ≤ b := by simp only [b, witnessAngle]; linarith
  have hbp : b < Real.pi := by simp only [b, witnessAngle]; linarith
  have hab : a + b ≤ Real.pi := by simp only [a, b, witnessAngle]; linarith
  set c1 := phase (a / 2) * phase (-b / 2) + phase (-a / 2) * phase (b / 2)
  set c2 := phase (a / 2) * phase (b / 2) + phase (-a / 2) * phase (-b / 2)
  have hc1 : c1 = ((2 * Real.cos ((a - b) / 2) : ℝ) : ℂ) := by
    simp only [c1, phase_mul]
    rw [← phase_add_neg]; ring_nf
  have hc2 : c2 = ((2 * Real.cos ((a + b) / 2) : ℝ) : ℂ) := by
    simp only [c2, phase_mul]
    rw [← phase_add_neg]; ring_nf
  have hH : saturatedNumerator (blend a P Q) (blend b R S) =
      c1 • (Matrix.kronecker P R + Matrix.kronecker Q S) +
        c2 • (Matrix.kronecker P S + Matrix.kronecker Q R) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [saturatedNumerator, blend, kron_eq, Matrix.kroneckerMap_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.conjTranspose_apply, smul_eq_mul, star_add, star_mul',
      star_phase, c1, c2]
    rw [hP.isHermitian.apply i j, hQ.isHermitian.apply i j, hR.isHermitian.apply k l,
      hS.isHermitian.apply k l]
    rw [show -(a / 2) = -a / 2 by ring, show -(b / 2) = -b / 2 by ring,
      show -(-a / 2) = a / 2 by ring, show -(-b / 2) = b / 2 by ring]
    ring
  have hcos1 : 0 < Real.cos ((a - b) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos2 : 0 ≤ Real.cos ((a + b) / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hpsd1 : (Matrix.kronecker P R + Matrix.kronecker Q S).PosSemidef :=
    (hP.kronecker hR).add (hQ.kronecker hS)
  have hpsd2 : (Matrix.kronecker P S + Matrix.kronecker Q R).PosSemidef :=
    (hP.kronecker hS).add (hQ.kronecker hR)
  refine ⟨?_, ?_, ?_⟩
  · rw [hH, hc1, hc2]
    exact (hpsd1.smul (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 2 * Real.cos ((a - b) / 2)))).add
      (hpsd2.smul (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 2 * Real.cos ((a + b) / 2))))
  · rw [hH, hc1, hc2]
    simp only [Matrix.trace_add, Matrix.trace_smul, trace_kron, smul_eq_mul]
    rw [psd_trace_re P hP, psd_trace_re Q hQ, psd_trace_re R hR, psd_trace_re S hS]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
    have hp0 : 0 ≤ P.trace.re := (Complex.nonneg_iff.mp hP.trace_nonneg).1
    have hq0 : 0 ≤ Q.trace.re := (Complex.nonneg_iff.mp hQ.trace_nonneg).1
    have hr0 : 0 ≤ R.trace.re := (Complex.nonneg_iff.mp hR.trace_nonneg).1
    have hs0 : 0 ≤ S.trace.re := (Complex.nonneg_iff.mp hS.trace_nonneg).1
    have hpq : P.trace.re + Q.trace.re = 1 := by
      have := congrArg Complex.re hPQ; simpa using this
    have hrs : R.trace.re + S.trace.re = 1 := by
      have := congrArg Complex.re hRS; simpa using this
    rcases eq_or_lt_of_le h3 with heq | hlt
    · -- both widths below `π`: all parts have positive trace
      have hMlt : infWidth M < Real.pi := by linarith
      have hLlt : infWidth L < Real.pi := by linarith
      obtain ⟨hp, hq⟩ := parts_pos M P Q hWM h1 hMlt
      obtain ⟨hr, hs⟩ := parts_pos L R S hWL h2 hLlt
      have : 0 < 2 * Real.cos ((a - b) / 2) * (P.trace.re * R.trace.re + Q.trace.re * S.trace.re) :=
        by positivity
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hcos2)
        (add_nonneg (mul_nonneg hp0 hs0) (mul_nonneg hq0 hr0))]
    · have hcos2' : 0 < Real.cos ((a + b) / 2) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith, by simp only [a, b, witnessAngle]; linarith⟩
      have htot : (P.trace.re * R.trace.re + Q.trace.re * S.trace.re) +
          (P.trace.re * S.trace.re + Q.trace.re * R.trace.re) = 1 := by
        have : (P.trace.re + Q.trace.re) * (R.trace.re + S.trace.re) = 1 := by rw [hpq, hrs]; ring
        linarith
      set m := min (Real.cos ((a - b) / 2)) (Real.cos ((a + b) / 2))
      have hm : 0 < m := lt_min hcos1 hcos2'
      have e1 : m ≤ Real.cos ((a - b) / 2) := min_le_left _ _
      have e2 : m ≤ Real.cos ((a + b) / 2) := min_le_right _ _
      nlinarith [mul_le_mul_of_nonneg_right e1 (add_nonneg (mul_nonneg hp0 hr0) (mul_nonneg hq0 hs0)),
        mul_le_mul_of_nonneg_right e2 (add_nonneg (mul_nonneg hp0 hs0) (mul_nonneg hq0 hr0))]
  · intro X hX Y hY
    simp only [saturatedNumerator, Matrix.add_mul, Matrix.trace_add, trace_kron_mul, hannM X hX,
      hannL Y hY, zero_mul, mul_zero, add_zero]

theorem main [Nonempty ι] [Nonempty κ] (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ)) :
    infWidth (tensorSpace M L) = min (infWidth M + infWidth L) Real.pi ∧
    (∃ P Q, WitnessParts M P Q) ∧ (∃ R S, WitnessParts L R S) ∧
    ∀ P Q R S, WitnessParts M P Q → WitnessParts L R S →
      ValidProbe (tensorSpace M L) (combineProbe M L P Q R S) ∧
      (0 < infWidth M → 0 < infWidth L → infWidth M + infWidth L < Real.pi →
        0 < pairMass P Q R S) ∧
      (0 < infWidth M → 0 < infWidth L → Real.pi ≤ infWidth M + infWidth L →
        0 < (saturatedNumerator (probe M P Q) (probe L R S)).trace.re) := by
  have hT := tensor_infWidth M L
  refine ⟨hT, witnessParts_exists M, witnessParts_exists L, ?_⟩
  intro P Q R S hWM hWL
  have hM0 := infWidth_nonneg M
  have hL0 := infWidth_nonneg L
  have hMπ := infWidth_le_pi M
  have hLπ := infWidth_le_pi L
  have hpm : 0 < infWidth M → 0 < infWidth L → infWidth M + infWidth L < Real.pi →
      0 < pairMass P Q R S := by
    intro h1 h2 h3
    obtain ⟨p1, q1⟩ := parts_pos M P Q hWM h1 (by linarith)
    obtain ⟨r1, s1⟩ := parts_pos L R S hWL h2 (by linarith)
    unfold pairMass; positivity
  refine ⟨?_, hpm, fun h1 h2 h3 => (sat_facts M L P Q R S hWM hWL h1 h2 h3).2.1⟩
  by_cases hz : infWidth M = 0 ∨ infWidth L = 0
  · have hc : combineProbe M L P Q R S = Matrix.kronecker (probe M P Q) (probe L R S) := by
      unfold combineProbe; rw [if_pos hz]
    rw [hc]
    by_cases hz2 : infWidth M = 0 ∧ infWidth L = 0
    · have hT0 : infWidth (tensorSpace M L) = 0 := by
        rw [hT, hz2.1, hz2.2, add_zero, min_eq_left Real.pi_pos.le]
      refine ⟨fun h => absurd hT0 h.ne', fun _ => ?_⟩
      have e1 : probe M P Q = mixedIdentity ι := by unfold probe; rw [if_pos hz2.1]
      have e2 : probe L R S = mixedIdentity κ := by unfold probe; rw [if_pos hz2.2]
      rw [e1, e2, kron_mixed]
    rcases hz with hMz | hLz
    · have hLpos : 0 < infWidth L := lt_of_le_of_ne hL0 (fun h => hz2 ⟨hMz, h.symm⟩)
      have hTL : infWidth (tensorSpace M L) = infWidth L := by
        rw [hT, hMz, zero_add, min_eq_left hLπ]
      obtain ⟨hR, hS, hRS, hannL⟩ := hWL.1 hLpos
      have e1 : probe M P Q = mixedIdentity ι := by unfold probe; rw [if_pos hMz]
      have e2 : probe L R S = blend (witnessAngle L) R S := by
        unfold probe; rw [if_neg hLpos.ne']
      have hD := mixedIdentity_density (ι := ι)
      refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd (hTL ▸ h) hLpos.ne'⟩
      · rw [e1, e2, kron_blend_left]
        unfold witnessAngle at *
        rw [hTL]
        exact ⟨by linarith, by linarith, _, _, hD.1.kronecker hR, hD.1.kronecker hS,
          by rw [Matrix.trace_kronecker, Matrix.trace_kronecker, ← mul_add, hRS, hD.2, one_mul], rfl⟩
      · refine ann_tensorSpace _ M L fun X _ Y hY => ?_
        rw [e1, e2, trace_kron_mul, hannL Y hY, mul_zero]
    · have hMpos : 0 < infWidth M := lt_of_le_of_ne hM0 (fun h => hz2 ⟨h.symm, hLz⟩)
      have hTM : infWidth (tensorSpace M L) = infWidth M := by
        rw [hT, hLz, add_zero, min_eq_left hMπ]
      obtain ⟨hP, hQ, hPQ, hannM⟩ := hWM.1 hMpos
      have e1 : probe L R S = mixedIdentity κ := by unfold probe; rw [if_pos hLz]
      have e2 : probe M P Q = blend (witnessAngle M) P Q := by
        unfold probe; rw [if_neg hMpos.ne']
      have hD := mixedIdentity_density (ι := κ)
      refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd (hTM ▸ h) hMpos.ne'⟩
      · rw [e1, e2, kron_blend_right]
        unfold witnessAngle at *
        rw [hTM]
        exact ⟨by linarith, by linarith, _, _, hP.kronecker hD.1, hQ.kronecker hD.1,
          by rw [Matrix.trace_kronecker, Matrix.trace_kronecker, ← add_mul, hPQ, hD.2, one_mul], rfl⟩
      · refine ann_tensorSpace _ M L fun X hX Y _ => ?_
        rw [e1, e2, trace_kron_mul, hannM X hX, zero_mul]
  push Not at hz
  obtain ⟨hMne, hLne⟩ := hz
  have h1 : 0 < infWidth M := lt_of_le_of_ne hM0 (Ne.symm hMne)
  have h2 : 0 < infWidth L := lt_of_le_of_ne hL0 (Ne.symm hLne)
  have hnz : ¬ (infWidth M = 0 ∨ infWidth L = 0) := by tauto
  by_cases hs : infWidth M + infWidth L < Real.pi
  · have hc : combineProbe M L P Q R S = ((pairMass P Q R S : ℂ)⁻¹) •
        blend (witnessAngle M + witnessAngle L - Real.pi)
          (Matrix.kronecker P R) (Matrix.kronecker Q S) := by
      unfold combineProbe; rw [if_neg hnz, if_pos hs]
    have hTs : infWidth (tensorSpace M L) = infWidth M + infWidth L := by
      rw [hT, min_eq_left hs.le]
    obtain ⟨hP, hQ, hPQ, hannM⟩ := hWM.1 h1
    obtain ⟨hR, hS, hRS, hannL⟩ := hWL.1 h2
    have hrM := parts_rel M P Q _ hannM
    have hrL := parts_rel L R S _ hannL
    have hm := hpm h1 h2 hs
    have hm0 : (0 : ℂ) ≤ ((pairMass P Q R S : ℂ)⁻¹) := by
      rw [show ((pairMass P Q R S : ℂ)⁻¹) = (((pairMass P Q R S)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
      exact_mod_cast (inv_pos.2 hm).le
    rw [hc]
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd (hTs ▸ h) (by linarith)⟩
    · rw [smul_blend]
      have hang : witnessAngle (tensorSpace M L) = witnessAngle M + witnessAngle L - Real.pi := by
        unfold witnessAngle; rw [hTs]; ring
      rw [hang]
      refine ⟨by unfold witnessAngle; linarith, by unfold witnessAngle; linarith, _, _,
        (hP.kronecker hR).smul hm0, (hQ.kronecker hS).smul hm0, ?_, rfl⟩
      simp only [Matrix.trace_smul, Matrix.trace_kronecker, smul_eq_mul]
      rw [psd_trace_re P hP, psd_trace_re Q hQ, psd_trace_re R hR, psd_trace_re S hS, ← mul_add]
      have : (pairMass P Q R S : ℂ) = (P.trace.re : ℂ) * R.trace.re + Q.trace.re * S.trace.re := by
        unfold pairMass; push_cast; ring
      rw [← this, inv_mul_cancel₀ (by exact_mod_cast hm.ne')]
    · refine ann_tensorSpace _ M L fun X hX Y hY => ?_
      simp only [Matrix.smul_mul, Matrix.trace_smul, blend, Matrix.add_mul, Matrix.trace_add,
        smul_eq_mul, trace_kron_mul, hrM X hX, hrL Y hY]
      set c := witnessAngle M + witnessAngle L - Real.pi
      have e : phase (-c / 2) * phase (witnessAngle M) * phase (witnessAngle L) =
          -phase (c / 2) := by
        rw [phase_mul, phase_mul, show -c / 2 + witnessAngle M + witnessAngle L =
          c / 2 + Real.pi by simp only [c]; ring, phase_add_pi]
      linear_combination ((pairMass P Q R S : ℂ)⁻¹ * ((P * X).trace * (R * Y).trace)) * e
  · push Not at hs
    have hc : combineProbe M L P Q R S =
        (((saturatedNumerator (probe M P Q) (probe L R S)).trace.re : ℂ)⁻¹) •
          saturatedNumerator (probe M P Q) (probe L R S) := by
      unfold combineProbe; rw [if_neg hnz, if_neg (not_lt.2 hs)]
    have hTs : infWidth (tensorSpace M L) = Real.pi := by rw [hT, min_eq_right hs]
    obtain ⟨hHpsd, hHtr, hHann⟩ := sat_facts M L P Q R S hWM hWL h1 h2 hs
    set H := saturatedNumerator (probe M P Q) (probe L R S)
    have hr0 : (0 : ℂ) ≤ ((H.trace.re : ℂ)⁻¹) := by
      rw [show ((H.trace.re : ℂ)⁻¹) = ((H.trace.re⁻¹ : ℝ) : ℂ) by push_cast; rfl]
      exact_mod_cast (inv_pos.2 hHtr).le
    rw [hc]
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd (hTs ▸ h) Real.pi_pos.ne'⟩
    · have hang : witnessAngle (tensorSpace M L) = 0 := by
        unfold witnessAngle; rw [hTs, sub_self]
      rw [hang, mem_omega_zero]
      refine ⟨hHpsd.smul hr0, ?_⟩
      rw [Matrix.trace_smul, smul_eq_mul, psd_trace_re H hHpsd]
      simp only [Complex.ofReal_re]
      exact inv_mul_cancel₀ (by exact_mod_cast hHtr.ne')
    · refine ann_tensorSpace _ M L fun X hX Y hY => ?_
      rw [Matrix.smul_mul, Matrix.trace_smul, hHann X hX Y hY, smul_zero]

end X6P75T3

open QAlgorithms.Papers.Independent.Information100.P75 in
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ)) :
    infWidth (tensorSpace M L) = min (infWidth M + infWidth L) Real.pi ∧
    (∃ P Q, WitnessParts M P Q) ∧ (∃ R S, WitnessParts L R S) ∧
    ∀ P Q R S, WitnessParts M P Q → WitnessParts L R S →
      ValidProbe (tensorSpace M L) (combineProbe M L P Q R S) ∧
      (0 < infWidth M → 0 < infWidth L → infWidth M + infWidth L < Real.pi →
        0 < pairMass P Q R S) ∧
      (0 < infWidth M → 0 < infWidth L → Real.pi ≤ infWidth M + infWidth L →
        0 < (saturatedNumerator (probe M P Q) (probe L R S)).trace.re) :=
  X6P75T3.main M L
