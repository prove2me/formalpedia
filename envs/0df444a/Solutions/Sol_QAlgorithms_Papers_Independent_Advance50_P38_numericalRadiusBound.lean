-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.numericalRadiusBound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:31:15.486271+00:00
-- url     : https://prove2.me/submissions/d8280144-e11a-4383-a8eb-5c2f4a820cf8

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
open QAlgorithms.Papers.Independent.Advance50.P38
open scoped Matrix

theorem frob_eq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    QAlgorithms.frobNorm X = Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) := by
  unfold QAlgorithms.frobNorm
  let _ := Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℂ)
  rw [Matrix.frobenius_norm_def]
  rw [Real.sqrt_eq_rpow]
  simp

noncomputable def ev {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => X p.1 p.2)

theorem ev_norm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ‖ev X‖ = QAlgorithms.frobNorm X := by
  rw [frob_eq, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  rfl

theorem ev_inner {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) :
    inner ℂ (ev C) (ev B) = Matrix.trace (C.conjTranspose * B) := by
  simp only [ev, PiLp.inner_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

theorem frob_zero {n : ℕ} : QAlgorithms.frobNorm (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  rw [frob_eq]; simp

theorem ev_eq_zero {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (h : ev B = 0) : B = 0 := by
  ext i j
  have := congrArg (fun v : EuclideanSpace ℂ (Fin n × Fin n) => v (i, j)) h
  simpa [ev] using this

theorem cs_le {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.trace (C.conjTranspose * B)‖ ≤ QAlgorithms.frobNorm B * QAlgorithms.frobNorm C := by
  rw [← ev_inner, ← ev_norm, ← ev_norm, mul_comm]
  exact norm_inner_le_norm (𝕜 := ℂ) (ev C) (ev B)

theorem cs_eq {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.trace (C.conjTranspose * B)‖ = QAlgorithms.frobNorm B * QAlgorithms.frobNorm C ↔
      ComplexCollinear B C := by
  by_cases hB : B = 0
  · subst hB
    simp only [Matrix.mul_zero, Matrix.trace_zero, norm_zero, frob_zero, zero_mul, true_iff]
    exact ⟨1, 0, Or.inl one_ne_zero, by simp⟩
  by_cases hC : C = 0
  · subst hC
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero, norm_zero, frob_zero,
      mul_zero, true_iff]
    exact ⟨0, 1, Or.inr one_ne_zero, by simp⟩
  have hxB : ev B ≠ 0 := fun h => hB (ev_eq_zero h)
  have hxC : ev C ≠ 0 := fun h => hC (ev_eq_zero h)
  rw [← ev_inner, ← ev_norm, ← ev_norm, mul_comm (‖ev B‖), norm_inner_eq_norm_iff hxC hxB]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨1, -r, Or.inl one_ne_zero, ?_⟩
    ext i j
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n × Fin n) => v (i, j)) h
    simp only [ev] at this
    simp [this]
  · rintro ⟨a, b, hab, h⟩
    have hent : ∀ i j, a * B i j + b * C i j = 0 := fun i j => by
      have := congrFun (congrFun h i) j
      simpa using this
    have ha : a ≠ 0 := by
      intro ha0
      rcases hab with h1 | h1
      · exact h1 ha0
      · apply hC
        ext i j
        have := hent i j
        simp only [ha0, zero_mul, zero_add] at this
        simpa [h1] using this
    have hb : b ≠ 0 := by
      intro hb0
      apply hB
      ext i j
      have := hent i j
      simp only [hb0, zero_mul, add_zero] at this
      simpa [ha] using this
    refine ⟨-b / a, div_ne_zero (neg_ne_zero.2 hb) ha, ?_⟩
    ext p
    have := hent p.1 p.2
    simp only [ev, PiLp.smul_apply, smul_eq_mul]
    field_simp
    linear_combination this

theorem frob_conj {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℂ) (h1 : U * U.conjTranspose = 1)
    (h2 : U.conjTranspose * U = 1) :
    QAlgorithms.frobNorm (U * A * U.conjTranspose) = QAlgorithms.frobNorm A := by
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      ((QAlgorithms.frobNorm X : ℝ) : ℂ) ^ 2 = Matrix.trace (X.conjTranspose * X) := by
    intro X
    rw [← ev_norm, ← ev_inner, inner_self_eq_norm_sq_to_K]
    rfl
  have hmain : Matrix.trace ((U * A * U.conjTranspose).conjTranspose * (U * A * U.conjTranspose)) =
      Matrix.trace (A.conjTranspose * A) := by
    have e1 : (U * A * U.conjTranspose).conjTranspose * (U * A * U.conjTranspose) =
        U * (A.conjTranspose * (U.conjTranspose * U) * A * U.conjTranspose) := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [e1, h2, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ U, h2, Matrix.mul_one]
  have := key (U * A * U.conjTranspose)
  rw [hmain, ← key A] at this
  have h3 : QAlgorithms.frobNorm (U * A * U.conjTranspose) ^ 2 = QAlgorithms.frobNorm A ^ 2 := by
    exact_mod_cast this
  have hn1 : 0 ≤ QAlgorithms.frobNorm (U * A * U.conjTranspose) := by rw [frob_eq]; exact Real.sqrt_nonneg _
  have hn2 : 0 ≤ QAlgorithms.frobNorm A := by rw [frob_eq]; exact Real.sqrt_nonneg _
  exact (sq_eq_sq₀ hn1 hn2).1 h3

theorem compactK (n : ℕ) :
    IsCompact {M : Matrix (Fin n) (Fin n) ℂ | M * M.conjTranspose = 1 ∧ M.det = 1} := by
  have hclosed : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | M * M.conjTranspose = 1 ∧ M.det = 1} := by
    refine IsClosed.inter ?_ ?_
    · exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const
    · exact isClosed_eq continuous_id.matrix_det continuous_const
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ
      fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset hbox hclosed ?_
  rintro M ⟨hM, -⟩ i - j -
  have h := congrFun (congrFun hM i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h' : ∑ j, ((‖M i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h'' : ∑ j, ‖M i j‖ ^ 2 = 1 := by exact_mod_cast h'
  have hle : ‖M i j‖ ^ 2 ≤ 1 := by
    rw [← h'']
    exact Finset.single_le_sum (f := fun j => ‖M i j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg (M i j)]

theorem solution {n : ℕ} (hn : 0 < n) (A C : (Matrix (Fin n) (Fin n) ℂ)) :
    (∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      numericalRadius A C =
        ‖Matrix.trace (C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))‖) ∧
    numericalRadius A C ≤ QAlgorithms.frobNorm A * QAlgorithms.frobNorm C ∧
    (numericalRadius A C = QAlgorithms.frobNorm A * QAlgorithms.frobNorm C ↔
      ∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
        ComplexCollinear ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose) C) := by
  set F : Matrix (Fin n) (Fin n) ℂ → ℝ :=
    fun M => ‖Matrix.trace (C.conjTranspose * (M * A * M.conjTranspose))‖ with hF
  have hcont : Continuous F := by
    refine Continuous.norm ?_
    exact (continuous_const.matrix_mul ((continuous_id.matrix_mul continuous_const).matrix_mul
      continuous_id.matrix_conjTranspose)).matrix_trace
  have hne : ({M : Matrix (Fin n) (Fin n) ℂ | M * M.conjTranspose = 1 ∧ M.det = 1}).Nonempty :=
    ⟨1, by simp⟩
  obtain ⟨M0, hM0, hmax⟩ := (compactK n).exists_isMaxOn hne hcont.continuousOn
  have hmem : ∀ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      (U : Matrix (Fin n) (Fin n) ℂ) ∈ {M : Matrix (Fin n) (Fin n) ℂ | M * M.conjTranspose = 1 ∧ M.det = 1} := by
    intro U
    have := Matrix.mem_specialUnitaryGroup_iff.1 U.2
    exact ⟨Matrix.mem_unitaryGroup_iff.1 this.1, this.2⟩
  let U0 : Matrix.specialUnitaryGroup (Fin n) ℂ :=
    ⟨M0, Matrix.mem_specialUnitaryGroup_iff.2 ⟨Matrix.mem_unitaryGroup_iff.2 hM0.1, hM0.2⟩⟩
  have hG : IsGreatest {r | ∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      r = ‖Matrix.trace (C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A *
        (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))‖} (F M0) := by
    refine ⟨⟨U0, rfl⟩, ?_⟩
    rintro r ⟨U, rfl⟩
    exact hmax (hmem U)
  have hnr : numericalRadius A C = F M0 := hG.csSup_eq
  have hunit : ∀ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      QAlgorithms.frobNorm ((U : Matrix (Fin n) (Fin n) ℂ) * A *
        (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose) = QAlgorithms.frobNorm A := by
    intro U
    have := (Matrix.mem_specialUnitaryGroup_iff.1 U.2).1
    exact frob_conj _ _ (Matrix.mem_unitaryGroup_iff.1 this) (Matrix.mem_unitaryGroup_iff'.1 this)
  have hle : F M0 ≤ QAlgorithms.frobNorm A * QAlgorithms.frobNorm C := by
    have := cs_le ((U0 : Matrix (Fin n) (Fin n) ℂ) * A * (U0 : Matrix (Fin n) (Fin n) ℂ).conjTranspose) C
    rw [hunit U0] at this
    exact this
  refine ⟨⟨U0, hnr⟩, hnr ▸ hle, ?_⟩
  constructor
  · intro h
    refine ⟨U0, (cs_eq _ C).1 ?_⟩
    rw [hunit U0, ← h, hnr]
  · rintro ⟨U, hU⟩
    have h1 := (cs_eq _ C).2 hU
    rw [hunit U] at h1
    refine le_antisymm (hnr ▸ hle) ?_
    rw [← h1, hnr]
    exact hG.2 ⟨U, rfl⟩
