-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P24.kacEffectiveSemigroup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:00:57.943982+00:00
-- url     : https://prove2.me/submissions/e5a1d94a-9546-44c4-a626-98e4abee3db3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24
noncomputable section


open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Renew46.P24

lemma g64g_bloch (nu : Matrix Bool Bool ℂ) (hh : nu.IsHermitian) (ht : nu.trace = 1) :
    nu = blochDensity (fun a => (traceExpectation nu (pauli a)).re) := by
  have h1 : nu true false = star (nu false true) := by
    have := congrFun (congrFun hh true) false; simpa [Matrix.conjTranspose_apply] using this.symm
  have h2 : (nu false false).im = 0 := by
    have := congrFun (congrFun hh false) false
    simp [Matrix.conjTranspose_apply] at this
    have := congrArg Complex.im this; simp at this; linarith
  have h3 : (nu true true).im = 0 := by
    have := congrFun (congrFun hh true) true
    simp [Matrix.conjTranspose_apply] at this
    have := congrArg Complex.im this; simp at this; linarith
  have ht' : nu false false + nu true true = 1 := by
    simpa [Matrix.trace, Fintype.sum_bool, add_comm] using ht
  have htr := congrArg Complex.re ht'
  simp at htr
  ext i j
  cases i <;> cases j <;>
    simp [blochDensity, traceExpectation, pauli, QAlgorithms.pauliX, QAlgorithms.pauliY,
      QAlgorithms.pauliZ, Matrix.trace, Matrix.mul_apply, Fintype.sum_bool, Fin.sum_univ_three, h1] <;>
    apply Complex.ext <;> simp <;> linarith

lemma g64g_bloch_herm (m : Fin 3 → ℝ) : (blochDensity m).IsHermitian ∧ (blochDensity m).trace = 1 := by
  constructor
  · ext i j
    cases i <;> cases j <;>
      simp [blochDensity, pauli, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
        Fin.sum_univ_three, Matrix.conjTranspose_apply] <;> ring
  · simp [blochDensity, pauli, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
        Fin.sum_univ_three, Matrix.trace, Fintype.sum_bool]
    ring

lemma g64g_kac_herm (mu : ℝ) (V : Matrix.unitaryGroup Bool ℂ) (nu : Matrix Bool Bool ℂ)
    (hh : nu.IsHermitian) (ht : nu.trace = 1) :
    (kacChannel mu V nu).IsHermitian ∧ (kacChannel mu V nu).trace = 1 := by
  have hVV : star (V : Matrix Bool Bool ℂ) * (V : Matrix Bool Bool ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 V.2
  constructor
  · unfold kacChannel
    have hs : ∀ (r : ℝ) (X : Matrix Bool Bool ℂ), X.IsHermitian → ((r : ℂ) • X).IsHermitian := by
      intro r X hX
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, hX.eq]; simp
    apply Matrix.IsHermitian.add
    · apply hs
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, hh.eq, Matrix.mul_assoc]
    · exact hs _ _ hh
  · unfold kacChannel
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_mul_cycle, hVV,
      Matrix.one_mul, ht]
    simp; push_cast; ring

lemma g64g_kac_density (mu : ℝ) (hmu : mu ∈ Set.Icc (-1) 1) (V : Matrix.unitaryGroup Bool ℂ)
    (nu : Matrix Bool Bool ℂ) (h : QAlgorithms.IsDensityMatrix nu) :
    QAlgorithms.IsDensityMatrix (kacChannel mu V nu) := by
  refine ⟨?_, (g64g_kac_herm mu V nu h.1.1 h.2).2⟩
  unfold kacChannel
  have h1 : (0 : ℂ) ≤ (((1 - mu) / 2 : ℝ) : ℂ) := by
    rw [Complex.zero_le_real]; linarith [hmu.2]
  have h2 : (0 : ℂ) ≤ (((1 + mu) / 2 : ℝ) : ℂ) := by
    rw [Complex.zero_le_real]; linarith [hmu.1]
  refine Matrix.PosSemidef.add (Matrix.PosSemidef.smul ?_ h1) (h.1.smul h2)
  have := h.1.mul_mul_conjTranspose_same (V : Matrix Bool Bool ℂ)
  simpa [Matrix.star_eq_conjTranspose] using this

lemma g64g_kac_step (mu : ℝ) (V : Matrix.unitaryGroup Bool ℂ) (m : Fin 3 → ℝ) :
    kacChannel mu V (blochDensity m) = blochDensity (kacSpinStep mu V m) := by
  have := g64g_bloch_herm m
  have h2 := g64g_kac_herm mu V _ this.1 this.2
  exact g64g_bloch _ h2.1 h2.2

theorem solution (mu : ℝ) (hmu : mu ∈ Set.Icc (-1) 1)
    (V : Matrix.unitaryGroup Bool ℂ) (m : Fin 3 → ℝ)
    (hnu : QAlgorithms.IsDensityMatrix (blochDensity m)) :
    (∀ t : ℕ, (kacChannel mu V)^[t] (blochDensity m) =
      blochDensity ((kacSpinStep mu V)^[t] m) ∧
      QAlgorithms.IsDensityMatrix ((kacChannel mu V)^[t] (blochDensity m))) ∧
    ∀ (s t : ℕ) (nu : Matrix Bool Bool ℂ),
      (kacChannel mu V)^[t + s] nu =
        (kacChannel mu V)^[t] ((kacChannel mu V)^[s] nu) := by
  refine ⟨fun t => ?_, fun s t nu => Function.iterate_add_apply _ _ _ _⟩
  have hA : ∀ t : ℕ, ∀ m, (kacChannel mu V)^[t] (blochDensity m) =
      blochDensity ((kacSpinStep mu V)^[t] m) := by
    intro t
    induction t with
    | zero => intro m; rfl
    | succ t ih =>
      intro m
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, g64g_kac_step, ih]
  refine ⟨hA t m, ?_⟩
  induction t with
  | zero => exact hnu
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact g64g_kac_density mu hmu V _ ih
