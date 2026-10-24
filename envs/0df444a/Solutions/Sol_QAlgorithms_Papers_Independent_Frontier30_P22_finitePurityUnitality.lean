-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P22.finitePurityUnitality
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T10:12:41.083601+00:00
-- url     : https://prove2.me/submissions/ba63c87b-83b9-4c62-a965-26b02b5b0a5e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P22


noncomputable section
open Filter
open scoped BigOperators Matrix ComplexConjugate Topology Matrix.Norms.L2Operator
namespace QAlgorithms.Papers.Independent.Frontier30.P22.FlowProof
open QAlgorithms.Papers.Independent.Dependency50.P16

/-- Arbitrary-time extension of the derivative-at-zero argument in the accepted
collectingSubspace proof 2c35ef6d-5587-447e-a311-4dd3aa4ad988 (fizzyinc3). -/
lemma hasDerivAt_evolution {d : ℕ}
    (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroupEvolution G s X)
      (G (semigroupEvolution G t X)) t := by
  let G' := LinearMap.toContinuousLinearMap G
  have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℂ) G' (Complex.ofRealCLM t)
  have h2 := h1.clm_apply (hasDerivAt_const (Complex.ofRealCLM t) X)
  have h3 := h2.scomp t Complex.ofRealCLM.hasDerivAt
  convert h3 using 1 <;> first
    | rfl
    | simp only [G', semigroupEvolution, Complex.ofRealCLM_apply,
        mul_apply_eq_comp, LinearMap.coe_toContinuousLinearMap', map_zero,
        add_zero, Complex.ofReal_one, one_smul]

lemma evolution_zero {d : ℕ} (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin d) (Fin d) ℂ) : semigroupEvolution G 0 X = X := by
  let G' := LinearMap.toContinuousLinearMap G
  have hz : NormedSpace.exp ((Complex.ofRealCLM 0) • G') = 1 := by
    rw [map_zero]
    convert NormedSpace.exp_zero using 2
    · exact zero_smul ℂ G'
    · infer_instance
  change NormedSpace.exp ((Complex.ofRealCLM 0) • G') X = X
  rw [hz]
  rfl

lemma evolution_hermitian {d : ℕ}
    (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hG : ∀ X, X.IsHermitian → (G X).IsHermitian)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) (t : ℝ) :
    (semigroupEvolution G t X).IsHermitian := by
  let G' := LinearMap.toContinuousLinearMap G
  let A := (t : ℂ) • G'
  have hp : ∀ k : ℕ, ((A ^ k) X).IsHermitian := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp]
      change ((t : ℂ) • G ((A ^ k) X)).IsHermitian
      exact (hG _ ih).smul (by simp [IsSelfAdjoint])
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have he : NormedSpace.exp A X =
      ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • A ^ k) X := by
    rw [NormedSpace.exp_eq_tsum ℂ]
    exact (ContinuousLinearMap.apply ℂ (Matrix (Fin d) (Fin d) ℂ) X).map_tsum hs
  change (NormedSpace.exp A X).IsHermitian
  rw [he]
  change (∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • A ^ k) X)ᴴ = _
  rw [Matrix.conjTranspose_tsum]
  apply tsum_congr
  intro k
  change (((k.factorial : ℂ)⁻¹) • (A ^ k) X)ᴴ = _
  exact ((hp k).smul (show IsSelfAdjoint ((k.factorial : ℂ)⁻¹) by
    simp [IsSelfAdjoint])).eq

lemma hasDerivAt_purity {d : ℕ}
    (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => finitePurity (semigroupEvolution G s X))
      (2 * ((semigroupEvolution G t X) * G (semigroupEvolution G t X)).trace.re) t := by
  have h := hasDerivAt_evolution G X t
  let tr : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.restrictScalars ℝ)
  have hm := tr.hasFDerivAt.comp_hasDerivAt t (h.mul h)
  change HasDerivAt (fun s : ℝ => finitePurity (semigroupEvolution G s X))
    (G (semigroupEvolution G t X) * semigroupEvolution G t X +
      semigroupEvolution G t X * G (semigroupEvolution G t X)).trace.re t at hm
  rw [Matrix.trace_add, Matrix.trace_mul_comm (G (semigroupEvolution G t X))] at hm
  simpa only [Complex.add_re, two_mul] using hm

lemma antitone_purity {d : ℕ}
    (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hG : ∀ X, X.IsHermitian → (G X).IsHermitian)
    (hdiss : ∀ X, X.IsHermitian → 2 * (X * G X).trace.re ≤ 0)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    Antitone (fun s : ℝ => finitePurity (semigroupEvolution G s X)) := by
  apply antitone_of_hasDerivAt_nonpos (hasDerivAt_purity G X)
  intro t
  exact hdiss _ (evolution_hermitian G hG X hX t)

lemma initial_derivative_nonpos {d : ℕ}
    (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin d) (Fin d) ℂ)
    (h : AntitoneOn (fun s : ℝ => finitePurity (semigroupEvolution G s X)) (Set.Ici 0)) :
    2 * (X * G X).trace.re ≤ 0 := by
  have hd := (hasDerivAt_purity G X 0).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Ici (0 : ℝ))
  have hb := h.derivWithin_nonpos (x := 0)
  rw [hd, evolution_zero] at hb
  exact hb

end QAlgorithms.Papers.Independent.Frontier30.P22.FlowProof


noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P16

namespace QAlgorithms.Papers.Independent.Frontier30.P22.GeneratorProof

variable {d : ℕ}

lemma generator_apply (D : LindbladData d) (X : Matrix (Fin d) (Fin d) ℂ) :
    gkslGenerator D X = (∑ j, D.jump j * X * (D.jump j)ᴴ) -
      driftK D * X - X * (driftK D)ᴴ := by
  simp [gkslGenerator, cpGenerator, sandwich, Matrix.mul_assoc]

lemma driftK_adjoint (D : LindbladData d) :
    (driftK D)ᴴ = -Complex.I • D.drift +
      (1 / 2 : ℂ) • ∑ j, (D.jump j)ᴴ * D.jump j := by
  simp [driftK, Matrix.conjTranspose_smul, D.drift_hermitian.eq,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]

lemma driftK_add_adjoint (D : LindbladData d) :
    driftK D + (driftK D)ᴴ = ∑ j, (D.jump j)ᴴ * D.jump j := by
  rw [driftK_adjoint, driftK]
  module

lemma identity_image (D : LindbladData d) :
    gkslGenerator D 1 = finiteIdentityImage D := by
  rw [generator_apply]
  simp only [Matrix.mul_one, Matrix.one_mul]
  rw [sub_sub, driftK_add_adjoint]
  simp only [finiteIdentityImage, Finset.sum_sub_distrib]

lemma trace_generator (D : LindbladData d) (X : Matrix (Fin d) (Fin d) ℂ) :
    (gkslGenerator D X).trace = 0 := by
  rw [generator_apply]
  simp only [Matrix.trace_sub, Matrix.trace_sum]
  have hterm : ∀ j, (D.jump j * X * (D.jump j)ᴴ).trace =
      ((D.jump j)ᴴ * D.jump j * X).trace := by
    intro j
    rw [Matrix.trace_mul_cycle]
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, ← driftK_add_adjoint,
    Matrix.add_mul, Matrix.trace_add, Matrix.trace_mul_comm X (driftK D)ᴴ]
  ring

lemma hermitian_generator (D : LindbladData d) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) : (gkslGenerator D X).IsHermitian := by
  rw [generator_apply]
  change _ᴴ = _
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX.eq]
  simp only [Matrix.mul_assoc]
  abel

lemma trace_mul_generator (D : LindbladData d) (X : Matrix (Fin d) (Fin d) ℂ) :
    (X * gkslGenerator D X).trace = ∑ j,
      ((X * D.jump j * X * (D.jump j)ᴴ).trace -
        (X * X * (D.jump j)ᴴ * D.jump j).trace) := by
  rw [generator_apply]
  simp only [Matrix.mul_sub, Matrix.mul_sum, Matrix.trace_sub, Matrix.trace_sum]
  have hK : (X * (driftK D * X)).trace = (X * X * driftK D).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle X (driftK D) X
  rw [hK, ← Matrix.mul_assoc X X (driftK D)ᴴ, sub_sub,
    ← Matrix.trace_add, ← Matrix.mul_add, driftK_add_adjoint,
    Matrix.mul_sum, Matrix.trace_sum, ← Finset.sum_sub_distrib]
  simp only [Matrix.mul_assoc]

lemma commutator_trace_identity (X V : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) :
    2 * ((X * V * X * Vᴴ).trace - (X * X * Vᴴ * V).trace) =
      -((X * V - V * X)ᴴ * (X * V - V * X)).trace +
        (X * X * (V * Vᴴ - Vᴴ * V)).trace := by
  have h₁ : (Vᴴ * X * X * V).trace = (X * X * V * Vᴴ).trace := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm Vᴴ (X * X * V))
  have h₂ : (Vᴴ * X * V * X).trace = (X * V * X * Vᴴ).trace := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm Vᴴ (X * V * X))
  have h₃ : (X * Vᴴ * X * V).trace = (X * V * X * Vᴴ).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (X * Vᴴ) (X * V)
  have h₄ : (X * Vᴴ * V * X).trace = (X * X * Vᴴ * V).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (X * Vᴴ) V X
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hX.eq,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  simp only [← Matrix.mul_assoc]
  rw [h₁, h₂, h₃, h₄]
  ring

/-- The exact complex trace identity; in particular no density or positivity
premise is needed beyond Hermiticity of the test matrix. -/
lemma dissipation_identity_complex (D : LindbladData d)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    2 * (X * gkslGenerator D X).trace =
      -(∑ j, ((X * D.jump j - D.jump j * X)ᴴ *
        (X * D.jump j - D.jump j * X)).trace) +
      (X * X * finiteIdentityImage D).trace := by
  rw [trace_mul_generator, Finset.mul_sum]
  simp_rw [commutator_trace_identity X _ hX]
  simp only [finiteIdentityImage, Matrix.mul_sum, Matrix.trace_sum,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

lemma dissipation_identity (D : LindbladData d)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    2 * (X * gkslGenerator D X).trace.re =
      -(∑ j, ((X * D.jump j - D.jump j * X)ᴴ *
        (X * D.jump j - D.jump j * X)).trace.re) +
      (X * X * finiteIdentityImage D).trace.re := by
  have h := congrArg Complex.re (dissipation_identity_complex D X hX)
  simpa using h

lemma dissipation_nonpos (D : LindbladData d) (hD : finiteIdentityImage D = 0)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    2 * (X * gkslGenerator D X).trace.re ≤ 0 := by
  rw [dissipation_identity D X hX, hD]
  simp only [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, add_zero,
    neg_nonpos]
  exact Finset.sum_nonneg fun j _ =>
    (Matrix.posSemidef_conjTranspose_mul_self (X * D.jump j - D.jump j * X)).trace_nonneg.1

end QAlgorithms.Papers.Independent.Frontier30.P22.GeneratorProof


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Unitary Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P22.NecessityProof

variable {d : ℕ}

lemma affine_posSemidef (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (t : ℝ) (ht : ∀ i, 0 ≤ 1 + t * hA.eigenvalues i) :
    (1 + (t : ℂ) • A).PosSemidef := by
  let U := hA.eigenvectorUnitary
  have hd : (Matrix.diagonal (fun i => ((1 + t * hA.eigenvalues i : ℝ) : ℂ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr (ht i)
  have hp := hd.mul_mul_conjTranspose_same (U : Matrix (Fin d) (Fin d) ℂ)
  have heq : Matrix.diagonal (fun i => ((1 + t * hA.eigenvalues i : ℝ) : ℂ)) =
      1 + (t : ℂ) • Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [heq] at hp
  have hu : (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  have hspec : (U : Matrix (Fin d) (Fin d) ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = A :=
    hA.spectral_theorem.symm
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
    Matrix.smul_mul, hu, hspec] using hp

/-- The entire two-sided interval around zero consists of density perturbations. -/
lemma eventually_density_perturb (hd : 1 ≤ d) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (htr : A.trace = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, QAlgorithms.IsDensityMatrix
      ((d : ℂ)⁻¹ • (1 + (t : ℂ) • A)) := by
  have heig : ∀ᶠ t : ℝ in 𝓝 0, ∀ i : Fin d, 0 ≤ 1 + t * hA.eigenvalues i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℝ => 1 + t * hA.eigenvalues i) 0 := by fun_prop
    exact (hc.eventually (Ioi_mem_nhds (by norm_num))).mono fun _ h => h.le
  filter_upwards [heig] with t ht
  refine ⟨(affine_posSemidef A hA t ht).smul ?_, ?_⟩
  · exact inv_nonneg.mpr (Complex.zero_le_real.mpr (Nat.cast_nonneg d))
  · have hdz : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    simp [Matrix.trace_smul, Matrix.trace_add, htr, hdz]

lemma exists_density_perturb_radius (hd : 1 ≤ d) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (htr : A.trace = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → QAlgorithms.IsDensityMatrix
      ((d : ℂ)⁻¹ • (1 + (t : ℂ) • A)) := by
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (eventually_density_perturb hd A hA htr)
  exact ⟨ε, hε, fun t ht => he (by simpa [Real.dist_eq] using ht)⟩

lemma linear_coefficient_zero (a b : ℝ)
    (h : ∀ᶠ t : ℝ in 𝓝 0, t * a + t ^ 2 * b ≤ 0) : a = 0 := by
  have hm : IsLocalMax (fun t : ℝ => t * a + t ^ 2 * b) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, t * a + t ^ 2 * b ≤ (0 : ℝ) * a + 0 ^ 2 * b
    simpa using h
  have hd : HasDerivAt (fun t : ℝ => t * a + t ^ 2 * b) a 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const a).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const b) using 1 <;> first | rfl | norm_num
  exact hm.hasDerivAt_eq_zero hd

end QAlgorithms.Papers.Independent.Frontier30.P22.NecessityProof


noncomputable section
open Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology
open QAlgorithms.Papers.Independent.Dependency50.P16

namespace QAlgorithms.Papers.Independent.Frontier30.P22.NecessityProof

variable {d : ℕ}

lemma trace_real_scale (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (r : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    (((r : ℂ) • X) * G ((r : ℂ) • X)).trace.re = r ^ 2 * (X * G X).trace.re := by
  simp [Matrix.trace_smul, smul_smul, Complex.mul_re, pow_two]

lemma perturb_trace_formula (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (htr : ∀ X, (G X).trace = 0) (t : ℝ) :
    ((1 + (t : ℂ) • G 1) * G (1 + (t : ℂ) • G 1)).trace.re =
      t * (G 1 * G 1).trace.re + t ^ 2 * (G 1 * G (G 1)).trace.re := by
  simp [map_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    Matrix.trace_smul, smul_smul, htr, Complex.mul_re, pow_two]

/-- A trace-annihilating linear generator with Hermitian image of I must annihilate
I if its instantaneous purity derivative is nonpositive on every density. -/
theorem generator_identity_zero (hd : 1 ≤ d)
    (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (htr : ∀ X, (G X).trace = 0) (hherm : (G 1).IsHermitian)
    (h : ∀ rho : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix rho →
      2 * (rho * G rho).trace.re ≤ 0) : G 1 = 0 := by
  have hevent : ∀ᶠ t : ℝ in 𝓝 0,
      t * (G 1 * G 1).trace.re + t ^ 2 * (G 1 * G (G 1)).trace.re ≤ 0 := by
    filter_upwards [eventually_density_perturb hd (G 1) hherm (htr 1)] with t ht
    have hh := h ((d : ℂ)⁻¹ • (1 + (t : ℂ) • G 1)) ht
    have hs : (((d : ℂ)⁻¹ • (1 + (t : ℂ) • G 1)) *
        G ((d : ℂ)⁻¹ • (1 + (t : ℂ) • G 1))).trace.re =
        ((d : ℝ)⁻¹)^2 * (((1 + (t : ℂ) • G 1) * G (1 + (t : ℂ) • G 1)).trace.re) := by
      simpa using trace_real_scale G (d : ℝ)⁻¹ (1 + (t : ℂ) • G 1)
    rw [hs, perturb_trace_formula G htr] at hh
    have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hc : 0 < ((d : ℝ)⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr hdp)
    have hp : ((d : ℝ)⁻¹)^2 *
        (t * (G 1 * G 1).trace.re + t ^ 2 * (G 1 * G (G 1)).trace.re) ≤ 0 := by linarith
    by_contra hn
    have hpos := mul_pos hc (lt_of_not_ge hn)
    linarith
  have ha : (G 1 * G 1).trace.re = 0 := linear_coefficient_zero _ _ hevent
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  apply Complex.ext
  · simpa only [hherm.eq, Complex.zero_re] using ha
  · exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (G 1)).trace_nonneg).2.symm

/-- The original instantaneous necessity direction, with precisely its original
positive-dimension and density hypotheses. -/
theorem identityImage_eq_zero_of_instantaneous {d : ℕ} (hd : 1 ≤ d) (D : LindbladData d)
    (h : ∀ rho : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix rho →
      2 * (rho * gkslGenerator D rho).trace.re ≤ 0) : finiteIdentityImage D = 0 := by
  rw [← GeneratorProof.identity_image D]
  exact generator_identity_zero hd (gkslGenerator D) (GeneratorProof.trace_generator D)
    (GeneratorProof.hermitian_generator D 1 Matrix.isHermitian_one) h

end QAlgorithms.Papers.Independent.Frontier30.P22.NecessityProof


open QAlgorithms.Papers.Independent.Dependency50.P16
open QAlgorithms.Papers.Independent.Frontier30.P22

/-- The original finite-dimensional purity/unitality theorem. -/
theorem solution {d : ℕ} (hd : 1 ≤ d) (D : LindbladData d) :
    (finitePurityNonincreasing D ↔ finiteIdentityImage D = 0) ∧
    ((∀ rho : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix rho →
      2 * (rho * gkslGenerator D rho).trace.re ≤ 0) ↔ finiteIdentityImage D = 0) ∧
    gkslGenerator D 1 = finiteIdentityImage D := by
  have hinst : (∀ rho : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix rho →
      2 * (rho * gkslGenerator D rho).trace.re ≤ 0) ↔ finiteIdentityImage D = 0 := by
    constructor
    · exact NecessityProof.identityImage_eq_zero_of_instantaneous hd D
    · intro h rho hrho
      exact GeneratorProof.dissipation_nonpos D h rho hrho.1.isHermitian
  refine ⟨⟨?_, ?_⟩, hinst, GeneratorProof.identity_image D⟩
  · intro h
    apply hinst.mp
    intro rho hrho
    exact FlowProof.initial_derivative_nonpos (gkslGenerator D) rho (h rho hrho)
  · intro h rho hrho
    exact (FlowProof.antitone_purity (gkslGenerator D)
      (GeneratorProof.hermitian_generator D) (GeneratorProof.dissipation_nonpos D h)
      rho hrho.1.isHermitian).antitoneOn _
