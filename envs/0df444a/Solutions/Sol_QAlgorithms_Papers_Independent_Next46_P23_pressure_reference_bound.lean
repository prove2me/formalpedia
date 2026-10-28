-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.pressure_reference_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:10:47.195988+00:00
-- url     : https://prove2.me/submissions/56967740-a5cb-4a5e-a0e8-1bec311e1433

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_entropy_variational
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology
namespace QAlgorithms.Papers.Independent.Next46.P23
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

section S173Q1
open scoped MatrixOrder
theorem S169E_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (O : Matrix ι ι ℂ) (w : ι → ℂ) :
    ‖star w ⬝ᵥ (O *ᵥ w)‖ ≤ QAlgorithms.specNorm O * ∑ j, ‖w j‖ ^ 2 := by
  set x : EuclideanSpace ℂ ι := WithLp.toLp 2 w
  have h1 : star w ⬝ᵥ (O *ᵥ w) = inner ℂ x ((EuclideanSpace.equiv ι ℂ).symm (O *ᵥ x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
  rw [h1]
  refine (norm_inner_le_norm _ _).trans ?_
  have h2 := Matrix.l2_opNorm_mulVec O x
  have hx : ‖x‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  unfold QAlgorithms.specNorm
  calc ‖x‖ * ‖(EuclideanSpace.equiv ι ℂ).symm (O *ᵥ x)‖ ≤ ‖x‖ * (‖O‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖O‖ * ‖x‖ ^ 2 := by ring
    _ = _ := by rw [hx]

theorem S169E_trbound {ι : Type*} [Fintype ι] [DecidableEq ι] (σ O : Matrix ι ι ℂ)
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) : |(σ * O).trace.re| ≤ QAlgorithms.specNorm O := by
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hσ.nonneg
  rw [Matrix.star_eq_conjTranspose] at hD
  set w : ι → ι → ℂ := fun k j => star (D k j)
  have hkk : ∀ k, (D * O * Dᴴ) k k = star (w k) ⬝ᵥ (O *ᵥ w k) := by
    intro k
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, w,
      Pi.star_apply, star_star, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have htr' : (σ * O).trace = ∑ k, star (w k) ⬝ᵥ (O *ᵥ w k) := by
    rw [hD, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [Matrix.trace]; exact Finset.sum_congr rfl fun k _ => hkk k
  have hnorm : ∑ k, ∑ j, ‖w k j‖ ^ 2 = 1 := by
    have : σ.trace = ∑ k, ∑ j, ((‖w k j‖ ^ 2 : ℝ) : ℂ) := by
      rw [hD, Matrix.trace_mul_comm, Matrix.trace]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, w]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_star, Complex.star_def, Complex.mul_conj']; push_cast; rfl
    rw [htr] at this
    have := congrArg Complex.re this
    simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at this
    linarith
  rw [htr']
  calc |(∑ k, star (w k) ⬝ᵥ (O *ᵥ w k)).re| ≤ ‖∑ k, star (w k) ⬝ᵥ (O *ᵥ w k)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ k, ‖star (w k) ⬝ᵥ (O *ᵥ w k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, QAlgorithms.specNorm O * ∑ j, ‖w k j‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => S169E_quad O (w k)
    _ = QAlgorithms.specNorm O := by rw [← Finset.mul_sum, hnorm, mul_one]
end S173Q1

lemma h54b_cfc_conj {B : Type*} [Fintype B] [DecidableEq B] (u : Matrix.unitaryGroup B ℂ)
    (f : ℝ → ℝ) (A : Matrix B B ℂ) :
    cfc f ((u : Matrix B B ℂ) * A * (u : Matrix B B ℂ)ᴴ) =
      (u : Matrix B B ℂ) * cfc f A * (u : Matrix B B ℂ)ᴴ := by
  by_cases hA : IsSelfAdjoint A
  · let φ := Unitary.conjStarAlgAut ℂ (Matrix B B ℂ) u
    have hφ : Continuous φ :=
      (φ.toAlgEquiv.toLinearEquiv.toLinearMap).continuous_of_finiteDimensional
    have hφa : IsSelfAdjoint (φ A) := by
      simp only [φ, Unitary.conjStarAlgAut_apply]
      exact hA.conjugate _
    have := StarAlgHomClass.map_cfc φ f A ((Matrix.finite_real_spectrum).continuousOn _) hφ hA hφa
    simpa [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using this.symm
  · have h2 : ¬ IsSelfAdjoint ((u : Matrix B B ℂ) * A * (u : Matrix B B ℂ)ᴴ) := by
      intro h
      apply hA
      have h3 := h.conjugate ((u : Matrix B B ℂ)ᴴ)
      have hu : (u : Matrix B B ℂ)ᴴ * (u : Matrix B B ℂ) = 1 := Unitary.star_mul_self_of_mem u.2
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at h3
      have : (u : Matrix B B ℂ)ᴴ * ((u : Matrix B B ℂ) * A * (u : Matrix B B ℂ)ᴴ) *
          (u : Matrix B B ℂ) = A := by
        rw [show (u : Matrix B B ℂ)ᴴ * ((u : Matrix B B ℂ) * A * (u : Matrix B B ℂ)ᴴ) *
          (u : Matrix B B ℂ) = ((u : Matrix B B ℂ)ᴴ * (u : Matrix B B ℂ)) * A *
            ((u : Matrix B B ℂ)ᴴ * (u : Matrix B B ℂ)) by simp only [Matrix.mul_assoc]]
        rw [hu, Matrix.one_mul, Matrix.mul_one]
      rwa [this] at h3
    rw [cfc_apply_of_not_predicate _ h2, cfc_apply_of_not_predicate _ hA]
    simp

variable {I : Type} [Fintype I] [DecidableEq I]

lemma S173Q_lip [Nonempty I] (X Y : Mat I) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Real.log ((NormedSpace.exp X).trace.re) - Real.log ((NormedSpace.exp Y).trace.re) ≤
      QAlgorithms.specNorm (X - Y) := by
  obtain ⟨hgX, hX2⟩ := entropy_variational.2 X hX
  obtain ⟨_, hY2⟩ := entropy_variational.2 Y hY
  set ρ := QAlgorithms.gibbsState X
  have e1 := ((hX2 ρ hgX).2).mpr rfl
  have e2 := (hY2 ρ hgX).1
  have hlin : ev ρ X - ev ρ Y = ((ρ * (X - Y)).trace).re := by
    simp only [ev, QAlgorithms.effectProb, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [Matrix.trace_mul_comm X ρ, Matrix.trace_mul_comm Y ρ]
  have hb := S169E_trbound ρ (X - Y) hgX.1 hgX.2
  have := le_abs_self ((ρ * (X - Y)).trace.re)
  linarith

lemma S173Q_lip_abs [Nonempty I] (X Y : Mat I) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    |Real.log ((NormedSpace.exp X).trace.re) - Real.log ((NormedSpace.exp Y).trace.re)| ≤
      QAlgorithms.specNorm (X - Y) := by
  rw [abs_le]
  have h1 := S173Q_lip X Y hX hY
  have h2 := S173Q_lip Y X hY hX
  have hn : QAlgorithms.specNorm (Y - X) = QAlgorithms.specNorm (X - Y) := by
    unfold QAlgorithms.specNorm; rw [← norm_neg, neg_sub]
  constructor <;> linarith

lemma S173Q_logMat_herm (A : Mat I) : (logMat A).IsHermitian :=
  cfc_predicate (R := ℝ) (p := IsSelfAdjoint) _ A

lemma S173Q_prop_unitary (H : Mat I) (hH : H.IsHermitian) (t : ℝ) :
    propagator H t ∈ Matrix.unitaryGroup I ℂ ∧ (propagator H t)ᴴ = propagator H (-t) := by
  have hc : (propagator H t)ᴴ = propagator H (-t) := by
    unfold propagator
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]
    congr 2; simp [Complex.star_def]
  refine ⟨?_, hc⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hc]
  unfold propagator
  rw [← Matrix.exp_add_of_commute]
  · have : ((-((-t : ℝ) : ℂ) * Complex.I) • H + (-(t : ℂ) * Complex.I) • H) = 0 := by
      rw [← add_smul]; push_cast; ring_nf; simp
    rw [this, NormedSpace.exp_zero]
  · exact (Commute.refl H).smul_left _ |>.smul_right _

lemma S173Q_norm_conj [Nonempty I] (U D : Mat I) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    QAlgorithms.specNorm (U * D * Uᴴ) ≤ QAlgorithms.specNorm D := by
  unfold QAlgorithms.specNorm
  have hU1 : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary hU
  have hU2 : ‖Uᴴ‖ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact CStarRing.norm_of_mem_unitary (Unitary.star_mem hU)
  calc ‖U * D * Uᴴ‖ ≤ ‖U * D‖ * ‖Uᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖U‖ * ‖D‖ * ‖Uᴴ‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ = ‖D‖ := by rw [hU1, hU2]; ring

theorem S173Q_main [Nonempty I] (H omega rho : Mat I) (hH : H.IsHermitian) :
    ∀ t a : ℝ, |pressure H omega ⊤ t a - pressure H rho ⊤ t a| ≤
      (|1-a| + |a|) * QAlgorithms.specNorm (relativeHamiltonian omega rho) := by
  intro t a
  obtain ⟨hU, hUc⟩ := S173Q_prop_unitary H hH t
  set U := propagator H t
  have hev : ∀ σ : Mat I, evolved H σ t = U * σ * Uᴴ := by
    intro σ; simp only [evolved, tau, neg_neg, hUc, U]
  have hlog : ∀ σ : Mat I, logMat (evolved H σ t) = U * logMat σ * Uᴴ := by
    intro σ; rw [hev]; exact h54b_cfc_conj ⟨U, hU⟩ Real.log σ
  unfold pressure
  simp only [if_true, hlog]
  set D := relativeHamiltonian omega rho
  have hherm : ∀ σ : Mat I, ((((1 - a : ℝ) : ℂ) • logMat σ + (a : ℂ) • (U * logMat σ * Uᴴ))).IsHermitian := by
    intro σ
    have h1 := S173Q_logMat_herm σ
    have h2 : (U * logMat σ * Uᴴ).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h1.eq,
        Matrix.mul_assoc]
    refine Matrix.IsHermitian.add ?_ ?_
    · unfold Matrix.IsHermitian at h1 ⊢; rw [Matrix.conjTranspose_smul, h1]; simp
    · unfold Matrix.IsHermitian at h2 ⊢; rw [Matrix.conjTranspose_smul, h2]; simp
  refine (S173Q_lip_abs _ _ (hherm omega) (hherm rho)).trans ?_
  have hdiff : (((1 - a : ℝ) : ℂ) • logMat omega + (a : ℂ) • (U * logMat omega * Uᴴ)) -
      (((1 - a : ℝ) : ℂ) • logMat rho + (a : ℂ) • (U * logMat rho * Uᴴ)) =
      ((1 - a : ℝ) : ℂ) • D + (a : ℂ) • (U * D * Uᴴ) := by
    simp only [D, relativeHamiltonian, smul_sub, Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [hdiff]
  unfold QAlgorithms.specNorm
  calc ‖((1 - a : ℝ) : ℂ) • D + (a : ℂ) • (U * D * Uᴴ)‖
      ≤ ‖((1 - a : ℝ) : ℂ) • D‖ + ‖(a : ℂ) • (U * D * Uᴴ)‖ := norm_add_le _ _
    _ = |1 - a| * ‖D‖ + |a| * ‖U * D * Uᴴ‖ := by
        rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |1 - a| * ‖D‖ + |a| * ‖D‖ := by
        gcongr; exact S173Q_norm_conj U D hU
    _ = (|1 - a| + |a|) * ‖D‖ := by ring

end QAlgorithms.Papers.Independent.Next46.P23

open QAlgorithms.Papers.Independent.Next46.P23
open QAlgorithms.Papers.Independent.Information100.P60 (Mat) in
theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (H omega rho : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hrhofaithful : rho.PosDef) :
    (∀ t a : ℝ, |pressure H omega ⊤ t a - pressure H rho ⊤ t a| ≤
      (|1-a| + |a|) * QAlgorithms.specNorm (relativeHamiltonian omega rho)) ∧
    (∀ t a : ℝ, 0 < t →
      |pressure H omega ⊤ t a / t - pressure H rho ⊤ t a / t| ≤
        (|1-a| + |a|) * QAlgorithms.specNorm (relativeHamiltonian omega rho) / t) := by
  refine ⟨S173Q_main H omega rho hH, fun t a ht => ?_⟩
  rw [← sub_div, abs_div, abs_of_pos ht]
  exact div_le_div_of_nonneg_right (S173Q_main H omega rho hH t a) ht.le
