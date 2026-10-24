-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P04.teleportationCovariant_iff_choiCommutes
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:46:42.850566+00:00
-- url     : https://prove2.me/submissions/2a11a6db-2375-4418-942b-bbbd103a4207

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P04
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_normalized_choi_covariance

noncomputable section
open QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P04.DensityProof

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

omit [DecidableEq A] in
lemma rankOne_zero (L : Matrix A A ℂ →ₗ[ℂ] W)
    (hL : ∀ rho, IsDensityMatrix rho → L rho = 0) (u : A → ℂ) :
    L (Matrix.vecMulVec u (star u)) = 0 := by
  classical
  by_cases hu : u = 0
  · subst u
    simp
  set t : ℝ := ∑ a, Complex.normSq (u a) with ht
  have htr : (Matrix.vecMulVec u (star u)).trace = (t : ℂ) := by
    simp [Matrix.trace, Matrix.vecMulVec_apply, ht, Complex.mul_conj]
  have hpos : 0 < t := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hu
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr ha)
      (Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (u b)) (Finset.mem_univ a))
  have hd : IsDensityMatrix (((t⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec u (star u)) := by
    refine ⟨(Matrix.posSemidef_vecMulVec_self_star u).smul ?_, ?_⟩
    · exact_mod_cast (inv_nonneg.mpr hpos.le)
    · rw [Matrix.trace_smul, htr, smul_eq_mul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
  have hz := hL _ hd
  rw [map_smul, Complex.ofReal_inv] at hz
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hc := congrArg (fun w : W => (t : ℂ) • w) hz
  simpa [smul_smul, htC] using hc

omit [Fintype A] [DecidableEq A] in
lemma polarization (u v : A → ℂ) :
    Matrix.vecMulVec u (star v) = (1 / 2 : ℂ) •
      (Matrix.vecMulVec (u + v) (star (u + v)) -
        Matrix.vecMulVec u (star u) - Matrix.vecMulVec v (star v) +
        Complex.I • (Matrix.vecMulVec (u + Complex.I • v) (star (u + Complex.I • v)) -
          Matrix.vecMulVec u (star u) - Matrix.vecMulVec v (star v))) := by
  ext i j
  simp [Matrix.vecMulVec, Matrix.of_apply]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

lemma linearMap_eq_zero_of_density (L : Matrix A A ℂ →ₗ[ℂ] W)
    (hL : ∀ rho, IsDensityMatrix rho → L rho = 0) : L = 0 := by
  classical
  have hrank : ∀ u v : A → ℂ, L (Matrix.vecMulVec u (star v)) = 0 := by
    intro u v
    rw [polarization]
    simp only [map_smul, map_add, map_sub, rankOne_zero L hL, sub_zero, add_zero,
      smul_zero]
  have hsingle : ∀ i j : A, L (Matrix.single i j 1) = 0 := by
    intro i j
    have hm : Matrix.vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single j (1 : ℂ))) =
        Matrix.single i j 1 := by
      ext a b
      by_cases hai : a = i <;> by_cases hbj : b = j <;>
        simp_all [Matrix.vecMulVec_apply, eq_comm]
    rw [← hm]
    exact hrank _ _
  ext M
  have hexp : M = ∑ a, ∑ b, M a b • Matrix.single a b (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp [Matrix.smul_single]
  rw [hexp, map_sum]
  simp only [map_sum, map_smul, hsingle, smul_zero, Finset.sum_const_zero,
    LinearMap.zero_apply]

lemma linearMap_eq_of_density (F G : Matrix A A ℂ →ₗ[ℂ] W)
    (h : ∀ rho, IsDensityMatrix rho → F rho = G rho) : F = G := by
  apply sub_eq_zero.mp
  apply linearMap_eq_zero_of_density
  intro rho hrho
  exact sub_eq_zero.mpr (h rho hrho)

/-- Complex linearity follows from the supplied finite Kraus representation.
The map construction follows fizzyinc3's accepted normalized_choi_covariance
submission7d659931-e5ec-4cdb-a7d5-3e2f203bdd54, with no helper import. -/
def channelLinear {B : Type*} [Fintype B] [DecidableEq B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun := Phi
  map_add' := by
    obtain ⟨m, E, _, hPhiE⟩ := hPhi
    intro X Y
    rw [hPhiE, hPhiE X, hPhiE Y]
    unfold krausApply
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := by
    obtain ⟨m, E, _, hPhiE⟩ := hPhi
    intro c X
    rw [hPhiE, hPhiE X]
    unfold krausApply
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp

def conjugateLinear (U : Matrix A A ℂ) : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ where
  toFun := fun X => U * X * Uᴴ
  map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' := by intros; simp

lemma covariance_all_matrices {B : Type*} [Fintype B] [DecidableEq B]
    (Phi : Superop A B) (hPhi : IsChannel Phi)
    (U : Matrix A A ℂ) (V : Matrix B B ℂ)
    (h : ∀ rho, IsDensityMatrix rho → Phi (U * rho * Uᴴ) = V * Phi rho * Vᴴ) :
    ∀ rho, Phi (U * rho * Uᴴ) = V * Phi rho * Vᴴ := by
  have heq : (channelLinear Phi hPhi).comp (conjugateLinear U) =
      (conjugateLinear V).comp (channelLinear Phi hPhi) :=
    linearMap_eq_of_density _ _ h
  intro rho
  exact LinearMap.congr_fun heq rho

end QAlgorithms.Papers.Independent.Dependency50.P04.DensityProof

namespace QAlgorithms.Papers.Independent.Dependency50.P04.WeylProof

lemma phase_star_mul (t : ℝ) :
    star (Complex.exp ((t : ℂ) * Complex.I)) *
      Complex.exp ((t : ℂ) * Complex.I) = 1 := by
  change starRingEnd ℂ (Complex.exp ((t : ℂ) * Complex.I)) *
    Complex.exp ((t : ℂ) * Complex.I) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

lemma teleportationUnitary_apply (d : ℕ) (a b i j : Fin d) :
    teleportationUnitary d a b i j =
      if i = j + a then
        Complex.exp (((2 * Real.pi * (b.val : ℝ) * (j.val : ℝ) / (d : ℝ) : ℝ) : ℂ) *
          Complex.I)
      else 0 := by
  simp only [teleportationUnitary, Fin.ext_iff, Fin.val_add]

/-- Every canonical finite-dimensional Weyl matrix is unitary; no primeness or
additional dimension hypothesis is required. The empty-index case is vacuous. -/
theorem teleportationUnitary_mem (d : ℕ) (a b : Fin d) :
    teleportationUnitary d a b ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  classical
  have hd : 0 < d := Nat.zero_lt_of_lt a.isLt
  let : NeZero d := ⟨ne_of_gt hd⟩
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  simp only [Matrix.mul_apply, Matrix.star_apply]
  rw [Finset.sum_eq_single (j + a)]
  · by_cases hjk : j = k
    · subst k
      simp only [teleportationUnitary_apply, Matrix.one_apply_eq]
      exact phase_star_mul (2 * Real.pi * (b.val : ℝ) * (j.val : ℝ) / (d : ℝ))
    · have hshift : j + a ≠ k + a := fun h => hjk (add_right_cancel h)
      simp [teleportationUnitary_apply, hshift, hjk]
  · intro i _ hi
    simp [teleportationUnitary_apply, hi]
  · simp

/-- Convenient original-root interface retaining its positive-dimension premise. -/
theorem teleportationUnitary_mem_of_pos (d : ℕ) (_hd : 0 < d) (a b : Fin d) :
    teleportationUnitary d a b ∈ Matrix.unitaryGroup (Fin d) ℂ :=
  teleportationUnitary_mem d a b

end QAlgorithms.Papers.Independent.Dependency50.P04.WeylProof

open QAlgorithms.Papers.Independent.Dependency50.P04

theorem solution
    {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (Phi : QAlgorithms.Superop (Fin d) (Fin e)) (hPhi : QAlgorithms.IsChannel Phi) :
    IsTeleportationCovariant Phi ↔
      ∀ a b : Fin d, ∃ V : Matrix.unitaryGroup (Fin e) ℂ,
        QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi Phi *
            Matrix.kronecker (fun i j => star (teleportationUnitary d a b i j))
              (V : Matrix (Fin e) (Fin e) ℂ) =
          Matrix.kronecker (fun i j => star (teleportationUnitary d a b i j))
              (V : Matrix (Fin e) (Fin e) ℂ) * QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi Phi := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
  let U (a b : Fin d) : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨teleportationUnitary d a b, WeylProof.teleportationUnitary_mem d a b⟩
  have key (a b : Fin d) (V : Matrix.unitaryGroup (Fin e) ℂ) :
      (∀ rho, Phi (teleportationUnitary d a b * rho * (teleportationUnitary d a b)ᴴ) =
        (V : Matrix (Fin e) (Fin e) ℂ) * Phi rho * (V : Matrix (Fin e) (Fin e) ℂ)ᴴ) ↔
      QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi Phi *
          Matrix.kronecker (fun i j => star (teleportationUnitary d a b i j))
            (V : Matrix (Fin e) (Fin e) ℂ) =
        Matrix.kronecker (fun i j => star (teleportationUnitary d a b i j))
          (V : Matrix (Fin e) (Fin e) ℂ) *
            QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi Phi := by
    have h := QAlgorithms.Papers.Independent.Information100.P56.normalized_choi_covariance
      Phi hPhi (fun _ : Unit => U a b) (fun _ : Unit => V) ()
    exact h.1.trans h.2
  constructor
  · intro h a b
    obtain ⟨V, hV⟩ := h a b
    refine ⟨V, (key a b V).mp ?_⟩
    exact DensityProof.covariance_all_matrices Phi hPhi _ _ hV
  · intro h a b
    obtain ⟨V, hV⟩ := h a b
    exact ⟨V, fun rho _ => (key a b V).mpr hV rho⟩

end
