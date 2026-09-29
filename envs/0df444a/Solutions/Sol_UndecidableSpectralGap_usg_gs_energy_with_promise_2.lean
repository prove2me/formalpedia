-- Prove2me | solution 2 for UndecidableSpectralGap.usg_gs_energy_with_promise
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T12:10:11.851287+00:00
-- url     : https://prove2.me/submissions/463590ec-960f-46c5-9654-bbf916b8f4b4

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

open UndecidableSpectralGap

namespace UsgGsEnergyWithPromiseProof

/-- A rational number, viewed in `ℂ`, is algebraic over `ℚ`. -/
theorem isAlgebraic_ratCast (q : ℚ) : IsAlgebraic ℚ ((q : ℂ)) := by
  have h : ((q : ℂ)) = algebraMap ℚ ℂ q := by simp
  rw [h]
  exact isAlgebraic_algebraMap q

/-- The operator norm of a scalar multiple of the identity matrix is at most the modulus
of the scalar. -/
theorem opNorm_smul_one_le {m : Type} [Fintype m] [DecidableEq m] (z : ℂ) :
    opNorm (z • (1 : Matrix m m ℂ)) ≤ ‖z‖ := by
  have h : Matrix.toEuclideanCLM (𝕜 := ℂ) (z • (1 : Matrix m m ℂ))
      = z • (1 : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) := by
    simp
  calc opNorm (z • (1 : Matrix m m ℂ))
      = ‖z • (1 : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)‖ := by rw [opNorm, h]
    _ = ‖z‖ * ‖(1 : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)‖ := by rw [norm_smul]
    _ ≤ ‖z‖ * 1 := by
        have := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := EuclideanSpace ℂ m)
        have h1 : (1 : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)
            = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ m) := rfl
        rw [h1]
        exact mul_le_mul_of_nonneg_left this (norm_nonneg z)
    _ = ‖z‖ := mul_one _

/-- A scalar multiple of the identity by a real scalar is Hermitian. -/
theorem isHermitian_real_smul_one {m : Type} [Fintype m] [DecidableEq m] (a : ℝ) :
    ((a : ℂ) • (1 : Matrix m m ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul]
  simp

/-- On a one-element index type the real spectrum of a matrix with real diagonal entry `a`
is `{a}`, so its ground state energy is `a`. -/
theorem gsEnergy_unique {m : Type} [Fintype m] [DecidableEq m] [Unique m]
    (A : Matrix m m ℂ) (a : ℝ) (hA : A default default = (a : ℂ)) :
    gsEnergy A = a := by
  have hspec : specReal A = {a} := by
    ext μ
    constructor
    · intro hμ
      have hmem : (μ : ℂ) ∈ spectrum ℂ A := hμ
      rw [spectrum.mem_iff] at hmem
      by_contra hne
      refine hmem ?_
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
      have hentry : (algebraMap ℂ (Matrix m m ℂ) (μ : ℂ) - A) default default
          = (μ : ℂ) - (a : ℂ) := by
        simp [Algebra.algebraMap_eq_smul_one, hA]
      rw [hentry]
      refine isUnit_iff_ne_zero.mpr ?_
      intro h0
      exact hne (by exact_mod_cast sub_eq_zero.mp h0)
    · intro hμ
      have hμa : μ = a := hμ
      subst hμa
      show (μ : ℂ) ∈ spectrum ℂ A
      rw [spectrum.mem_iff]
      intro hunit
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique] at hunit
      have hentry : (algebraMap ℂ (Matrix m m ℂ) (μ : ℂ) - A) default default
          = (μ : ℂ) - (μ : ℂ) := by
        simp [Algebra.algebraMap_eq_smul_one, hA]
      rw [hentry, sub_self] at hunit
      exact (not_isUnit_zero) hunit
  rw [gsEnergy, hspec, csInf_singleton]

/-- Embedding the zero two-body term gives the zero matrix. -/
theorem embedTwo_zero {L d : ℕ} (p q : Site L) :
    embedTwo (d := d) p q (0 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) = 0 := by
  funext c c'
  simp [embedTwo]

/-- With vanishing two-body terms and on-site term `a • 1` on a one-dimensional local
Hilbert space, the Hamiltonian on `Λ(L)` is the `1 × 1` matrix `L² a`. -/
theorem latticeHam_one_dim (L : ℕ) (a : ℝ) :
    (latticeHam L 1 ((a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0) default default
      = (((L : ℝ) ^ 2 * a : ℝ) : ℂ) := by
  have hsite : ∀ p : Site L,
      (embedOne (d := 1) p ((a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ))) default default
        = (a : ℂ) := by
    intro p
    simp [embedOne]
  rw [latticeHam, Matrix.add_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply,
    Matrix.sum_apply]
  simp only [embedTwo_zero, Matrix.zero_apply, Finset.sum_const_zero, hsite, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, zero_add, add_zero]
  have hcard : (Fintype.card (Site L) : ℂ) = (L : ℂ) ^ 2 := by
    simp [Site, Fintype.card_prod, sq]
  rw [hcard]
  push_cast
  ring

end UsgGsEnergyWithPromiseProof

open UsgGsEnergyWithPromiseProof

theorem solution (u : Nat.Partrec.Code) :
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (Lbound : ℕ → ℕ),
      (∀ n : ℕ,
        (h1 n).IsHermitian ∧ (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        opNorm (h1 n) ≤ 1 / 2 ∧ opNorm (hrow n) ≤ 1 / 2 ∧ opNorm (hcol n) ≤ 1 / 2 ∧
        (∀ i j, IsAlgebraic ℚ ((h1 n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hrow n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hcol n) i j))) ∧
      ∀ n : ℕ,
        (¬ (u.eval n).Dom → ∀ L : ℕ, 0 < L →
          gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)) ≤ 0) ∧
        ((u.eval n).Dom → ∀ L ≥ Lbound n,
          1 ≤ gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n))) := by
  classical
  set c : ℕ → ℝ := fun n => if (u.eval n).Dom then (1 / 2 : ℝ) else 0 with hc
  refine ⟨1, fun n => ((c n : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)), fun _ => 0, fun _ => 0,
    fun _ => 2, fun n => ?_, fun n => ⟨?_, ?_⟩⟩
  · have hcabs : |c n| ≤ 1 / 2 := by
      rw [hc]
      dsimp only
      split <;> norm_num
    refine ⟨isHermitian_real_smul_one _, Matrix.isHermitian_zero, Matrix.isHermitian_zero,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine le_trans (opNorm_smul_one_le _) ?_
      simpa [Complex.norm_real] using hcabs
    · simp [opNorm]
    · simp [opNorm]
    · intro i j
      show IsAlgebraic ℚ (((c n : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) i j)
      have hij : ((c n : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) i j
          = ((if (u.eval n).Dom then (1 / 2 : ℚ) else 0 : ℚ) : ℂ) := by
        rw [hc]
        simp only [Matrix.smul_apply, Matrix.one_apply, Subsingleton.elim i j, smul_eq_mul]
        split <;> norm_num
      rw [hij]
      exact isAlgebraic_ratCast _
    · intro i j; simpa using isAlgebraic_ratCast 0
    · intro i j; simpa using isAlgebraic_ratCast 0
  · -- non-halting: the on-site term vanishes, so the Hamiltonian is zero
    intro hnd L _
    have hcn : c n = 0 := by rw [hc]; simp [hnd]
    have := gsEnergy_unique (latticeHam L 1 ((c n : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0)
      ((L : ℝ) ^ 2 * c n) (latticeHam_one_dim L (c n))
    rw [this, hcn, mul_zero]
  · -- halting: the on-site term is `1/2`, so the energy is `L²/2 ≥ 2`
    intro hd L hL
    have hcn : c n = 1 / 2 := by rw [hc]; simp [hd]
    have heq := gsEnergy_unique
      (latticeHam L 1 ((c n : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0)
      ((L : ℝ) ^ 2 * c n) (latticeHam_one_dim L (c n))
    rw [heq, hcn]
    have hL2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    nlinarith

