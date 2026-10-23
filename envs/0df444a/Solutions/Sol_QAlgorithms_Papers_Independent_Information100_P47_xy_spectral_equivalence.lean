-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P47.xy_spectral_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:12:19.582729+00:00
-- url     : https://prove2.me/submissions/125e9268-df4e-4041-9060-d161a284e8a0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix ComplexOrder

namespace X6P47X

open QAlgorithms.Papers.Independent.Information100.P47 hiding spectralNorm

local notation "SN" => QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
local notation "TR" => QAlgorithms.Papers.Independent.Information100.P47.trivial

/-- an entry bounds the spectral norm from below -/
theorem entry_le {d : ℕ} (X : Mat d) (i j : Fin d) :
    ENNReal.ofReal ‖X i j‖ ≤ SN X := by
  unfold QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
  set v : EuclideanSpace ℂ (Fin d) := EuclideanSpace.single j 1
  have hv : ‖v‖ = 1 := by simp [v]
  refine le_trans ?_ (le_iSup _ ⟨v, hv⟩)
  apply ENNReal.ofReal_le_ofReal
  have h1 : (QAlgorithms.act X v) i = X i j := by
    simp [QAlgorithms.act, v]
  rw [← h1]
  exact PiLp.norm_apply_le _ i

/-- conjugation by a unitary does not increase the spectral norm -/
theorem conj_le {d : ℕ} (U Y : Mat d) (hU : IsUnitary U) :
    SN (Uᴴ * Y * U) ≤ SN Y := by
  unfold QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
  refine iSup_le fun v => ?_
  set w : EuclideanSpace ℂ (Fin d) := QAlgorithms.act U v.val
  have hiso : ∀ (W : Mat d), Wᴴ * W = 1 → ∀ u : EuclideanSpace ℂ (Fin d),
      ‖QAlgorithms.act W u‖ = ‖u‖ := by
    intro W hW u
    have key : (W *ᵥ WithLp.ofLp u) ⬝ᵥ star (W *ᵥ WithLp.ofLp u) =
        WithLp.ofLp u ⬝ᵥ star (WithLp.ofLp u) := by
      rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        hW, Matrix.one_mulVec, dotProduct_comm]
    have h2 : ‖QAlgorithms.act W u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, QAlgorithms.act, WithLp.ofLp_toLp]
      rw [key]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hw : ‖w‖ = 1 := by rw [hiso U hU.1, v.2]
  refine le_trans ?_ (le_iSup _ ⟨w, hw⟩)
  apply ENNReal.ofReal_le_ofReal
  have : QAlgorithms.act (Uᴴ * Y * U) v.val = QAlgorithms.act Uᴴ (QAlgorithms.act Y w) := by
    simp [QAlgorithms.act, w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [this, hiso Uᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hU.2)]


theorem hn (z : ℂ) (h1 : z.re ^ 2 = 1) (h2 : z.im ^ 2 = 1) : |√2|⁻¹ * ‖z‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, h1, h2, abs_of_pos (by positivity)]
  norm_num

theorem diag_entries : ∀ x : Fin 4, xyPOVM x 0 0 = 1/4 ∧ xyPOVM x 1 1 = 1/4 := by
  intro x; fin_cases x <;> simp [xyPOVM, sigmaX, sigmaY]

theorem off_entries : ∀ x : Fin 4, ‖xyPOVM x 0 1‖ = 1/4 ∧ ‖xyPOVM x 1 0‖ = 1/4 := by
  intro x; fin_cases x <;> simp [xyPOVM, sigmaX, sigmaY] <;>
    exact ⟨hn _ (by simp) (by simp), hn _ (by simp) (by simp)⟩

theorem offdiag_bound (X : Mat 2) (h00 : X 0 0 = 0) (h11 : X 1 1 = 0)
    (h01 : ‖X 0 1‖ = 1/4) (h10 : ‖X 1 0‖ = 1/4) : SN X ≤ ENNReal.ofReal (1/4) := by
  unfold QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
  refine iSup_le fun v => ENNReal.ofReal_le_ofReal ?_
  have hv := v.2
  have hsq : ‖QAlgorithms.act X v.val‖ ^ 2 = (1/16) * ‖v.val‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [QAlgorithms.act, Fin.sum_univ_two, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
      h00, h11, zero_mul, zero_add, add_zero, norm_mul, h01, h10, mul_pow]
    ring
  rw [hv] at hsq
  have h0 : 0 ≤ ‖QAlgorithms.act X v.val‖ := norm_nonneg _
  nlinarith

end X6P47X

open X6P47X QAlgorithms.Papers.Independent.Information100.P47 in
theorem solution :
    maxCoherence spectralDistance xyPOVM = sharpness spectralDistance xyPOVM := by
  set c : ℝ≥0∞ := (1 / 2 : ℝ≥0∞) * ∑ _x : Fin 4, ENNReal.ofReal (1/4)
  -- general: maxCoherence ≤ sharpness
  have h4 : maxCoherence spectralDistance xyPOVM ≤ sharpness spectralDistance xyPOVM := by
    refine iSup_le fun U => le_iInf fun p => ?_
    have hP : QAlgorithms.IsPOVM (QAlgorithms.Papers.Independent.Information100.P47.trivial (d := 2) p.val) ∧ IsIncoherent (QAlgorithms.Papers.Independent.Information100.P47.trivial (d := 2) p.val) := by
      refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
      · exact Matrix.PosSemidef.one.smul (Complex.zero_le_real.2 (p.2.1 x))
      · simp only [QAlgorithms.Papers.Independent.Information100.P47.trivial]
        rw [← Finset.sum_smul, ← Complex.ofReal_sum, p.2.2]; simp
      · intro x i j hij; simp [QAlgorithms.Papers.Independent.Information100.P47.trivial, Matrix.one_apply_ne hij]
    refine (iInf_le _ ⟨QAlgorithms.Papers.Independent.Information100.P47.trivial p.val, hP⟩).trans ?_
    simp only [spectralDistance]
    gcongr with x
    have : rotate U.val xyPOVM x - QAlgorithms.Papers.Independent.Information100.P47.trivial p.val x =
        U.valᴴ * (xyPOVM x - QAlgorithms.Papers.Independent.Information100.P47.trivial p.val x) * U.val := by
      simp only [rotate, QAlgorithms.Papers.Independent.Information100.P47.trivial, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, U.2.1]
    rw [this]
    exact conj_le _ _ U.2
  -- sharpness ≤ c
  have h2 : sharpness spectralDistance xyPOVM ≤ c := by
    have hp : IsProbability (fun _ : Fin 4 => (1/4 : ℝ)) := ⟨fun _ => by norm_num, by simp⟩
    refine (iInf_le _ ⟨_, hp⟩).trans ?_
    simp only [spectralDistance, c]
    gcongr with x
    apply offdiag_bound
    · simp [QAlgorithms.Papers.Independent.Information100.P47.trivial, (diag_entries x).1]
    · simp [QAlgorithms.Papers.Independent.Information100.P47.trivial, (diag_entries x).2]
    · simpa [QAlgorithms.Papers.Independent.Information100.P47.trivial] using (off_entries x).1
    · simpa [QAlgorithms.Papers.Independent.Information100.P47.trivial] using (off_entries x).2
  -- c ≤ maxCoherence
  have h3 : c ≤ maxCoherence spectralDistance xyPOVM := by
    refine le_trans ?_ (le_iSup _ ⟨1, by simp [IsUnitary]⟩)
    refine le_iInf fun B => ?_
    simp only [spectralDistance, c]
    gcongr with x
    have hrot : rotate (1 : Mat 2) xyPOVM x = xyPOVM x := by simp [rotate]
    rw [hrot]
    have := entry_le (xyPOVM x - B.val x) 0 1
    have hB : B.val x 0 1 = 0 := B.2.2 x 0 1 (by decide)
    rw [Matrix.sub_apply, hB, sub_zero, (off_entries x).1] at this
    exact this
  exact le_antisymm h4 (h2.trans h3)
