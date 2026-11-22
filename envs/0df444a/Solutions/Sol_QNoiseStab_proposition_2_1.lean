-- Prove2me | solution 1 for QNoiseStab.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T07:01:54.102162+00:00
-- url     : https://prove2.me/submissions/89ada188-a9f5-407b-a02c-39c6589f2101

import Mathlib

open Matrix

theorem solution {N : ℕ} (hN : 0 < N) (M : Matrix (Fin N) (Fin N) ℝ)
    (hM : M.IsHermitian) (hnn : ∀ i j, 0 ≤ M i j) :
    let hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    let r : Fin N → ℝ := fun i => ∑ j, M i j
    let lamMax : ℝ := Finset.univ.sup' hne hM.eigenvalues
    (Finset.univ.inf' hne r ≤ lamMax ∧ lamMax ≤ Finset.univ.sup' hne r) ∧
      ∀ c : ℝ, (∀ i, r i = c) → lamMax = c := by
  dsimp only
  set hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩ with hne_def
  set r : Fin N → ℝ := fun i => ∑ j, M i j with hr
  set lamMax : ℝ := Finset.univ.sup' hne hM.eigenvalues with hlam
  -- Upper bound: every eigenvalue is at most the largest row sum.
  have hsup_le : lamMax ≤ Finset.univ.sup' hne r := by
    rw [hlam]
    apply Finset.sup'_le hne
    intro i _
    set w : Fin N → ℝ := (hM.eigenvectorBasis i).ofLp with hw
    have hwne : w ≠ 0 := by
      intro hzero
      have h1 : hM.eigenvectorBasis i = 0 := (WithLp.ofLp_eq_zero 2).mp hzero
      exact (hM.eigenvectorBasis.orthonormal.ne_zero i) h1
    obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
      by_contra h
      push Not at h
      exact hwne (funext h)
    obtain ⟨j, -, hjmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset (Fin N)) (fun k => |w k|) hne
    have hwjpos : 0 < |w j| := by
      have h1 : 0 < |w k| := abs_pos.mpr hk
      have h2 : |w k| ≤ |w j| := hjmax k (Finset.mem_univ k)
      linarith
    have h1 : hM.eigenvalues i * w j = ∑ k, M j k * w k := by
      have h := congrFun (hM.mulVec_eigenvectorBasis i) j
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
      exact h.symm
    have h3 : |∑ k, M j k * w k| ≤ ∑ k, M j k * |w k| := by
      refine (Finset.abs_sum_le_sum_abs (fun k => M j k * w k) Finset.univ).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul, abs_of_nonneg (hnn j k)]
    have h4 : ∑ k, M j k * |w k| ≤ ∑ k, M j k * |w j| := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hjmax k (Finset.mem_univ k)) (hnn j k)
    have h5 : ∑ k, M j k * |w j| = r j * |w j| := by
      simp [hr, Finset.sum_mul]
    have h6 : |hM.eigenvalues i| * |w j| ≤ Finset.univ.sup' hne r * |w j| := by
      calc |hM.eigenvalues i| * |w j| = |hM.eigenvalues i * w j| := (abs_mul _ _).symm
        _ = |∑ k, M j k * w k| := by rw [h1]
        _ ≤ ∑ k, M j k * |w k| := h3
        _ ≤ ∑ k, M j k * |w j| := h4
        _ = r j * |w j| := h5
        _ ≤ Finset.univ.sup' hne r * |w j| :=
            mul_le_mul_of_nonneg_right (Finset.le_sup' r (Finset.mem_univ j)) (abs_nonneg _)
    have h7 : |hM.eigenvalues i| ≤ Finset.univ.sup' hne r :=
      le_of_mul_le_mul_right h6 hwjpos
    calc hM.eigenvalues i ≤ |hM.eigenvalues i| := le_abs_self _
      _ ≤ Finset.univ.sup' hne r := h7
  -- Lower bound via the Rayleigh quotient of the constant vector.
  have hinf_le : Finset.univ.inf' hne r ≤ lamMax := by
    set U : Matrix (Fin N) (Fin N) ℝ := ↑hM.eigenvectorUnitary with hUdef
    set d : Fin N → ℝ := fun i => hM.eigenvalues i with hd
    have hstarU : star U = Uᵀ := by
      rw [hUdef, ← Unitary.coe_star]
      ext i j
      simp
    have hcoU : (↑hM.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) *
        (↑hM.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)ᵀ = 1 := by
      have h := Unitary.coe_mul_star_self hM.eigenvectorUnitary
      rw [show (↑(star hM.eigenvectorUnitary) : Matrix (Fin N) (Fin N) ℝ) =
          (↑hM.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)ᵀ from by
        ext i j
        simp] at h
      exact h
    have hUU : U * Uᵀ = 1 := by
      rw [hUdef]
      exact hcoU
    have hspec : M = U * diagonal d * Uᵀ := by
      rw [hUdef, hd]
      conv_lhs => rw [hM.spectral_theorem]
      rw [Unitary.conjStarAlgAut_apply]
      rw [show star (↑hM.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) =
          (↑hM.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)ᵀ from by
        rw [← Unitary.coe_star]
        ext i j
        simp]
      simp [Matrix.mul_assoc, RCLike.ofReal]
    have hassoc : ∀ (A B : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ),
        (A * B) *ᵥ v = A *ᵥ (B *ᵥ v) := by
      intro A B v
      rw [← Matrix.mulVecLin_apply, Matrix.mulVecLin_mul, LinearMap.comp_apply,
        Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    set x : Fin N → ℝ := fun _ => 1 with hx
    set c : Fin N → ℝ := Uᵀ *ᵥ x with hc
    have hMx : M *ᵥ x = U *ᵥ (diagonal d *ᵥ c) := by
      rw [hspec, hc, hassoc, hassoc]
    have hq1 : x ⬝ᵥ (M *ᵥ x) = c ⬝ᵥ (diagonal d *ᵥ c) := by
      rw [hMx, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← hc]
    have hq2 : c ⬝ᵥ (diagonal d *ᵥ c) = ∑ i, d i * (c i) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec_diagonal]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hdle : ∀ i, d i ≤ lamMax := by
      intro i
      rw [hd, hlam]
      exact Finset.le_sup' hM.eigenvalues (Finset.mem_univ i)
    have hq3 : ∑ i, d i * (c i) ^ 2 ≤ lamMax * ∑ i, (c i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hdle i) (sq_nonneg _)
    have hcsq : ∑ i, (c i) ^ 2 = c ⬝ᵥ c := by
      simp [dotProduct, sq]
    have hcc : c ⬝ᵥ c = x ⬝ᵥ x := by
      rw [hc]
      calc (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = (x ᵥ* U) ⬝ᵥ (Uᵀ *ᵥ x) := by
            rw [Matrix.mulVec_transpose]
        _ = x ⬝ᵥ (U *ᵥ (Uᵀ *ᵥ x)) := by rw [← Matrix.dotProduct_mulVec]
        _ = x ⬝ᵥ ((U * Uᵀ) *ᵥ x) := by rw [hassoc]
        _ = x ⬝ᵥ (1 *ᵥ x) := by rw [hUU]
        _ = x ⬝ᵥ x := by rw [Matrix.one_mulVec]
    have hxN : x ⬝ᵥ x = (N : ℝ) := by
      simp [dotProduct, hx]
    have hqbound : x ⬝ᵥ (M *ᵥ x) ≤ lamMax * (x ⬝ᵥ x) := by
      calc x ⬝ᵥ (M *ᵥ x) = ∑ i, d i * (c i) ^ 2 := by rw [hq1, hq2]
        _ ≤ lamMax * ∑ i, (c i) ^ 2 := hq3
        _ = lamMax * (c ⬝ᵥ c) := by rw [hcsq]
        _ = lamMax * (x ⬝ᵥ x) := by rw [hcc]
    have hsumr : ∑ i, r i = x ⬝ᵥ (M *ᵥ x) := by
      simp only [dotProduct, Matrix.mulVec, hr, hx]
      simp
    have hsum_le : ∑ i, r i ≤ lamMax * (N : ℝ) := by
      rw [hsumr]
      simpa [hxN] using hqbound
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hNinf : (N : ℝ) * Finset.univ.inf' hne r ≤ ∑ i, r i := by
      calc (N : ℝ) * Finset.univ.inf' hne r = ∑ _i : Fin N, Finset.univ.inf' hne r := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ∑ i, r i := by
            apply Finset.sum_le_sum
            intro i _
            exact Finset.inf'_le r (Finset.mem_univ i)
    have h1 : (N : ℝ) * Finset.univ.inf' hne r ≤ (N : ℝ) * lamMax := by
      calc (N : ℝ) * Finset.univ.inf' hne r ≤ ∑ i, r i := hNinf
        _ ≤ lamMax * (N : ℝ) := hsum_le
        _ = (N : ℝ) * lamMax := by ring
    exact le_of_mul_le_mul_left h1 hNpos
  refine ⟨⟨hinf_le, hsup_le⟩, ?_⟩
  intro c hc
  have hc' : ∀ i, r i = c := hc
  have hsupc : Finset.univ.sup' hne r = c := by
    apply le_antisymm
    · exact Finset.sup'_le hne r (fun i _ => (hc' i).le)
    · have h := Finset.le_sup' r (Finset.mem_univ (⟨0, hN⟩ : Fin N))
      rw [hc'] at h
      exact h
  have hinfc : Finset.univ.inf' hne r = c := by
    apply le_antisymm
    · have h := Finset.inf'_le r (Finset.mem_univ (⟨0, hN⟩ : Fin N))
      rw [hc'] at h
      exact h
    · exact Finset.le_inf' hne r (fun i _ => (hc' i).ge)
  linarith [hinf_le, hsup_le, hinfc, hsupc]

