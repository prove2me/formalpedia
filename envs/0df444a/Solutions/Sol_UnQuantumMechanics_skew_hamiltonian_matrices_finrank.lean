-- Prove2me | solution 1 for UnQuantumMechanics.skew_hamiltonian_matrices_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:17:41.02921+00:00
-- url     : https://prove2.me/submissions/2847eae4-64df-486c-91ac-997b3fc6b4b6

import Mathlib
import Definitions.Def_UnQM_phase_space

set_option autoImplicit false

namespace S903964C3

open Matrix UnQuantumMechanics
open scoped Kronecker

lemma eta0_sq : eta0 * eta0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0, Matrix.mul_apply, Fin.sum_univ_two]

lemma gamma0_sq (n : ℕ) : gamma0 n * gamma0 n = -1 := by
  unfold gamma0
  change (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ eta0 * ((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ eta0) = -1
  rw [← Matrix.mul_kronecker_mul, eta0_sq, Matrix.one_mul]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [kroneckerMap_apply, Matrix.neg_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : i = j <;> by_cases h2 : a = b <;> simp [h1, h2]

/-- An injective key used to orient off-diagonal pairs. -/
noncomputable def key (n : ℕ) (i : PhaseIdx n) : ℕ := (Fintype.equivFin (PhaseIdx n) i : ℕ)

lemma key_inj (n : ℕ) : Function.Injective (key n) := by
  intro i j h
  exact (Fintype.equivFin (PhaseIdx n)).injective (Fin.ext h)

/-- Orientation sign. -/
noncomputable def sgn (n : ℕ) (i j : PhaseIdx n) : ℝ := if key n i < key n j then 1 else -1

lemma sgn_swap (n : ℕ) {i j : PhaseIdx n} (h : i ≠ j) : sgn n j i = - sgn n i j := by
  have hk : key n i ≠ key n j := fun e => h (key_inj n e)
  unfold sgn
  rcases lt_or_gt_of_ne hk with h1 | h1
  · rw [if_neg (not_lt.mpr h1.le), if_pos h1]
  · rw [if_pos h1, if_neg (not_lt.mpr h1.le)]; norm_num

lemma sgn_sq (n : ℕ) (i j : PhaseIdx n) : sgn n i j * sgn n i j = 1 := by
  unfold sgn; split_ifs <;> norm_num

/-- Extend a function on off-diagonal pairs by zero. -/
noncomputable def ext0 (n : ℕ) (g : {s : Sym2 (PhaseIdx n) // ¬ s.IsDiag} → ℝ)
    (s : Sym2 (PhaseIdx n)) : ℝ :=
  if h : s.IsDiag then 0 else g ⟨s, h⟩

/-- The skew matrix attached to a function on off-diagonal pairs. -/
noncomputable def skewMat (n : ℕ) (g : {s : Sym2 (PhaseIdx n) // ¬ s.IsDiag} → ℝ) :
    Matrix (PhaseIdx n) (PhaseIdx n) ℝ :=
  Matrix.of fun i j => sgn n i j * ext0 n g s(i, j)

lemma skewMat_add (n : ℕ) (g h : {s : Sym2 (PhaseIdx n) // ¬ s.IsDiag} → ℝ) :
    skewMat n (g + h) = skewMat n g + skewMat n h := by
  ext i j
  simp only [skewMat, ext0, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> ring

lemma skewMat_smul (n : ℕ) (c : ℝ) (g : {s : Sym2 (PhaseIdx n) // ¬ s.IsDiag} → ℝ) :
    skewMat n (c • g) = c • skewMat n g := by
  ext i j
  simp only [skewMat, ext0, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The linear map `g ↦ γ₀ * skewMat g`. -/
noncomputable def G (n : ℕ) :
    ({s : Sym2 (PhaseIdx n) // ¬ s.IsDiag} → ℝ) →ₗ[ℝ] Matrix (PhaseIdx n) (PhaseIdx n) ℝ where
  toFun g := gamma0 n * skewMat n g
  map_add' g h := by rw [skewMat_add, Matrix.mul_add]
  map_smul' c g := by
    simp only [RingHom.id_apply]
    rw [skewMat_smul, Matrix.mul_smul]

lemma G_inj (n : ℕ) : Function.Injective (G n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  have h1 : skewMat n g = 0 := by
    have h2 : gamma0 n * (gamma0 n * skewMat n g) = 0 := by
      change gamma0 n * (G n g) = 0
      rw [hg, Matrix.mul_zero]
    rw [← Matrix.mul_assoc, gamma0_sq, Matrix.neg_mul, Matrix.one_mul, neg_eq_zero] at h2
    exact h2
  funext ⟨s, hs⟩
  induction s using Sym2.ind with
  | h i j =>
    have hij : ¬ (s(i, j)).IsDiag := hs
    have := congrFun (congrFun h1 i) j
    simp only [skewMat, ext0, Matrix.of_apply, Matrix.zero_apply, dif_neg hij] at this
    have h3 := congrArg (fun x => sgn n i j * x) this
    rw [← mul_assoc, sgn_sq, one_mul, mul_zero] at h3
    exact h3

lemma skewMat_skew (n : ℕ) (g : {s : Sym2 (PhaseIdx n) // ¬ s.IsDiag} → ℝ) :
    (skewMat n g)ᵀ = - skewMat n g := by
  ext i j
  simp only [skewMat, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    simp [ext0, Sym2.mk_isDiag_iff]
  · rw [sgn_swap n hij, Sym2.eq_swap]; ring

lemma set_eq (n : ℕ) :
    {M | IsSkewHamiltonianMatrix n M} = (LinearMap.range (G n) : Set _) := by
  ext M
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_range]
  constructor
  · rintro ⟨B, hB, rfl⟩
    have hB' : ∀ i j, B j i = - B i j := by
      intro i j
      have := congrFun (congrFun hB i) j
      simpa [Matrix.transpose_apply] using this
    have hsym : ∀ i j, sgn n i j * B i j = sgn n j i * B j i := by
      intro i j
      by_cases hij : i = j
      · subst hij; rfl
      · rw [sgn_swap n hij, hB' i j]; ring
    refine ⟨fun s => Sym2.lift ⟨fun i j => sgn n i j * B i j, hsym⟩ s.1, ?_⟩
    change gamma0 n * skewMat n _ = _
    congr 1
    ext i j
    simp only [skewMat, ext0, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      have h0 : B i i = 0 := by have := hB' i i; linarith
      simp [Sym2.mk_isDiag_iff, h0]
    · have hd : ¬ (s(i, j)).IsDiag := by rw [Sym2.mk_isDiag_iff]; exact hij
      rw [dif_neg hd, Sym2.lift_mk, ← mul_assoc, sgn_sq, one_mul]
  · rintro ⟨g, rfl⟩
    exact ⟨skewMat n g, skewMat_skew n g, rfl⟩

lemma choose_eq (n : ℕ) : Nat.choose (n * 2) 2 = n * (2 * n - 1) := by
  rw [Nat.choose_two_right]
  rcases n with _ | m
  · simp
  · have h : (m + 1) * 2 * ((m + 1) * 2 - 1) = 2 * ((m + 1) * (2 * (m + 1) - 1)) := by
      have e1 : (m + 1) * 2 - 1 = 2 * m + 1 := by omega
      have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [e1, e2]; ring
    rw [h, Nat.mul_div_cancel_left _ (by norm_num)]

end S903964C3

open Matrix UnQuantumMechanics in
theorem solution (n : ℕ) :
    Module.finrank ℝ (Submodule.span ℝ {M | IsSkewHamiltonianMatrix n M}) = n * (2 * n - 1) := by
  rw [S903964C3.set_eq, Submodule.span_eq, LinearMap.finrank_range_of_inj (S903964C3.G_inj n),
    Module.finrank_fintype_fun_eq_card, Sym2.card_subtype_not_diag]
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact S903964C3.choose_eq n
