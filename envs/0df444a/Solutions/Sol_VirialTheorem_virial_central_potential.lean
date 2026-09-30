-- Prove2me | solution 1 for VirialTheorem.virial_central_potential
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:29:25.592092+00:00
-- url     : https://prove2.me/submissions/9f67cf48-4e08-4205-baf6-d54e21f5198c

import Definitions.Def_virial_theorem_defs
set_option autoImplicit false
open VirialTheorem
private theorem central_gradient (V : ℝ → ℝ) (a b : Space) (hne : a ≠ b)
    (hV : DifferentiableAt ℝ V (dist b a)) :
    gradient (fun y => V (dist y a)) b = (deriv V (dist b a) / dist b a) • (b-a) := by
  have hn : ‖b-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hs := ((hasFDerivAt_id b).sub_const a).norm_sq
  have hroot := hs.sqrt (pow_ne_zero 2 hn)
  have hd : HasFDerivAt (fun y : Space => dist y a)
      (‖b-a‖⁻¹ • innerSL ℝ (b-a)) b := by
    convert! hroot using 1
    · funext y
      simp [dist_eq_norm, Real.sqrt_sq (norm_nonneg (y-a))]
    · ext y
      simp [Real.sqrt_sq (norm_nonneg (b-a))]
      field_simp
      <;> ring
  have hcomp := hV.hasDerivAt.comp_hasFDerivAt b hd
  have hg : HasGradientAt (fun y => V (dist y a))
      ((deriv V (dist b a) / dist b a) • (b-a)) b := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! hcomp using 1
    ext y
    simp [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, dist_eq_norm,
      div_eq_mul_inv, mul_assoc]
  exact hg.gradient

theorem central_force {N : ℕ} (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space)
    (j k : Fin N) (hjk : j ≠ k) (hx : x j ≠ x k)
    (hV : DifferentiableAt ℝ (V j k) (dist (x k) (x j))) :
    pairForce V x j k =
      -(deriv (V j k) (dist (x k) (x j)) / dist (x k) (x j)) • (x k - x j) := by
  rw [pairForce, if_neg hjk, central_gradient (V j k) (x j) (x k) hx hV]
  simp only [neg_smul]

theorem forces_antisymm {N : ℕ} (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space)
    (hsymm : ∀ j k, V j k = V k j)
    (hx : ∀ j k, j ≠ k → x j ≠ x k)
    (hV : ∀ j k, j ≠ k → DifferentiableAt ℝ (V j k) (dist (x k) (x j))) :
    ∀ j k, pairForce V x j k = -pairForce V x k j := by
  intro j k
  by_cases hjk : j = k
  · subst k
    simp [pairForce]
  rw [central_force V x j k hjk (hx j k hjk) (hV j k hjk),
    central_force V x k j (Ne.symm hjk) (hx k j (Ne.symm hjk)) (hV k j (Ne.symm hjk)),
    hsymm k j, dist_comm (x j) (x k), ← neg_sub (x k) (x j), smul_neg, neg_neg]

private theorem sum_pairs {N : ℕ} (Fp : Fin N → Fin N → EuclideanSpace ℝ (Fin 3))
    (x : Fin N → EuclideanSpace ℝ (Fin 3))
    (hanti : ∀ j k, Fp j k = -Fp k j) :
    ∑ k, inner ℝ (∑ j, Fp j k) (x k) =
      ∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k), inner ℝ (Fp j k) (x k - x j) := by
  classical
  have hdiag (k : Fin N) : Fp k k = 0 := by
    ext i
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v i) (hanti k k)
    change Fp k k i = -(Fp k k i) at h
    change Fp k k i = 0
    linarith
  let g (j k : Fin N) : ℝ := inner ℝ (Fp j k) (x k)
  have hsplit (j k : Fin N) : g j k =
      (if j < k then g j k else 0) + (if k < j then g j k else 0) := by
    rcases lt_trichotomy j k with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst k; simp [g, hdiag]
    · simp [h, not_lt.mpr h.le]
  have hswap : (∑ k, ∑ j, if k < j then g j k else 0) =
      ∑ k, ∑ j, if j < k then g k j else 0 := by
    exact Finset.sum_comm
  have hpair (j k : Fin N) : g j k + g k j = inner ℝ (Fp j k) (x k - x j) := by
    dsimp [g]
    rw [hanti k j, inner_neg_left, inner_sub_right]
    ring
  calc
    ∑ k, inner ℝ (∑ j, Fp j k) (x k) = ∑ k, ∑ j, g j k := by
      simp only [g, sum_inner]
    _ = ∑ k, ∑ j, ((if j < k then g j k else 0) + (if k < j then g j k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_congr rfl (fun j _ => hsplit j k)
    _ = (∑ k, ∑ j, if j < k then g j k else 0) +
        (∑ k, ∑ j, if k < j then g j k else 0) := by simp only [Finset.sum_add_distrib]
    _ = (∑ k, ∑ j, if j < k then g j k else 0) +
        (∑ k, ∑ j, if j < k then g k j else 0) := by rw [hswap]
    _ = ∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k), inner ℝ (Fp j k) (x k - x j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_add_distrib, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j < k
      · simp only [if_pos h, hpair]
      · simp [h]

theorem solution {N : ℕ} (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space)
    (hsymm : ∀ j k, V j k = V k j)
    (hx : ∀ j k, j ≠ k → x j ≠ x k)
    (hV : ∀ j k, j ≠ k → DifferentiableAt ℝ (V j k) (dist (x k) (x j))) :
    ∑ k, inner ℝ (netPairForce V x k) (x k) =
      -∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k),
        deriv (V j k) (dist (x k) (x j)) * dist (x k) (x j) := by
  change (∑ k, inner ℝ (∑ j, pairForce V x j k) (x k)) = _
  rw [sum_pairs (pairForce V x) x (forces_antisymm V x hsymm hx hV)]
  have hterm (j k : Fin N) (hjk : j < k) :
      inner ℝ (pairForce V x j k) (x k - x j) =
        -(deriv (V j k) (dist (x k) (x j)) * dist (x k) (x j)) := by
    rw [central_force V x j k hjk.ne (hx j k hjk.ne) (hV j k hjk.ne),
      real_inner_smul_left, real_inner_self_eq_norm_sq, dist_eq_norm]
    have hn : ‖x k - x j‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hx j k hjk.ne).symm)
    field_simp
    <;> ring
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j hj
  exact hterm j k (Finset.mem_filter.mp hj).2

