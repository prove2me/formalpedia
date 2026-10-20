-- Prove2me | solution 2 for SpherePacking.CohnElkies.real_lattice_sum_bounded_by_origin_term
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:02:46.116036+00:00
-- url     : https://prove2.me/submissions/54a673c3-b495-4686-96c3-eac50e4e7237

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators SchwartzMap
open SpherePacking SpherePacking.CohnElkies
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
variable {P : PeriodicSpherePacking d}
variable {D : Set (EuclideanSpace ℝ (Fin d))}
theorem h48_summable_re (Q : PeriodicSpherePacking d) (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (z : EuclideanSpace ℝ (Fin d)) :
    Summable (fun ℓ : Q.lattice => (g (z + (ℓ : EuclideanSpace ℝ (Fin d)))).re) := by
  set k : ℕ := Module.finrank ℤ Q.lattice + 1 with hk
  obtain ⟨C, hCpos, hC⟩ := g.decay k 0
  have hC' : ∀ w : EuclideanSpace ℝ (Fin d), ‖w‖ ^ k * ‖g w‖ ≤ C := by
    simpa [norm_iteratedFDeriv_zero] using hC
  have hsum := ZLattice.summable_norm_sub_inv_pow Q.lattice k (by omega) (-z)
  refine Summable.of_norm_bounded_eventually (hsum.mul_left C) ?_
  have hfin : ({ℓ : Q.lattice | z + (ℓ : EuclideanSpace ℝ (Fin d)) = 0} : Set Q.lattice).Finite := by
    apply Set.Subsingleton.finite
    intro a ha b hb
    apply Subtype.ext
    have h1 : (a : EuclideanSpace ℝ (Fin d)) = -z := by
      exact eq_neg_of_add_eq_zero_right ha
    have h2 : (b : EuclideanSpace ℝ (Fin d)) = -z := by
      exact eq_neg_of_add_eq_zero_right hb
    rw [h1, h2]
  filter_upwards [hfin.eventually_cofinite_notMem] with ℓ hℓ
  replace hℓ : z + (ℓ : EuclideanSpace ℝ (Fin d)) ≠ 0 := hℓ
  have hpos : 0 < ‖z + (ℓ : EuclideanSpace ℝ (Fin d))‖ := norm_pos_iff.mpr hℓ
  have heq : ‖(ℓ : EuclideanSpace ℝ (Fin d)) - -z‖ = ‖z + (ℓ : EuclideanSpace ℝ (Fin d))‖ := by
    rw [sub_neg_eq_add, add_comm]
  rw [heq, Real.norm_eq_abs, inv_pow]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos _), mul_comm]
  exact hC' _

theorem solution (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x y : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ite (x = y) (f 0).re 0 := by
  have hsum := h48_summable_re P f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))
  have hkey : ∀ ℓ : P.lattice, ¬ (x = y ∧ ℓ = 0) →
      1 ≤ ‖(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
        (ℓ : EuclideanSpace ℝ (Fin d))‖ := by
    intro ℓ hne
    have hc : -(ℓ : EuclideanSpace ℝ (Fin d)) + (y : EuclideanSpace ℝ (Fin d)) ∈ P.centers :=
      P.lattice_action (P.lattice.neg_mem ℓ.2) y.2.1
    have hrw : (x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
        (ℓ : EuclideanSpace ℝ (Fin d)) =
        (x : EuclideanSpace ℝ (Fin d)) - (-(ℓ : EuclideanSpace ℝ (Fin d)) + (y : EuclideanSpace ℝ (Fin d))) := by
      abel
    by_cases hxe : (x : EuclideanSpace ℝ (Fin d)) = -(ℓ : EuclideanSpace ℝ (Fin d)) + (y : EuclideanSpace ℝ (Fin d))
    · exfalso
      apply hne
      have hy : (y : EuclideanSpace ℝ (Fin d)) = (ℓ : EuclideanSpace ℝ (Fin d)) + x := by
        rw [hxe]; abel
      obtain ⟨g0, _, huniq⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
      have h0 : (0 : P.lattice) = g0 := huniq 0 (by
        simpa [Submodule.vadd_def, vadd_eq_add] using x.2.2)
      have hl : ℓ = g0 := huniq ℓ (by
        simp only [Submodule.vadd_def, vadd_eq_add]
        rw [← hy]; exact y.2.2)
      have hl0 : ℓ = 0 := hl.trans h0.symm
      refine ⟨?_, hl0⟩
      apply Subtype.ext
      rw [hy, hl0]; simp
    · have := P.distinct_centers_separation_bound _ _ x.2.1 hc hxe
      rw [hP, dist_eq_norm] at this
      rw [hrw]; exact this
  have hnp : ∀ ℓ : P.lattice, ¬ (x = y ∧ ℓ = 0) →
      (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
        (ℓ : EuclideanSpace ℝ (Fin d)))).re ≤ 0 :=
    fun ℓ h => hCohnElkies₁ _ (hkey ℓ h)
  split_ifs with hxy
  · rw [hsum.tsum_eq_add_tsum_ite 0]
    have h1 : (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
        ((0 : P.lattice) : EuclideanSpace ℝ (Fin d)))).re = (f 0).re := by
      rw [hxy]; simp
    rw [h1]
    have h2 : (∑' ℓ : P.lattice, if ℓ = 0 then (0 : ℝ) else
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re) ≤ 0 := by
      apply tsum_nonpos
      intro ℓ
      split_ifs with hl
      · exact le_rfl
      · exact hnp ℓ (fun h => hl h.2)
    linarith
  · exact tsum_nonpos (fun ℓ => hnp ℓ (fun h => hxy h.1))

