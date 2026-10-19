-- Prove2me | solution 1 for SpherePacking.CohnElkies.real_lattice_sum_bounded_by_origin_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/4981c7cb-e52d-43b8-8475-11fd4d12e7a9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_CohnElkies_LPBoundSummability_summable_lattice_shift_real_parts

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
namespace SpherePacking.CohnElkies
theorem _root_.solution (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x y : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ite (x = y) (f 0).re 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  have hsum :
      Summable (fun ℓ : P.lattice =>
        (f ((x : E) - (y : E) + (ℓ : E))).re) :=
    SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_shift_real_parts
      (Λ := P.lattice) (f := f) ((x : E) - (y : E))
  have hnonpos (ℓ : P.lattice)
      (hne : (ℓ : E) + (x : E) ≠ (y : E)) :
      (f ((x : E) - (y : E) + (ℓ : E))).re ≤ 0 := by
    have hcenter : (ℓ : E) + (x : E) ∈ P.centers :=
      P.lattice_action ℓ.property x.property.1
    have hdist : 1 ≤ dist ((ℓ : E) + (x : E)) (y : E) := by
      rw [← hP]
      exact P.toSpherePacking.distinct_centers_separation_bound
        ((ℓ : E) + (x : E)) (y : E) hcenter y.property.1 hne
    apply hCohnElkies₁
    simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hdist
  by_cases hxy : x = y
  · subst y
    simp only []
    have hmajor :
        Summable (fun ℓ : P.lattice =>
          if ℓ = 0 then (f 0).re else 0) := by
      apply summable_of_ne_finset_zero (s := {0})
      intro ℓ hℓ
      have hne : ℓ ≠ 0 := by
        intro hzero
        exact hℓ (by simp [hzero])
      simp [hne]
    calc
      (∑' ℓ : P.lattice,
        (f ((x : E) - (x : E) + (ℓ : E))).re)
          ≤ ∑' ℓ : P.lattice, if ℓ = 0 then (f 0).re else 0 := by
            apply Summable.tsum_le_tsum (hf := hsum) (hg := hmajor)
            intro ℓ
            by_cases hℓ : ℓ = 0
            · simp [hℓ]
            · simp only [if_neg hℓ]
              apply hnonpos ℓ
              intro heq
              apply hℓ
              apply Subtype.ext
              have hz := congrArg (fun z : E => z - (x : E)) heq
              simpa using hz
      _ = (f 0).re := by simp
  · simp only [if_neg hxy]
    have hterms (ℓ : P.lattice) :
        (f ((x : E) - (y : E) + (ℓ : E))).re ≤ 0 := by
      apply hnonpos ℓ
      intro heq
      have hℓD : ℓ +ᵥ (x : E) ∈ D := by
        change (ℓ : E) + (x : E) ∈ D
        rw [heq]
        exact y.property.2
      have hzeroD : (0 : P.lattice) +ᵥ (x : E) ∈ D := by
        simpa using x.property.2
      have hℓ : ℓ = (0 : P.lattice) :=
        (hD_unique_covers (x : E)).unique hℓD hzeroD
      apply hxy
      apply Subtype.ext
      simpa [hℓ] using heq
    simpa using
      (Summable.tsum_le_tsum hterms hsum
        (summable_zero : Summable (fun _ : P.lattice => (0 : ℝ))))
end SpherePacking.CohnElkies
