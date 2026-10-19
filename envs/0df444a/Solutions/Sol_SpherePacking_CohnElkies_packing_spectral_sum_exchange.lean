-- Prove2me | solution 1 for SpherePacking.CohnElkies.packing_spectral_sum_exchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/ebd49445-a3cd-444f-b7c0-ac1adc3a616b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_CohnElkies_LPBoundAux_summable_norm_on_translated_integral_lattice

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform SchwartzMap Real
open Complex MeasureTheory
open SpherePacking SpherePacking.CohnElkies
variable {d : ℕ}
namespace SpherePacking.CohnElkies
theorem _root_.solution (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (((𝓕 f) x).re : ℂ) = (𝓕 f) x)
    (P : PeriodicSpherePacking d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D) (hd : 0 < d) :
    (∑' x : ↑(P.centers ∩ D),
        ∑' y : ↑(P.centers ∩ D),
          (1 / ZLattice.covolume P.lattice volume) *
            ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
              (𝓕 f m) *
                exp (2 * π * I *
                  ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re
      =
      ((1 / ZLattice.covolume P.lattice volume) *
          ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            (𝓕 f m).re *
              (∑' x : ↑(P.centers ∩ D),
                ∑' y : ↑(P.centers ∩ D),
                  exp (2 * π * I *
                    ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                      (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
  classical
  letI := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  have hFourierNorm :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa using
      (LPBoundAux.summable_norm_on_translated_integral_lattice
        (SchwartzMap.polarIntegerLattice (d := d) P.lattice) (𝓕 f)
        (0 : EuclideanSpace ℝ (Fin d)))
  have hWeighted (x y : ↑(P.centers ∩ D)) :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        (𝓕 f m) * exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
    apply Summable.of_norm
    simpa [norm_mul, Complex.norm_exp, Complex.mul_re, mul_assoc] using hFourierNorm
  have hSwap
      (g : ↑(P.centers ∩ D) →
        SchwartzMap.polarIntegerLattice (d := d) P.lattice → ℂ)
      (hg : ∀ x, Summable (g x)) :
      Summable (fun m => ∑ x : ↑(P.centers ∩ D), g x m) ∧
        (∑ x : ↑(P.centers ∩ D), ∑' m, g x m) =
          ∑' m, ∑ x : ↑(P.centers ∩ D), g x m := by
    have hAux (s : Finset ↑(P.centers ∩ D)) :
        Summable (fun m => ∑ x ∈ s, g x m) ∧
          (∑ x ∈ s, ∑' m, g x m) = ∑' m, ∑ x ∈ s, g x m := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert x s hx ih =>
        constructor
        · simpa [hx] using (hg x).add ih.1
        · simpa [hx, ih.2] using ((hg x).tsum_add ih.1).symm
    simpa using hAux Finset.univ
  let c : ℂ := 1 / ZLattice.covolume P.lattice volume
  have hInner (x : ↑(P.centers ∩ D)) :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ∑ y : ↑(P.centers ∩ D),
          (𝓕 f m) * exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ∧
      (∑ y : ↑(P.centers ∩ D),
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          (𝓕 f m) * exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) =
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          ∑ y : ↑(P.centers ∩ D),
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
    exact hSwap
      (fun y m => (𝓕 f m) * exp (2 * π * I *
        ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
      (hWeighted x)
  have hOuter :
      (∑ x : ↑(P.centers ∩ D),
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          ∑ y : ↑(P.centers ∩ D),
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) =
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          ∑ x : ↑(P.centers ∩ D),
            ∑ y : ↑(P.centers ∩ D),
              (𝓕 f m) * exp (2 * π * I *
                ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
    exact (hSwap
      (fun x m => ∑ y : ↑(P.centers ∩ D),
        (𝓕 f m) * exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
      (fun x => (hInner x).1)).2
  have hExchange :
      (∑ x : ↑(P.centers ∩ D),
        ∑ y : ↑(P.centers ∩ D),
          c * ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) =
        c * ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          (𝓕 f m) *
            (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
    calc
      _ = c * ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
          ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
        simp [Finset.mul_sum]
      _ = c * ∑ x : ↑(P.centers ∩ D),
          ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            ∑ y : ↑(P.centers ∩ D),
              (𝓕 f m) * exp (2 * π * I *
                ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
        congr 1
        exact Finset.sum_congr rfl (fun x _ => (hInner x).2)
      _ = c * ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) :=
        congrArg (fun z : ℂ => c * z) hOuter
      _ = _ := by
        congr 1
        apply tsum_congr
        intro m
        simp [Finset.mul_sum, mul_assoc]
  have hRealCoeff (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      (((𝓕 f m).re : ℝ) : ℂ) = 𝓕 f m :=
    hRealFourier (m : EuclideanSpace ℝ (Fin d))
  simpa [tsum_fintype, c, hRealCoeff] using congrArg Complex.re hExchange
end SpherePacking.CohnElkies
