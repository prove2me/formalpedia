-- Prove2me | solution 1 for SpherePacking.CohnElkies.center_double_sum_eq_region_lattice_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/95e22886-51f3-46b6-8179-8ad8a3d66f70

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_CohnElkies_LPBoundSummability_summable_lattice_shift_real_parts

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open SpherePacking SpherePacking.CohnElkies
noncomputable section
open scoped BigOperators SchwartzMap
variable {d : ℕ}
namespace SpherePacking.CohnElkies
theorem _root_.solution
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re =
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
  classical
  letI : Fintype ↑(P.centers ∩ D) :=
    @Fintype.ofFinite _
      (finite_centers_in_bounded_region P D hD_isBounded hd)
  let e := fundamentalCentersLatticeProductEquiv P hD_unique_covers
  have hs (x y : ↑(P.centers ∩ D)) :
      Summable (fun ℓ : P.lattice =>
        (f ((x : EuclideanSpace ℝ (Fin d)) -
          (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re) :=
    LPBoundSummability.summable_lattice_shift_real_parts
      (Λ := P.lattice) f
      ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))
  have hswap (x : ↑(P.centers ∩ D)) :
      Summable (fun ℓ : P.lattice => ∑' y : ↑(P.centers ∩ D),
        (f ((x : EuclideanSpace ℝ (Fin d)) -
          (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re) ∧
      (∑' ℓ : P.lattice, ∑' y : ↑(P.centers ∩ D),
        (f ((x : EuclideanSpace ℝ (Fin d)) -
          (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re) =
        ∑' y : ↑(P.centers ∩ D), ∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) -
            (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
    have haux (s : Finset ↑(P.centers ∩ D)) :
        Summable (fun ℓ : P.lattice => ∑ y ∈ s,
          (f ((x : EuclideanSpace ℝ (Fin d)) -
            (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re) ∧
        (∑' ℓ : P.lattice, ∑ y ∈ s,
          (f ((x : EuclideanSpace ℝ (Fin d)) -
            (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re) =
          ∑ y ∈ s, ∑' ℓ : P.lattice,
            (f ((x : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)) +
              (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert y s hy ih =>
        constructor
        · simpa [hy] using (hs x y).add ih.1
        · simpa [hy, ih.2] using (hs x y).tsum_add ih.1
    constructor
    · simpa [tsum_fintype] using (haux Finset.univ).1
    · simpa [tsum_fintype] using (haux Finset.univ).2
  calc
    _ = ∑' z : ↑(P.centers ∩ D) × P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f (((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) +
              (z.1 : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)))).re := by
      simpa [e, fundamentalCentersLatticeProductEquiv] using
        (e.tsum_eq (f := fun x : P.centers =>
          ∑' y : ↑(P.centers ∩ D),
            (f ((x : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)))).re)).symm
    _ = ∑' x : ↑(P.centers ∩ D), ∑' ℓ : P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f ((x : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)) +
              (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
      let ep :
          (Σ _ : ↑(P.centers ∩ D), P.lattice) ≃
            (↑(P.centers ∩ D) × P.lattice) :=
        Equiv.sigmaEquivProd _ _
      have htotal :
          Summable (fun z : Σ _ : ↑(P.centers ∩ D), P.lattice =>
            ∑' y : ↑(P.centers ∩ D),
              (f ((z.1 : EuclideanSpace ℝ (Fin d)) -
                (y : EuclideanSpace ℝ (Fin d)) +
                ((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)))).re) := by
        let G : (Σ _ : ↑(P.centers ∩ D), P.lattice) → ℝ := fun z =>
          ∑' y : ↑(P.centers ∩ D),
            (f ((z.1 : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)) +
              ((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)))).re
        change Summable G
        have hind (x : ↑(P.centers ∩ D)) :
            Summable
              (({z : Σ _ : ↑(P.centers ∩ D), P.lattice | z.1 = x}).indicator G) := by
          let ex : P.lattice ≃
              {z : Σ _ : ↑(P.centers ∩ D), P.lattice | z.1 = x} :=
            { toFun := fun ℓ => ⟨⟨x, ℓ⟩, rfl⟩
              invFun := fun z => z.val.2
              left_inv := fun _ => rfl
              right_inv := by
                intro z
                apply Subtype.ext
                cases z with
                | mk z hz =>
                  cases z with
                  | mk x' ℓ =>
                    cases hz
                    rfl }
          apply summable_subtype_iff_indicator.mp
          apply (ex.summable_iff).mp
          simpa [G, ex, Function.comp_def] using (hswap x).1
        have hall := summable_sum (s := Finset.univ) (fun x _ => hind x)
        simpa [Set.indicator, eq_comm] using hall
      calc
        _ = ∑' z : Σ _ : ↑(P.centers ∩ D), P.lattice,
              ∑' y : ↑(P.centers ∩ D),
                (f (((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) +
                  (z.1 : EuclideanSpace ℝ (Fin d)) -
                  (y : EuclideanSpace ℝ (Fin d)))).re := by
          simpa [ep] using
            (ep.tsum_eq (f := fun z : ↑(P.centers ∩ D) × P.lattice =>
              ∑' y : ↑(P.centers ∩ D),
                (f (((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) +
                  (z.1 : EuclideanSpace ℝ (Fin d)) -
                  (y : EuclideanSpace ℝ (Fin d)))).re)).symm
        _ = ∑' z : Σ _ : ↑(P.centers ∩ D), P.lattice,
              ∑' y : ↑(P.centers ∩ D),
                (f ((z.1 : EuclideanSpace ℝ (Fin d)) -
                  (y : EuclideanSpace ℝ (Fin d)) +
                  ((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)))).re := by
          apply tsum_congr
          intro z
          apply tsum_congr
          intro y
          congr 2
          abel
        _ = _ :=
          Summable.tsum_sigma' (fun x => (hswap x).1) htotal
    _ = _ := by
      apply tsum_congr
      intro x
      exact (hswap x).2
end SpherePacking.CohnElkies
