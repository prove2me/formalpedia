-- Prove2me | solution 1 for SoficGroups.KunCompletedComponentMidrankVariation.normalized_permutationRealVariation_tendsto_zero_of_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/5a4a2043-43bb-434d-90f9-89073f6667cc

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_permutationRealVariation_sq_le_card_mul_energy

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedComponentMidrankVariation
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunCompletedComponentMidrankVariation
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (ι : Type*) [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (f : (n : ℕ) → V n → ℝ)
    (henergy : Tendsto
      (fun n =>
        (∑ i : ι, ∑ x : V n,
          (f n (σ n i x) - f n x) ^ 2) /
            (Fintype.card (V n) : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        permutationRealVariation (σ n) (f n) /
          (Fintype.card (V n) : ℝ))
      atTop (nhds 0) := by
  have hN (n : ℕ) : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hupper (n : ℕ) :
      permutationRealVariation (σ n) (f n) /
          (Fintype.card (V n) : ℝ) ≤
        Real.sqrt
          ((Fintype.card ι : ℝ) *
            ((∑ i : ι, ∑ x : V n,
              (f n (σ n i x) - f n x) ^ 2) /
                (Fintype.card (V n) : ℝ))) := by
    apply Real.le_sqrt_of_sq_le
    calc
      (permutationRealVariation (σ n) (f n) /
        (Fintype.card (V n) : ℝ)) ^ 2 =
          permutationRealVariation (σ n) (f n) ^ 2 /
            (Fintype.card (V n) : ℝ) ^ 2 := by
              ring
      _ ≤
          (((Fintype.card ι : ℝ) * Fintype.card (V n)) *
            (∑ i : ι, ∑ x : V n,
              (f n (σ n i x) - f n x) ^ 2)) /
            (Fintype.card (V n) : ℝ) ^ 2 := by
              exact div_le_div_of_nonneg_right
                (permutationRealVariation_sq_le_card_mul_energy
                  (σ n) (f n))
                (sq_nonneg (Fintype.card (V n) : ℝ))
      _ = (Fintype.card ι : ℝ) *
          ((∑ i : ι, ∑ x : V n,
            (f n (σ n i x) - f n x) ^ 2) /
              (Fintype.card (V n) : ℝ)) := by
            field_simp [ne_of_gt (hN n)]
  have hroot : Tendsto
      (fun n =>
        Real.sqrt
          ((Fintype.card ι : ℝ) *
            ((∑ i : ι, ∑ x : V n,
              (f n (σ n i x) - f n x) ^ 2) /
                (Fintype.card (V n) : ℝ))))
      atTop (nhds 0) := by
    have hscaled : Tendsto
        (fun n =>
          (Fintype.card ι : ℝ) *
            ((∑ i : ι, ∑ x : V n,
              (f n (σ n i x) - f n x) ^ 2) /
                (Fintype.card (V n) : ℝ)))
        atTop (nhds 0) := by
      simpa using henergy.const_mul (Fintype.card ι : ℝ)
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hscaled
  apply squeeze_zero'
    (Eventually.of_forall (fun n => ?_))
    (Eventually.of_forall hupper)
    hroot
  apply div_nonneg _ (hN n).le
  unfold permutationRealVariation
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
end SoficGroups.KunCompletedComponentMidrankVariation
