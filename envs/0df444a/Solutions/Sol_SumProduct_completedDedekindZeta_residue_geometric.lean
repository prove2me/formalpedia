-- Prove2me | solution 1 for SumProduct.completedDedekindZeta_residue_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:08:56.876733+00:00
-- url     : https://prove2.me/submissions/8c582fc4-2b4c-44ca-b4e0-c32c32fb7d7c

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
import Theorems.Thm_SumProduct_completedPartialZeta_residue_perIdeal

set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]
open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors
namespace SumProduct
theorem _root_.solution :
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedDedekindZeta K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((Fintype.card (ClassGroup (𝓞 K)) : ℂ) * (surfaceVolume K / (Units.torsionOrder K : ℂ))))
      := by
  classical
  -- `(s-1)·completedDedekindZeta = ∑_c (s-1)·completedPartialZeta (rep c)`.
  have hrw : (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedDedekindZeta K (s : ℂ))
      = (fun s : ℝ => ∑ c : ClassGroup (𝓞 K),
          ((s : ℂ) - 1) * DedekindZeta.completedPartialZeta K (DedekindZeta.idealClassRep K c) (s : ℂ))
      := by
    funext s
    rw [DedekindZeta.completedDedekindZeta, Finset.mul_sum]
  rw [hrw]
  -- Each summand tends to `V/w` (per-ideal residue applied to the representative `≠ 0`).
  have hsummand : ∀ c : ClassGroup (𝓞 K),
      Filter.Tendsto (fun s : ℝ =>
        ((s : ℂ) - 1) * DedekindZeta.completedPartialZeta K (DedekindZeta.idealClassRep K c) (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (surfaceVolume K / (Units.torsionOrder K : ℂ))) := by
    intro c
    refine completedPartialZeta_residue_perIdeal K (DedekindZeta.idealClassRep K c) ?_
    exact mem_nonZeroDivisors_iff_ne_zero.mp (Function.surjInv ClassGroup.mk0_surjective c).2
  have hsum := tendsto_finsetSum (Finset.univ : Finset (ClassGroup (𝓞 K)))
    (fun c _ => hsummand c)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  exact hsum
end SumProduct
