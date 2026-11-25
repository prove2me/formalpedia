-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_sum_rpow_neg_le_pow_add2b3ef4a0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:38.136241+00:00
-- url     : https://prove2.me/submissions/1993a607-c838-496c-9093-c948cc0ae926

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prod_tuple_1b1f6df7d3f6
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_tuple_injOn_e0a8cda4a4ec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid
noncomputable section
open GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
theorem _root_.solution (T : Finset (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) ≤ (∑' m : ℕ, (m : ℝ) ^ (-s)) ^ Module.finrank ℚ K := by
  classical
  set g : ℕ → ℝ := fun m => (m : ℝ) ^ (-s) with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => by positivity
  have hsum : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  have hgz : g 0 = 0 := by simp [hg, Real.zero_rpow (by linarith : -s ≠ 0)]
  set T' := T.filter (· ≠ ⊥)
  have e1 : ∑ I ∈ T, g (absNorm I) = ∑ I ∈ T', g (absNorm I) := by
    refine (Finset.sum_filter_of_ne fun I _ hne => ?_).symm
    rintro rfl
    exact hne (by simp [hgz])
  have e2 : ∑ I ∈ T', g (absNorm I) = ∑ I ∈ T', ∏ j, g (tuple K I j) := by
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [← prod_tuple (Finset.mem_filter.mp hI).2]
    simp only [hg, Nat.cast_prod]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  have e3 : ∑ I ∈ T', ∏ j, g (tuple K I j) = ∑ t ∈ T'.image (tuple K), ∏ j, g (t j) := by
    rw [Finset.sum_image]
    intro I hI J hJ h
    exact tuple_injOn (Finset.mem_filter.mp hI).2 (Finset.mem_filter.mp hJ).2 h
  set M := ∑ t ∈ T'.image (tuple K), ∑ j, t j + 1
  have hsub : T'.image (tuple K) ⊆ Fintype.piFinset fun _ => Finset.range M := by
    intro t ht
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    have h1 : t j ≤ ∑ j, t j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : ∑ j, t j ≤ ∑ t ∈ T'.image (tuple K), ∑ j, t j :=
      Finset.single_le_sum (f := fun t : Fin (Module.finrank ℚ K) → ℕ => ∑ j, t j)
        (fun _ _ => Nat.zero_le _) ht
    omega
  calc ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) = ∑ I ∈ T, g (absNorm I) := rfl
    _ = ∑ t ∈ T'.image (tuple K), ∏ j, g (t j) := by rw [e1, e2, e3]
    _ ≤ ∑ t ∈ Fintype.piFinset (fun _ => Finset.range M), ∏ j, g (t j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.prod_nonneg fun _ _ => hg0 _)
    _ = (∑ m ∈ Finset.range M, g m) ^ Module.finrank ℚ K := (Finset.sum_pow' _ _ _).symm
    _ ≤ (∑' m, g m) ^ Module.finrank ℚ K :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hg0 _)
          (hsum.sum_le_tsum _ fun _ _ => hg0 _) _
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
