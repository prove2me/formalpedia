-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_bnd_finite_04cd16ef5319
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:01:48.384867+00:00
-- url     : https://prove2.me/submissions/8ab8a154-5e77-4164-9951-61fa16552cbb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_negSet_131f8e45df3d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
theorem _root_.solution (c : ℤ) : (bnd (N := N) c).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin (N + 1) => Set.Icc (-|c|) |c|)
    fun _ => Set.finite_Icc _ _).subset ?_
  rintro a ⟨hc, h | h⟩ j -
  · have hnn : ∀ k ∈ Finset.univ, 0 ≤ a k := fun k _ => by
      by_contra hk
      have : k ∈ negSet a := mem_negSet.mpr (by omega)
      rw [h] at this
      exact Finset.notMem_empty _ this
    have h1 := Finset.single_le_sum hnn (Finset.mem_univ j)
    rw [hc] at h1
    have := hnn j (Finset.mem_univ j)
    exact ⟨by linarith [abs_nonneg c], h1.trans (le_abs_self c)⟩
  · have hng : ∀ k ∈ Finset.univ, 0 ≤ -a k := fun k _ => by
      have := mem_negSet.mp (h ▸ Finset.mem_univ k)
      omega
    have h1 := Finset.single_le_sum hng (Finset.mem_univ j)
    rw [Finset.sum_neg_distrib, hc] at h1
    have := mem_negSet.mp (h ▸ Finset.mem_univ j)
    exact ⟨by linarith [neg_abs_le c], by linarith [abs_nonneg c]⟩
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
