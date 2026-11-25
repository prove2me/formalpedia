-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_zero_8c0149e3f6e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:16.957613+00:00
-- url     : https://prove2.me/submissions/a37a1337-6b4c-4c3f-b2c4-3cffa25a791b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_eq_zero_5c5c6203c57c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_d_b9ed291a3cb0

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
theorem _root_.solution (hC : Cech.Cone.Statement.{u, u}) {c : ℤ} {J : Finset (Fin (N + 1))}
    (hJ0 : J ≠ ∅) (hJ : J ≠ Finset.univ) {z : Cech.Cochain (G S N) 0}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) 0) : partC S J 0 z = 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_iff_forall.mpr fun x => by by_contra hx; exact h ⟨x, hx⟩)
  exact (hC S (Laurent S N) N J).2.1 (Finset.nonempty_iff_ne_empty.mpr hJ0) i₀ hi₀ _
    (by rw [partC_d, LinearMap.mem_ker.mp hz.1, map_zero])
    (fun I h => part_eq_zero (hz.2 I (Set.mem_univ _)) h)
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
