-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_bdry_c8f9b9260b31
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:17.337919+00:00
-- url     : https://prove2.me/submissions/98464357-ff46-44ed-9de8-a19c1cf46bb1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_mem_w_99de7a96f87b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_eq_zero_5c5c6203c57c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_deg_of_w_5673bc6b73c7
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
theorem _root_.solution (hC : Cech.Cone.Statement.{u, u}) {c : ℤ} {i : ℕ}
    {J : Finset (Fin (N + 1))} (hJ : J ≠ Finset.univ) {z : Cech.Cochain (G S N) (i + 1)}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) (i + 1)) :
    partC S J (i + 1) z ∈ Cech.bdryDeg (G S N) (laurentDeg S N c) (ρ S N) (i + 1) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_iff_forall.mpr fun x => by by_contra hx; exact h ⟨x, hx⟩)
  have hzI : ∀ I, z I ∈ laurentDeg S N c I.1 := fun I => hz.2 I (Set.mem_univ _)
  obtain ⟨y, hyW, hy0, hyd⟩ := (hC S (Laurent S N) N J).1 (wPart S N c J) i₀ hi₀ i (partC S J (i + 1) z)
    (by rw [partC_d, LinearMap.mem_ker.mp hz.1, map_zero]) (fun I => part_mem_w (hzI I))
    (fun I h => part_eq_zero (hzI I) h)
  exact Submodule.mem_map.mpr ⟨y, fun I _ => mem_deg_of_w (hyW I) (hy0 I), hyd⟩
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
