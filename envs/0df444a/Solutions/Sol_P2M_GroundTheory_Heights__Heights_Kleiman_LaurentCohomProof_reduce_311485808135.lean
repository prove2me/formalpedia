-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_reduce_311485808135
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:16.295436+00:00
-- url     : https://prove2.me/submissions/851734e2-db03-4dee-b634-488b32c9827b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_apply_c050aba19709
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_exps_3fdef6a3d557
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_cocy_7d4273effee3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_bdry_c8f9b9260b31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_zero_8c0149e3f6e7

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
theorem _root_.solution (hC : Cech.Cone.Statement.{u, u}) {c : ℤ} {i : ℕ} {z : Cech.Cochain (G S N) i}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i) :
    ∃ w ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i,
      (∀ I, w I ∈ Finsupp.supported S S (bnd c)) ∧
      z - w ∈ Cech.bdryDeg (G S N) (laurentDeg S N c) (ρ S N) i := by
  classical
  let K : Finset (Finset (Fin (N + 1))) := Finset.univ.filter fun J => J ≠ ∅ ∧ J ≠ Finset.univ
  refine ⟨z - ∑ J ∈ K, partC S J i z,
    Submodule.sub_mem _ hz (Submodule.sum_mem _ fun J _ => partC_mem_cocy J hz), fun I => ?_, ?_⟩
  · refine (Finsupp.mem_supported' S _).mpr fun a ha => ?_
    change z I a - (∑ J ∈ K, partC S J i z) I a = 0
    rw [Finset.sum_apply, Finsupp.finsetSum_apply]
    change z I a - ∑ J ∈ K, part S J (z I) a = 0
    simp only [part_apply]
    rw [Finset.sum_ite_eq]
    split_ifs with hK
    · exact sub_self _
    · rw [sub_zero]
      by_contra h'
      have hc := (mem_exps (hz.2 I (Set.mem_univ _)) h').1
      apply ha
      refine ⟨hc, ?_⟩
      by_contra hb
      exact hK (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h0 => hb (Or.inl h0),
        fun h1 => hb (Or.inr h1)⟩)
  · rw [sub_sub_cancel]
    cases i with
    | zero =>
      have h0 : ∑ J ∈ K, partC S J 0 z = 0 := Finset.sum_eq_zero fun J hJ =>
        partC_zero hC (Finset.mem_filter.mp hJ).2.1 (Finset.mem_filter.mp hJ).2.2 hz
      rw [h0]
      exact Submodule.zero_mem _
    | succ i =>
      exact Submodule.sum_mem _ fun J hJ => partC_mem_bdry hC (Finset.mem_filter.mp hJ).2.2 hz
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
