-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_d_liftCochain_83e6b3accbc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:16.326559+00:00
-- url     : https://prove2.me/submissions/a8f4932d-3470-4981-8b73-e3a8d35cdfc3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_d_sub_61e0f8775efc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_liftTilde_362ee858b2e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_liftCochain_of_93b1acc26c11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_d_a1b4827e5d39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_injective_e55cadb52ac8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locModE_subsingleton_579608ddf9fc


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
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) (i + 1))
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res (i + 1) t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS (i + 1) (liftCochain M c t) = 0 := by
  funext K
  change _ = 0
  by_cases hK : K.1.1 ⊆ support x
  · apply locConeE_injective M K.1.1 hK
    rw [locConeE_d M (liftCochain M c t) K hK, map_zero]
    have h0 := coe_d_sub (M.tildeSys c) t ⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩
    rw [ht] at h0
    calc ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
          ((Cech.face_subset K j).trans hK) (liftCochain M c t (Cech.face K j))
        = ∑ j : K.1.1, Cech.sgn K.1.1 j • singleE S x E c
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (i + 1 + 1)) j) : E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [liftCochain_of M c t _ ((Cech.face_subset K j).trans hK)]
          congr 1
          exact locConeE_liftTilde M c _ _ _
      _ = singleE S x E c (∑ j : K.1.1, Cech.sgn K.1.1 j •
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (i + 1 + 1)) j) : E)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul]
      _ = 0 := by
          rw [← h0]
          exact map_zero _
  · haveI := locModE_subsingleton (S := S) M (Finset.not_subset.mp hK).choose_spec.1
      (by simpa [mem_support] using (Finset.not_subset.mp hK).choose_spec.2)
    exact Subsingleton.elim _ _
end GroundTheory.Heights₂.Heights.Kleiman
