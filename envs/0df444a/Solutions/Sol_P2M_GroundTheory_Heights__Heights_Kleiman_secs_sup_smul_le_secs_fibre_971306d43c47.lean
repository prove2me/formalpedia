-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_secs_sup_smul_le_secs_fibre_971306d43c47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:43:34.264576+00:00
-- url     : https://prove2.me/submissions/c3fbe542-4d54-4ded-bc73-39a5d8757383

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreRestrKer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_iff_forall_sub_69edc3c1eb74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_idealMod_0664d1e72b9b

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
open MvPolynomial Filter
open scoped Pointwise nonZeroDivisors
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (Q : SubSystem S x Ω) (qq : Ideal (Poly S N)) (𝔪 : Ideal S) :
    (Q.twist (idealSys x qq)).secs ⊔ 𝔪 • Q.secs ≤
      (Q.twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).secs := by
  refine sup_le (fun y hy => ?_) (Submodule.smul_le.mpr fun a ha y hy => ?_)
  · rw [mem_secs_iff_forall_sub] at hy ⊢
    intro I
    have := hy I
    rw [SubSystem.twist_sub_eq_mul_of_line] at this ⊢
    exact Submodule.mul_le.mpr (fun a ha b hb =>
      Submodule.mul_mem_mul (idealMod_le_idealMod le_sup_left I ha) hb) this
  · rw [mem_secs_iff_forall_sub] at hy ⊢
    intro I
    rw [SubSystem.twist_sub_eq_mul_of_line, Algebra.smul_def]
    refine Submodule.mul_mem_mul (Submodule.subset_span ⟨C a, 1, 0, Ideal.mem_sup_right
      (Ideal.mem_map_of_mem _ ha), one_mem _, isHomogeneous_C _ _, isHomogeneous_one _ _, by simp⟩) (hy I)
end GroundTheory.Heights₂.Heights.Kleiman
