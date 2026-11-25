-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_span_coe_submodule_a526c011a29f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:25:33.296883+00:00
-- url     : https://prove2.me/submissions/ca89de9b-f23b-4fc3-8252-800f2e307184

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefExtendIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_mem_chartRing_iff_e71779db8a8e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
theorem _root_.solution (hφ : Function.Bijective (algebraMap S F)) (I : Kleiman.Chart x)
    (M : Submodule (Kleiman.chartRing S x I) Ω) :
    ((Submodule.span (Kleiman.chartRing F x I) (M : Set Ω) : Submodule _ Ω) : Set Ω) = M := by
  apply le_antisymm
  · intro z hz
    refine Submodule.span_induction (p := fun z _ => z ∈ M) (fun y hy => hy) M.zero_mem
      (fun _ _ _ _ ha hb => M.add_mem ha hb) ?_ hz
    intro a z _ hz
    have : a • z = (⟨(a : Ω), (mem_chartRing_iff hφ).mp a.2⟩ : Kleiman.chartRing S x I) • z := by
      rw [Kleiman.chartRing_smul_def, Kleiman.chartRing_smul_def]
    rw [this]
    exact M.smul_mem _ hz
  · exact Submodule.subset_span
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
