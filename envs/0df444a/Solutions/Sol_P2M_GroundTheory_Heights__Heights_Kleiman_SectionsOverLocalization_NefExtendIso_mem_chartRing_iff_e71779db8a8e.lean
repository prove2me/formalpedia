-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_mem_chartRing_iff_e71779db8a8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:10.505638+00:00
-- url     : https://prove2.me/submissions/203990d7-76b1-4a47-af50-af3ea801e099

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefExtendIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_mem_monos_hom_1d615dc0e8cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_pre_2d52bc105c55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_extend_09d18153b28b


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
theorem _root_.solution (hφ : Function.Bijective (algebraMap S F)) {I : Kleiman.Chart x} {a : Ω} :
    a ∈ Kleiman.chartRing F x I ↔ a ∈ Kleiman.chartRing S x I := by
  constructor
  · rintro ⟨f, s, e, hs, hf, hse, rfl⟩
    let g : F →+* S := (RingEquiv.ofBijective _ hφ).symm
    refine ⟨map g f, map g s, e, map_mem_monos_hom g hs, hf.map g, hse.map g, ?_⟩
    rw [← aeval_map_algebraMap F x (map g f), ← aeval_map_algebraMap F x (map g s), map_pre hφ,
      map_pre hφ]
  · exact Kleiman.mem_chartRing_extend
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
