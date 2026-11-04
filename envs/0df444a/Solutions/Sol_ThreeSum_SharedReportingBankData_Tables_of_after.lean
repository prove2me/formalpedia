-- Prove2me | solution 1 for ThreeSum.SharedReportingBankData.Tables.of_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:03:16.3882+00:00
-- url     : https://prove2.me/submissions/56192ad3-9a40-4658-8505-d340c30e629a

import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Theorems.Thm_ThreeSum_ReportingHostQueryBounds_boxStored_of_on
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankData
open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1500000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankData
namespace Tables
theorem _root_.solution {h J k low : ℕ} {μ ν : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Tables μ D hk f g)
    (heq : ∀ a, low ≤ a → ν a=μ a)
    (hindex : low ≤ D.indexBase) (hptr : low ≤ D.ptrBase) (hbox : low ≤ D.boxBase) :
    Tables ν D hk f g := by
  obtain ⟨S,hs,hperm,hsort⟩ := H.index
  refine ⟨⟨S,?_,hperm,hsort⟩,?_,?_⟩
  · intro i hi
    exact (heq _ (by omega)).trans (hs i hi)
  · intro i hi
    exact (heq _ (by omega)).trans (H.pointers i hi)
  · intro i hi
    exact ReportingHostQueryBounds.boxStored_of_on (H.boxes i hi)
      (by intro a ha _; exact heq a (by omega))
end Tables
end ThreeSum.SharedReportingBankData
