-- Prove2me | solution 1 for ThreeSum.SharedReportingBankData.Tables.reporting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:02:53.490126+00:00
-- url     : https://prove2.me/submissions/cf4c9e4a-051d-44a3-ae55-6c5cb3b288fd

import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_SharedReportingBankData

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankData
open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1500000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankData
namespace Tables
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalEncoding.GlobalOutput h J)
    (H : Tables μ D hk (BlockIndexedQuery.leftSource p B b q)
      (BlockIndexedQuery.rightSource p shift C c q)) :
    ReportingHostLevelData.Stored μ D hk p shift B C b c q :=
  ⟨H.index,H.pointers,H.boxes⟩
end Tables
end ThreeSum.SharedReportingBankData
