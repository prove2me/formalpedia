-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.source_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:19:06.103677+00:00
-- url     : https://prove2.me/submissions/27537cdb-8ac5-4421-83fb-9a63d9806384

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords
namespace ThreeSum.SharedReportingBankSources
theorem _root_.solution {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {base NB NC g h J cut occ i j s : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fB fC base NB NC g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NB NC g) (hj : j < SourceBandPairSlices.count NB NC g)
    (hs : s < LightBlockSourceCatalog.count h J) :
    μ (leftCell base h J cut i s)=(leftBase base h J cut i s : ℤ) ∧
      μ (rightCell base h J cut j s)=(rightBase base h J cut j s : ℤ) ∧
      LightZetaStages.StoredThrough μ (leftBase base h J cut i s) cut
        (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
          (representative h J s)) (J*(512*h)) ∧
      LightZetaStages.StoredThrough μ (rightBase base h J cut j s) cut
        (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
          (representative h J s)) (J*(512*h)) :=
  ⟨(H.banks i hi s hs).headerLeft,(H.banks j hj s hs).headerRight,
    (H.banks i hi s hs).left,(H.banks j hj s hs).right⟩
end ThreeSum.SharedReportingBankSources
