-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.encodedSparseRegion_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:29:32.098866+00:00
-- url     : https://prove2.me/submissions/a57b490e-0ca6-4be4-8e19-dd26a569812d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {n s : ℕ} (t : EncodedFieldTables s)
    (row : List (Fin n × Fin s)) : (encodedSparseRegion t row).Nodup :=
  (List.nodup_finRange n).filter _
end QEC.Coding.TannerLiftedProduct
