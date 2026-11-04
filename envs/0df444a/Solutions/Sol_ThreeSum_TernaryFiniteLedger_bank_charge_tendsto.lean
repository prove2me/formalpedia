-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.bank_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:32:19.336209+00:00
-- url     : https://prove2.me/submissions/ce55b73b-b814-414b-86de-b1e97062dac2

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_TernaryParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology
namespace ThreeSum.TernaryFiniteLedger
theorem _root_.solution :
    Tendsto bankCharge atTop (𝓝 (2*bankEntropy/Hpi)) :=
  tendsto_const_nhds.div actual_output_rate Hpi_pos.ne'
end ThreeSum.TernaryFiniteLedger
