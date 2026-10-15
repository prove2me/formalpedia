-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_spectrum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:46:29.992242+00:00
-- url     : https://prove2.me/submissions/3ee5d668-0c5c-4ed4-9b2e-d8fb96bf8938

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K00
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K01
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K02
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K03
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K04
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K05
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K06
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK01
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK03
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK04
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK05
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK06
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK07
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperPos64K00
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperPos64K01
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperPos64K02
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperPos64K03
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperPos64K04
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperPos64K05
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperPos64K06
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperPos64K07
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHHighContourSpectrumBounds
theorem checked00 : (RHHighContourSpectrumUpperNeg64K00.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked01 : (RHHighContourSpectrumUpperNeg64K01.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked02 : (RHHighContourSpectrumUpperNeg64K02.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked03 : (RHHighContourSpectrumUpperNeg64K03.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked04 : (RHHighContourSpectrumUpperNeg64K04.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked05 : (RHHighContourSpectrumUpperNeg64K05.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked06 : (RHHighContourSpectrumUpperNeg64K06.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked07 : (RHHighContourSpectrumUpperNeg64K07.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked08 : (RHHighContourSpectrumUpperZeroK00.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked09 : (RHHighContourSpectrumUpperZeroK01.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked10 : (RHHighContourSpectrumUpperZeroK02.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked11 : (RHHighContourSpectrumUpperZeroK03.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked12 : (RHHighContourSpectrumUpperZeroK04.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked13 : (RHHighContourSpectrumUpperZeroK05.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked14 : (RHHighContourSpectrumUpperZeroK06.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked15 : (RHHighContourSpectrumUpperZeroK07.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked16 : (RHHighContourSpectrumUpperPos64K00.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked17 : (RHHighContourSpectrumUpperPos64K01.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked18 : (RHHighContourSpectrumUpperPos64K02.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked19 : (RHHighContourSpectrumUpperPos64K03.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked20 : (RHHighContourSpectrumUpperPos64K04.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked21 : (RHHighContourSpectrumUpperPos64K05.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked22 : (RHHighContourSpectrumUpperPos64K06.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked23 : (RHHighContourSpectrumUpperPos64K07.rows.flatten).all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
end RHHighContourSpectrumBounds
theorem solution :
  ∀ v ∈ [RHHighContourSpectrumUpperNeg64K00.rows.flatten,RHHighContourSpectrumUpperNeg64K01.rows.flatten,RHHighContourSpectrumUpperNeg64K02.rows.flatten,RHHighContourSpectrumUpperNeg64K03.rows.flatten,RHHighContourSpectrumUpperNeg64K04.rows.flatten,RHHighContourSpectrumUpperNeg64K05.rows.flatten,RHHighContourSpectrumUpperNeg64K06.rows.flatten,RHHighContourSpectrumUpperNeg64K07.rows.flatten,RHHighContourSpectrumUpperZeroK00.rows.flatten,RHHighContourSpectrumUpperZeroK01.rows.flatten,RHHighContourSpectrumUpperZeroK02.rows.flatten,RHHighContourSpectrumUpperZeroK03.rows.flatten,RHHighContourSpectrumUpperZeroK04.rows.flatten,RHHighContourSpectrumUpperZeroK05.rows.flatten,RHHighContourSpectrumUpperZeroK06.rows.flatten,RHHighContourSpectrumUpperZeroK07.rows.flatten,RHHighContourSpectrumUpperPos64K00.rows.flatten,RHHighContourSpectrumUpperPos64K01.rows.flatten,RHHighContourSpectrumUpperPos64K02.rows.flatten,RHHighContourSpectrumUpperPos64K03.rows.flatten,RHHighContourSpectrumUpperPos64K04.rows.flatten,RHHighContourSpectrumUpperPos64K05.rows.flatten,RHHighContourSpectrumUpperPos64K06.rows.flatten,RHHighContourSpectrumUpperPos64K07.rows.flatten],v.all (fun p=>let z:=RHHighContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by
  intro v hv
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact RHHighContourSpectrumBounds.checked00
  · exact RHHighContourSpectrumBounds.checked01
  · exact RHHighContourSpectrumBounds.checked02
  · exact RHHighContourSpectrumBounds.checked03
  · exact RHHighContourSpectrumBounds.checked04
  · exact RHHighContourSpectrumBounds.checked05
  · exact RHHighContourSpectrumBounds.checked06
  · exact RHHighContourSpectrumBounds.checked07
  · exact RHHighContourSpectrumBounds.checked08
  · exact RHHighContourSpectrumBounds.checked09
  · exact RHHighContourSpectrumBounds.checked10
  · exact RHHighContourSpectrumBounds.checked11
  · exact RHHighContourSpectrumBounds.checked12
  · exact RHHighContourSpectrumBounds.checked13
  · exact RHHighContourSpectrumBounds.checked14
  · exact RHHighContourSpectrumBounds.checked15
  · exact RHHighContourSpectrumBounds.checked16
  · exact RHHighContourSpectrumBounds.checked17
  · exact RHHighContourSpectrumBounds.checked18
  · exact RHHighContourSpectrumBounds.checked19
  · exact RHHighContourSpectrumBounds.checked20
  · exact RHHighContourSpectrumBounds.checked21
  · exact RHHighContourSpectrumBounds.checked22
  · exact RHHighContourSpectrumBounds.checked23
