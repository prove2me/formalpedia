-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_contour_spectrum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:08:44.68039+00:00
-- url     : https://prove2.me/submissions/a02063fa-044c-466d-8b58-48238691b955

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ContourCoefficient
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K01
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K03
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K06
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK01
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK03
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK06
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK07
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperPos64K00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperPos64K01
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperPos64K02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperPos64K03
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperPos64K04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperPos64K05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperPos64K06
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperPos64K07
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01ContourSpectrumBounds
theorem checked00 : (RHBatch01ContourSpectrumUpperNeg64K00.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked01 : (RHBatch01ContourSpectrumUpperNeg64K01.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked02 : (RHBatch01ContourSpectrumUpperNeg64K02.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked03 : (RHBatch01ContourSpectrumUpperNeg64K03.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked04 : (RHBatch01ContourSpectrumUpperNeg64K04.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked05 : (RHBatch01ContourSpectrumUpperNeg64K05.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked06 : (RHBatch01ContourSpectrumUpperNeg64K06.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked07 : (RHBatch01ContourSpectrumUpperNeg64K07.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked08 : (RHBatch01ContourSpectrumUpperZeroK00.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked09 : (RHBatch01ContourSpectrumUpperZeroK01.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked10 : (RHBatch01ContourSpectrumUpperZeroK02.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked11 : (RHBatch01ContourSpectrumUpperZeroK03.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked12 : (RHBatch01ContourSpectrumUpperZeroK04.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked13 : (RHBatch01ContourSpectrumUpperZeroK05.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked14 : (RHBatch01ContourSpectrumUpperZeroK06.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked15 : (RHBatch01ContourSpectrumUpperZeroK07.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked16 : (RHBatch01ContourSpectrumUpperPos64K00.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked17 : (RHBatch01ContourSpectrumUpperPos64K01.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked18 : (RHBatch01ContourSpectrumUpperPos64K02.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked19 : (RHBatch01ContourSpectrumUpperPos64K03.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked20 : (RHBatch01ContourSpectrumUpperPos64K04.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked21 : (RHBatch01ContourSpectrumUpperPos64K05.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked22 : (RHBatch01ContourSpectrumUpperPos64K06.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
theorem checked23 : (RHBatch01ContourSpectrumUpperPos64K07.rows.flatten).all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by decide +kernel
end RHBatch01ContourSpectrumBounds
theorem solution :
  ∀ v ∈ [RHBatch01ContourSpectrumUpperNeg64K00.rows.flatten,RHBatch01ContourSpectrumUpperNeg64K01.rows.flatten,RHBatch01ContourSpectrumUpperNeg64K02.rows.flatten,RHBatch01ContourSpectrumUpperNeg64K03.rows.flatten,RHBatch01ContourSpectrumUpperNeg64K04.rows.flatten,RHBatch01ContourSpectrumUpperNeg64K05.rows.flatten,RHBatch01ContourSpectrumUpperNeg64K06.rows.flatten,RHBatch01ContourSpectrumUpperNeg64K07.rows.flatten,RHBatch01ContourSpectrumUpperZeroK00.rows.flatten,RHBatch01ContourSpectrumUpperZeroK01.rows.flatten,RHBatch01ContourSpectrumUpperZeroK02.rows.flatten,RHBatch01ContourSpectrumUpperZeroK03.rows.flatten,RHBatch01ContourSpectrumUpperZeroK04.rows.flatten,RHBatch01ContourSpectrumUpperZeroK05.rows.flatten,RHBatch01ContourSpectrumUpperZeroK06.rows.flatten,RHBatch01ContourSpectrumUpperZeroK07.rows.flatten,RHBatch01ContourSpectrumUpperPos64K00.rows.flatten,RHBatch01ContourSpectrumUpperPos64K01.rows.flatten,RHBatch01ContourSpectrumUpperPos64K02.rows.flatten,RHBatch01ContourSpectrumUpperPos64K03.rows.flatten,RHBatch01ContourSpectrumUpperPos64K04.rows.flatten,RHBatch01ContourSpectrumUpperPos64K05.rows.flatten,RHBatch01ContourSpectrumUpperPos64K06.rows.flatten,RHBatch01ContourSpectrumUpperPos64K07.rows.flatten],v.all (fun p=>let z:=RHBatch01ContourCoefficientData.decode p;decide (|z.1|+|z.2|≤(2:Int)^80))=true := by
  intro v hv
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact RHBatch01ContourSpectrumBounds.checked00
  · exact RHBatch01ContourSpectrumBounds.checked01
  · exact RHBatch01ContourSpectrumBounds.checked02
  · exact RHBatch01ContourSpectrumBounds.checked03
  · exact RHBatch01ContourSpectrumBounds.checked04
  · exact RHBatch01ContourSpectrumBounds.checked05
  · exact RHBatch01ContourSpectrumBounds.checked06
  · exact RHBatch01ContourSpectrumBounds.checked07
  · exact RHBatch01ContourSpectrumBounds.checked08
  · exact RHBatch01ContourSpectrumBounds.checked09
  · exact RHBatch01ContourSpectrumBounds.checked10
  · exact RHBatch01ContourSpectrumBounds.checked11
  · exact RHBatch01ContourSpectrumBounds.checked12
  · exact RHBatch01ContourSpectrumBounds.checked13
  · exact RHBatch01ContourSpectrumBounds.checked14
  · exact RHBatch01ContourSpectrumBounds.checked15
  · exact RHBatch01ContourSpectrumBounds.checked16
  · exact RHBatch01ContourSpectrumBounds.checked17
  · exact RHBatch01ContourSpectrumBounds.checked18
  · exact RHBatch01ContourSpectrumBounds.checked19
  · exact RHBatch01ContourSpectrumBounds.checked20
  · exact RHBatch01ContourSpectrumBounds.checked21
  · exact RHBatch01ContourSpectrumBounds.checked22
  · exact RHBatch01ContourSpectrumBounds.checked23
#print axioms solution
