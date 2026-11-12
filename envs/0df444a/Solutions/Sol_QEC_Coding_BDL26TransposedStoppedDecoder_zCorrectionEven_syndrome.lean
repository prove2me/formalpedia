-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.zCorrectionEven_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:48:10.424607+00:00
-- url     : https://prove2.me/submissions/49bd0ba3-318f-4430-b6fb-5b1de7717a5f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_zCorrection_syndrome
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators
private theorem rightInverse_cast (S : OddScale) {m r : Nat} (h : m = r)
    (f : LinearMap.range (xSyndrome S m) → Word BDL26Field (Physical S m))
    (hf : ∀ v, xSyndrome S m (f v) = v.val)
    (v : LinearMap.range (xSyndrome S r)) :
    xSyndrome S r (cast (congrArg (fun l => Word BDL26Field (Physical S l)) h)
      (f (cast (congrArg (fun l => ↥(LinearMap.range (xSyndrome S l))) h).symm v))) = v.val := by
  cases h
  exact hf v
end QEC.Coding.BDL26TransposedStoppedDecoder
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (v : LinearMap.range (xSyndrome S (2 * k))) :
    xSyndrome S (2 * k) (zCorrectionEven S k hk v) = v.val :=
  rightInverse_cast S (source_even_level k hk) (zCorrection S (2 * (k - 1)))
    (zCorrection_syndrome S (2 * (k - 1))) v
end QEC.Coding.BDL26TransposedStoppedDecoder
