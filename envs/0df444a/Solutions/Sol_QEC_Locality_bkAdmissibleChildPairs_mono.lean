-- Prove2me | solution 1 for QEC.Locality.bkAdmissibleChildPairs_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:25:22.914193+00:00
-- url     : https://prove2.me/submissions/11d50630-d362-4aef-89bb-1660e8e2b5d8

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {small large : Nat} (hscale : small ≤ large) :
    bkAdmissibleChildPairs small ⊆ bkAdmissibleChildPairs large := by
  intro children hchildren
  have hsmall := (mem_bkAdmissibleChildPairs_iff).1 hchildren
  apply (mem_bkAdmissibleChildPairs_iff).2
  exact ⟨by omega, by omega, by
    unfold BKAdmissibleChildPair at hsmall ⊢
    omega⟩
end QEC.Locality
