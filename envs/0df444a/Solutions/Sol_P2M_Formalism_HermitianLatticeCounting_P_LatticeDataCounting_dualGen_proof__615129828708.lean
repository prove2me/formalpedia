-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_dualGen_proof__615129828708
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:36.610083+00:00
-- url     : https://prove2.me/submissions/17ea0588-0339-4739-8709-2bd03a06e9d9

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_mem_sup_span_iff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_dualGen_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution : DualGen := by
  intro E _ _ _ U _ _ _ _ h M N e s _ hfin hM hs
  obtain ⟨t, ht, hle⟩ := dualGen_span h M N e s hfin hM hs
  exact ⟨t, ht, fun x hx => (mem_sup_span_iff _ t x).mp (hle hx)⟩
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
