-- Prove2me | solution 1 for P2M_Erdos1219_Ctx___lt_lam_02132eacf1ef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:49:24.561949+00:00
-- url     : https://prove2.me/submissions/f884c447-61f7-429f-86b2-19c8a38c2249

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
import Theorems.Thm_Erdos1219_le_two_pow_self


set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
open Erdos1219.Ctx
variable {V : Type u} (S : Ctx V)
namespace Erdos1219.Ctx
theorem _root_.solution (k : ℕ) : S.μ k < S.lam k :=
  le_two_pow_self.trans_lt (S.two_pow_lt_lam k)
end Erdos1219.Ctx
