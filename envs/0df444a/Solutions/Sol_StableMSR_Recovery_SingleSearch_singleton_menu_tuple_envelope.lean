-- Prove2me | solution 1 for StableMSR.Recovery.SingleSearch.singleton_menu_tuple_envelope
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:11.924145+00:00
-- url     : https://prove2.me/submissions/b0fd752e-fecd-4d15-bf02-e11db40098e1

import Definitions.Def_StableMSR_SingleVertexSearch
import Theorems.Thm_StableMSR_Recovery_WindowCuts_universal_separator_enumeration_envelope
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
theorem solution (x : OracleQueries.World) (e : ℝ) (ep : 0< e) (el : e<1) (hn : 2≤ x.n) :
    x.n^3*(x.n+1)^(widthBound e+1)*WindowCSP.bagBound x (WindowCSP.budget e) (widthBound e)≤ x.n^(25*parameterEnvelope e) := by
  let n:=x.n;let t:=widthBound e+1;let b:=WindowCSP.bagBound x (WindowCSP.budget e) (widthBound e);let E:=parameterEnvelope e
  have h : n^6*(n+1)^(2*t)*b^2≤ n^(50*E):=universal_separator_enumeration_envelope x e ep el hn
  have sq : (n^3*(n+1)^t*b)^2≤(n^(25*E))^2:=by
    rw [mul_pow,mul_pow,←pow_mul,←pow_mul,←pow_mul]
    rw [show 3*2=6 by decide,show t*2=2*t by omega,show 25*E*2=50*E by omega]
    exact h
  by_contra! lt
  exact (Nat.not_lt_of_ge sq) (Nat.pow_lt_pow_left lt (by decide : 2≠0))
