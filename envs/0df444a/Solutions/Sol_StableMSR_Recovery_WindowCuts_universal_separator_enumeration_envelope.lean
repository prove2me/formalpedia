-- Prove2me | solution 1 for StableMSR.Recovery.WindowCuts.universal_separator_enumeration_envelope
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:37:24.057834+00:00
-- url     : https://prove2.me/submissions/1ca033cb-cce1-4a5f-a3dc-31346528750f

import Definitions.Def_StableMSR_WindowSeparatorCuts
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowCuts
theorem solution (x : World) (e : ℝ) (ep : 0< e) (el : e<1) (hn : 2≤ x.n) :
    x.n^6*(x.n+1)^(2*(widthBound e+1))*(bagBound x (budget e) (widthBound e))^2≤ x.n^(50*parameterEnvelope e) := by
  let n:=x.n
  let m:=budget e+1
  let t:=widthBound e+1
  let E:=parameterEnvelope e
  have two : 2≤ n:=hn
  have own : 1≤ ownerBound e := by
    unfold ownerBound;apply Nat.le_floor
    norm_num
    exact (le_div_iff₀ ep).mpr (by linarith)
  have ltm : 0< m:=by dsimp [m];omega
  have lm : m≤5*ownerBound e:=by dsimp [m,budget];omega
  have prod : m*t≤5*E := by
    have le:=Nat.mul_le_mul_right t lm
    have major : ownerBound e*t≤ E:=by dsimp [t,E,parameterEnvelope];omega
    exact le.trans (by rw [Nat.mul_assoc];exact Nat.mul_le_mul_left 5 major)
  have base : m*n^(2*m)+1≤ n^(4*m) := by
    have a : m≤ n^m:=(Nat.lt_pow_self (by omega : 1< n)).le
    have g:=Nat.mul_le_mul_right (n^(2*m)) a
    rw [←Nat.pow_add,show m+2*m=3*m by omega] at g
    have one : 1≤ n^(3*m):=Nat.one_le_pow _ _ (by omega)
    have twice:=Nat.mul_le_mul_left (n^(3*m)) two
    calc
      _ ≤ n^(3*m)*n := by omega
      _ = n^(3*m+1) := (Nat.pow_succ ..).symm
      _ ≤ n^(4*m) := Nat.pow_le_pow_right (by omega) (by omega)
  have bag : bagBound x (budget e) (widthBound e)≤ n^(20*E) := by
    change (m*n^(2*m)+1)^t≤_
    apply (Nat.pow_le_pow_left base t).trans
    rw [←Nat.pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by rw [Nat.mul_assoc];omega)
  have tE : t≤ E:=by
    have v : t≤ ownerBound e*t:=Nat.le_mul_of_pos_left _ own
    dsimp [t,E,parameterEnvelope] at *;omega
  have tpos : 1≤ t:=by dsimp [t];omega
  have plus : n+1≤ n^2:=by rw [pow_two];have a:=Nat.mul_le_mul_left n two;omega
  have u:=Nat.pow_le_pow_left plus (2*t)
  have b:=Nat.pow_le_pow_left bag 2
  change n^6*(n+1)^(2*t)*(bagBound x (budget e) (widthBound e))^2≤ n^(50*E)
  calc
    _ ≤ n^6*((n^2)^(2*t))*(n^(20*E))^2:=Nat.mul_le_mul (Nat.mul_le_mul_left _ u) b
    _ = n^(6+2*(2*t)+20*E*2):=by rw [←Nat.pow_mul,←Nat.pow_mul,←Nat.pow_add,←Nat.pow_add]
    _ ≤ _:=Nat.pow_le_pow_right (by omega) (by omega)
