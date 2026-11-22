-- Prove2me | solution 1 for StableMSR.Recovery.WindowPorts.native_separator_ports
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:26:25.196734+00:00
-- url     : https://prove2.me/submissions/eae89390-435e-4af0-969b-260ed07ea43a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_StableMSR_WindowBlockMasks
import Theorems.Thm_StableMSR_Recovery_WindowMasks_native_regional_block_incidences
import Theorems.Thm_StableMSR_Recovery_WindowMasks_native_block_literal_compiler
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowMasks
open Polynomial
private lemma powerBound (p : Polynomial ℕ) : ∃C T : ℕ,0< T ∧ ∀v : ℕ,1≤ v → p.eval v≤ C*v^T:=by
  classical
  let T:=p.natDegree+1
  refine ⟨∑i∈Finset.range T,p.coeff i,T,by dsimp [T];omega,?_⟩
  intro v hv;rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv (Finset.mem_range.mp hi).le))
theorem solution : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,portSpec e c D b cmd := by
  obtain ⟨c,D,b,cp,bp,build⟩:=native_regional_block_incidences
  obtain ⟨P,solve,run⟩:=native_block_literal_compiler
  obtain ⟨C,T,tp,major⟩:=powerBound P
  refine ⟨(C+1)*(c+1)^T,(D+1)*T,b*T,Nat.mul_pos (by omega) (pow_pos (by omega) _),Nat.mul_pos bp tp,?_⟩
  intro e ep el;obtain ⟨make,construct⟩:=build e ep el
  refine ⟨make.seq solve,?_⟩
  intro x s hk kn metric ready
  obtain ⟨a,l,H,ea,time,height,ar,cert⟩:=construct x s hk kn metric ready
  let y:=worldOf x.k H x.dist a
  obtain ⟨t,j,et,pol,rd,prof⟩:=run x e H a hk kn metric ar cert
  let E:=parameterEnvelope (e:ℝ);let V:=x.cap;let N:=x.n^(b*E)
  let B:=(c+1)*V^(D+1)*N
  have vp : 1≤ V:=by dsimp [V,World.cap];omega
  have np : 1≤ N:=Nat.one_le_pow _ _ (by omega)
  have one : 1≤ V^(D+1):=Nat.one_le_pow _ _ vp
  have up : V^D≤ V^(D+1):=Nat.pow_le_pow_right vp (by omega)
  have ve : V≤ V^(D+1):=by simpa only [pow_one] using Nat.pow_le_pow_right vp (show 1≤ D+1 by omega)
  have scale : V≤ V^(D+1)*N:=ve.trans (Nat.le_mul_of_pos_right _ np)
  have lim : c*V^D*N≤ c*V^(D+1)*N:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ up)
  have beq : B=c*V^(D+1)*N+V^(D+1)*N:=by dsimp [B];ring
  have old : l≤ B:=by change l≤ c*V^D*N at time;omega
  have extra : H≤ c*V^(D+1)*N:=height.trans lim
  have cover : y.cap≤ V+H:=by dsimp [y,V,worldOf,World.cap];omega
  have big : y.cap≤ B:=by omega
  have Bpos : 1≤ B:=by omega
  have Bup : B≤ B^T:=by simpa only [pow_one] using Nat.pow_le_pow_right Bpos (show 1≤ T by omega)
  have yp : 1≤ y.cap:=by dsimp [World.cap];omega
  have later : j≤ C*B^T:=pol.trans ((major _ yp).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left big _)))
  have polyEq : (C+1)*B^T=(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E):=by
    dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
  have hB : H≤ B:=by omega
  refine ⟨t,_,H,.seq ea et,?_,?_,rd,prof⟩
  rotate_left
  · change H≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E);rw [←polyEq]
    exact (hB.trans Bup).trans (Nat.le_mul_of_pos_left _ (by omega))
  change l+j≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E)
  calc l+j≤ B^T+C*B^T:=Nat.add_le_add (old.trans Bup) later
       _=(C+1)*B^T:=by ring
       _=_:=by dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
