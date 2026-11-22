-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.native_single_region_profiles
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:47:07.594803+00:00
-- url     : https://prove2.me/submissions/a69029ee-86b1-4056-8d5a-f9f60122e687
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_WindowJoins_native_window_join_records
import Theorems.Thm_StableMSR_Recovery_WindowJoins_native_join_decoder
import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open Polynomial
private lemma powerBound (p : Polynomial ℕ) : ∃C T : ℕ,0< T ∧ ∀v : ℕ,1≤ v → p.eval v≤ C*v^T:=by
  classical
  let T:=p.natDegree+1
  refine ⟨∑i∈Finset.range T,p.coeff i,T,by dsimp [T];omega,?_⟩
  intro v hv;rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv (Finset.mem_range.mp hi).le))
theorem solution : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,profileSpec e c D b cmd := by
  obtain ⟨c,D,b,cp,bp,build⟩:=native_window_join_records
  obtain ⟨P,solve,run⟩:=native_join_decoder
  obtain ⟨C,T,tp,major⟩:=powerBound P
  refine ⟨(C+1)*(c+1)^T,(D+1)*T,b*T,Nat.mul_pos (by omega) (pow_pos (by omega) _),Nat.mul_pos bp tp,?_⟩
  intro e ep el;obtain ⟨make,construct⟩:=build e ep el
  refine ⟨make.seq solve,?_⟩
  intro x s hk kn metric ready
  obtain ⟨a,l,H,ea,time,height,ar,cert⟩:=construct x s hk kn metric ready
  let y:=worldOf x.k H x.dist a
  obtain ⟨t,j,et,pol,rd,prof⟩:=run x e H a hk (by omega) ar cert
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
  refine ⟨t,_,.seq ea et,?_,rd,prof⟩
  change l+j≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E)
  calc l+j≤ B^T+C*B^T:=Nat.add_le_add (old.trans Bup) later
       _=(C+1)*B^T:=by ring
       _=_:=by dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
