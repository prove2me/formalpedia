-- Prove2me | solution 1 for StableMSR.Recovery.SingleWindows.emit_singleton_separator_grammar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:13:47.168777+00:00
-- url     : https://prove2.me/submissions/619d15d1-dc30-4261-abd6-97a8152c010f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_StableMSR_DenseSingletonCompilation
import Theorems.Thm_StableMSR_Recovery_SingleRAM_native_dense_window_circuits
import Theorems.Thm_StableMSR_Recovery_SingleRAM_native_board_realizes_circuit_language
import Theorems.Thm_StableMSR_Recovery_SingleRAM_native_circuit_record_emitter
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Writes field)
open StableMSR.Recovery.SingleRAM
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)
open Polynomial
private lemma powerBound (p : Polynomial ℕ) : ∃C T : ℕ,0< T ∧ ∀v : ℕ,1≤ v → p.eval v≤ C*v^T:=by
  classical
  let T:=p.natDegree+1
  refine ⟨∑i∈Finset.range T,p.coeff i,T,by dsimp [T];omega,?_⟩
  intro v hv;rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv (Finset.mem_range.mp hi).le))
theorem solution : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,nativeSpec e c D b cmd := by
  obtain ⟨c,D,b,cp,bp,build⟩:=native_dense_window_circuits
  obtain ⟨P,solve,run⟩:=native_circuit_record_emitter
  obtain ⟨C,T,tp,major⟩:=powerBound P
  refine ⟨(C+1)*(c+1)^T,(D+1)*T,b*T,Nat.mul_pos (by omega) (pow_pos (by omega) _),Nat.mul_pos bp tp,?_⟩
  intro e ep el;obtain ⟨make,construct⟩:=build e ep el
  refine ⟨make.seq solve,?_⟩
  intro x s hk kn metric ready
  obtain ⟨a,l,H,ea,time,height,ar,scene,g,roots,size,encoded,lang⟩:=construct x s hk kn metric ready
  let y:=worldOf x.k H x.dist a
  obtain ⟨t,j,et,pol,rd,head,rep⟩:=run y a g roots hk (by change 0< x.n;omega) size ar encoded
  let out:=worldOf x.k H x.dist t
  have prof : Implements x e out:=by
    refine ⟨rep.1,head.trans scene,?_⟩;intro u hu i hi
    obtain ⟨index,valid,unused,dry,live⟩:=lang.2.2 u hu i hi
    have eq:=(rep.2.2 (u*x.n+i) index).2.2.2.1
    change (board out).root (u*x.n+i)=roots (u*x.n+i) at eq
    have vol : (board out).size=3*g.size:=rep.2.1
    have equiv (L : List (Cluster x.n)) := native_board_realizes_circuit_language out g roots rep lang.1 lang.2.1 (roots (u*x.n+i)) L
    change u*x.n+i<(board out).size ∧ (board out).root (u*x.n+i)<(board out).size ∧ _
    rw [eq,vol];refine ⟨index,valid,?_,?_,?_⟩
    · intro no L;exact (equiv L).trans (unused no L)
    · intro key nonpos L tr;exact dry key nonpos L ((equiv L).mp tr)
    · intro key pos;refine ⟨fun L tr=>(live key pos).1 L ((equiv L).mp tr),?_⟩
      intro Q gen;obtain ⟨L,hl,eL⟩:=(live key pos).2 Q gen
      exact ⟨L,(equiv L).mpr hl,eL⟩
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
