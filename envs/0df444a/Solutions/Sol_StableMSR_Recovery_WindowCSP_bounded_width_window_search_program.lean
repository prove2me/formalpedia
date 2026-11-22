-- Prove2me | solution 1 for StableMSR.Recovery.WindowCSP.bounded_width_window_search_program
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:13:43.508655+00:00
-- url     : https://prove2.me/submissions/6cda1f4c-9f6c-4677-82a0-f3b58034300f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_WindowProfiles_native_single_region_profiles
import Theorems.Thm_StableMSR_Recovery_WindowProfiles_native_count_graph
import Theorems.Thm_StableMSR_Recovery_WindowProfiles_local_profiles_certify_exact_count_search
import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_decode_regional_menus
import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
open Polynomial
private noncomputable def boundPoly : Polynomial ℕ := X+C 4*(1+X^4)+1
private lemma capUp (x : World) (m : Mem) : (arena x m).cap≤ boundPoly.eval x.cap:=by
  have ns : x.n≤ x.cap:=by dsimp [World.cap];omega
  have rs : x.rows≤ x.cap:=by dsimp [World.cap];omega
  have prod:=Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul rs ns) ns) ns
  have plus : x.n+x.k+1≤ x.cap:=by dsimp [World.cap];omega
  change x.n+x.k+height x+1≤_
  simp only [boundPoly,eval_add,eval_mul,eval_one,eval_X,eval_C,eval_pow]
  rw [show x.cap^4=x.cap*x.cap*x.cap*x.cap by ring]
  unfold height capacity;omega
private lemma monoEval (p : Polynomial ℕ) {i j : ℕ} (h : i≤ j) : p.eval i≤ p.eval j:=by
  rw [Polynomial.eval_eq_sum_range,Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun k _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k))
private lemma capPoly (p : Polynomial ℕ) : ∃c D : ℕ,∀m : ℕ,1≤ m → p.eval m≤ c*m^D := by
  classical
  let D:=p.natDegree+1
  refine ⟨∑i ∈ Finset.range D,p.coeff i,D,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  apply Finset.sum_le_sum;intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Finset.mem_range.mp hi).le)
theorem solution : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,searchSpec e c D b cmd := by
  obtain ⟨c,D,b,hc,hb,make⟩:=native_single_region_profiles
  obtain ⟨P,packC,packRun⟩:=native_count_graph
  obtain ⟨Q,solve,solveRun⟩:=RegionalBallDP.decode_regional_menus
  let A:=P+Q.comp boundPoly+boundPoly
  obtain ⟨C,T,major⟩:=capPoly A
  refine ⟨c+C+1,D+T,b,by omega,hb,?_⟩
  intro e epos el
  obtain ⟨makeC,makeRun⟩:=make e epos el
  refine ⟨makeC.seq (packC.seq solve),?_⟩
  intro x s hk kn metric ready
  obtain ⟨a,l,ea,al,ar,profile⟩:=makeRun x s hk kn metric ready
  let y:=worldOf x.k x.rows x.dist a
  obtain ⟨v,j,ev,jp,vr,grid⟩:=packRun y a hk kn ar
  let m : Mem:=fun i=>v.imem (i:ℤ)
  let g:=arena y m
  obtain ⟨t,z,et,zq,tReady,ends,best⟩:=solveRun g v hk (by change 0< x.n;omega) grid.sized vr
  let N:=x.n^(b*parameterEnvelope (e:ℝ))
  let V:=x.cap
  have non : 1≤ V:=by dsimp [V,World.cap];omega
  have npos : 1≤ N:=Nat.one_le_pow _ _ (by omega)
  have gup : g.cap≤ boundPoly.eval V:=capUp y m
  have K:=major V non
  change (P+Q.comp boundPoly+boundPoly).eval V≤ C*V^T at K
  simp only [eval_add,eval_comp] at K
  have jq : j≤ P.eval V:=jp
  have zq' :=zq.trans (monoEval Q gup)
  have heightB : height y≤ boundPoly.eval V:=by
    apply le_trans _ gup;change height y≤ y.n+y.k+height y+1;omega
  have small (a : ℕ) (h : a≤ T+D) : V^a≤ V^(D+T):=Nat.pow_le_pow_right non (by omega)
  have additive : j+z≤ C*V^(D+T)*N:=calc
    j+z≤ C*V^T :=by omega
    _≤ C*V^(D+T)*N :=by
      apply le_trans (Nat.mul_le_mul_left _ (small T (by omega)))
      exact Nat.le_mul_of_pos_right _ npos
  have localBound : l≤ c*V^(D+T)*N:=al.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (small D (by omega))))
  have upper : c*V^(D+T)*N+C*V^(D+T)*N≤(c+C+1)*V^(D+T)*N:=by
    rw [←Nat.add_mul,←Nat.add_mul];exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have heightC : height y≤ C*V^(D+T)*N:=calc
    height y≤ C*V^T:=by omega
    _≤ C*V^(D+T)*N:=(Nat.mul_le_mul_left _ (small T (by omega))).trans (Nat.le_mul_of_pos_right _ npos)
  refine ⟨t,_,height y,.seq ea (.seq ev et),by change l+(j+z)≤(c+C+1)*V^(D+T)*N;omega,by change height y≤(c+C+1)*V^(D+T)*N;omega,tReady,ends,?_⟩
  intro u hu pos tw P' validP total
  obtain ⟨vert,table,w,path,cheap⟩:=local_profiles_certify_exact_count_search x e y.mem m (by omega) profile grid u hu pos tw P' validP total
  obtain ⟨good,cost⟩:=best _ vert table w path
  exact ⟨_,table.1,good,cost.trans cheap⟩

