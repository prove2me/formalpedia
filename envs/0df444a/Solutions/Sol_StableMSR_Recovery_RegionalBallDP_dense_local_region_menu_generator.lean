-- Prove2me | solution 1 for StableMSR.Recovery.RegionalBallDP.dense_local_region_menu_generator
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T16:10:54.148163+00:00
-- url     : https://prove2.me/submissions/aa5db9f6-00b6-4935-b078-56ac40122e6e

import Theorems.Thm_StableMSR_Recovery_WindowCSP_dense_aligned_scenario_program
import Theorems.Thm_StableMSR_Recovery_WindowCSP_bounded_width_window_search_program
import Theorems.Thm_StableMSR_Recovery_WindowCSP_aligned_scenario_has_exact_assignment
import Theorems.Thm_StableMSR_Recovery_WindowCSP_catalog_to_local_trials
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
open StableMSR.Recovery.RegionalBallDP
open Polynomial
private lemma capPoly (p : Polynomial ℕ) : ∃c D : ℕ,∀m : ℕ,1≤ m → p.eval m≤ c*m^D := by
  classical
  let D:=p.natDegree+1
  refine ⟨∑i ∈ Finset.range D,p.coeff i,D,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  apply Finset.sum_le_sum;intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Finset.mem_range.mp hi).le)
private lemma absorb (a b c D f n k H E z l : ℕ) (hn : 1≤ n) (hk : k≤ n) (hb : 1≤ b) (he : 1≤ E)
    (hz : z≤ a*n^(b*E)) (hH : H≤ a*n^(b*E)) (hl : l≤ c*(n+k+H+1)^D*n^(f*E)) :
    z+l≤(a+c*(a+3)^D)*n^((b*(D+1)+f)*E) := by
  let K:=n^(b*E)
  have one : 1≤ K:=Nat.one_le_pow _ _ hn
  have small : n≤ K := by simpa [K] using Nat.pow_le_pow_right hn (show 1≤ b*E by exact Nat.mul_pos hb he)
  change H≤ a*K at hH
  have cap : n+k+H+1≤(a+3)*K := by rw [Nat.add_mul];omega
  have l' := hl.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c (Nat.pow_le_pow_left cap D)))
  rw [Nat.mul_pow] at l'
  have bp : b≤ b*(D+1)+f := by rw [Nat.mul_add];omega
  have dp : b*D+f≤ b*(D+1)+f := by rw [Nat.mul_add];omega
  have base := Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E bp)
  have high := Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E dp)
  have prod : K^D*n^(f*E)=n^((b*D+f)*E) := by
    dsimp [K];rw [←Nat.pow_mul,←Nat.pow_add];congr 1;ring
  rw [Nat.add_mul]
  apply Nat.add_le_add (hz.trans (Nat.mul_le_mul_left a base))
  calc
    l ≤ c*((a+3)^D*K^D)*n^(f*E) := l'
    _ = (c*(a+3)^D)*(K^D*n^(f*E)) := by ring
    _ ≤ _ := by rw [prod];exact Nat.mul_le_mul_left _ high
theorem solution : ∃a b : ℕ,0< a ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 →
    ∃cmd : Cmd,∀(n k : ℕ) (d : Point n→Point n→ℝ),
      1≤ k → k< n → fewBound (e:ℝ)< k → IsMetricArray d → localSpec e a b cmd n k d := by
  obtain ⟨a,b,apos,bpos,start⟩:=dense_aligned_scenario_program
  obtain ⟨c,D,f,_,_,search⟩:=bounded_width_window_search_program
  obtain ⟨p,wrap,encode⟩:=catalog_to_local_trials
  obtain ⟨c₂,D₂,ce⟩:=capPoly (p+C 4*X+C 5)
  let A:=a+c*(a+3)^D
  let B:=b*(D+1)+f
  have positive : 0< B:= by dsimp [B];positivity
  refine ⟨A+c₂*(A+3)^D₂,B*(D₂+1)+0,by dsimp [A];omega,by positivity,?_⟩
  intro e he hl
  obtain ⟨prep,hPrep⟩:=start e he hl
  obtain ⟨post,hPost⟩:=search e he hl
  refine ⟨.seq prep (.seq post wrap),?_⟩
  intro n k d hk kn big met
  obtain ⟨s,z,H,ez,tz,hH,rs,scene⟩:=hPrep n k d hk kn big met
  let x:=worldOf k H d s
  obtain ⟨m,l,J,el,tl,hJ,rm,ends,answer⟩:=hPost x s hk kn met rs
  let y:=worldOf k J d m
  obtain ⟨t,u,eu,tu,rt,shape',trial⟩:=encode y m hk rm ends
  let E:=parameterEnvelope (e:ℝ)
  have epos : 1≤ E:=by dsimp [E,parameterEnvelope];omega
  have first := absorb a b c D f n k H E z l (by omega) kn.le bpos epos tz hH tl
  have size₁ := absorb a b c D f n k H E 0 J (by omega) kn.le bpos epos (by omega) hH hJ
  change z+l≤ A*n^(B*E) at first
  change 0+J≤ A*n^(B*E) at size₁
  simp only [Nat.zero_add] at size₁
  have cap:=ce y.cap (by unfold World.cap;omega)
  simp only [eval_add,eval_mul,eval_X,eval_C] at cap
  have ul : u≤ c₂*(n+k+J+1)^D₂*n^(0*E) := by simp;change u≤ c₂*y.cap^D₂;omega
  have hj : 1+4*(J+1)≤ c₂*(n+k+J+1)^D₂*n^(0*E) := by
    simp;change 1+4*(J+1)≤ c₂*y.cap^D₂
    have le : J≤ y.cap:=by dsimp [World.cap,y,worldOf];omega
    omega
  have second:=absorb A B c₂ D₂ 0 n k J E (z+l) u (by omega) kn.le positive epos first size₁ ul
  have last:=absorb A B c₂ D₂ 0 n k J E 0 (1+4*(J+1)) (by omega) kn.le positive epos (by omega) size₁ hj
  refine ⟨t,_,1+4*(J+1),.seq ez (.seq el eu),?_,by simpa only [Nat.zero_add] using last,rt,shape',?_⟩
  · simpa only [Nat.add_assoc] using second
  · intro O stable many
    obtain ⟨a,ah,ap,ae,ad⟩:=scene O stable many
    obtain ⟨widths,P,hp,num,cost'⟩:=aligned_scenario_has_exact_assignment x a (e:ℝ)
      (by exact_mod_cast he) (by exact_mod_cast hl) hk kn met O stable ap ae ad
    obtain ⟨r,hr,good',le⟩:=answer a ah ap widths P hp num
    exact ⟨r+2,trial r hr good' (cost d O) (le.trans cost'.le)⟩

