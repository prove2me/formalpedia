-- Prove2me | solution 1 for StableMSR.Recovery.CartesianBallRows.interior_ball_cover_catalog
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T23:35:02.341168+00:00
-- url     : https://prove2.me/submissions/9b764216-9098-496a-8956-1ac1f442f5a0

import Theorems.Thm_StableMSR_Recovery_FewBallRows_append_few_large_recovery
import Theorems.Thm_StableMSR_Recovery_FewBallRows_dense_ball_cover_catalog
import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma capPoly (p : Polynomial ℕ) :
    ∃c D : ℕ,∀m : ℕ,1 ≤ m → p.eval m ≤ c*m^D := by
  classical
  let e := p.natDegree+1
  let s := ∑ i ∈ Finset.range e,p.coeff i
  refine ⟨s,e,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑i ∈ Finset.range e,p.coeff i*m^e := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Nat.le_of_lt (Finset.mem_range.mp hi)))
    _ = s*m^e := (Finset.sum_mul ..).symm
private lemma combineTime (a b c D n k H E z l : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hb : 1 ≤ b) (he : 1 ≤ E) (hz : z ≤ a*n^(b*E)) (hh : H ≤ a*n^(b*E))
    (hl : l ≤ c*(n+k+H+1)^D) :
    z+l+1 ≤ (a+c*(a+3)^D+1)*n^((b*(D+1))*E) := by
  let B := n^(b*E)
  have hB : 1 ≤ B := Nat.one_le_pow _ _ hn
  have bn : n ≤ B := by
    change n ≤ n^(b*E)
    have t := Nat.pow_le_pow_right hn (show 1 ≤ b*E by exact Nat.mul_pos hb he)
    simpa using t
  change H ≤ a*B at hh
  change z ≤ a*B at hz
  have cap : n+k+H+1 ≤ (a+3)*B := by rw [Nat.add_mul];omega
  have bound := hl.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left cap D))
  rw [Nat.mul_pow] at bound
  have bd : B^D ≤ B^(D+1) := Nat.pow_le_pow_right hB (by omega)
  have bb : B ≤ B^(D+1) := by
    simpa using Nat.pow_le_pow_right hB (show 1 ≤ D+1 by omega)
  have one : 1 ≤ B^(D+1) := Nat.one_le_pow _ _ hB
  rw [show (b*(D+1))*E=(b*E)*(D+1) by ring,Nat.pow_mul]
  change z+l+1 ≤ (a+c*(a+3)^D+1)*B^(D+1)
  rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
  apply Nat.add_le_add _ one
  apply Nat.add_le_add (hz.trans (Nat.mul_le_mul_left a bb))
  rw [← Nat.mul_assoc] at bound
  exact bound.trans (Nat.mul_le_mul_left _ bd)

theorem solution : ∃a b : ℕ,0 < a ∧ 0 < b ∧ ∀e : ℚ,0 < e → e < 1 →
    ∃cmd : Cmd,∀ (n k : ℕ) (d : Point n→Point n→ℝ),
      1 ≤ k → k < n → fewBound (e:ℝ) < k → IsMetricArray d → runSpec e a b cmd n k d := by
  classical
  obtain ⟨a,b,ha,hb,dense⟩ := dense_ball_cover_catalog
  obtain ⟨p,appendRows⟩ := append_few_large_recovery
  obtain ⟨c,D,poly⟩ := capPoly p
  let A := a+1
  let B := b+2
  refine ⟨A+c*(A+3)^D+1,B*(D+1),by omega,Nat.mul_pos (by dsimp [B];omega) (by omega),?_⟩
  intro e he hlt
  let h := fewBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  obtain ⟨G,gen⟩ := dense e he hlt
  obtain ⟨J,joinRows⟩ := appendRows h
  refine ⟨.seq G J,?_⟩
  intro n k d hk kn largeK metric
  obtain ⟨s,z,H,ez,tz,th,rd,ends,covers⟩ := gen n k d hk kn largeK metric
  let x := worldOf k H d s
  let F := rows n (h+1)
  obtain ⟨t,l,el,tl,ready,valid,old,new'⟩ := joinRows x s hk kn largeK metric rd
  have hn : 1≤n := by omega
  have wE : h+1≤E := by dsimp [h,E,parameterEnvelope];omega
  have hp : 1≤E := by omega
  have shift : n^(b*E) ≤ n^(B*E) := Nat.pow_le_pow_right hn (Nat.mul_le_mul_right _ (by dsimp [B];omega))
  have up := Nat.mul_le_mul_left a shift
  have ff : F≤n^(B*E) := Nat.pow_le_pow_right hn (Nat.mul_le_mul (by dsimp [B];omega : 2≤B) wE)
  have H' : H+F≤A*n^(B*E) := by
    change H≤a*n^(b*E) at th
    dsimp [A];rw [Nat.add_mul,Nat.one_mul];omega
  have zz : z≤A*n^(B*E) := by
    change z≤a*n^(b*E) at tz
    dsimp [A];rw [Nat.add_mul,Nat.one_mul];omega
  have cap : x.cap+rows x.n (h+1)=n+k+(H+F)+1 := by dsimp [x,worldOf,World.cap,F];omega
  have smallTime := tl.trans (poly _ (by rw [cap];omega))
  rw [cap] at smallTime
  have total := combineTime A B c D n k (H+F) E z l hn kn.le (by dsimp [B];omega) hp zz H' smallTime
  have exponent : B*E≤(B*(D+1))*E := Nat.mul_le_mul_right _ (by nlinarith [Nat.zero_le (B*D)])
  have tableTime := H'.trans (Nat.mul_le_mul (show A≤A+c*(A+3)^D+1 by omega) (Nat.pow_le_pow_right hn exponent))
  refine ⟨t,_,H+F,Executes.seq ez el,(Nat.le_succ (z+l)).trans total,tableTime,ready,valid ends,?_⟩
  intro O stable
  by_cases few : (largeClusters d O (e:ℝ)).card≤h
  · obtain ⟨u,hu,g,price⟩ := new' (e:ℝ) (by exact_mod_cast he) (by exact_mod_cast hlt) O stable few
    exact ⟨H+u,Nat.add_lt_add_left hu _,g,price.le⟩
  · obtain ⟨r,hr,g,price⟩ := covers O stable (lt_of_not_ge few)
    obtain ⟨good',eq⟩ := old r hr g
    exact ⟨r,by omega,good',eq.le.trans price⟩
