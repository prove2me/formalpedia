-- Prove2me | solution 1 for StableMSR.Recovery.FewBallRows.dense_ball_cover_catalog
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T13:13:34.519182+00:00
-- url     : https://prove2.me/submissions/f116206f-e457-4c41-81ee-42be6c2d9962

import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_dense_factorized_regional_catalog
import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_decode_regional_menus
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
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
      1 ≤ k → k < n → fewBound (e:ℝ) < k → IsMetricArray d → denseSpec e a b cmd n k d := by
  obtain ⟨a,b,ha,hb,gen⟩:=dense_factorized_regional_catalog
  obtain ⟨p,post,runPost⟩:=decode_regional_menus
  obtain ⟨c,D,cp⟩:=capPoly p
  refine ⟨a+c*(a+3)^D+1,b*(D+1),by omega,Nat.mul_pos hb (by omega),?_⟩
  intro e he he'
  obtain ⟨cmd,run⟩:=gen e he he'
  refine ⟨.seq cmd post,?_⟩
  intro n k d hk hn hlarge metric
  obtain ⟨s,z,H,ez,tz,hH,rs,shape',localOpt⟩:=run n k d hk hn hlarge metric
  let x:=worldOf k H d s
  obtain ⟨t,l,el,tl,rt,ep,decode⟩:=runPost x s hk (by change 0<n;omega) shape' rs
  have budget:=combineTime a b c D n k H (parameterEnvelope (e:ℝ)) z l (by omega) hn.le hb
    (by unfold parameterEnvelope;omega) tz hH (tl.trans (cp x.cap (by unfold World.cap;omega)))
  have total : a*n^(b*parameterEnvelope (e:ℝ))≤(a+c*(a+3)^D+1)*n^((b*(D+1))*parameterEnvelope (e:ℝ)) := by
    apply Nat.mul_le_mul (by omega)
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right b (by omega))
  refine ⟨t,_,H,.seq ez el,by omega,hH.trans total,rt,ep,?_⟩
  intro O stable many
  obtain ⟨v,hv,cert,u,path,bound⟩:=localOpt O stable many
  obtain ⟨good',le⟩:=decode v hv cert u path
  exact ⟨v,cert.1,good',le.trans bound⟩

