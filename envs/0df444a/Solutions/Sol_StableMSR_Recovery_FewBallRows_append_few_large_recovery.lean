-- Prove2me | solution 1 for StableMSR.Recovery.FewBallRows.append_few_large_recovery
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T23:36:47.754866+00:00
-- url     : https://prove2.me/submissions/16ca1953-b3a8-42a9-8778-690c52ac5e63

import Theorems.Thm_StableMSR_Recovery_FewBallRows_extend_by_short_rows
import Theorems.Thm_StableMSR_Recovery_FewBallRows_tabulate_ball_row_expressions
import Theorems.Thm_StableMSR_Recovery_FewBallRows_row_decoder_expression
import Theorems.Thm_StableMSR_Recovery_FewBallRows_relation_ball_certificate
import Theorems.Thm_StableMSR_Recovery_FewBallRows_few_ball_seed_completeness
import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
open Polynomial
theorem solution : ∃p : Polynomial ℕ,∀h : ℕ,∃cmd : Cmd,∀(x : World) (s : Store),
    1 ≤ x.k → x.k < x.n → h < x.k → IsMetricArray x.dist → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z ≤ p.eval (x.cap + rows x.n (h+1)) ∧
    let y := worldOf x.k (x.rows + rows x.n (h+1)) x.dist t
    Ready y t ∧ (endpoints x → endpoints y) ∧
    (∀r < x.rows,good x r → good y r ∧ score y r=score x r) ∧
    ∀(e : ℝ),0 < e → e < 1 → ∀O,Stable x.dist x.k (1+e) O →
      (largeClusters x.dist O e).card ≤ h →
      ∃u < rows x.n (h+1),good y (x.rows+u) ∧ score y (x.rows+u)=cost x.dist O := by
  classical
  obtain ⟨p,gen⟩ := extend_by_short_rows
  obtain ⟨q,post,applyPost⟩ := tabulate_ball_row_expressions transformed row_decoder_expression
  refine ⟨p+q,?_⟩;intro h
  obtain ⟨build,hb⟩ := gen h
  refine ⟨.seq build post,?_⟩;intro x s kpos kn hk metric ready
  have np : 0 < x.n := by omega
  let F := rows x.n (h+1)
  obtain ⟨v,z,ev,tz,rv,word,cut,pre,raw⟩ := hb x s np hk kn.le ready
  let mid := worldOf x.k (x.rows+F) x.dist v
  obtain ⟨t,z',et,tz',rt,out⟩ := applyPost mid v rv
  let y := worldOf x.k (x.rows+F) x.dist t
  have cut' : cutoff mid=x.rows := by unfold cutoff;change ((worldOf x.k (x.rows+F) x.dist v).mem 2).toNat=_;rw [cut];simp
  have word' : (mid.mem 1).toNat=h := by change ((worldOf x.k (x.rows+F) x.dist v).mem 1).toNat=_;rw [word];simp
  have before {r : ℕ} (hr : r < x.rows) {j : ℕ} (hj : j < x.k) :
      center y r j=center x r j ∧ witness y r j=witness x r j := by
    have lt : r < mid.rows := by change r < x.rows+F;omega
    obtain ⟨c,w⟩ := out r lt j hj
    obtain ⟨a,b⟩ := pre r hr j hj
    exact ⟨c.trans (by simpa [transformed,cut',hr] using a),w.trans (by simpa [transformed,cut',hr] using b)⟩
  have after {r : ℕ} (hr : x.rows ≤ r) (lt : r < mid.rows) : encoded mid y r (storedRel mid r) := by
    intro j hj
    obtain ⟨c,w⟩ := out r lt j hj
    change center y r j=transformed mid r j false at c
    change witness y r j=transformed mid r j true at w
    exact ⟨by simpa [transformed,cut',not_lt.mpr hr] using c,by simpa [transformed,cut',not_lt.mpr hr] using w⟩
  have bounds := fun r=> (relation_ball_certificate mid np (storedRel mid r)).1
  refine ⟨t,_,Executes.seq ev et,?_,rt,?_,?_,?_⟩
  · have cap : mid.cap=x.cap+F := by simp [mid,World.cap,worldOf];omega
    rw [cap] at tz';simp only [eval_add];exact Nat.add_le_add tz tz'
  · intro ends r hr j hj
    by_cases lt : r < x.rows
    · obtain ⟨c,w,cp,wp⟩ := ends r lt j hj
      exact ⟨c,w,(before lt hj).1.trans cp,(before lt hj).2.trans wp⟩
    · obtain ⟨c,w,cp,wp⟩ := bounds r j
      have e := after (by omega) hr j hj
      exact ⟨c,w,e.1.trans cp,e.2.trans wp⟩
  · intro r hr g
    have price (j : ℕ) (hj : j < x.k) : charge y r j=charge x r j := by
      rw [charge,(before hr hj).1,(before hr hj).2];rfl
    refine ⟨⟨?_,?_⟩,Finset.sum_congr rfl (fun j hj=>price j (Finset.mem_range.mp hj))⟩
    · intro j hj l hl eq
      exact g.1 j hj l hl (by rwa [←(before hr hj).1,←(before hr hl).1])
    · intro i hi;obtain ⟨j,hj,hit⟩ := g.2 i hi
      refine ⟨j,hj,?_⟩;rw [hits,(before hr hj).1,price j hj];exact hit
  · intro e he hlt O stable small
    obtain ⟨u,hu,match'⟩ := few_ball_seed_completeness x h kpos kn hk metric e he hlt O stable small
    let r := x.rows+u
    have lt : r < mid.rows := by dsimp [r,mid,worldOf];change u < F at hu;omega
    have code (j : ℕ) (hj : j ≤ h) : center mid r j=(digit x.n u (2*j):ℤ) ∧ witness mid r j=(digit x.n u (2*j+1):ℤ) :=
      raw u hu j hj
    let sHit (j i : ℕ) := hits mid r i j
    let dHit (j i : ℕ) := MinSumFPT.oracleAnswer x.dist (digit x.n u (2*j):ℤ) (i:ℤ) ≤
      MinSumFPT.oracleAnswer x.dist (digit x.n u (2*j):ℤ) (digit x.n u (2*j+1):ℤ)
    have val (j i : ℕ) (hj : j ≤ h) : sHit j i ↔ dHit j i := by
      dsimp [sHit,hits,charge,dHit];rw [(code j hj).1,(code j hj).2];rfl
    have one (i : ℕ) : (∃j < x.k,(0 < j ∧ j ≤ h) ∧ sHit j i) ↔ ∃j < x.k,(0 < j ∧ j ≤ h) ∧ dHit j i := by
      constructor <;> rintro ⟨j,hk,hj,hi⟩
      · exact ⟨j,hk,hj,(val j i hj.2).mp hi⟩
      · exact ⟨j,hk,hj,(val j i hj.2).mpr hi⟩
    have two (i l : ℕ) : (∃j < x.k,(0 < j ∧ j ≤ h) ∧ sHit j i ∧ sHit j l) ↔
        ∃j < x.k,(0 < j ∧ j ≤ h) ∧ dHit j i ∧ dHit j l := by
      constructor <;> rintro ⟨j,hk,hj,hi,hl⟩
      · exact ⟨j,hk,hj,(val j i hj.2).mp hi,(val j l hj.2).mp hl⟩
      · exact ⟨j,hk,hj,(val j i hj.2).mpr hi,(val j l hj.2).mpr hl⟩
    have same (i l : ℕ) : storedRel mid r i l ↔ digitRel x h u i l := by
      unfold storedRel;rw [word'];change
        ((∃j < x.k,(0 < j ∧ j ≤ h) ∧ sHit j i ∧ sHit j l) ∨
          (¬∃j < x.k,(0 < j ∧ j ≤ h) ∧ sHit j i) ∧ (¬∃j < x.k,(0 < j ∧ j ≤ h) ∧ sHit j l) ∧
          distAt mid i l ≤ MinSumFPT.oracleAnswer mid.dist (center mid r 0) (witness mid r 0)) ↔ _
      rw [two,one,one,(code 0 (Nat.zero_le _)).1,(code 0 (Nat.zero_le _)).2];rfl
    have sm : FewBallRows.exact O (storedRel mid r) := fun i j=>(same i.val j.val).trans (match' i j)
    refine ⟨u,hu,?_⟩
    exact (relation_ball_certificate mid np (storedRel mid r)).2 O stable.1 sm y.mem r
      (after (by dsimp [r];omega) lt)
