-- Prove2me | solution 1 for StableMSR.Recovery.BallCoverCatalog.uniform_ball_cover_catalog
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:34:10.979874+00:00
-- url     : https://prove2.me/submissions/89b95ff7-dbdf-4eb2-9093-32d79144cfb2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_cartesian_row_machine
import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_cartesian_rows_certify_partitions
import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_singleton_cover_machine
import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_interior_ball_cover_catalog
import Definitions.Def_StableMSR_BallCoverCatalog
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial
open StableMSR.Recovery.BallCoverCatalog
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
open StableMSR.Recovery.CartesianBallRows
private def setup (B : ℕ) := Cmd.seq (.atom (.integerLoad 0 2)) (.seq (.atom (.pointerConst 1 1))
  (.seq (.atom (.integerLoad 1 1)) (.atom (.pointerConst 2 B))))
private def reset := Cmd.seq (.atom (.pointerConst 0 0)) (.seq (.atom (.pointerConst 1 0)) (.atom (.pointerConst 2 0)))
private lemma prepare {n : ℕ} (d : Point n→Point n→ℝ) (k B : ℕ) :
    ∃s,Executes d (setup B) (initialStore n k) s 4 ∧ s.ptrs 0=(n:ℤ) ∧
      s.ptrs 1=(k:ℤ) ∧ s.ptrs 2=(B:ℤ) ∧ Executes d reset s (initialStore n k) 3 := by
  let s := (Op.pointerConst 2 B).eval d ((Op.integerLoad 1 1).eval d ((Op.pointerConst 1 1).eval d
    ((Op.integerLoad 0 2).eval d (initialStore n k))))
  let t := (Op.pointerConst 2 0).eval d ((Op.pointerConst 1 0).eval d ((Op.pointerConst 0 0).eval d s))
  have endState : t=initialStore n k := by
    dsimp [t,s,Op.eval,initialStore]
    congr 1
    funext j
    by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;> simp [Function.update,h0,h1,h2]
  refine ⟨s,.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))),?_,?_,?_,?_⟩
  all_goals try solve | simp [s,Op.eval,initialStore,Function.update]
  rw [← endState]
  exact .seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))

theorem solution : ∃a b : ℕ,0 < a ∧ 0 < b ∧
    ∀e : ℚ,0 < e → e < 1 → ∃cmd : Cmd,HasCatalog e a b cmd := by
  obtain ⟨a,b,ha,hb,hard⟩ := interior_ball_cover_catalog
  obtain ⟨c,v,hc,hv,S,small⟩ := cartesian_row_machine
  obtain ⟨l,hl,D,diag⟩ := singleton_cover_machine
  let A := a+c+l
  let B := b+v+2
  refine ⟨A+20,B,by omega,by dsimp [B];omega,?_⟩
  intro e he he'
  obtain ⟨G,hG⟩ := hard e he he'
  let N := fewBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  let first := Cond.pointerLE 0 1
  let second := Cond.pointerLE 1 2
  let wrap := fun cmd=>Cmd.seq reset cmd
  refine ⟨.seq (setup N) (.ite first (wrap D) (.ite second (wrap S) (wrap G))),?_⟩
  intro n k d hk hn hm
  have npos : 0 < n := by omega
  have epos : 1 ≤ E := by unfold E parameterEnvelope;omega
  let K := n^(B*E)
  have kpos : 1 ≤ K := Nat.one_le_pow _ _ npos
  have nK : n ≤ K := by
    simpa using Nat.pow_le_pow_right npos (show 1 ≤ B*E from Nat.mul_pos (by dsimp [B];omega) epos)
  have reserve : A*K+11 ≤ (A+20)*K := by rw [Nat.add_mul A 20 K];omega
  have padding : A*K ≤ (A+20)*K := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨s,setupEx,p0,p1,p2,restore⟩ := prepare d k N
  by_cases eq : n=k
  · subst k
    obtain ⟨t,z,ez,tz,rd,ep,gu⟩ := diag n d npos hm
    have cond : first.test s := by change s.ptrs 0 ≤ s.ptrs 1;rw [p0,p1]
    have tt : z ≤ A*K := tz.trans (Nat.mul_le_mul (by dsimp [A];omega) nK)
    refine ⟨t,_,1,.seq setupEx (.ite_true cond (.seq restore ez)),?_,?_,rd,ep,?_⟩
    · apply le_trans _ reserve;omega
    · apply le_trans kpos;change K ≤ (A+20)*K;rw [Nat.add_mul];omega
    · intro O hO;exact gu O hO.1
  · have less : k < n := by omega
    have nfirst : ¬first.test s := by change ¬s.ptrs 0 ≤ s.ptrs 1;rw [p0,p1];omega
    by_cases ks : k ≤ N
    · obtain ⟨t,z,ez,tz,rd,pp⟩ := small n k d hk hn
      have cond : second.test s := by change s.ptrs 1 ≤ s.ptrs 2;rw [p1,p2];exact_mod_cast ks
      have kE : k+1 ≤ E := by unfold E parameterEnvelope;change k ≤ fewBound _ at ks;omega
      have bv : v ≤ B := by dsimp [B];omega
      have tt : z ≤ A*K := tz.trans (Nat.mul_le_mul (by dsimp [A];omega)
        (Nat.pow_le_pow_right npos (Nat.mul_le_mul bv kE)))
      have H : rows n k ≤ K := Nat.pow_le_pow_right npos (Nat.mul_le_mul (show 2 ≤ B by dsimp [B];omega) (by omega))
      obtain ⟨ends,cover⟩ := cartesian_rows_certify_partitions _ npos pp
      refine ⟨t,_,rows n k,.seq setupEx (.ite_false nfirst (.ite_true cond (.seq restore ez))),?_,?_,rd,ends,?_⟩
      · apply le_trans _ reserve;omega
      · apply H.trans;change K ≤ (A+20)*K;rw [Nat.add_mul];omega
      · intro O ho;obtain ⟨r,hr,g,eq⟩ := cover O ho.1;exact ⟨r,hr,g,eq.le⟩
    · obtain ⟨t,z,H,ez,tz,rr,rd,ep,gu⟩ := hG n k d hk less (by exact lt_of_not_ge ks) hm
      have cond : ¬second.test s := by change ¬s.ptrs 1 ≤ s.ptrs 2;rw [p1,p2];omega
      have mag : a*n^(b*parameterEnvelope (e:ℝ)) ≤ A*K := Nat.mul_le_mul (by dsimp [A];omega)
        (Nat.pow_le_pow_right npos (Nat.mul_le_mul_right E (by dsimp [B];omega)))
      refine ⟨t,_,H,.seq setupEx (.ite_false nfirst (.ite_false cond (.seq restore ez))),?_,?_,rd,ep,gu⟩
      · apply le_trans _ reserve;have := tz.trans mag;omega
      · exact (rr.trans mag).trans padding
