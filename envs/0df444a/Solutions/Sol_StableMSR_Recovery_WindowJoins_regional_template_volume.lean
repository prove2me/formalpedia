-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.regional_template_volume
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:51:52.957806+00:00
-- url     : https://prove2.me/submissions/54f05a55-a0e3-44ea-b6cb-b980260531eb

import Theorems.Thm_StableMSR_Recovery_WindowCSP_window_tree_plan
import Definitions.Def_StableMSR_WindowJoinTemplates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery.TreeDP StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds
private lemma volumeBound (x : World) (e : ℝ) (he : 0< e) (hl : e<1) (hk : 1≤ x.k) (hn : x.k< x.n) :
    (2*x.n+1)*((bagBound x (budget e) (widthBound e))^3*(x.k+1)^2)≤ x.n^(70*parameterEnvelope e) := by
  let n:=x.n
  let m:=budget e+1
  let t:=widthBound e+1
  let E:=parameterEnvelope e
  have two : 2≤ n:=by dsimp [n];omega
  have own : 1≤ ownerBound e := by
    unfold ownerBound;apply Nat.le_floor
    norm_num
    exact (le_div_iff₀ he).mpr (by linarith)
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
  have c : x.k+1≤ n^2 := by
    have le:=Nat.mul_le_mul_right n two
    rw [pow_two]
    change x.k< n at hn;omega
  have g : 2*n+1≤ n^3 := by
    have a:=Nat.mul_le_mul_right n two
    have b:=Nat.mul_le_mul_right (n*n) two
    rw [pow_succ,pow_two]
    nlinarith
  have epos : 1≤ E:=by dsimp [E,parameterEnvelope];omega
  calc
    _ ≤ n^3*((n^(20*E))^3*(n^2)^2) :=
      Nat.mul_le_mul g (Nat.mul_le_mul (Nat.pow_le_pow_left bag 3) (Nat.pow_le_pow_left c 2))
    _ = n^(3+(20*E)*3+2*2) := by rw [←Nat.pow_mul,←Nat.pow_mul,←Nat.pow_add,←Nat.pow_add] <;> congr 1 <;> omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
private lemma rootChoices {V X : Type} {p : Plan V X} {B : ℕ} (bd : p.AllData (fun d=>d.choices.card≤ B)) : p.root.choices.card≤ B:=by
  cases p with
  | leaf d=>exact bd
  | branch d l r=>exact bd.1
private lemma countSlots {V X : Type} (k B : ℕ) (pb : 1≤ B) (p : Plan V X) (bd : p.AllData (fun d=>d.choices.card≤ B)) :
    templateSlots k p≤ p.nodes*(B^3*(k+1)^2):=by
  induction p with
  | leaf d =>
    have one:=Nat.pow_le_pow_right pb (show 1≤3 by decide)
    have plus : 0<(k+1)^2:=pow_pos (by omega) _
    change d.choices.card≤1*(B^3*(k+1)^2)
    have upper : B≤ B^3:=by simpa using one
    simpa only [one_mul] using bd.trans (upper.trans (Nat.le_mul_of_pos_right _ plus))
  | branch d L R il ir =>
    obtain ⟨da,bl,br⟩:=bd
    have cap:=Nat.mul_le_mul (Nat.mul_le_mul da (rootChoices bl)) (rootChoices br)
    have term:=Nat.mul_le_mul_right ((k+1)^2) cap
    have a:=il bl;have b:=ir br
    simp only [templateSlots,Plan.nodes,add_mul,one_mul];rw [show B^3=B*B*B by ring] at *;omega
private lemma reduceBound {V X : Type} (p : Plan V X) (B w : ℕ) (h : p.AllData (fun d=>d.bag.card≤ w ∧ d.choices.card≤ B)) :
    p.AllData (fun d=>d.choices.card≤ B):=by
  induction p with
  | leaf d=>exact h.2
  | branch d l r ih jh=>exact ⟨h.1.2,ih h.2.1,jh h.2.2⟩
theorem solution (x : World) (W : Cluster x.n) (R e : ℝ) (ep : 0< e) (el : e<1) (hk : 1≤ x.k) (hn : x.k< x.n)
    (tw : RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist R W) (widthBound e)) :
    ∃p : Plan ↥(greedyNet x.dist R W) (Partition x.n),realizesWindows x W R (budget e) (widthBound e) p ∧
      templateSlots x.k p≤ x.n^(70*parameterEnvelope e) := by
  obtain ⟨p,plan⟩:=window_tree_plan x W R (budget e) (widthBound e) tw
  let B:=bagBound x (budget e) (widthBound e)
  have pb : 1≤ B:=by unfold B bagBound;apply Nat.one_le_pow;omega
  have all:=reduceBound p B (widthBound e+1) plan.2.2.2.1
  refine ⟨p,plan,?_⟩
  exact (countSlots x.k B pb p all).trans ((Nat.mul_le_mul_right _ plan.2.2.1).trans (volumeBound x e ep el hk hn))
