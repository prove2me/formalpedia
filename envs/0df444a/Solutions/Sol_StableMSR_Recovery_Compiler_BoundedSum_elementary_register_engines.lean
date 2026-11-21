-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.BoundedSum.elementary_register_engines
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:10:22.134583+00:00
-- url     : https://prove2.me/submissions/dfb3609f-6192-4f0c-b729-e8598d92194d

import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
set_option maxHeartbeats 1600000
open scoped Classical
private def binaryCmd (o : Gate) (b : ℕ) : Cmd :=
  match o with
  | .add => .atom (.pointerAdd b b (b+1))
  | .cut => .ite (.pointerLE b (b+1)) (.atom (.pointerConst b 0)) (.atom (.pointerSub b b (b+1)))
  | .leFlag => .ite (.pointerLE b (b+1)) (.atom (.pointerConst b 1)) (.atom (.pointerConst b 0))
private lemma evalBinary {n : ℕ} (d : Point n→Point n→ℝ) (o : Gate) (b x y : ℕ) (s : Store)
    (hx : s.ptrs b=x) (hy : s.ptrs (b+1)=y) :
    ∃ t z, Executes d (binaryCmd o b) s t z ∧ Keeps b s t ∧ t.ptrs b=(o.val x y:ℤ) ∧ z ≤ 3 := by
  have guard : (Cond.pointerLE b (b+1)).test s ↔ x ≤ y := by simp [Cond.test,hx,hy]
  have keeps (v : ℤ) : Keeps b s {s with ptrs:=Function.update s.ptrs b v} :=
    ⟨fun i hi=>Function.update_of_ne (ne_of_lt hi) _ _,rfl⟩
  cases o with
  | add =>
    refine ⟨_,_,Executes.atom _ _,keeps _,?_,by decide⟩
    simp [Op.eval,Gate.val,hx,hy]
  | cut =>
    by_cases h : x ≤ y
    · refine ⟨_,_,Executes.ite_true (guard.mpr h) (Executes.atom _ _),keeps _,?_,by decide⟩
      simp [Op.eval,Gate.val,Nat.sub_eq_zero_of_le h]
    · refine ⟨_,_,Executes.ite_false (mt guard.mp h) (Executes.atom _ _),keeps _,?_,by decide⟩
      simp [Op.eval,Gate.val,hx,hy,Int.ofNat_sub (by omega : y ≤ x)]
  | leFlag =>
    by_cases h : x ≤ y
    · refine ⟨_,_,Executes.ite_true (guard.mpr h) (Executes.atom _ _),keeps _,?_,by decide⟩
      simp [Op.eval,Gate.val,h]
    · refine ⟨_,_,Executes.ite_false (mt guard.mp h) (Executes.atom _ _),keeps _,?_,by decide⟩
      simp [Op.eval,Gate.val,h]

theorem solution : (∀a : ℕ, Engine (fun _=>a)) ∧ (∀i : ℕ,Engine (fun ρ=>ρ i)) ∧
    ∀ (o : Gate) (f g : Env→ℕ), Engine f → Engine g → Engine (fun ρ=>o.val (f ρ) (g ρ)) := by
  refine ⟨?_,?_,?_⟩
  · intro a
    refine ⟨C (a+1),fun src b _=>⟨.atom (.pointerConst b a),?_⟩⟩
    intro n d s ρ M _ _
    exact ⟨_,1,.atom _ _,⟨fun i hi=>Function.update_of_ne (ne_of_lt hi) _ _,rfl⟩,
      Function.update_self ..,by simp,by simp⟩
  · intro j
    refine ⟨X+1,fun src b _=>⟨.atom (.pointerCopy b (src j)),?_⟩⟩
    intro n d s ρ M bound reads
    refine ⟨_,1,.atom _ _,⟨fun i hi=>Function.update_of_ne (ne_of_lt hi) _ _,rfl⟩,?_,by simp,?_⟩
    · simp [Op.eval,reads]
    · simp only [eval_add,eval_X,eval_one];have := bound j;omega
  · intro o f g hf hg
    obtain ⟨p,pa⟩ := hf
    obtain ⟨q,qa⟩ := hg
    refine ⟨p+q+C 4,?_⟩
    intro src b small
    obtain ⟨a,sa⟩ := pa src b small
    obtain ⟨c,sc⟩ := qa src (b+1) (fun j=>(small j).trans (Nat.lt_succ_self _))
    refine ⟨.seq a (.seq c (binaryCmd o b)),?_⟩
    intro n d s ρ M bound reads
    obtain ⟨s₁,t₁,h₁,k₁,v₁,tb₁,fb⟩ := sa n d s ρ M bound reads
    obtain ⟨s₂,t₂,h₂,k₂,v₂,tb₂,gb⟩ := sc n d s₁ ρ M bound (fun j=>(k₁.1 _ (small j)).trans (reads j))
    obtain ⟨s₃,t₃,h₃,k₃,v₃,tb₃⟩ := evalBinary d o b (f ρ) (g ρ) s₂ ((k₂.1 b (by omega)).trans v₁) v₂
    refine ⟨s₃,_,.seq h₁ (.seq h₂ h₃),⟨fun i hi=> (k₃.1 i hi).trans
      ((k₂.1 i (by omega)).trans (k₁.1 i hi)),k₃.2.trans (k₂.2.trans k₁.2)⟩,v₃,?_,?_⟩
    · simp only [eval_add,eval_C];omega
    · simp only [eval_add,eval_C]
      cases o <;> simp [Gate.val] <;> (try split_ifs) <;> omega

