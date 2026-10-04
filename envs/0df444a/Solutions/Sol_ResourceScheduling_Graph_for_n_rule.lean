-- Prove2me | solution 1 for ResourceScheduling.Graph.for_n_rule
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:58:54.701257+00:00
-- url     : https://prove2.me/submissions/c5635282-baa9-4773-9193-5d99fb549228

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set
import Theorems.Thm_ResourceScheduling_Graph_ram_safe_laws
import Theorems.Thm_ResourceScheduling_Graph_ram_footprint
import Theorems.Thm_ResourceScheduling_Graph_ram_loop_invariant

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg

theorem solution (counter idx : GraphReg) (hc : n ≠ counter) (hi : idx ≠ n)
    (hic : idx ≠ counter) (p : GraphProgram.Code)
    (hw : p.writes n = false ∧ p.writes idx = false ∧ p.writes counter = false)
    (B N : ℕ) (P : ℕ → RAMState GraphReg → Prop)
    (hpc : ∀ k x a, P k (x.set counter a) ↔ P k x)
    (hpi : ∀ k x a, P k (x.set idx a) ↔ P k x)
    (s : RAMState GraphReg) (hs : RAMBound B s) (hn : s.val n = N) (hp : P 0 s)
    (hstep : ∀ k < N, ∀ x, RAMBound B x → x.val n = N → x.val idx = k → P k x →
      RAMSafe p B x ∧ P (k + 1) (p.eval x)) :
    RAMSafe (GraphProgram.forN counter idx hc p) B s ∧
      ((GraphProgram.forN counter idx hc p).eval s).val idx = N ∧
      ((GraphProgram.forN counter idx hc p).eval s).val counter = 0 ∧
      P N ((GraphProgram.forN counter idx hc p).eval s) := by
  have hNB : N ≤ B := hn ▸ hs.1 n
  let s1 := s.set counter N
  let s0 := s1.set idx 0
  let body : GraphProgram.Code := p.seq (.inc idx)
  let loop : GraphProgram.Code := .loop counter body
  let I := fun k x => RAMBound B x ∧ x.val n = N ∧ x.val idx = k ∧
    x.val counter = N - k ∧ P k x
  have hs1 : RAMBound B s1 := ram_bound_set B s hs counter N hNB
  have hs0 : RAMBound B s0 := ram_bound_set B s1 hs1 idx 0 (Nat.zero_le _)
  have hstart : I 0 s0 := by
    refine ⟨hs0, ?_, ?_, ?_, ?_⟩
    · simp [s0, s1, RAMState.set, hc, Ne.symm hi, hn]
    · simp [s0, RAMState.set]
    · simp [s0, s1, RAMState.set, Ne.symm hic]
    · exact (hpi 0 s1 0).2 ((hpc 0 s N).2 hp)
  have hrule := ram_loop_invariant counter body B N I s0 hs0
    (by simpa using hstart.2.2.2.1) hstart (by
      intro k hk x hx
      let xd := x.set counter (x.val counter - 1)
      have hxd : RAMBound B xd := ram_bound_set B x hx.1 counter _
        ((Nat.sub_le _ _).trans (hx.1.1 counter))
      have hxn : xd.val n = N := by simpa [xd, RAMState.set, hc] using hx.2.1
      have hxi : xd.val idx = k := by simpa [xd, RAMState.set, hic] using hx.2.2.1
      obtain ⟨hb, hp'⟩ := hstep k hk xd hxd hxn hxi ((hpc k x _).2 hx.2.2.2.2)
      let y := p.eval xd
      have hyn : y.val n = N := (ram_footprint p n hw.1 xd).trans hxn
      have hyi : y.val idx = k := (ram_footprint p idx hw.2.1 xd).trans hxi
      have hyc : y.val counter = N - k - 1 := by
        rw [show y.val counter = xd.val counter from ram_footprint p counter hw.2.2 xd]
        simp only [xd, RAMState.set, Function.update_self, hx.2.2.2.1]
      have hz := ram_bound_set B y hb.2 idx (y.val idx + 1) (by omega)
      refine ⟨⟨hb.1, hb.2⟩, hz, ?_, ?_, ?_, ?_⟩
      · change (y.set idx (y.val idx + 1)).val n = N
        simpa only [RAMState.set, Function.update_of_ne (Ne.symm hi)] using hyn
      · change (y.set idx (y.val idx + 1)).val idx = k + 1
        simpa only [RAMState.set, Function.update_self] using congrArg (· + 1) hyi
      · change (y.set idx (y.val idx + 1)).val counter = N - (k + 1)
        simp only [RAMState.set, Function.update_of_ne (Ne.symm hic), hyc]
        omega
      · exact (hpi (k + 1) y (y.val idx + 1)).2 hp')
  have he : (GraphProgram.forN counter idx hc p).eval s = loop.eval s0 := by
    simp [GraphProgram.forN, GraphProgram.block, RAMCode.eval, s0, s1, loop, body, hn]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hloop : RAMSafe loop B s0 := ⟨hrule.1, hrule.2.1⟩
    have hskip : RAMSafe (.skip : GraphProgram.Code) B (loop.eval s0) :=
      ⟨hrule.2.1, hrule.2.1⟩
    have htail := (ram_safe_laws loop .skip counter B s0).2.1 hloop hskip
    have hzero : RAMSafe (.zero idx : GraphProgram.Code) B s1 := ⟨hs1, hs0⟩
    have hmid := (ram_safe_laws (.zero idx) (loop.seq .skip) counter B s1).2.1 hzero htail
    have hcopy : RAMSafe (.copy n counter hc) B s := by
      exact ⟨hs, by simpa only [RAMCode.eval, hn] using hs1⟩
    have hall := (ram_safe_laws (.copy n counter hc) ((RAMCode.zero idx).seq (loop.seq .skip))
      counter B s).2.1 hcopy (by simpa only [RAMCode.eval, hn] using hmid)
    exact hall
  · rw [he]; exact hrule.2.2.2.1
  · rw [he]; simpa using hrule.2.2.2.2.1
  · rw [he]; exact hrule.2.2.2.2.2

#print axioms solution
