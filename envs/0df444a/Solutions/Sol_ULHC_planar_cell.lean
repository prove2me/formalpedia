-- Prove2me | solution 1 for ULHC.planar_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:06.274079+00:00
-- url     : https://prove2.me/submissions/7e1b8be2-cc65-482e-8f40-195127b6c8b8

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
import Theorems.Thm_ULHC_stepFlow_ne_zero
import Theorems.Thm_ULHC_flowL_ne_zero
import Theorems.Thm_ULHC_rot_balanced
import Theorems.Thm_ULHC_rot_supp_of
import Theorems.Thm_ULHC_pot_around
import Theorems.Thm_ULHC_chain_reach
import Theorems.Thm_ULHC_unit_shared
import Theorems.Thm_ULHC_adj_right_mem
import Theorems.Thm_ULHC_adj_up_mem
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Adj_unit
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_outflow_add
import Theorems.Thm_ULHC_outflow_flowL
import Theorems.Thm_ULHC_outflow_step
import Theorems.Thm_ULHC_pot_jump
import Theorems.Thm_ULHC_unit_cases
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (G : Finset Edge) (x y : ℤ)
    (hb : bot (x, y) ∉ G) (hl : lft (x, y) ∉ G)
    (h1 : Conn G (x + 1, y) (x, y + 1)) (h2 : Conn G (x + 1, y + 1) (x, y))
    (h3 : ¬ Conn G (x, y) (x + 1, y)) : False := by
  -- Corners.
  set a : Pt := (x, y) with ha
  set b : Pt := (x + 1, y) with hbdef
  set d : Pt := (x, y + 1) with hd
  set k : Pt := (x + 1, y + 1) with hk
  obtain ⟨pl, hpc, hpl⟩ := List.exists_isChain_cons_of_relationReflTransGen h1
  obtain ⟨ql, hqc, hql⟩ := List.exists_isChain_cons_of_relationReflTransGen h2
  -- The closed chain b → … → d → a → b and its flow.
  let f : Edge → ℤ := fun e => flowL b pl e + stepFlow d a e + stepFlow a b e
  let Lst : List Pt := a :: d :: b :: pl
  have hunit_p : List.IsChain Unit (b :: pl) := hpc.imp (fun _ _ h => h.unit)
  have hout : ∀ z, outflow f z = 0 := by
    intro z
    have e1 : f = fun e => (fun e => flowL b pl e + stepFlow d a e) e + stepFlow a b e := rfl
    rw [e1, outflow_add, outflow_add, outflow_flowL b pl hunit_p,
      outflow_step d a z (by simp [Unit, d, a]), outflow_step a b z (by simp [Unit, a, b]), hpl]
    ring
  have hfmem : ∀ e, f e ≠ 0 → e.p ∈ Lst ∧ e.q ∈ Lst := by
    intro e he
    by_cases f1 : flowL b pl e = 0
    · by_cases f2 : stepFlow d a e = 0
      · have f3 : stepFlow a b e ≠ 0 := by simp only [f] at he; rw [f1, f2] at he; simpa using he
        rcases stepFlow_ne_zero f3 with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> simp [Lst, q1, q2]
      · rcases stepFlow_ne_zero f2 with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> simp [Lst, q1, q2]
    · obtain ⟨q1, q2⟩ := flowL_ne_zero f1
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ q1),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ q2)⟩
  have hS : Supp (edgesAt Lst) (rot f) := rot_supp_of (fun e he => (hfmem e he).1)
  have hB : Balanced (rot f) := rot_balanced hout
  let P : Pt → ℤ := pot (edgesAt Lst) (rot f)
  -- Off the closed chain, the four edges at a point carry no flow.
  have hzero : ∀ z, z ∉ Lst →
      rot f (eR z) = 0 ∧ rot f (eU z) = 0 ∧ rot f (eL z) = 0 ∧ rot f (eD z) = 0 := by
    intro z hz
    have g : ∀ e : Edge, (e.p = z ∨ e.q = z) → rot f e = 0 := by
      intro e hez
      have : f e = 0 := by
        by_contra hne
        obtain ⟨q1, q2⟩ := hfmem e hne
        rcases hez with hez | hez
        · rw [hez] at q1; exact hz q1
        · rw [hez] at q2; exact hz q2
      unfold rot; cases e.d <;> simp [this]
    refine ⟨g _ (Or.inl rfl), g _ (Or.inl rfl), g _ (Or.inr ?_), g _ (Or.inr ?_)⟩ <;>
      simp [eL, eD, Edge.q]
  -- Classes: the closed chain minus `a` lies in `b`'s class; the chain from `k` in `a`'s.
  have hLb : ∀ z ∈ Lst, z ≠ a → Conn G b z := by
    intro z hz hza
    simp only [Lst, List.mem_cons] at hz
    rcases hz with hz | hz | hz | hz
    · exact absurd hz hza
    · rw [hz]; exact h1
    · rw [hz]; exact Conn.refl _ _
    · exact chain_reach hpc (List.mem_cons_of_mem _ hz)
  have hqa : ∀ z ∈ k :: ql, Conn G z a := by
    intro z hz
    have hkz : Conn G k z := chain_reach hqc hz
    exact Conn.trans hkz.symm h2
  have hmeet : ∀ z ∈ k :: ql, z ∈ Lst → z = a := by
    intro z hzq hzL
    by_contra hza
    exact h3 (Conn.trans (hqa z hzq).symm (hLb z hzL hza).symm)
  have hkL : k ∉ Lst := by
    intro hkL
    have := hmeet k (List.mem_cons_self) hkL
    simp [k, a] at this
  have haL : a ∈ Lst := List.mem_cons_self
  -- Walk the chain from `k` until it first meets the closed chain.
  have exit : ∀ (u : Pt) (l : List Pt), List.IsChain (Adj G) (u :: l) → u ∉ Lst →
      (u :: l).getLast (by simp) ∈ Lst →
      ∃ z z', Adj G z z' ∧ z ∉ Lst ∧ z' ∈ Lst ∧ z' ∈ u :: l ∧ P z = P u := by
    intro u l
    induction l generalizing u with
    | nil => intro _ hu hlast; simp at hlast; exact absurd hlast hu
    | cons v l ih =>
      intro hc hu hlast
      rw [List.isChain_cons_cons] at hc
      by_cases hv : v ∈ Lst
      · exact ⟨u, v, hc.1, hu, hv, by simp, rfl⟩
      · rw [List.getLast_cons_cons] at hlast
        obtain ⟨z, z', hzz, hz, hz', hmem, hP⟩ := ih v hc.2 hv hlast
        refine ⟨z, z', hzz, hz, hz', List.mem_cons_of_mem _ hmem, ?_⟩
        rw [hP]
        obtain ⟨s1, s2⟩ := unit_shared hc.1.unit
        have := pot_around hS hB (hzero u hu) s1
        have := pot_around hS hB (hzero v hv) s2
        simp only [P]
        linarith
  obtain ⟨z, z', hzz, hz, hz', hmem, hP⟩ := exit k ql hqc hkL (by rw [hql]; exact haL)
  have hz'a : z' = a := hmeet z' hmem hz'
  subst hz'a
  -- Values next to `a`.
  have aNotPl : a ∉ b :: pl := by
    intro h
    exact h3 (Conn.symm (chain_reach hpc h))
  have fl : f (lft (x, y)) = -1 := by
    have : flowL b pl (lft (x, y)) = 0 := by
      by_contra hne
      exact aNotPl (flowL_ne_zero hne).1
    show flowL b pl (lft (x, y)) + stepFlow d a (lft (x, y)) + stepFlow a b (lft (x, y)) = -1
    rw [this]; simp [stepFlow, lft, Edge.q, a, b, d]
  have fb : f (bot (x, y)) = 1 := by
    have : flowL b pl (bot (x, y)) = 0 := by
      by_contra hne
      exact aNotPl (flowL_ne_zero hne).1
    show flowL b pl (bot (x, y)) + stepFlow d a (bot (x, y)) + stepFlow a b (bot (x, y)) = 1
    rw [this]; simp [stepFlow, bot, Edge.q, a, b, d]
  have jl := pot_jump hS hB (lft (x, y))
  have jb := pot_jump hS hB (bot (x, y))
  simp only [lft, bot, Edge.hi_mk, Edge.lo_v, Edge.lo_h] at jl jb
  simp only [rot] at jl jb
  rw [show (⟨.v, (x, y)⟩ : Edge) = lft (x, y) from rfl, fl] at jl
  rw [show (⟨.h, (x, y)⟩ : Edge) = bot (x, y) from rfl, fb] at jb
  have hPk : P k = P (x, y) := (pot_around hS hB (hzero k hkL) (by simp [Around, k])).symm
  -- `z` is the left or lower neighbour of `a`.
  have hzv : z = (x - 1, y) ∨ z = (x, y - 1) := by
    obtain ⟨z1, z2⟩ := z
    rcases unit_cases hzz.unit with h | h | h | h <;>
      simp only [a, Prod.mk.injEq] at h
    · left; simp only [Prod.mk.injEq]; omega
    · exfalso; apply hb
      have e1 : z1 = x + 1 := by omega
      have e2 : z2 = y := by omega
      subst e1 e2; exact adj_right_mem hzz
    · right; simp only [Prod.mk.injEq]; omega
    · exfalso; apply hl
      have e1 : z1 = x := by omega
      have e2 : z2 = y + 1 := by omega
      subst e1 e2; exact adj_up_mem hzz
  rcases hzv with hzv | hzv <;> subst hzv <;> simp only [P] at hP hPk <;> linarith
end ULHC
