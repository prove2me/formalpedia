-- Prove2me | solution 1 for ULHC.phase1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:16:33.104714+00:00
-- url     : https://prove2.me/submissions/91566f90-3fc6-4c28-a223-7b4beee53988

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
import Theorems.Thm_ULHC_sideEdge_nb_opp
import Theorems.Thm_ULHC_outArc_nb_opp
import Theorems.Thm_ULHC_D_mono
import Theorems.Thm_ULHC_Good_step
import Theorems.Thm_ULHC_Good_isCell
import Theorems.Thm_ULHC_nb_nb_opp
import Theorems.Thm_ULHC_sig_spec
import Theorems.Thm_ULHC_uniq_of_out
import Theorems.Thm_ULHC_stop_of_not_out
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_mem_cells
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P) (hT : NoTypeIII V F)
  (o : Bool)
include hF hH hs hB hT
namespace ULHC
theorem _root_.solution (v : Pt) (s0 : Side) (hcut : Cut P (sideEdge v s0)) (hin : outArc F v s0 = !o)
    (hjump : if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2)
    (hgood : Good o (D F H v)) :
    ∃ w, IsCell V w ∧ Good o (D F H w) ∧ Stop F P o w := by
  set u := nb v s0
  let wk : ℕ → Pt := fun k => (sig F P o)^[k] v
  have wk0 : wk 0 = v := rfl
  have wks : ∀ k, wk (k + 1) = sig F P o (wk k) := fun k => Function.iterate_succ_apply' _ _ _
  -- Invariant along the walk.
  have inv : ∀ k, (∀ i < k, Out F P o (wk i)) →
      Entered F P o (wk k) ∧ Good o (D F H (wk k)) ∧
        (if o then D F H v ≤ D F H (wk k) else D F H (wk k) ≤ D F H v) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⟨s0, hcut, hin⟩, hgood, ?_⟩
      rw [wk0]; cases o <;> simp
    | succ k ih =>
      intro hall
      obtain ⟨_, hg, hm⟩ := ih (fun i hi => hall i (by omega))
      obtain ⟨so, hsig, hc, ho⟩ := sig_spec o (hall k (by omega))
      rw [wks, hsig]
      refine ⟨⟨so.opp, by rw [sideEdge_nb_opp]; exact hc, by rw [outArc_nb_opp, ho]⟩,
        Good.step hF hH ho hg, ?_⟩
      have := D_mono hF hH o (wk k) so ho
      cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hm this ⊢ <;> omega
  set N := (cells V).card
  by_cases hall : ∀ k ≤ N, Out F P o (wk k)
  · exfalso
    -- No cell repeats.
    have inj : ∀ i j, i < j → j ≤ N → wk i ≠ wk j := by
      intro i
      induction i with
      | zero =>
        intro j hj hjN heq
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨so, hsig, hc, ho⟩ := sig_spec o (hall j' (by omega))
        rw [wk0, wks, hsig] at heq
        -- `v` is entered from `wk j'` through `so.opp`, and from `u` through `s0`.
        have uniq := uniq_of_out hF hB hT o (Good.isCell hF hH hs hgood) s0 hcut hin
          (by have := hall 0 (by omega); rwa [wk0] at this)
        have e := uniq s0 so.opp hcut hin
          (by rw [heq, sideEdge_nb_opp]; exact hc) (by rw [heq, outArc_nb_opp, ho])
        have hwu : wk j' = u := by
          rw [show u = nb v s0 from rfl, e, heq, nb_nb_opp]
        obtain ⟨_, _, hm⟩ := inv j' (fun i hi => hall i (by omega))
        rw [hwu] at hm
        cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hm hjump <;> omega
      | succ i ih =>
        intro j hij hjN heq
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨so1, hs1, hc1, ho1⟩ := sig_spec o (hall i (by omega))
        obtain ⟨so2, hs2, hc2, ho2⟩ := sig_spec o (hall j' (by omega))
        rw [wks, wks, hs1, hs2] at heq
        set z := nb (wk i) so1
        have hzc := (inv (i + 1) (fun k hk => hall k (by omega))).2.1
        rw [wks, hs1] at hzc
        have uniq := uniq_of_out hF hB hT o (Good.isCell hF hH hs hzc) so1.opp
          (by rw [sideEdge_nb_opp]; exact hc1) (by rw [outArc_nb_opp, ho1])
          (by have := hall (i + 1) (by omega); rwa [wks, hs1] at this)
        have e := uniq so1.opp so2.opp (by rw [sideEdge_nb_opp]; exact hc1)
          (by rw [outArc_nb_opp, ho1]) (by rw [heq, sideEdge_nb_opp]; exact hc2)
          (by rw [heq, outArc_nb_opp, ho2])
        apply ih j' (by omega) (by omega)
        have h1 : nb z so1.opp = wk i := nb_nb_opp _ _
        have h2 : nb z so2.opp = wk j' := by rw [heq, nb_nb_opp]
        rw [← h1, ← h2, e]
    -- Pigeonhole.
    have hmaps : ∀ k ∈ Finset.range (N + 1), wk k ∈ cells V := by
      intro k hk
      rw [Finset.mem_range] at hk
      exact mem_cells.2 (Good.isCell hF hH hs
        (inv k (fun i hi => hall i (by omega))).2.1)
    have hinj : Set.InjOn wk (Finset.range (N + 1)) := by
      intro i hi j hj heq
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact inj i j h (by omega) heq
      · exact inj j i h (by omega) heq.symm
    have := Finset.card_le_card_of_injOn wk hmaps hinj
    simp only [Finset.card_range] at this
    omega
  · push Not at hall
    obtain ⟨k, hkN, hk⟩ := hall
    -- The first cell with no way out.
    have ex : ∃ k, ¬ Out F P o (wk k) := ⟨k, hk⟩
    let k0 := Nat.find ex
    have hk0 : ¬ Out F P o (wk k0) := Nat.find_spec ex
    have hbefore : ∀ i < k0, Out F P o (wk i) := fun i hi => by
      have := Nat.find_min ex hi; push Not at this; exact this
    obtain ⟨he, hg, _⟩ := inv k0 hbefore
    have hc := Good.isCell hF hH hs hg
    exact ⟨wk k0, hc, hg, stop_of_not_out hF hB hT o hc he hk0⟩
end ULHC
