-- Prove2me | solution 1 for SimpleGraph.exists_isEulerian_of_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:59:23.604453+00:00
-- url     : https://prove2.me/submissions/cbe08069-61be-4d5d-998d-37c21e311e98

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
public import Theorems.Thm_SimpleGraph_exists_closed_trail_avoiding
public import Theorems.Thm_SimpleGraph_exists_mem_support_adj_not_mem_edges


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (hconn : G.Connected) {a b : V}
    (h : ∀ x, Even (G.degree x) ↔ (a ≠ b → x ≠ a ∧ x ≠ b)) :
    ∃ p : G.Walk a b, p.IsEulerian := by
  by_contra hno
  -- Todo trail `a → b` se extiende a uno más largo.
  have ext : ∀ p : G.Walk a b, p.IsTrail → ∃ q : G.Walk a b, q.IsTrail ∧ p.length < q.length := by
    intro p hp
    obtain ⟨x, hx, y, hxy, hnot⟩ :=
      exists_mem_support_adj_not_mem_edges hconn hp fun he => hno ⟨p, he⟩
    have hpar : ∀ z, Even (p.edges.countP fun e => z ∈ e) ↔ Even (G.degree z) := fun z => by
      rw [hp.even_countP_edges_iff, h]
    obtain ⟨c, hc, hcpos, hcdisj⟩ := exists_closed_trail_avoiding hp.edges_nodup
      (fun e he => p.edges_subset_edgeSet he) hpar hxy hnot
    have hedges : p.edges = (p.takeUntil x hx).edges ++ (p.dropUntil x hx).edges := by
      rw [← edges_append, p.take_spec hx]
    have hlen : p.length = (p.takeUntil x hx).length + (p.dropUntil x hx).length := by
      rw [← length_append, p.take_spec hx]
    refine ⟨(p.takeUntil x hx).append (c.append (p.dropUntil x hx)), ?_, ?_⟩
    · have hperm : List.Perm ((p.takeUntil x hx).edges ++ (c.edges ++ (p.dropUntil x hx).edges))
          (c.edges ++ p.edges) := by
        rw [hedges, ← List.append_assoc, ← List.append_assoc]
        exact List.perm_append_comm.append_right _
      rw [isTrail_def, edges_append, edges_append, hperm.nodup_iff]
      exact List.nodup_append.mpr
        ⟨hc.edges_nodup, hp.edges_nodup, fun e he e' he' hee => hcdisj e he (hee ▸ he')⟩
    · rw [length_append, length_append]
      omega
  -- Existe algún trail `a → b`.
  have h0 : ∃ p : G.Walk a b, p.IsTrail := by
    obtain ⟨q⟩ := hconn.preconnected a b
    exact ⟨q.bypass, q.bypass_isPath.isTrail⟩
  have key : ∀ k : ℕ, ∃ q : G.Walk a b, q.IsTrail ∧ k ≤ q.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨p, hp⟩ := h0
      exact ⟨p, hp, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨q, hq, hk⟩ := ih
      obtain ⟨q', hq', hlt⟩ := ext q hq
      exact ⟨q', hq', by omega⟩
  obtain ⟨q, hq, hk⟩ := key (G.edgeFinset.card + 1)
  have := hq.length_le_card_edgeFinset
  omega
end SimpleGraph
