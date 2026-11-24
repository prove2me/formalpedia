-- Prove2me | solution 1 for Propositions.riemann_roch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:57:56.066429+00:00
-- url     : https://prove2.me/submissions/725814f5-00a3-49ee-b565-77a8875657c7

module
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Definitions.Def_ChipFiringWithLean_PalomarSolution
public import Theorems.Thm_rank_geq_iff
public import Theorems.Thm_riemann_roch_for_graphs

section
@[expose] public section
namespace Propositions
private lemma rank_eq_rank (G : CFGraph) (D : CFDiv G) (r : ℤ)
    (h : rank_eq G D r) : rank G D = r := by
  change rank_geq G D r ∧ ¬rank_geq G D (r + 1) at h
  rw [rank_geq_iff, rank_geq_iff] at h
  omega
end Propositions
end
end

set_option autoImplicit true
@[expose] public section
public section
open Propositions
namespace Propositions
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    ∀ r rdual : ℤ, rank_eq G D r → rank_eq G (canonical_divisor G - D) rdual →
      r - rdual = deg D + 1 - genus G := by
  intro r rdual h_rank h_rankdual
  have hr : rank G D = r := rank_eq_rank G D r h_rank
  have hrdual : rank G (canonical_divisor G - D) = rdual :=
    rank_eq_rank G (canonical_divisor G - D) rdual h_rankdual
  have h_rr := riemann_roch_for_graphs h_conn D
  rw [hr, hrdual] at h_rr
  linarith
end Propositions
