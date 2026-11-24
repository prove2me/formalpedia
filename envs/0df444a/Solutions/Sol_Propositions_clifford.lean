-- Prove2me | solution 1 for Propositions.clifford
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:58:40.879568+00:00
-- url     : https://prove2.me/submissions/ee52a68a-e10a-4965-ba23-cdc759b8aad8

module
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Definitions.Def_ChipFiringWithLean_PalomarSolution
public import Theorems.Thm_clifford_theorem
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_gonality_geq_iff
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_rank_geq_iff
attribute [local simp] deg_one_chip
attribute [local simp] gonality_geq_iff
attribute [local simp] legal_set_empty


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
      0 ≤ r → 0 ≤ rdual → (r : ℚ) ≤ (deg D : ℚ) / 2 := by
  intro r rdual h_rank h_rankdual hr_nonneg hrdual_nonneg
  have hr : rank G D = r := rank_eq_rank G D r h_rank
  have hrdual : rank G (canonical_divisor G - D) = rdual :=
    rank_eq_rank G (canonical_divisor G - D) rdual h_rankdual
  have h_clifford := clifford_theorem h_conn D (by simpa [hr] using hr_nonneg)
    (by simpa [hrdual] using hrdual_nonneg)
  rw [hr] at h_clifford
  exact h_clifford
end Propositions
