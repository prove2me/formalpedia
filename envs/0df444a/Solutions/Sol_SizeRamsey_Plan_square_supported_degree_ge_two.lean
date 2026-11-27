-- Prove2me | solution 1 for SizeRamsey.Plan.square_supported_degree_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:24:57.675258+00:00
-- url     : https://prove2.me/submissions/b2d42f8c-9644-4fa2-aef1-d0d929a0f1ed

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_two_le_degree_of_adj
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_adj_at
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_ne_at

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution
    (hs : SquareSupported G) (v : V)
    (hv : 0 < G.degree v) :
    2 ≤ G.degree v := by
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
  obtain ⟨g, hg, rfl, rfl⟩ := hs hw
  obtain ⟨-, -, -, h30⟩ := IsC4Map.adj_at G hg 0
  have hne := IsC4Map.ne_at G hg 0 (a := 1) (b := 3) (by decide)
  simp only [zero_add] at h30 hne
  exact two_le_degree_of_adj G hw h30.symm hne
end SizeRamsey.Plan
