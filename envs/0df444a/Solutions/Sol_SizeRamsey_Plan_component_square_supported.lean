-- Prove2me | solution 1 for SizeRamsey.Plan.component_square_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:03.145555+00:00
-- url     : https://prove2.me/submissions/87e31956-7a35-4c03-9358-86b458151706

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_induce_mk


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
    (hsq : SquareSupported G) (C : G.ConnectedComponent) :
    SquareSupported (compGraph G C) := by
  intro a b hab
  obtain ⟨f, hf, h0, h1⟩ := hsq (show G.Adj a.val b.val from hab)
  have hmem : ∀ i, f i ∈ C.supp := by
    obtain ⟨_, h01, h12, h23, h30⟩ := hf
    have m0 : f 0 ∈ C.supp := h0 ▸ a.2
    have m1 : f 1 ∈ C.supp := (C.mem_supp_congr_adj h01).mp m0
    have m2 : f 2 ∈ C.supp := (C.mem_supp_congr_adj h12).mp m1
    have m3 : f 3 ∈ C.supp := (C.mem_supp_congr_adj h23).mp m2
    intro i; fin_cases i
    exacts [m0, m1, m2, m3]
  exact ⟨_, IsC4Map.induce_mk hf hmem, Subtype.ext h0, Subtype.ext h1⟩
end SizeRamsey.Plan
