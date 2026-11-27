-- Prove2me | solution 1 for SizeRamsey.Plan.erase_degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:29.582988+00:00
-- url     : https://prove2.me/submissions/ee7b1958-6436-4c14-ad78-0a649bfb22bf

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_induce_degree_eq

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (D : Finset V) (v : {x : V // x ∉ D}) :
    (erase G D).degree v = ((G.neighborFinset v.val).filter (· ∉ D)).card := by
  convert induce_degree_eq G {x | x ∉ D} v using 2
  · rfl
  · rfl
  · ext w; simp
end SizeRamsey.Plan
