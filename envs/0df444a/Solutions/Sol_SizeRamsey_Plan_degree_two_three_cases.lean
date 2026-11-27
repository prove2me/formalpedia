-- Prove2me | solution 1 for SizeRamsey.Plan.degree_two_three_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:24:09.003166+00:00
-- url     : https://prove2.me/submissions/3227ce3c-45dd-444d-8177-214f747a9384

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions

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
    (hcon : G.Connected)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    (∀ v, G.degree v = 2) ∨
    (∀ v, G.degree v = 3) ∨
    ∃ u v, G.Adj u v ∧
      G.degree u = 2 ∧ G.degree v = 3 := by
  by_cases h2 : ∀ v, G.degree v = 2
  · exact Or.inl h2
  by_cases h3 : ∀ v, G.degree v = 3
  · exact Or.inr (Or.inl h3)
  push Not at h2 h3
  obtain ⟨a, ha⟩ := h2
  obtain ⟨b, hb⟩ := h3
  have hb2 : G.degree b = 2 := (hdeg b).resolve_right hb
  obtain ⟨p⟩ := hcon.preconnected b a
  obtain ⟨⟨⟨x, y⟩, hxy⟩, -, hx, hy⟩ :=
    p.exists_boundary_dart {w | G.degree w = 2} hb2 ha
  exact Or.inr (Or.inr ⟨x, y, hxy, hx, (hdeg y).resolve_left hy⟩)
end SizeRamsey.Plan
