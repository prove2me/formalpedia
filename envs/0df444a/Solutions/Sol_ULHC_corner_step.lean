-- Prove2me | solution 1 for ULHC.corner_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:42:31.846168+00:00
-- url     : https://prove2.me/submissions/a28a6281-9478-4eff-8038-70a1d1dadbc4

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_inc_of_deg_two


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {K : Finset Pt} {x : Pt} {e1 e2 : Edge} {a1 b1 a2 b2 : Pt}
    (h1 : Ends e1 a1 b1) (h2 : Ends e2 a2 b2) (he1 : e1 ∈ F) (he2 : e2 ∈ F) (hne : e1 ≠ e2)
    (hd : deg F x = 2) (i1 : x = a1 ∨ x = b1) (i2 : x = a2 ∨ x = b2)
    (k1 : a1 ∈ K ∧ b1 ∈ K) (k2 : a2 ∈ K ∧ b2 ∈ K) : ∀ y, Adj F x y → y ∈ K := by
  intro y hxy
  obtain ⟨f, hf, hfe⟩ := hxy
  have hfx : f.p = x ∨ f.q = x := by
    rcases hfe with ⟨q, _⟩ | ⟨_, q⟩
    · exact Or.inl q
    · exact Or.inr q
  have hfy : f.p = y ∨ f.q = y := by
    rcases hfe with ⟨_, q⟩ | ⟨q, _⟩
    · exact Or.inr q
    · exact Or.inl q
  rcases inc_of_deg_two hd he1 ((h1.inc_iff x).2 i1) he2 ((h2.inc_iff x).2 i2) hne hf hfx with
    rfl | rfl
  · rcases (h1.inc_iff y).1 hfy with rfl | rfl
    · exact k1.1
    · exact k1.2
  · rcases (h2.inc_iff y).1 hfy with rfl | rfl
    · exact k2.1
    · exact k2.2
end ULHC
