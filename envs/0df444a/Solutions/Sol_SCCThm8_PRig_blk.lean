-- Prove2me | solution 1 for SCCThm8.PRig.blk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:03:25.634664+00:00
-- url     : https://prove2.me/submissions/e0b9817b-8964-4a0a-b33d-97df719f918b

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
public import Theorems.Thm_SCCThm8_PRig_D_spec

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function
variable {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
namespace SCCThm8.PRig
theorem _root_.solution (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) (A₀ : Fin m → Finset (Fin (3 * k)))
    (hA₀ : ∀ j, (A₀ j).card = k) (j : Fin m) :
    ∀ X : Finset (Fin (3 * k)), X.card = k → ∀ s t, s ∈ X → t ∉ X →
      f₁ (update A₀ j (sw X s t)) = D k f₁ j s t * f₁ (update A₀ j X) := by
  intro X hX s t hs ht
  have hv : ∀ j', (update A₀ j X j').card = k := by
    intro j'; rcases eq_or_ne j' j with rfl | h' <;> simp [*]
  have := D_spec hk hP (update A₀ j X) hv j s t (by simpa using hs) (by simpa using ht)
  simpa using this
end SCCThm8.PRig
