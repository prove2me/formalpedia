-- Prove2me | solution 1 for ShannonColouring.card_misses_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:33:32.01595+00:00
-- url     : https://prove2.me/submissions/57ac4768-a1ce-4edd-adb1-ccc41df679e8

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
public import Theorems.Thm_ShannonColouring_card_incident_le
public import Theorems.Thm_ShannonColouring_card_misses_add

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]
namespace ShannonColouring
theorem _root_.solution {k Δ : ℕ} {ends : ι → V × V} (hΔ : ∀ v, degree ends v ≤ Δ)
    (s : Finset ι) (c : ι → Fin k) (x : V) :
    k ≤ (Finset.univ.filter (Misses ends s c x)).card + Δ := by
  have h1 := card_misses_add ends s c x
  have h2 := card_incident_le ends s x
  have h3 := hΔ x
  omega
end ShannonColouring
