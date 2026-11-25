-- Prove2me | solution 1 for ShannonColouring.card_misses_ge_of_incident
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:22:31.20392+00:00
-- url     : https://prove2.me/submissions/ee04790b-8ccc-4987-995d-5661807ae2c2

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
public import Theorems.Thm_ShannonColouring_card_incident_lt
public import Theorems.Thm_ShannonColouring_card_misses_add

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]
namespace ShannonColouring
theorem _root_.solution {k Δ : ℕ} {ends : ι → V × V} (hΔ : ∀ v, degree ends v ≤ Δ)
    {s : Finset ι} {e : ι} (he : e ∉ s) (c : ι → Fin k) {x : V} (hex : Incident ends e x) :
    k + 1 ≤ (Finset.univ.filter (Misses ends s c x)).card + Δ := by
  have h1 := card_misses_add ends s c x
  have h2 := card_incident_lt ends he hex
  have h3 := hΔ x
  omega
end ShannonColouring
