-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.limsup_vanishing_lower
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:14.426702+00:00
-- url     : https://prove2.me/submissions/1df1461e-384d-4594-ae28-94350f63eea9

import Mathlib
set_option autoImplicit false
open Filter Topology

theorem solution {α : Type} (F : Filter α) [F.NeBot] (A B g : α → ℝ)
    (hg : Tendsto g F (𝓝 0)) (hbound : ∀ᶠ x in F, A x + g x ≤ B x) :
    limsup (fun x => (A x : EReal)) F ≤ limsup (fun x => (B x : EReal)) F := by
  have hg' : Tendsto (fun x => (g x : EReal)) F (𝓝 0) := by
    simpa using (EReal.tendsto_coe.mpr hg)
  have hlim : liminf (fun x => (g x : EReal)) F = 0 := hg'.liminf_eq
  have hh := EReal.le_limsup_add (u := fun x => (A x : EReal)) (v := fun x => (g x : EReal)) (f := F)
  rw [hlim,add_zero] at hh
  have hmono : limsup ((fun x => (A x : EReal)) + (fun x => (g x : EReal))) F ≤
      limsup (fun x => (B x : EReal)) F := by
    apply Filter.limsup_le_limsup _
      (Filter.isCoboundedUnder_le_of_le F (x := ⊥) (fun _ => bot_le))
      (Filter.isBoundedUnder_of ⟨⊤,fun _ => le_top⟩)
    filter_upwards [hbound] with x hx
    change (A x : EReal) + (g x : EReal) ≤ (B x : EReal)
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr hx
  exact hh.trans hmono
