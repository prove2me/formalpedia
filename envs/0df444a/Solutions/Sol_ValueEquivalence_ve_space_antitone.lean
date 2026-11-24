-- Prove2me | solution 1 for ValueEquivalence.ve_space_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:28:28.622033+00:00
-- url     : https://prove2.me/submissions/096e3bbb-8fc5-4e1b-ba65-e58d3ba6ea7e

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

set_option autoImplicit false

open Filter Topology

open ValueEquivalence

theorem solution {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A)
    (Pol Pol' : Set (S → A → ℝ)) (V V' : Set (S → ℝ)) (hPol : Pol ⊆ policies)
    (hPol' : Pol' ⊆ Pol) (hV' : V' ⊆ V) :
    veSpace γ M mstar Pol V ⊆ veSpace γ M mstar Pol' V' := by
  rintro m ⟨hm, hve⟩
  exact ⟨hm, fun π hπ v hv => hve π (hPol' hπ) v (hV' hv)⟩
