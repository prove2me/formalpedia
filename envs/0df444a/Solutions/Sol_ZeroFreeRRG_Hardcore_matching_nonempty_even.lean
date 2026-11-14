-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.matching_nonempty_even
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:27:57.403335+00:00
-- url     : https://prove2.me/submissions/a47ad47f-5c84-4495-b8fd-1292f2292b55

import Definitions.Def_AFIsingKS_Matching
import Mathlib
set_option autoImplicit false
open AFIsingKS

theorem solution (n d : ℕ) (he : Even (n*d)) : Nonempty (Matching n d) := by
  classical
  obtain ⟨k,hk⟩ := even_iff_two_dvd.mp he
  have hc : Fintype.card (Fin n × Fin d) = Fintype.card (Fin k × Bool) := by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  let e : (Fin n × Fin d) ≃ (Fin k × Bool) := Fintype.equivOfCardEq hc
  let p : Equiv.Perm (Fin n × Fin d) :=
    e.trans ((Equiv.prodCongr (Equiv.refl (Fin k)) Equiv.boolNot).trans e.symm)
  refine ⟨⟨p,?_,?_⟩⟩
  · intro x
    simp [p,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_map,Function.comp_def,Prod.map,Equiv.boolNot_apply]
  · intro x h
    have hh := congrArg e h
    have h' : (e x).2 = !(e x).2 := by
      have h' := congrArg Prod.snd hh
      simpa [p,Equiv.trans_apply,Equiv.prodCongr_apply,eq_comm] using h'
    cases (e x).2 <;> simp at h'
