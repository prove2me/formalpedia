-- Prove2me | solution 1 for R03DescentCertificateM2.reaches_zero
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:22:04.536402+00:00
-- url     : https://prove2.me/submissions/a556b3b5-ed93-4631-85dc-e697380ec381

import Mathlib.Logic.Relation

/- Candidate-only certificate soundness. This does not provide an R03
   graph certificate or an independently frozen challenge. -/
set_option Elab.async false
namespace R03DescentCertificateM2


end R03DescentCertificateM2

open R03DescentCertificateM2
theorem solution {S : Type} (rank height : S → Nat) (next : S → S)
    (step : S → S → Prop)
    (cert : ∀ s, height s ≠ 0 →
      step s (next s) ∧ height (next s) ≤ height s ∧ rank (next s) < rank s) :
    ∀ s, ∃ t, Relation.ReflTransGen
      (fun u v => step u v ∧ height v ≤ height u) s t ∧ height t = 0 := by
  have aux : ∀ n, ∀ s, rank s = n → ∃ t, Relation.ReflTransGen
      (fun u v => step u v ∧ height v ≤ height u) s t ∧ height t = 0 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s hs
      by_cases hz : height s = 0
      · exact ⟨s, Relation.ReflTransGen.refl, hz⟩
      · obtain ⟨hedge, hmono, hrank⟩ := cert s hz
        have hlt : rank (next s) < n := by simpa only [hs] using hrank
        obtain ⟨t, hpath, hzero⟩ := ih (rank (next s)) hlt (next s) rfl
        exact ⟨t, Relation.ReflTransGen.head ⟨hedge, hmono⟩ hpath, hzero⟩
  intro s
  exact aux (rank s) s rfl

