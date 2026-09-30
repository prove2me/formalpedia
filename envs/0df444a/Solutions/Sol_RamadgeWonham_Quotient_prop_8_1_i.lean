-- Prove2me | solution 1 for RamadgeWonham.Quotient.prop_8_1_i
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:29:23.038753+00:00
-- url     : https://prove2.me/submissions/1bd7463d-3a4a-4bf6-8bd7-184bac9e2f8a

import Definitions.Def_RamadgeWonham_Quotient_Projection
import Mathlib.Tactic
set_option autoImplicit false
open RamadgeWonham RamadgeWonham.Quotient

private theorem run_snoc {α : Type} (G : Shared.Generator α) (s : List α) (σ : α) :
    G.run (s++[σ])=(G.run s).bind (G.δ σ) := by
  simp [Shared.Generator.run,Shared.Generator.runFrom,List.foldl_append]

private theorem projection_run {α : Type} {Ec : Set α} (S Sh : Shared.Supervisor α Ec)
    (π : S.S.Q → Sh.S.Q) (hπ : IsProjection S Sh π) (s : List α) :
    ∀ q, S.S.run s=some q → Sh.S.run s=some (π q) := by
  induction s using List.reverseRecOn with
  | nil =>
    intro q hq
    have he : S.S.q0=q := Option.some.inj hq
    subst q
    change some Sh.S.q0=some (π S.S.q0)
    rw [hπ.2.1.1]
  | append_singleton s σ ih =>
    intro q hq
    rw [run_snoc] at hq
    obtain ⟨r,hr,hrq⟩ := Option.bind_eq_some_iff.mp hq
    rw [run_snoc,ih r hr]
    exact hπ.2.2.1 σ r q hrq

theorem solution
    {α : Type} [Fintype α] {Ec : Set α} (G : Shared.Generator α) (hG : G.L = Shared.pre G.Lm)
    (S Sh : Shared.Supervisor α Ec) (hSacc : S.S.Accessible) (hShacc : Sh.S.Accessible)
    (hS : Shared.Complete G S)
    (π π' : S.S.Q → Sh.S.Q) (hπ : IsProjection S Sh π) (hπ' : IsProjection S Sh π') :
    π=π' := by
  funext q
  obtain ⟨s,hs⟩ := hSacc q
  have h1 := projection_run S Sh π hπ s q hs
  have h2 := projection_run S Sh π' hπ' s q hs
  exact Option.some.inj (h1.symm.trans h2)
