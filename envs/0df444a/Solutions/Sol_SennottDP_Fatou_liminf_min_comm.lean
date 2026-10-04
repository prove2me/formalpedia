-- Prove2me | solution 1 for SennottDP.Fatou.liminf_min_comm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:40:48.999483+00:00
-- url     : https://prove2.me/submissions/73876a76-62b4-47dc-a0ae-3ef873f5d273

import Mathlib

open Filter Topology
open scoped ENNReal

open Filter Topology in
theorem solution {A : Type*} [Fintype A] [Nonempty A] (u : A → ℕ → EReal) :
    liminf (fun N => ⨅ a, u a N) atTop = ⨅ a, liminf (fun N => u a N) atTop ∧
    ∀ l : A → EReal, (∀ a, Tendsto (fun N => u a N) atTop (𝓝 (l a))) →
      Tendsto (fun N => ⨅ a, u a N) atTop (𝓝 (⨅ a, l a)) := by
  constructor
  · have h := liminf_finset_inf (f := atTop) (F := u) (s := Finset.univ)
    simpa only [Finset.inf_univ_eq_iInf] using h
  · intro l hl
    have h := Filter.Tendsto.finset_inf_nhds_apply (s := Finset.univ) (f := u) (g := l)
      (l := atTop) (fun a _ => hl a)
    simpa only [Finset.inf_univ_eq_iInf] using h
