-- Prove2me | solution 2 for StudentTeacher976.Adaptivity.certified_replacement_resources
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T18:57:24.88935+00:00
-- url     : https://prove2.me/submissions/02325740-3051-4d90-9c78-fd95e5cda914

import Theorems.Thm_StudentTeacher976_Adaptivity_total_certified_refinement_resources

set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity

theorem solution {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
    (c : Polynomial ℕ) (V : Word → Word → Word → Prop)
    (heff : {s | ∃ x y z, s = tup [x,y,z] ∧ V x y z} ∈ Delta i)
    (hV : ∀ x y, R x y ↔ ∃ v, v.length = c.eval x.length ∧ V x y v)
    (r q : ℕ → ℕ) (hr : PolyTimeLength r) (hq : PolyTimeLength q)
    (hrpos : ∀ n, 1 ≤ resource r n) (hqpos : ∀ n, 1 ≤ resource q n)
    (hevent : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ resource r n) : R ∈ ST i r q := by
  refine total_certified_refinement_resources P c V heff ?_ ?_
    r q hr hq hrpos hqpos hevent
  · intro x y v hv hvalid
    exact (hV x y).mpr ⟨v, hv, hvalid⟩
  · intro x
    obtain ⟨y, hy⟩ := P.total x
    obtain ⟨v, hv, hvalid⟩ := (hV x y).mp hy
    exact ⟨y, v, hv, hvalid⟩
