-- Prove2me | solution 2 for StudentTeacher976.Adaptivity.total_certified_refinement_resources
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T21:46:30.19426+00:00
-- url     : https://prove2.me/submissions/e1e47a9d-0d3d-4d87-a8e0-e54abe9b548d

import Theorems.Thm_StudentTeacher976_Adaptivity_conditional_certified_refinement_resources

set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity

theorem solution {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
    (c : Polynomial ℕ) (V : Word → Word → Word → Prop)
    (heff : {s | ∃ x y z, s = tup [x,y,z] ∧ V x y z} ∈ Delta i)
    (hsound : ∀ x y v, v.length = c.eval x.length → V x y v → R x y)
    (htotal : ∀ x, ∃ y v, v.length = c.eval x.length ∧ V x y v)
    (r q : ℕ → ℕ) (hr : PolyTimeLength r) (hq : PolyTimeLength q)
    (hrpos : ∀ n, 1 ≤ resource r n) (hqpos : ∀ n, 1 ≤ resource q n)
    (hevent : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ resource r n) : R ∈ ST i r q := by
  exact conditional_certified_refinement_resources P c V heff hsound
    (fun x _ => htotal x) r q hr hq hrpos hqpos hevent
