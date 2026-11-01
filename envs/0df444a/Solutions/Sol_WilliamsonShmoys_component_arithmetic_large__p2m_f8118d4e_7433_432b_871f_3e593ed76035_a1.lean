-- Prove2me | solution 1 for WilliamsonShmoys.component_arithmetic_large__p2m_f8118d4e_7433_432b_871f_3e593ed76035_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:17:12.86436+00:00
-- url     : https://prove2.me/submissions/80470e8c-ee49-4b73-8385-1c84e092a417

import Mathlib
set_option autoImplicit false

theorem solution
    (n E : Nat)
    (parts : List (Prod Nat Nat))
    (hvertices : (parts.map Prod.fst).sum = n)
    (hedges : (parts.map Prod.snd).sum = E)
    (hparts : forall p, List.Mem p parts ->
      (3 <= p.1 -> p.2 <= 3 * p.1 - 6) /\
      (p.1 < 3 -> p.2 <= p.1))
    (hlarge : Exists (fun p => And (List.Mem p parts) (3 <= p.1))) :
    E <= 3 * n - 6 := by
  have allbound : ∀ l : List (Prod Nat Nat),
      (∀ p, p ∈ l → p.2 ≤ 3 * p.1) →
      (l.map Prod.snd).sum ≤ 3 * (l.map Prod.fst).sum := by
    intro l
    induction l with
    | nil =>
        intro _
        simp
    | cons a l ih =>
        intro hlocal
        simp only [List.map_cons, List.sum_cons]
        have ha := hlocal a (by simp)
        have htail : ∀ p, p ∈ l → p.2 ≤ 3 * p.1 := by
          intro p hp
          exact hlocal p (by simp [hp])
        have ht := ih htail
        omega
  have aggregate : ∀ l : List (Prod Nat Nat),
      (∀ p, p ∈ l →
        (3 ≤ p.1 → p.2 ≤ 3 * p.1 - 6) ∧
        (p.1 < 3 → p.2 ≤ p.1)) →
      (∃ p, p ∈ l ∧ 3 ≤ p.1) →
      (l.map Prod.snd).sum + 6 ≤ 3 * (l.map Prod.fst).sum := by
    intro l
    induction l with
    | nil =>
        intro _ hex
        rcases hex with ⟨p, hp, _⟩
        simp at hp
    | cons a l ih =>
        intro hprop hex
        simp only [List.map_cons, List.sum_cons]
        rcases hex with ⟨p, hp, hpbig⟩
        have hmem : p = a ∨ p ∈ l := by simpa using hp
        have ha_prop := hprop a (by simp)
        have ha_smallbound : a.2 ≤ 3 * a.1 := by
          by_cases hge : 3 ≤ a.1
          · have := ha_prop.1 hge
            omega
          · have := ha_prop.2 (by omega)
            omega
        rcases hmem with hhead | htail
        · subst p
          have hstrong := ha_prop.1 hpbig
          have htail_local : ∀ q, q ∈ l → q.2 ≤ 3 * q.1 := by
            intro q hq
            have hqprop := hprop q (by simp [hq])
            by_cases hge : 3 ≤ q.1
            · have := hqprop.1 hge
              omega
            · have := hqprop.2 (by omega)
              omega
          have ht := allbound l htail_local
          omega
        · have hprop_tail : ∀ q, q ∈ l →
              (3 ≤ q.1 → q.2 ≤ 3 * q.1 - 6) ∧
              (q.1 < 3 → q.2 ≤ q.1) := by
            intro q hq
            exact hprop q (by simp [hq])
          have ht := ih hprop_tail ⟨p, htail, hpbig⟩
          have := ha_smallbound
          omega
  have hsum := aggregate parts (by
    intro p hp
    exact hparts p hp) (by
    rcases hlarge with ⟨p, hp, hpbig⟩
    exact ⟨p, hp, hpbig⟩)
  rw [hvertices, hedges] at hsum
  omega