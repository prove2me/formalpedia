-- Prove2me | solution 1 for Timetabling.StableHalf.closed_extend_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:23:10.517304+00:00
-- url     : https://prove2.me/submissions/843eff3b-8504-4be8-a84c-4fd2e3a72152

import Mathlib
import Definitions.Def_Timetabling_StableHalf_IsStableTransversal
import Definitions.Def_Timetabling_StableHalf_IsClosed

namespace Aux_TSHcei

def ext {n : ℕ} (a : Fin n → Option Bool) (c : Fin n → Bool) : Fin n → Bool :=
  fun j => (a j).getD (c j)

theorem ext_some {n : ℕ} (a : Fin n → Option Bool) (c : Fin n → Bool) (j : Fin n) (b : Bool)
    (h : a j = some b) : ext a c j = b := by
  simp [ext, h]

theorem ext_none {n : ℕ} (a : Fin n → Option Bool) (c : Fin n → Bool) (j : Fin n)
    (h : a j = none) : ext a c j = c j := by
  simp [ext, h]

open Timetabling.StableHalf in
theorem key {n : ℕ} (G : SimpleGraph (Fin n × Bool)) (a : Fin n → Option Bool)
    (ha : IsClosed G a) (c : Fin n → Bool) (j k : Fin n) (hj : a j ≠ none) :
    ¬ G.Adj (j, ext a c j) (k, ext a c k) := by
  intro hadj
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hj
  have hu : a (j, ext a c j).1 = some (j, ext a c j).2 := by
    show a j = some (ext a c j)
    rw [ext_some a c j b hb, hb]
  have h2 : a k = some (!ext a c k) := ha _ hu _ hadj
  have h3 : ext a c k = !ext a c k := ext_some a c k _ h2
  have hne : ∀ x : Bool, x ≠ !x := by decide
  exact hne _ h3

end Aux_TSHcei

open Timetabling.StableHalf Aux_TSHcei in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n × Bool)) (a : Fin n → Option Bool)
    (ha : IsClosed G a) :
    (∃ c : Fin n → Bool, IsStableTransversal G c) ↔
      ∃ c : Fin n → Bool, IsStableTransversal G c ∧ ∀ j b, a j = some b → c j = b := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨ext a c, ?_, fun j b h => ext_some a c j b h⟩
    intro x hx y hy hxy
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := hy
    by_cases hj : a j = none
    · by_cases hk : a k = none
      · simp only at hxy ⊢
        rw [ext_none a c j hj, ext_none a c k hk] at hxy ⊢
        exact hc (Set.mem_range_self j) (Set.mem_range_self k) hxy
      · intro hadj
        exact key G a ha c k j hk hadj.symm
    · exact key G a ha c j k hj
  · rintro ⟨c, hc, -⟩
    exact ⟨c, hc⟩
