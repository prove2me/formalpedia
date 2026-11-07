-- Prove2me | solution 1 for SymBoolPCSP.CFixing.eq_false_of_vanish_increasing
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:08:32.755245+00:00
-- url     : https://prove2.me/submissions/7eb32d72-487e-4804-a657-4b2fb4d5e2d1

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_eq_false_of_vanish_increasing

theorem indicator_filter {L : ℕ} (x : Fin L → Bool) :
    x = indicator (Finset.univ.filter (fun i => x i = true)) := by
  funext i; simp [indicator]

end Aux_eq_false_of_vanish_increasing

open Aux_eq_false_of_vanish_increasing in
/-- If `f(0) = 0`, then `f(x) = 0` for every `x` vanishing on the set of coordinates on which
`f` is somewhere-increasing, i.e. the `j` with `f(e_Y) = 0`, `f(e_{Y ∪ {j}}) = 1` for some
`Y ∌ j` (BG, proof of Lemma 4.12, Case 1). -/
theorem eq_false_of_vanish_increasing {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (x : Fin L → Bool)
    (hx : ∀ i ∈ Finset.univ.filter (fun j : Fin L => ∃ Y : Finset (Fin L), j ∉ Y ∧
      f (indicator Y) = false ∧ f (indicator (insert j Y)) = true), x i = false) :
    f x = false := by
  classical
  have claim : ∀ X : Finset (Fin L), f (indicator X) = true → ∃ j ∈ X, ∃ Y : Finset (Fin L),
      j ∉ Y ∧ f (indicator Y) = false ∧ f (indicator (insert j Y)) = true := by
    intro X
    induction X using Finset.induction_on with
    | empty =>
      intro h
      have he : indicator (∅ : Finset (Fin L)) = fun _ => false := funext fun i => by
        simp [indicator]
      rw [he, h0] at h; exact absurd h (by simp)
    | @insert a X ha ih =>
      intro h
      cases hX : f (indicator X) with
      | true =>
        obtain ⟨j, hj, rest⟩ := ih hX
        exact ⟨j, Finset.mem_insert_of_mem hj, rest⟩
      | false => exact ⟨a, Finset.mem_insert_self a X, X, ha, hX, h⟩
  by_contra h
  have ht : f x = true := by simpa using h
  rw [indicator_filter x] at ht
  obtain ⟨j, hj, hjI⟩ := claim _ ht
  have h1 := hx j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjI⟩)
  have h2 : x j = true := (Finset.mem_filter.mp hj).2
  rw [h1] at h2; exact absurd h2 (by simp)

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (x : Fin L → Bool)
    (hx : ∀ i ∈ Finset.univ.filter (fun j : Fin L => ∃ Y : Finset (Fin L), j ∉ Y ∧
      f (indicator Y) = false ∧ f (indicator (insert j Y)) = true), x i = false) :
    f x = false :=
  SymBoolPCSP.CFixing.eq_false_of_vanish_increasing f h0 x hx
