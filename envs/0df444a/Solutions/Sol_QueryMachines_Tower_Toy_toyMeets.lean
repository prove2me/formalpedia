-- Prove2me | solution 1 for QueryMachines.Tower.Toy.toyMeets
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:55:35.401236+00:00
-- url     : https://prove2.me/submissions/4f2f099b-755c-4ff6-b4e2-cf4b496b5f11

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_Toy_Spec
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_TowerRuns
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Toy_Meets
import Theorems.Thm_QueryMachines_Tower_wfHalt
import Theorems.Thm_QueryMachines_Tower_wfStep
import Theorems.Thm_QueryMachines_Tower_wfQuery
import Theorems.Thm_QueryMachines_Tower_wfMono
import Theorems.Thm_Groundwork_Prog_size_bools
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.Prog

namespace QueryMachines.Tower.Toy

/-- `sumF` depends only on table entries for strings of the specified length. -/
theorem sumF_congr_aux : ∀ (l : ℕ) (f g : List Bool → Option ℕ),
    (∀ q, q.length = l → f q = g q) → sumF l f = sumF l g
  | 0, f, g, h => by simp only [sumF, h [] rfl]
  | l + 1, f, g, h => by
    simp only [sumF]
    rw [sumF_congr_aux l _ _ fun q hq => h (false :: q) (by simp [hq]),
      sumF_congr_aux l _ _ fun q hq => h (true :: q) (by simp [hq])]

/-- `sumF` is bounded by the number of strings times the largest entry. -/
theorem sumF_le_aux (M0 : ℕ) : ∀ (l : ℕ) (f : List Bool → Option ℕ),
    (∀ q, q.length = l → ∃ a, a ≤ M0 ∧ f q = some a) → sumF l f ≤ 2 ^ l * M0
  | 0, f, h => by
    obtain ⟨a, ha, e⟩ := h [] rfl
    simp only [sumF, e, Option.getD_some]
    omega
  | l + 1, f, h => by
    have h0 := sumF_le_aux M0 l (fun q => f (false :: q)) fun q hq =>
      h (false :: q) (by simp [hq])
    have h1 := sumF_le_aux M0 l (fun q => f (true :: q)) fun q hq =>
      h (true :: q) (by simp [hq])
    simp only [sumF, pow_succ]
    have e : 2 ^ l * 2 * M0 = 2 ^ l * M0 + 2 ^ l * M0 := by
      rw [Nat.mul_assoc, Nat.two_mul, Nat.mul_add]
    omega

/-- The value at a child is the sum over strings beginning with its bit. -/
theorem val_child_aux (ℓ0 M0 l : ℕ) (b : Bool) (f : List Bool → Option ℕ) :
    (spec ℓ0 M0).val (l, b) ((spec ℓ0 M0).tab (l, b) f) =
      sumF l fun q => f (b :: q) :=
  sumF_congr_aux l _ _ fun _ hq => if_pos hq

/-- The size of the solver's initial state. -/
theorem size_start_aux (l : ℕ) : size ((l, Sum.inl ()) : ℕ × Ph) = l.size + 3 := by
  simp only [size_prod, size_inl, size_nat, size_unit]

/-- The size after the first recursive result arrives. -/
theorem size_one_aux (l u : ℕ) :
    size ((l, Sum.inr (Sum.inl u)) : ℕ × Ph) = l.size + u.size + 4 := by
  simp only [size_prod, size_inl, size_inr, size_nat]
  omega

/-- The size after both recursive results arrive. -/
theorem size_two_aux (l u v : ℕ) :
    size ((l, Sum.inr (Sum.inr (Sum.inl (u, v)))) : ℕ × Ph) =
      l.size + u.size + v.size + 6 := by
  simp only [size_prod, size_inl, size_inr, size_nat]
  omega

/-- The size of a halted solver state. -/
theorem size_done_aux (l v : ℕ) :
    size ((l, Sum.inr (Sum.inr (Sum.inr v))) : ℕ × Ph) = l.size + v.size + 5 := by
  simp only [size_prod, size_inr, size_nat]
  omega

/-- A recursive call is answered by the sum over strings with the selected prefix. -/
theorem oracle_call_aux (ℓ0 M0 l : ℕ) (b b' : Bool) (f : List Bool → Option ℕ) :
    (spec ℓ0 M0).oracle noG (l + 1, b) f (Sum.inl (l, b')) =
      some (sumF l fun q => f (b' :: q)) := by
  rw [← val_child_aux ℓ0 M0]
  exact if_pos rfl

/-- The explicit solver meets its output, time, and state-size bounds. -/
theorem sol_within_aux (ℓ0 M0 : ℕ) (c : ℕ × Bool) (f : List Bool → Option ℕ)
    (hG : (spec ℓ0 M0).Good c f) (tc tq : ℕ) :
    Sol.Within ((spec ℓ0 M0).oracle noG c f)
      (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) c
      (TS c.1 tc tq) (SS ℓ0 M0) (sumF c.1 f) := by
  obtain ⟨l, b⟩ := c
  obtain ⟨hl, hf⟩ := hG
  replace hl : l ≤ ℓ0 := hl
  replace hf : ∀ q : List Bool, q.length = l → ∃ a, a ≤ M0 ∧ f q = some a := hf
  have hls := Nat.size_le_size hl
  have hV : sumF l f ≤ 2 ^ ℓ0 * M0 :=
    (sumF_le_aux M0 l f hf).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hl))
  have hVs := Nat.size_le_size hV
  show Sol.WithinFrom _ _ ((l, Sum.inl ()) : ℕ × Ph)
    (TS l tc tq) (SS ℓ0 M0) (sumF l f)
  cases l with
  | zero =>
    obtain ⟨a, ha, e⟩ := hf [] rfl
    have hval : sumF 0 f = a := by simp [sumF, e]
    rw [hval] at hVs ⊢
    have h2 : Sol.WithinFrom ((spec ℓ0 M0).oracle noG (0, b) f)
        (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW))
        ((0, Sum.inr (Sum.inr (Sum.inr a))) : ℕ × Ph) 0 (SS ℓ0 M0) a :=
      wfHalt rfl (by
        show size ((0, Sum.inr (Sum.inr (Sum.inr a))) : ℕ × Ph) ≤ _
        rw [size_done_aux, SS]
        omega)
    have h1 := wfQuery (M := Sol) (s := ((0, Sum.inl ()) : ℕ × Ph))
      (x := Sum.inr (Sum.inl [])) (v := a) rfl rfl e
      (by
        show size ((0, Sum.inl ()) : ℕ × Ph) ≤ _
        rw [size_start_aux, SS]
        omega) h2
    exact wfMono h1 (by show 0 + tq ≤ tq; omega) le_rfl
  | succ l =>
    have hu : sumF l (fun q => f (false :: q)) ≤ sumF (l + 1) f := Nat.le_add_right _ _
    have hv : sumF l (fun q => f (true :: q)) ≤ sumF (l + 1) f := Nat.le_add_left _ _
    have hus := Nat.size_le_size hu
    have hvs := Nat.size_le_size hv
    generalize hU : sumF l (fun q => f (false :: q)) = u at *
    generalize hW : sumF l (fun q => f (true :: q)) = v at *
    have hsum : sumF (l + 1) f = u + v := by simp only [sumF, hU, hW]
    rw [hsum] at hVs hus hvs ⊢
    have h5 : Sol.WithinFrom ((spec ℓ0 M0).oracle noG (l + 1, b) f)
        (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW))
        ((l + 1, Sum.inr (Sum.inr (Sum.inr (u + v)))) : ℕ × Ph)
        0 (SS ℓ0 M0) (u + v) :=
      wfHalt rfl (by
        show size ((l + 1, Sum.inr (Sum.inr (Sum.inr (u + v)))) : ℕ × Ph) ≤ _
        rw [size_done_aux, SS]
        omega)
    have h4 := wfStep (M := Sol)
      (s := ((l + 1, Sum.inr (Sum.inr (Sum.inl (u, v)))) : ℕ × Ph)) rfl rfl
      (by
        show size ((l + 1, Sum.inr (Sum.inr (Sum.inl (u, v)))) : ℕ × Ph) ≤ _
        rw [size_two_aux, SS]
        omega) h5
    have h3 := wfQuery (M := Sol)
      (s := ((l + 1, Sum.inr (Sum.inl u)) : ℕ × Ph))
      (x := Sum.inl (l, true)) (v := v) rfl rfl (by rw [oracle_call_aux, hW])
      (by
        show size ((l + 1, Sum.inr (Sum.inl u)) : ℕ × Ph) ≤ _
        rw [size_one_aux, SS]
        omega) h4
    have h2 := wfQuery (M := Sol) (O := (spec ℓ0 M0).oracle noG (l + 1, b) f)
      (w := Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) (S := SS ℓ0 M0)
      (s := ((l + 1, Sum.inl ()) : ℕ × Ph))
      (x := Sum.inl (l, false)) (v := u) rfl (by simp [Sol, solAsk])
      (by rw [oracle_call_aux, hU])
      (by
        show size ((l + 1, Sum.inl ()) : ℕ × Ph) ≤ _
        rw [size_start_aux, SS]
        omega)
      (by
        rw [show Sol.resume ((l + 1, Sum.inl ()) : ℕ × Ph) u =
          ((l + 1, Sum.inr (Sum.inl u)) : ℕ × Ph) by simp [Sol, solResume]]
        exact h3)
    exact wfMono h2 (by show 0 + 1 + tc + tc ≤ 2 * tc + 1; omega) le_rfl

/-- The inner machine returns the requested entry within its bounds. -/
theorem inn_within_aux (ℓ0 M0 : ℕ) (c : ℕ × Bool) (f : List Bool → Option ℕ)
    (c' : ℕ × Bool) (hG : (spec ℓ0 M0).Good c f)
    (hch : (spec ℓ0 M0).Child c f c') (q : List Bool) (a : ℕ)
    (ht : (spec ℓ0 M0).tab c' f q = some a) (tq : ℕ) :
    Inn.Within (Sum.elim f noG) (Sum.elim (fun _ => tq) noW) (c', q)
      (TI c'.1 tq) (SI ℓ0 M0) a := by
  replace hch : c'.1 + 1 = c.1 := hch
  replace ht : (if q.length = c'.1 then f (c'.2 :: q) else none) = some a := ht
  have hl : c.1 ≤ ℓ0 := hG.1
  by_cases hq : q.length = c'.1
  · rw [if_pos hq] at ht
    obtain ⟨a', ha', e⟩ := hG.2 (c'.2 :: q) (by
      rw [List.length_cons, hq]
      exact hch)
    obtain rfl : a' = a := Option.some.inj (e.symm.trans ht)
    have has := Nat.size_le_size ha'
    have h2 : Inn.WithinFrom (Sum.elim f noG) (Sum.elim (fun _ => tq) noW)
        (Sum.inr a' : (Bool × List Bool) ⊕ ℕ) 0 (SI ℓ0 M0) a' :=
      wfHalt rfl (by
        show size (Sum.inr a' : (Bool × List Bool) ⊕ ℕ) ≤ _
        rw [size_inr, size_nat, SI]
        omega)
    have h1 := wfQuery (M := Inn)
      (s := (Sum.inl (c'.2, q) : (Bool × List Bool) ⊕ ℕ))
      (x := Sum.inl (c'.2 :: q)) (v := a') rfl rfl ht
      (by
        show size (Sum.inl (c'.2, q) : (Bool × List Bool) ⊕ ℕ) ≤ _
        rw [size_inl, size_prod, size_bool, size_bools, SI]
        dsimp only
        omega) h2
    exact wfMono h1 (by show 0 + tq ≤ tq; omega) le_rfl
  · rw [if_neg hq] at ht
    cases ht

/-- The two explicit machines satisfy every `Meets` field. -/
theorem toyMeets_aux : ToyMeets := fun ℓ0 M0 => {
  child_lev := fun _ _ _ _ h => h
  child_good := fun c f c' hG h => by
    replace h : c'.1 + 1 = c.1 := h
    have hl : c.1 ≤ ℓ0 := hG.1
    refine ⟨(by omega : c'.1 ≤ ℓ0), fun q hq => ?_⟩
    replace hq : q.length = c'.1 := hq
    obtain ⟨a, ha, e⟩ := hG.2 (c'.2 :: q) (by
      rw [List.length_cons, hq]
      exact h)
    exact ⟨a, ha, (if_pos hq).trans e⟩
  child_size := fun c f c' hG h => by
    replace h : c'.1 + 1 = c.1 := h
    have hl : c.1 ≤ ℓ0 := hG.1
    have := Nat.size_le_size (by omega : c'.1 ≤ ℓ0)
    rw [size_prod, size_nat, size_bool, SC]
    omega
  sol := fun c f hG tc tq => sol_within_aux ℓ0 M0 c f hG tc tq
  inn := fun c f c' hG hch q a ht tq => inn_within_aux ℓ0 M0 c f c' hG hch q a ht tq }

end QueryMachines.Tower.Toy

theorem solution : ToyMeets := QueryMachines.Tower.Toy.toyMeets_aux
