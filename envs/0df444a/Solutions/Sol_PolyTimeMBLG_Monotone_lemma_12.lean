-- Prove2me | solution 1 for PolyTimeMBLG.Monotone.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:43:46.593094+00:00
-- url     : https://prove2.me/submissions/e4a21524-b765-4f82-903a-64d3dec1b558

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_NumberGame

open PolyTimeMBLG.Monotone

namespace NG

def U (B : Multiset ℕ) : ℕ := (B.map (fun x => 2 ^ x - 1)).sum

lemma U_cons (a : ℕ) (B : Multiset ℕ) : U (a ::ₘ B) = (2 ^ a - 1) + U B := by
  simp [U]

lemma U_add (A B : Multiset ℕ) : U (A + B) = U A + U B := by
  simp [U]

lemma U_replicate_zero (z : ℕ) : U (Multiset.replicate z 0) = 0 := by
  simp [U, Multiset.map_replicate]

lemma U_ge {B : Multiset ℕ} {x : ℕ} (hx : x ∈ B) : 2 ^ x - 1 ≤ U B := by
  have : B = x ::ₘ B.erase x := (Multiset.cons_erase hx).symm
  rw [this, U_cons]
  omega

lemma step_U {B I B' : Multiset ℕ} (h : GameStep B I B') :
    ∃ m ∈ B, (∀ x ∈ B, m ≤ x) ∧ I = (m + 1) ::ₘ B.erase m ∧ U I = U B + 2 ^ m ∧ U B' ≤ U B + 1 := by
  obtain ⟨m, hm, hmin, hI, D, hD0, hDI, z, hB'⟩ := h
  have hB : B = m ::ₘ B.erase m := (Multiset.cons_erase hm).symm
  have hUB : U B = (2 ^ m - 1) + U (B.erase m) := by
    conv_lhs => rw [hB]
    rw [U_cons]
  have hUI : U I = U B + 2 ^ m := by
    rw [hI, U_cons, hUB]
    have : 0 < 2 ^ m := Nat.two_pow_pos m
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  refine ⟨m, hm, hmin, hI, hUI, ?_⟩
  -- an element of D
  obtain ⟨d, hd⟩ := Multiset.exists_mem_of_ne_zero hD0
  have hdI : d ∈ I := Multiset.mem_of_le hDI hd
  have hdm : m ≤ d := by
    rw [hI, Multiset.mem_cons] at hdI
    rcases hdI with rfl | hdI
    · omega
    · exact hmin d (Multiset.mem_of_mem_erase hdI)
  have hUD : 2 ^ m - 1 ≤ U D := by
    have h1 := U_ge hd
    have h2 : 2 ^ m ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hdm
    omega
  have hsplit : I = (I - D) + D := (tsub_add_cancel_of_le hDI).symm
  have hUI2 : U I = U (I - D) + U D := by
    conv_lhs => rw [hsplit]
    rw [U_add]
  rw [hB', U_add, U_replicate_zero]
  have : 0 < 2 ^ m := Nat.two_pow_pos m
  omega

end NG

theorem solution (T : ℕ) (board inter : ℕ → Multiset ℕ) (hplay : IsPlay T board inter)
    (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) (htT : t ≤ T) (hkt : k ∈ inter t) :
    2 ^ (k - 1) ≤ t := by
  obtain ⟨⟨z, hz⟩, hsteps⟩ := hplay
  have hinv : ∀ s, s ≤ T → NG.U (board s) ≤ s := by
    intro s
    induction s with
    | zero => intro _; rw [hz, NG.U_replicate_zero]
    | succ s ih =>
      intro hs
      have := ih (by omega)
      obtain ⟨m, _, _, _, _, hB'⟩ := NG.step_U (hsteps s (by omega))
      omega
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  obtain ⟨m, hm, hmin, hI, hUI, _⟩ := NG.step_U (hsteps t' (by omega))
  have hinv' := hinv t' (by omega)
  rw [hI, Multiset.mem_cons] at hkt
  rcases hkt with rfl | hkt
  · -- k = m + 1
    have := NG.U_ge hm
    have h2 : 2 ^ m ≤ t' + 1 := by omega
    simpa using h2
  · have hkB : k ∈ board t' := Multiset.mem_of_mem_erase hkt
    have := NG.U_ge hkB
    have h3 : 2 ^ k ≤ t' + 1 := by omega
    have h4 : 2 ^ (k - 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
