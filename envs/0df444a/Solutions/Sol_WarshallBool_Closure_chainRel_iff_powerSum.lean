-- Prove2me | solution 1 for WarshallBool.Closure.chainRel_iff_powerSum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:01:26.302442+00:00
-- url     : https://prove2.me/submissions/8c26ee71-187c-4822-9f3a-318fa0b24185

import Mathlib
import Definitions.Def_WarshallBool_Closure_Setting



namespace WarshallBool.Closure

def WalkP {d : ℕ} (M : Fin d → Fin d → Bool) (i j : Fin d) (p : ℕ) : Prop :=
  ∃ v : ℕ → Fin d, v 0 = i ∧ v p = j ∧ ∀ t, t < p → M (v t) (v (t+1)) = true

lemma walkP_snoc {d : ℕ} {M : Fin d → Fin d → Bool} {i b c : Fin d} {p : ℕ}
    (h : WalkP M i b p) (hc : M b c = true) : WalkP M i c (p+1) := by
  obtain ⟨v, h0, hp, he⟩ := h
  refine ⟨fun t => if t ≤ p then v t else c, ?_, ?_, ?_⟩
  · simp [h0]
  · simp
  · intro t ht
    by_cases h1 : t + 1 ≤ p
    · simp [h1, show t ≤ p by omega]; exact he t (by omega)
    · have : t = p := by omega
      subst this
      simp [hp, hc]

lemma walkP_unsnoc {d : ℕ} {M : Fin d → Fin d → Bool} {i c : Fin d} {p : ℕ}
    (h : WalkP M i c (p+1)) : ∃ b, WalkP M i b p ∧ M b c = true := by
  obtain ⟨v, h0, hp, he⟩ := h
  refine ⟨v p, ⟨v, h0, rfl, fun t ht => he t (by omega)⟩, ?_⟩
  have := he p (by omega); rwa [hp] at this

lemma boolPow_iff {d : ℕ} (M : Fin d → Fin d → Bool) (p : ℕ) (i j : Fin d) :
    boolPow M p i j = true ↔ WalkP M i j p := by
  induction p generalizing j with
  | zero =>
    simp only [boolPow, decide_eq_true_eq]
    constructor
    · rintro rfl; exact ⟨fun _ => i, rfl, rfl, fun t ht => by omega⟩
    · rintro ⟨v, h0, hp, -⟩; rw [← h0, hp]
  | succ p ih =>
    simp only [boolPow, boolProd, decide_eq_true_eq]
    constructor
    · rintro ⟨k, hk, hm⟩
      exact walkP_snoc ((ih k).1 hk) hm
    · intro h
      obtain ⟨b, hb, hm⟩ := walkP_unsnoc h
      exact ⟨b, (ih b).2 hb, hm⟩

lemma walkP_pos_transGen {d : ℕ} {M : Fin d → Fin d → Bool} {i j : Fin d} {p : ℕ}
    (h : WalkP M i j p) (hp : 1 ≤ p) : Relation.TransGen (fun a c => M a c = true) i j := by
  induction p generalizing j with
  | zero => omega
  | succ p ih =>
    obtain ⟨b, hb, hm⟩ := walkP_unsnoc h
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · obtain ⟨v, h0, hp0, -⟩ := hb
      subst h0
      rw [← hp0] at hm
      exact Relation.TransGen.single hm
    · exact Relation.TransGen.tail (ih hb hpos) hm

lemma transGen_walkP {d : ℕ} {M : Fin d → Fin d → Bool} {i j : Fin d}
    (h : Relation.TransGen (fun a c => M a c = true) i j) : ∃ p, 1 ≤ p ∧ WalkP M i j p := by
  induction h with
  | @single c hm =>
    refine ⟨1, le_rfl, fun t => if t = 0 then i else c, by simp, by simp, ?_⟩
    intro t ht
    have : t = 0 := by omega
    subst this
    simpa using hm
  | tail _ hm ih =>
    obtain ⟨p, hp, hw⟩ := ih
    exact ⟨p+1, by omega, walkP_snoc hw hm⟩

lemma walkP_short {d : ℕ} {M : Fin d → Fin d → Bool} {i j : Fin d} :
    ∀ p, 1 ≤ p → WalkP M i j p → ∃ q, 1 ≤ q ∧ q ≤ d ∧ WalkP M i j q := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp hw
    by_cases hpd : p ≤ d
    · exact ⟨p, hp, hpd, hw⟩
    · obtain ⟨v, h0, hpj, he⟩ := hw
      have hlt : Fintype.card (Fin d) < Fintype.card (Fin p) := by simp; omega
      obtain ⟨a', b', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun t : Fin p => v t) hlt
      have key : ∃ a b, a < b ∧ b < p ∧ v a = v b := by
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
        · exact ⟨a', b', h, b'.2, heq⟩
        · exact ⟨b', a', h, a'.2, heq.symm⟩
      obtain ⟨a, b, hab, hbp, hvab⟩ := key
      have hw' : WalkP M i j (p - (b - a)) := by
        refine ⟨fun t => if t ≤ a then v t else v (t + (b - a)), ?_, ?_, ?_⟩
        · simp [h0]
        · have : ¬ (p - (b - a) ≤ a) := by omega
          simp only [this, if_false]
          rw [show p - (b - a) + (b - a) = p by omega]; exact hpj
        · intro t ht
          by_cases h1 : t + 1 ≤ a
          · simp only [h1, show t ≤ a by omega, if_true]
            exact he t (by omega)
          · by_cases h2 : t = a
            · subst h2
              simp only [le_refl, if_true, h1, if_false]
              rw [hvab, show t + 1 + (b - t) = b + 1 by omega]
              exact he b (by omega)
            · have h3 : ¬ t ≤ a := by omega
              simp only [h1, h3, if_false]
              rw [show t + 1 + (b - a) = (t + (b - a)) + 1 by omega]
              exact he _ (by omega)
      exact ih (p - (b - a)) (by omega) (by omega) hw'

lemma powerSum_iff {d : ℕ} (M : Fin d → Fin d → Bool) (i j : Fin d) :
    powerSum M i j = true ↔ Relation.TransGen (fun a c => M a c = true) i j := by
  simp only [powerSum, decide_eq_true_eq, Finset.mem_Icc]
  constructor
  · rintro ⟨p, ⟨hp1, hpd⟩, hb⟩
    exact walkP_pos_transGen ((boolPow_iff M p i j).1 hb) hp1
  · intro h
    obtain ⟨p, hp, hw⟩ := transGen_walkP h
    obtain ⟨q, hq1, hqd, hwq⟩ := walkP_short p hp hw
    exact ⟨q, ⟨hq1, hqd⟩, (boolPow_iff M q i j).2 hwq⟩

lemma chainRel_iff_transGen {d : ℕ} (M : Fin d → Fin d → Bool) (i j : Fin d) :
    ChainRel M i j ↔ Relation.TransGen (fun a c => M a c = true) i j := by
  constructor
  · rintro ⟨ks, hk⟩
    induction ks generalizing i with
    | nil =>
      simp [List.isChain_cons_cons] at hk
      exact Relation.TransGen.single hk
    | cons k ks ih =>
      simp only [List.cons_append, List.isChain_cons_cons] at hk
      exact Relation.TransGen.head hk.1 (ih k hk.2)
  · intro h
    induction h using Relation.TransGen.head_induction_on with
    | single hm => exact ⟨[], by simpa [List.isChain_cons_cons] using hm⟩
    | head hm _ ih =>
      obtain ⟨ks, hk⟩ := ih
      exact ⟨_ :: ks, by simp only [List.cons_append, List.isChain_cons_cons]; exact ⟨hm, hk⟩⟩

theorem chain_core {d : ℕ} (M : Fin d → Fin d → Bool) (i j : Fin d) :
    ChainRel M i j ↔ powerSum M i j = true := by
  rw [chainRel_iff_transGen, powerSum_iff]

end WarshallBool.Closure

open WarshallBool.Closure


theorem solution {d : ℕ} (M : Fin d → Fin d → Bool) (i j : Fin d) :
    ChainRel M i j ↔ powerSum M i j = true := by
  exact chain_core M i j
