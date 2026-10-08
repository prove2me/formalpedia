-- Prove2me | solution 1 for WarshallBool.Closure.warshall_eq_powerSum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:01:30.070327+00:00
-- url     : https://prove2.me/submissions/bef09f0d-20f7-48d7-b193-67e04ba8e965

import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm96
import Definitions.Def_WarshallBool_Closure_Setting

open FloydAlgorithms.ShortestPath

namespace WarshallBool.Closure
namespace A96

variable {n : ℕ}

abbrev BM (n : ℕ) := Fin n → Fin n → Bool

def kstep (i j : Fin n) (m : BM n) (k : Fin n) : BM n :=
  if m i k then Function.update m j (Function.update (m j) k true) else m

def G (m0 : BM n) (i j : Fin n) (S : List (Fin n)) : BM n :=
  Function.update m0 j (fun k => if k ∈ S then (m0 j k || (m0 j i && m0 i k)) else m0 j k)

lemma G_jk (m0 : BM n) (i j k : Fin n) (S : List (Fin n)) (hk : k ∉ S) :
    G m0 i j S j k = m0 j k := by
  simp [G, hk]

lemma G_ik (m0 : BM n) (i j k : Fin n) (S : List (Fin n)) (hk : k ∉ S) :
    G m0 i j S i k = m0 i k := by
  by_cases h : i = j
  · subst h; simp [G, hk]
  · simp [G, Function.update_apply, h]

lemma G_ji (m0 : BM n) (i j : Fin n) (S : List (Fin n)) :
    G m0 i j S j i = m0 j i := by
  simp only [G, Function.update_self]
  split_ifs <;> cases m0 j i <;> simp

lemma kloop (m0 : BM n) (i j : Fin n) (hji : m0 j i = true) :
    ∀ (l S : List (Fin n)), l.Nodup → (∀ x ∈ l, x ∉ S) →
      l.foldl (kstep i j) (G m0 i j S) = G m0 i j (l ++ S) := by
  intro l
  induction l with
  | nil => intro S _ _; simp
  | cons k l ih =>
    intro S hnd hdis
    rw [List.foldl_cons]
    have hk : k ∉ S := hdis k (by simp)
    have hstep : kstep i j (G m0 i j S) k = G m0 i j (k :: S) := by
      have e1 := G_ik m0 i j k S hk
      have e2 := G_jk m0 i j k S hk
      have e3 := G_ji m0 i j S
      funext a c
      unfold kstep
      rw [e1]
      by_cases ha : a = j
      · subst ha
        by_cases hc : c = k
        · subst hc
          cases h1 : m0 i c <;> simp [G, h1, hk, hji]
        · cases h1 : m0 i k <;> simp [G, h1, hc, Function.update_apply]
      · cases h1 : m0 i k <;> simp [G, h1, ha, Function.update_apply]
    rw [hstep, ih (k :: S) (List.nodup_cons.mp hnd).2 ?_]
    · have hm : ∀ x, x ∈ l ++ k :: S ↔ x ∈ k :: l ++ S := by
        intro x; simp only [List.mem_append, List.mem_cons]; tauto
      unfold G; simp only [hm]
    · intro x hx hxS
      rcases List.mem_cons.mp hxS with h | h
      · subst h; exact (List.nodup_cons.mp hnd).1 hx
      · exact hdis x (by simp [hx]) h

def rowS (i j : Fin n) (m : BM n) : BM n :=
  if m j i then (List.finRange n).foldl (kstep i j) m else m

lemma rowS_eq (i j : Fin n) (m : BM n) :
    rowS i j m = Function.update m j (fun k => m j k || (m j i && m i k)) := by
  unfold rowS
  have hG : G m i j [] = m := by
    funext a c; by_cases ha : a = j
    · subst ha; simp [G]
    · simp [G, ha]
  split_ifs with h
  · conv_lhs => rw [← hG]
    rw [kloop m i j h _ [] (List.nodup_finRange n) (by simp)]
    simp [G]
  · funext a c; by_cases ha : a = j
    · subst ha; simp [h]
    · simp [ha]

def pstep (m : BM n) (i : Fin n) : BM n := fun a c => m a c || (m a i && m i c)

def G2 (m0 : BM n) (i : Fin n) (S : List (Fin n)) : BM n :=
  fun a c => if a ∈ S then m0 a c || (m0 a i && m0 i c) else m0 a c

lemma jloop (m0 : BM n) (i : Fin n) :
    ∀ (l S : List (Fin n)), l.Nodup → (∀ x ∈ l, x ∉ S) →
      l.foldl (fun m j => rowS i j m) (G2 m0 i S) = G2 m0 i (l ++ S) := by
  intro l
  induction l with
  | nil => intro S _ _; simp
  | cons j l ih =>
    intro S hnd hdis
    rw [List.foldl_cons]
    have hj : j ∉ S := hdis j (by simp)
    have hstep : rowS i j (G2 m0 i S) = G2 m0 i (j :: S) := by
      rw [rowS_eq]
      funext a c
      by_cases ha : a = j
      · subst ha
        have hik : G2 m0 i S i c = m0 i c := by
          unfold G2; split_ifs <;> cases m0 i c <;> simp
        simp only [Function.update_self, hik]
        simp [G2, hj]
      · simp [G2, ha, Function.update_apply]
    rw [hstep, ih (j :: S) (List.nodup_cons.mp hnd).2 ?_]
    · have hm : ∀ x, x ∈ l ++ j :: S ↔ x ∈ j :: l ++ S := by
        intro x; simp only [List.mem_append, List.mem_cons]; tauto
      unfold G2; simp only [hm]
    · intro x hx hxS
      rcases List.mem_cons.mp hxS with h | h
      · subst h; exact (List.nodup_cons.mp hnd).1 hx
      · exact hdis x (by simp [hx]) h

lemma pivot_eq (m : BM n) (i : Fin n) :
    (List.finRange n).foldl (fun m j => rowS i j m) m = pstep m i := by
  have h0 : G2 m i [] = m := by funext a c; simp [G2]
  conv_lhs => rw [← h0]
  rw [jloop m i _ [] (List.nodup_finRange n) (by simp)]
  funext a c; simp [G2, pstep]

lemma alg_eq (b : BM n) :
    algorithm96 b = (List.finRange n).foldl pstep b := by
  unfold algorithm96
  have : (fun (m : BM n) (i : Fin n) => (List.finRange n).foldl (fun m j =>
      if m j i then
        (List.finRange n).foldl (fun m k =>
          if m i k then Function.update m j (Function.update (m j) k true)
          else m) m
      else m) m) = pstep := by
    funext m i
    rw [← pivot_eq]
    rfl
  rw [this]

def Closed (m : BM n) (u : Fin n) : Prop := ∀ a c, m a u = true → m u c = true → m a c = true

lemma pstep_closed_old (m : BM n) (u v : Fin n) (h : Closed m u) : Closed (pstep m v) u := by
  intro a c h1 h2
  simp only [pstep, Bool.or_eq_true, Bool.and_eq_true] at h1 h2 ⊢
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h a c h1 h2)
  · exact Or.inr ⟨h a v h1 h2, h2'⟩
  · exact Or.inr ⟨h1, h v c h1' h2⟩
  · exact Or.inr ⟨h1, h2'⟩

lemma pstep_closed_new (m : BM n) (v : Fin n) : Closed (pstep m v) v := by
  intro a c h1 h2
  simp only [pstep, Bool.or_eq_true, Bool.and_eq_true] at h1 h2 ⊢
  have h1' : m a v = true := by rcases h1 with h1 | h1 <;> [exact h1; exact h1.1]
  have h2' : m v c = true := by rcases h2 with h2 | h2 <;> [exact h2; exact h2.2]
  exact Or.inr ⟨h1', h2'⟩

lemma foldl_closed : ∀ (l : List (Fin n)) (m : BM n) (u : Fin n),
    (Closed m u ∨ u ∈ l) → Closed (l.foldl pstep m) u := by
  intro l
  induction l with
  | nil => intro m u h; simpa using h
  | cons v l ih =>
    intro m u h
    rw [List.foldl_cons]
    apply ih
    by_cases hv : u = v
    · subst hv; exact Or.inl (pstep_closed_new m u)
    · rcases h with h | h
      · exact Or.inl (pstep_closed_old m u v h)
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h hv
        · exact Or.inr h

lemma foldl_mono : ∀ (l : List (Fin n)) (m : BM n) (a c : Fin n),
    m a c = true → (l.foldl pstep m) a c = true := by
  intro l
  induction l with
  | nil => intro m a c h; simpa using h
  | cons v l ih =>
    intro m a c h
    rw [List.foldl_cons]
    apply ih
    simp [pstep, h]

lemma foldl_sound (R : Fin n → Fin n → Prop) (hR : Transitive R) : ∀ (l : List (Fin n)) (m : BM n),
    (∀ a c, m a c = true → R a c) → ∀ a c, (l.foldl pstep m) a c = true → R a c := by
  intro l
  induction l with
  | nil => intro m h; simpa using h
  | cons v l ih =>
    intro m h
    rw [List.foldl_cons]
    apply ih
    intro a c hac
    simp only [pstep, Bool.or_eq_true, Bool.and_eq_true] at hac
    rcases hac with hac | ⟨h1, h2⟩
    · exact h a c hac
    · exact hR (h a v h1) (h v c h2)

theorem a96_core (b : Fin n → Fin n → Bool) (i j : Fin n) :
    algorithm96 b i j = true ↔ Relation.TransGen (fun a c => b a c = true) i j := by
  rw [alg_eq]
  constructor
  · intro h
    exact foldl_sound (Relation.TransGen (fun a c => b a c = true)) (fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2) _ b
      (fun a c h => Relation.TransGen.single (r := fun a c => b a c = true) h) i j h
  · intro h
    induction h with
    | single h => exact foldl_mono _ b _ _ h
    | tail _ hbc ih =>
      exact foldl_closed _ b _ (Or.inr (List.mem_finRange _)) _ _ ih (foldl_mono _ b _ _ hbc)

end A96

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


theorem goal_core {d : ℕ} (M : Fin d → Fin d → Bool) :
    FloydAlgorithms.ShortestPath.algorithm96 M = powerSum M := by
  funext i j
  apply Bool.eq_iff_iff.2
  rw [A96.a96_core M i j, powerSum_iff]

end WarshallBool.Closure

open WarshallBool.Closure
open FloydAlgorithms.ShortestPath

theorem solution {d : ℕ} (M : Fin d → Fin d → Bool) :
    FloydAlgorithms.ShortestPath.algorithm96 M = powerSum M := by
  exact goal_core M
