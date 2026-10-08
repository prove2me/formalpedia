-- Prove2me | solution 1 for OnlineSetCover.LowerBound.block_adversary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:07:24.308264+00:00
-- url     : https://prove2.me/submissions/a655590e-8524-41fd-b93a-614643cc4ecc

import Mathlib
import Definitions.Def_OnlineSetCover_LowerBound_Game
import Definitions.Def_OnlineSetCover_LowerBound_BlockFamily



namespace OnlineSetCover.LowerBound

section G
variable {X : Type*} [DecidableEq X]

lemma osc_chosenFrom_append (A : OnlineAlg X) (σ τ h : List X) :
    chosenFrom A h (σ ++ τ) = chosenFrom A h σ ∪ chosenFrom A (h ++ σ) τ := by
  induction σ generalizing h with
  | nil => simp [chosenFrom]
  | cons a σ ih =>
    simp only [List.cons_append, chosenFrom, ih, List.append_assoc, List.nil_append,
      Finset.union_assoc]

lemma osc_chosen_snoc (A : OnlineAlg X) (σ : List X) (x : X) :
    chosen A (σ ++ [x]) = chosen A σ ∪ A σ x := by
  unfold chosen
  rw [osc_chosenFrom_append]
  simp [chosenFrom]

lemma osc_chosenFrom_sub (𝓕 : Finset (Finset X)) (A : OnlineAlg X) (hA : IsValid 𝓕 A)
    (σ h : List X) : chosenFrom A h σ ⊆ 𝓕 := by
  induction σ generalizing h with
  | nil => simp [chosenFrom]
  | cons a σ ih =>
    simp only [chosenFrom]
    exact Finset.union_subset (hA h a).1 (ih _)

lemma osc_chosen_sub (𝓕 : Finset (Finset X)) (A : OnlineAlg X) (hA : IsValid 𝓕 A)
    (σ : List X) : chosen A σ ⊆ 𝓕 := osc_chosenFrom_sub 𝓕 A hA σ []

end G

lemma osc_bits_exists (k : ℕ) (P : Fin k → Prop) [DecidablePred P] :
    ∃ j : Fin (2 ^ k), ∀ t : Fin k, j.val.testBit t.val = true ↔ P t := by
  let f : Fin (2 ^ k) → (Fin k → Bool) := fun j t => j.val.testBit t.val
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · exact congrFun hab ⟨i, hi⟩
    · push_neg at hi
      have ha : a.val < 2 ^ i := lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by norm_num) hi)
      have hb : b.val < 2 ^ i := lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by norm_num) hi)
      rw [Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb]
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  obtain ⟨j, hj⟩ := hbij.2 (fun t => decide (P t))
  refine ⟨j, fun t => ?_⟩
  have := congrFun hj t
  simp only [f] at this
  rw [this]; simp

def oscPw (k : ℕ) (t : Fin k) : Fin (2 ^ k) := ⟨2 ^ t.val, Nat.pow_lt_pow_right (by norm_num) t.isLt⟩

lemma osc_pw_bit (k : ℕ) (t s : Fin k) : (oscPw k t).val.testBit s.val = true ↔ s = t := by
  simp [oscPw, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]


section Blk
variable {k r B : ℕ} {X : Type*} [DecidableEq X]

lemma osc_mem_blockSet (R : Finset (Fin B)) (I : Fin B → Fin k) (p : Fin B × Fin (2 ^ k)) :
    p ∈ blockSet R I ↔ p.1 ∈ R ∧ p.2.val.testBit (I p.1).val = true := by
  simp [blockSet]

lemma osc_pw_mem_blockSet (R : Finset (Fin B)) (I : Fin B → Fin k) (b : Fin B) (t : Fin k) :
    (b, oscPw k t) ∈ blockSet R I ↔ b ∈ R ∧ I b = t := by
  rw [osc_mem_blockSet]; simp only
  rw [osc_pw_bit]

/-- unhit bits of block `b` -/
noncomputable def oscU (e : Fin B × Fin (2 ^ k) → X) (A : OnlineAlg X) (σ : List X) (b : Fin B) :
    Finset (Fin k) :=
  Finset.univ.filter (fun t => ∀ S ∈ chosen A σ, e (b, oscPw k t) ∉ S)

def OscInv (k r : ℕ) (e : Fin B × Fin (2 ^ k) → X) (A : OnlineAlg X) (σ : List X)
    (D : Finset (Fin B)) (b : Fin B) (c : Fin B → Fin k) : Prop :=
  b ∉ D ∧ D.card + 1 ≤ r ∧
  (∀ y ∈ σ, ∃ p : Fin B × Fin (2 ^ k), y = e p ∧ p.1 ∈ insert b D ∧
      p.2.val.testBit (c p.1).val = true ∧
      (p.1 = b → ∀ t ∈ oscU e A σ b, p.2.val.testBit t.val = true)) ∧
  σ.length + (oscU e A σ b).card ≤ k * (D.card + 1) ∧
  k * (D.card + 1) ≤ cost A σ + (oscU e A σ b).card

variable (e : Fin B × Fin (2 ^ k) → X) (𝓕 : Finset (Finset X))
  (hF1 : ∀ S ∈ 𝓕, ∃ R : Finset (Fin B), ∃ I : Fin B → Fin k, R.card ≤ r ∧
      ∀ p, e p ∈ S ↔ p ∈ blockSet R I)
  (hF2 : ∀ (R : Finset (Fin B)) (I : Fin B → Fin k), R.card = r → ∃ S ∈ 𝓕, ∀ p ∈ blockSet R I, e p ∈ S)
include hF1 hF2

lemma osc_step (hrB : r ≤ B) (A : OnlineAlg X) (hA : IsValid 𝓕 A) (σ : List X)
    (D : Finset (Fin B)) (b : Fin B) (c : Fin B → Fin k) (hI : OscInv k r e A σ D b c)
    (hU : (oscU e A σ b).Nonempty) :
    ∃ x, ∃ c', OscInv k r e A (σ ++ [x]) D b c' := by
  obtain ⟨hbD, hDr, hel, hlen, hcost⟩ := hI
  set U := oscU e A σ b with hUdef
  obtain ⟨j, hj⟩ := osc_bits_exists k (fun t => t ∈ U)
  set x := e (b, j) with hxdef
  set U' := oscU e A (σ ++ [x]) b with hU'def
  have hsnoc := osc_chosen_snoc A σ x
  have hmono : chosen A σ ⊆ chosen A (σ ++ [x]) := by rw [hsnoc]; exact Finset.subset_union_left
  have hU'U : U' ⊆ U := by
    intro t ht
    simp only [hU'def, hUdef, oscU, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact fun S hS => ht S (hmono hS)
  obtain ⟨t0, ht0⟩ := hU
  -- x lies in some member
  have hxF : ∃ S ∈ 𝓕, x ∈ S := by
    obtain ⟨R, hbR, hR⟩ := Finset.exists_superset_card_eq (s := ({b} : Finset (Fin B))) (n := r)
      (by simp; omega) (by simpa using hrB)
    obtain ⟨S, hS, hpS⟩ := hF2 R (fun _ => t0) hR
    refine ⟨S, hS, hpS _ ?_⟩
    rw [osc_mem_blockSet]
    exact ⟨hbR (by simp), (hj t0).2 ht0⟩
  obtain ⟨S1, hS1, hxS1⟩ := (hA σ x).2 hxF
  obtain ⟨R1, I1, _, hRI1⟩ := hF1 S1 (osc_chosen_sub 𝓕 A hA _ hS1)
  have h1 := (hRI1 (b, j)).1 hxS1
  rw [osc_mem_blockSet] at h1
  have hIbU : I1 b ∈ U := (hj (I1 b)).1 h1.2
  have hIbU' : I1 b ∉ U' := by
    simp only [hU'def, oscU, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not]
    exact ⟨S1, hS1, (hRI1 _).2 ((osc_pw_mem_blockSet R1 I1 b (I1 b)).2 ⟨h1.1, rfl⟩)⟩
  have hcardU : U'.card + 1 ≤ U.card := by
    have : U'.card < U.card := Finset.card_lt_card
      ⟨hU'U, fun h => hIbU' (h hIbU)⟩
    omega
  -- cost growth
  have hcostg : cost A σ + (U \ U').card ≤ cost A (σ ++ [x]) := by
    classical
    let g : Fin k → Finset X := fun t =>
      if h : ∃ S ∈ chosen A (σ ++ [x]), e (b, oscPw k t) ∈ S then h.choose else ∅
    have hg : ∀ t ∈ U \ U', g t ∈ chosen A (σ ++ [x]) ∧ e (b, oscPw k t) ∈ g t := by
      intro t ht
      have hex : ∃ S ∈ chosen A (σ ++ [x]), e (b, oscPw k t) ∈ S := by
        have := (Finset.mem_sdiff.1 ht).2
        simpa [hU'def, oscU] using this
      simp only [g, dif_pos hex]
      exact hex.choose_spec
    have hmaps : ∀ t ∈ U \ U', g t ∈ chosen A (σ ++ [x]) \ chosen A σ := by
      intro t ht
      refine Finset.mem_sdiff.2 ⟨(hg t ht).1, fun hc => ?_⟩
      have := (Finset.mem_sdiff.1 ht).1
      simp only [hUdef, oscU, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this _ hc (hg t ht).2
    have hinj : Set.InjOn g (U \ U' : Finset (Fin k)) := by
      intro t ht s hs hts
      have h1 := (hg t ht)
      have h2 := (hg s hs)
      obtain ⟨R, I, _, hRI⟩ := hF1 (g t) (osc_chosen_sub 𝓕 A hA _ h1.1)
      have a1 := (osc_pw_mem_blockSet R I b t).1 ((hRI _).1 h1.2)
      have a2 := (osc_pw_mem_blockSet R I b s).1 ((hRI _).1 (hts ▸ h2.2))
      rw [← a1.2, ← a2.2]
    have := Finset.card_le_card_of_injOn g hmaps hinj
    rw [Finset.card_sdiff_of_subset hmono] at this
    have := Finset.card_le_card hmono
    unfold cost; omega
  have hsd : (U \ U').card + U'.card = U.card := by
    rw [Finset.card_sdiff_of_subset hU'U]
    have := Finset.card_le_card hU'U; omega
  refine ⟨x, Function.update c b t0, hbD, hDr, ?_, ?_, ?_⟩
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨p, rfl, hp1, hp2, hp3⟩ := hel y hy
      refine ⟨p, rfl, hp1, ?_, fun hpb t ht => hp3 hpb t (hU'U ht)⟩
      by_cases hpb : p.1 = b
      · rw [hpb, Function.update_self]; rw [hpb] at hp3; exact hp3 rfl t0 ht0
      · rw [Function.update_of_ne hpb]; exact hp2
    · simp at hy; subst hy
      refine ⟨(b, j), rfl, by simp, ?_, fun _ t ht => (hj t).2 (hU'U ht)⟩
      simp only [Function.update_self]; exact (hj t0).2 ht0
  · simp only [List.length_append, List.length_singleton]; rw [← hU'def]; omega
  · rw [← hU'def]; omega

lemma osc_switch (hkB : k * r ^ 2 ≤ B) (hk : 0 < k) (A : OnlineAlg X) (hA : IsValid 𝓕 A)
    (σ : List X)
    (D : Finset (Fin B)) (b : Fin B) (c : Fin B → Fin k) (hI : OscInv k r e A σ D b c)
    (hU : oscU e A σ b = ∅) (hc : cost A σ < k * r) :
    ∃ b', OscInv k r e A σ (insert b D) b' c ∧ (oscU e A σ b').Nonempty := by
  obtain ⟨hbD, hDr, hel, hlen, hcost⟩ := hI
  rw [hU, Finset.card_empty] at hlen hcost
  have hD1 : D.card + 1 < r := by
    by_contra h; push_neg at h
    have : k * r ≤ k * (D.card + 1) := Nat.mul_le_mul_left _ h
    omega
  classical
  let T : Finset (Fin B) := (chosen A σ).biUnion
    (fun S => Finset.univ.filter (fun d => ∃ j, e (d, j) ∈ S))
  have hT : T.card ≤ cost A σ * r := by
    refine (Finset.card_biUnion_le).trans ?_
    have : ∀ S ∈ chosen A σ, (Finset.univ.filter (fun d => ∃ j, e (d, j) ∈ S)).card ≤ r := by
      intro S hS
      obtain ⟨R, I, hR, hRI⟩ := hF1 S (osc_chosen_sub 𝓕 A hA _ hS)
      refine le_trans (Finset.card_le_card ?_) hR
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      obtain ⟨j, hj⟩ := hd
      exact ((osc_mem_blockSet R I _).1 ((hRI _).1 hj)).1
    refine (Finset.sum_le_card_nsmul _ _ r this).trans ?_
    simp [cost]
  have hcard : (T ∪ insert b D).card < (Finset.univ : Finset (Fin B)).card := by
    have h1 := Finset.card_union_le T (insert b D)
    have h2 := Finset.card_insert_le b D
    simp only [Finset.card_univ, Fintype.card_fin]
    have h3 : cost A σ * r + r ≤ k * r * r := by
      have : cost A σ + 1 ≤ k * r := hc
      nlinarith
    have h4 : k * r * r ≤ B := by nlinarith
    omega
  obtain ⟨b', _, hb'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_union, not_or] at hb'
  have hU' : oscU e A σ b' = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro t
    simp only [oscU, Finset.mem_filter, Finset.mem_univ, true_and]
    intro S hS hmem
    apply hb'.1
    exact Finset.mem_biUnion.2 ⟨S, hS, by simp; exact ⟨_, hmem⟩⟩
  have hkU : (oscU e A σ b').card = k := by rw [hU']; simp
  refine ⟨b', ⟨hb'.2, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Finset.card_insert_of_notMem hbD]; omega
  · intro y hy
    obtain ⟨p, rfl, hp1, hp2, _⟩ := hel y hy
    refine ⟨p, rfl, Finset.mem_insert_of_mem hp1, hp2, fun hpb => absurd (hpb ▸ hp1) hb'.2⟩
  · rw [hkU, Finset.card_insert_of_notMem hbD]; nlinarith
  · rw [hkU, Finset.card_insert_of_notMem hbD]; nlinarith
  · rw [hU']; exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩

theorem osc_block_core (hk : 0 < k) (hr : 0 < r) (hkB : k * r ^ 2 ≤ B)
    (A : OnlineAlg X) (hA : IsValid 𝓕 A) :
    ∃ σ : List X, σ ≠ [] ∧ σ.length ≤ k * r ∧
      (∃ S ∈ 𝓕, ∀ x ∈ σ, x ∈ S) ∧ k * r ≤ cost A σ := by
  have hrB : r ≤ B := by
    have : r ≤ k * r ^ 2 := by nlinarith
    omega
  have hB : 0 < B := by omega
  have main : ∀ n ≤ k * r, ∃ σ : List X, (∃ D b c, OscInv k r e A σ D b c) ∧
      ((k * r ≤ cost A σ ∧ σ.length ≤ k * r ∧ σ ≠ []) ∨ σ.length = n) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨[], ⟨∅, ⟨0, hB⟩, fun _ => ⟨0, hk⟩, ?_⟩, Or.inr rfl⟩
      have hU : oscU e A [] ⟨0, hB⟩ = Finset.univ := by
        apply Finset.eq_univ_of_forall; intro t
        simp [oscU, chosen, chosenFrom]
      refine ⟨by simp, by simp; omega, by simp, ?_, ?_⟩ <;> simp [hU, cost, chosen, chosenFrom]
    | succ n ih =>
      intro hn
      obtain ⟨σ, ⟨D, b, c, hI⟩, hor⟩ := ih (by omega)
      rcases hor with hdone | hlen
      · exact ⟨σ, ⟨D, b, c, hI⟩, Or.inl hdone⟩
      by_cases hc : k * r ≤ cost A σ
      · refine ⟨σ, ⟨D, b, c, hI⟩, Or.inl ⟨hc, by omega, ?_⟩⟩
        rintro rfl
        simp [cost, chosen, chosenFrom] at hc
        have : 0 < k * r := Nat.mul_pos hk hr
        omega
      push_neg at hc
      have hlen' : σ.length + 1 = n + 1 := by omega
      by_cases hU : (oscU e A σ b).Nonempty
      · obtain ⟨x, c', hI'⟩ := osc_step e 𝓕 hF1 hF2 hrB A hA σ D b c hI hU
        exact ⟨σ ++ [x], ⟨D, b, c', hI'⟩, Or.inr (by simp; omega)⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at hU
        obtain ⟨b', hI2, hU2⟩ := osc_switch e 𝓕 hF1 hF2 hkB hk A hA σ D b c hI hU hc
        obtain ⟨x, c', hI'⟩ := osc_step e 𝓕 hF1 hF2 hrB A hA σ _ b' c hI2 hU2
        exact ⟨σ ++ [x], ⟨_, b', c', hI'⟩, Or.inr (by simp; omega)⟩
  obtain ⟨σ, ⟨D, b, c, hI⟩, hor⟩ := main (k * r) le_rfl
  have hcover : ∃ S ∈ 𝓕, ∀ x ∈ σ, x ∈ S := by
    obtain ⟨hbD, hDr, hel, _, _⟩ := hI
    obtain ⟨R, hbR, hR⟩ := Finset.exists_superset_card_eq (s := insert b D) (n := r)
      (by rw [Finset.card_insert_of_notMem hbD]; omega) (by simpa using hrB)
    obtain ⟨S, hS, hpS⟩ := hF2 R c hR
    refine ⟨S, hS, fun y hy => ?_⟩
    obtain ⟨p, rfl, hp1, hp2, _⟩ := hel y hy
    exact hpS p ((osc_mem_blockSet R c p).2 ⟨hbR hp1, hp2⟩)
  rcases hor with ⟨h1, h2, h3⟩ | hlen
  · exact ⟨σ, h3, h2, hcover, h1⟩
  · obtain ⟨_, _, _, hl, hcst⟩ := hI
    refine ⟨σ, ?_, by omega, hcover, by omega⟩
    rintro rfl
    simp at hlen
    have : 0 < k * r := Nat.mul_pos hk hr
    omega

end Blk

theorem block_adversary_core (k r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (A : OnlineAlg (Fin (k * r ^ 2) × Fin (2 ^ k))) (hA : IsValid (blockFamily k r) A) :
    ∃ σ : List (Fin (k * r ^ 2) × Fin (2 ^ k)), σ ≠ [] ∧ σ.length ≤ k * r ∧
      (∃ S ∈ blockFamily k r, ∀ x ∈ σ, x ∈ S) ∧ k * r ≤ cost A σ := by
  refine osc_block_core id (blockFamily k r) ?_ ?_ hk hr le_rfl A hA
  · intro S hS
    simp only [blockFamily, Finset.mem_image, Finset.mem_product, Finset.mem_powersetCard] at hS
    obtain ⟨⟨R, I⟩, ⟨⟨_, hR⟩, _⟩, rfl⟩ := hS
    exact ⟨R, I, hR.le, fun p => Iff.rfl⟩
  · intro R I hR
    refine ⟨blockSet R I, ?_, fun p hp => hp⟩
    simp only [blockFamily, Finset.mem_image, Finset.mem_product, Finset.mem_powersetCard]
    exact ⟨(R, I), ⟨⟨Finset.subset_univ _, hR⟩, Finset.mem_univ _⟩, rfl⟩

end OnlineSetCover.LowerBound

open OnlineSetCover.LowerBound


theorem solution (k r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (A : OnlineAlg (Fin (k * r ^ 2) × Fin (2 ^ k))) (hA : IsValid (blockFamily k r) A) :
    ∃ σ : List (Fin (k * r ^ 2) × Fin (2 ^ k)), σ ≠ [] ∧ σ.length ≤ k * r ∧
      (∃ S ∈ blockFamily k r, ∀ x ∈ σ, x ∈ S) ∧ k * r ≤ cost A σ := by
  exact block_adversary_core k r hk hr A hA
