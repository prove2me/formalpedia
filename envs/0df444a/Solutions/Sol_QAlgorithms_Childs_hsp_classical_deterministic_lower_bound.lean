-- Prove2me | solution 1 for QAlgorithms.Childs.hsp_classical_deterministic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:50:17.94861+00:00
-- url     : https://prove2.me/submissions/691687b7-aad1-4d5a-b592-6111dd0de3d1

import Definitions.Def_QAlgorithms_Defs_Fourier
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open QAlgorithms

universe u v

private def asked {G S O : Type*} [DecidableEq G] : DecisionTree G S O → (G → S) → Finset G
  | .leaf _, _ => ∅
  | .node x next, f => insert x (asked (next (f x)) f)

private lemma asked_card {G S O : Type*} [DecidableEq G]
    (A : DecisionTree G S O) (f : G → S) : (asked A f).card ≤ A.queries f := by
  induction A with
  | leaf o => simp [asked, DecisionTree.queries]
  | node x next ih =>
    simp only [asked, DecisionTree.queries]
    have := Finset.card_insert_le x (asked (next (f x)) f)
    have := ih (f x)
    omega

private lemma eval_eq_of_agree {G S O : Type*} [DecidableEq G]
    (A : DecisionTree G S O) (f f' : G → S)
    (h : ∀ x ∈ asked A f, f x = f' x) : A.eval f = A.eval f' := by
  induction A with
  | leaf o => rfl
  | node x next ih =>
    have hx := h x (by simp [asked])
    simp only [DecisionTree.eval, ← hx]
    exact ih (f x) (fun y hy => h y (by simp [asked, hy]))

private lemma hides_bot {G : Type u} {S : Type v} [Group G]
    (e : G ↪ S) : Hides e ⊥ := by
  intro x y
  simp only [e.injective.eq_iff, Subgroup.mem_bot, inv_mul_eq_one]

private lemma complete_oracle {G : Type u} {S : Type v} [Group G]
    (e : G ↪ S) (H : Subgroup G) (Q : Finset G)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x⁻¹ * y ∈ H → x = y) :
    ∃ f : G → S, Hides f H ∧ ∀ x ∈ Q, f x = e x := by
  classical
  let rep : G ⧸ H → G := fun q =>
    if h : ∃ x ∈ Q, (QuotientGroup.mk x : G ⧸ H) = q then h.choose else q.out
  have hrep (q : G ⧸ H) : (QuotientGroup.mk (rep q) : G ⧸ H) = q := by
    dsimp [rep]
    split_ifs with h
    · exact h.choose_spec.2
    · exact q.out_eq'
  have hinj : Function.Injective rep := by
    intro q r h
    rw [← hrep q, ← hrep r, h]
  refine ⟨fun x => e (rep (QuotientGroup.mk x)), ?_, ?_⟩
  · intro x y
    exact (e.injective.eq_iff.trans hinj.eq_iff).trans QuotientGroup.eq
  · intro x hx
    apply congrArg e
    have h : ∃ y ∈ Q, (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk x := ⟨x, hx, rfl⟩
    have hr : rep (QuotientGroup.mk x) ∈ Q := by
      dsimp [rep]; rw [dif_pos h]; exact h.choose_spec.1
    exact hQ _ hr x hx (QuotientGroup.eq.mp (hrep (QuotientGroup.mk x)))

private lemma collision_of_correct {G : Type u} {S : Type v} [Group G] [DecidableEq G]
    (e : G ↪ S) (A : DecisionTree G S (Subgroup G))
    (hA : ∀ H f, Hides f H → A.eval f = H)
    (H : Subgroup G) (hH : H ≠ ⊥) :
    ∃ x ∈ asked A e, ∃ y ∈ asked A e, x ≠ y ∧ x⁻¹ * y ∈ H := by
  classical
  by_contra hn
  have hQ : ∀ x ∈ asked A e, ∀ y ∈ asked A e, x⁻¹ * y ∈ H → x = y := by
    intro x hx y hy hxy
    by_contra hne
    exact hn ⟨x, hx, y, hy, hne, hxy⟩
  obtain ⟨f, hf, hagree⟩ := complete_oracle e H (asked A e) hQ
  have heq := eval_eq_of_agree A e f (fun x hx => (hagree x hx).symm)
  rw [hA _ _ (hides_bot e), hA _ _ hf] at heq
  exact hH heq.symm

private lemma family_bound {G : Type u} {S : Type v} [Group G] [DecidableEq G]
    (e : G ↪ S) (A : DecisionTree G S (Subgroup G))
    (hA : ∀ H f, Hides f H → A.eval f = H)
    (F : Finset (Subgroup G))
    (hF : (F : Set (Subgroup G)).Pairwise (fun H K => H ⊓ K = ⊥)) :
    F.card ≤ (A.queries e) ^ 2 + 1 := by
  classical
  let Q := asked A e
  let T := F.erase ⊥
  have hw (H : T) : ∃ p : G × G,
      p.1 ∈ Q ∧ p.2 ∈ Q ∧ p.1 ≠ p.2 ∧ p.1⁻¹ * p.2 ∈ H.val := by
    obtain ⟨x, hx, y, hy, hne, hmem⟩ := collision_of_correct e A hA H.val
      (Finset.mem_erase.mp H.property).1
    exact ⟨(x, y), hx, hy, hne, hmem⟩
  let w : T → Q ×ˢ Q := fun H => ⟨(hw H).choose, by
    exact Finset.mem_product.mpr ⟨(hw H).choose_spec.1, (hw H).choose_spec.2.1⟩⟩
  have winj : Function.Injective w := by
    intro H K heq
    apply Subtype.ext
    by_contra hne
    have hp : (hw H).choose = (hw K).choose := congrArg Subtype.val heq
    have hmem : (hw H).choose.1⁻¹ * (hw H).choose.2 ∈ H.val ⊓ K.val := by
      constructor
      · exact (hw H).choose_spec.2.2.2
      · rw [hp]; exact (hw K).choose_spec.2.2.2
    rw [hF (Finset.mem_erase.mp H.property).2 (Finset.mem_erase.mp K.property).2 hne] at hmem
    have hxy : (hw H).choose.1 = (hw H).choose.2 := by
      simpa only [Subgroup.mem_bot, inv_mul_eq_one] using hmem
    exact (hw H).choose_spec.2.2.1 hxy
  have hcard := Finset.card_le_card_of_injective winj
  have hT : F.card ≤ T.card + 1 := by
    have := Finset.pred_card_le_card_erase (s := F) (a := ⊥)
    dsimp [T]
    omega
  have hQ := asked_card A e
  simp only [Finset.card_product] at hcard
  dsimp [Q] at hcard
  nlinarith

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (G : Type u) [Group G] [Fintype G] (S : Type v) [Fintype S],
        Fintype.card G ≤ Fintype.card S →
        ∀ ℋ : Finset (Subgroup G), ℋ.card = N →
        (ℋ : Set (Subgroup G)).Pairwise (fun H K => H ⊓ K = ⊥) →
        ∀ A : DecisionTree G S (Subgroup G),
          (∀ (H : Subgroup G) (f : G → S), Hides f H → A.eval f = H) →
          ∃ (H : Subgroup G) (f : G → S), Hides f H ∧
            c * Real.sqrt (N : ℝ) ≤ (A.queries f : ℝ) := by
  classical
  refine ⟨1 / 2, by norm_num, 2, ?_⟩
  intro N hN G _ _ S _ hGS F hFN hF A hA
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hGS
  refine ⟨⊥, e, hides_bot e, ?_⟩
  have hb := family_bound e A hA F hF
  rw [hFN] at hb
  have ht : 1 ≤ A.queries e := by nlinarith
  have hbR : (N : ℝ) ≤ (A.queries e : ℝ) ^ 2 + 1 := by exact_mod_cast hb
  have htR : (1 : ℝ) ≤ (A.queries e : ℝ) := by exact_mod_cast ht
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hpos := Real.sqrt_nonneg (N : ℝ)
  nlinarith [sq_nonneg (Real.sqrt (N : ℝ) - 2 * (A.queries e : ℝ))]
