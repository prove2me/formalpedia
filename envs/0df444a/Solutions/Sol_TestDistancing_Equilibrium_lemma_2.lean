-- Prove2me | solution 1 for TestDistancing.Equilibrium.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:28:18.013203+00:00
-- url     : https://prove2.me/submissions/118409a6-2d0f-4f44-a34d-683fdc9c32b3

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model
open Classical

namespace TestDistancing.Equilibrium


/-! ### Generic facts on independent Bernoulli coins -/

lemma bern_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : Bool) : 0 ≤ bern q b := by
  cases b <;> simp [bern] <;> linarith

lemma sum_bern (q : ℝ) : ∑ b : Bool, bern q b = 1 := by
  simp [bern]

lemma sum_prod_bern {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) :
    ∑ ω : ι → Bool, ∏ k, bern (q k) (ω k) = 1 := by
  rw [← Fintype.prod_sum]
  simp [bern]

/-- Expectation of `F` under independent coins with success probabilities `q`. -/
noncomputable def bexp {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ∑ ω : ι → Bool, (∏ k, bern (q k) (ω k)) * F ω

lemma bexp_mono_one {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (q q' : ι → ℝ)
    (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1) (hoff : ∀ k, k ≠ a → q' k = q k) (ha : q a ≤ q' a)
    (F : (ι → Bool) → ℝ) (hF : Monotone F) : bexp q F ≤ bexp q' F := by
  set D : (ι → Bool) → ℝ := fun ω => ∏ k ∈ Finset.univ.erase a, bern (q k) (ω k) with hDdef
  have hsplit : ∀ r : ι → ℝ, (∀ k, k ≠ a → r k = q k) → ∀ ω : ι → Bool,
      ∏ k, bern (r k) (ω k) = bern (r a) (ω a) * D ω := by
    intro r hr ω
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [hr k (Finset.ne_of_mem_erase hk)]
  set g : (ι → Bool) → ℝ := fun ω => (if ω a then (1:ℝ) else -1) * D ω * F ω with hgdef
  have hdiff : bexp q' F - bexp q F = (q' a - q a) * ∑ ω, g ω := by
    unfold bexp
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    rw [hsplit q' hoff ω, hsplit q (fun _ _ => rfl) ω]
    simp only [hgdef]
    cases ω a <;> simp [bern] <;> ring
  have hD : ∀ ω, 0 ≤ D ω := fun ω =>
    Finset.prod_nonneg (fun k _ => bern_nonneg (hq k).1 (hq k).2 _)
  let fl : (ι → Bool) → (ι → Bool) := fun ω => Function.update ω a (!ω a)
  have hinv : Function.Involutive fl := by
    intro ω
    simp [fl]
  have hDfl : ∀ ω, D (fl ω) = D ω := by
    intro ω
    simp only [hDdef]
    apply Finset.prod_congr rfl
    intro k hk
    simp [fl, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have hsum : ∑ ω, g (fl ω) = ∑ ω, g ω := Equiv.sum_comp hinv.toPerm g
  have hterm : ∀ ω, 0 ≤ g ω + g (fl ω) := by
    intro ω
    simp only [hgdef, hDfl]
    cases hωa : ω a
    · have hle : ω ≤ fl ω := by
        intro k
        by_cases hk : k = a
        · subst hk; simp [fl, hωa]
        · simp [fl, Function.update_of_ne hk]
      have := hF hle
      have h1 : fl ω a = true := by simp [fl, hωa]
      simp [h1]
      nlinarith [hD ω]
    · have hle : fl ω ≤ ω := by
        intro k
        by_cases hk : k = a
        · subst hk; simp [fl, hωa]
        · simp [fl, Function.update_of_ne hk]
      have := hF hle
      have h1 : fl ω a = false := by simp [fl, hωa]
      simp [h1]
      nlinarith [hD ω]
  have hpos : 0 ≤ ∑ ω, g ω := by
    have h2 : 2 * ∑ ω, g ω = ∑ ω, (g ω + g (fl ω)) := by
      rw [Finset.sum_add_distrib, hsum]; ring
    have := Finset.sum_nonneg (fun ω (_ : ω ∈ Finset.univ) => hterm ω)
    linarith
  have : 0 ≤ (q' a - q a) * ∑ ω, g ω := mul_nonneg (by linarith) hpos
  linarith

lemma bexp_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (q q' : ι → ℝ)
    (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1) (hq' : ∀ k, 0 ≤ q' k ∧ q' k ≤ 1)
    (hle : ∀ k, q k ≤ q' k) (F : (ι → Bool) → ℝ) (hF : Monotone F) :
    bexp q F ≤ bexp q' F := by
  let r : Finset ι → ι → ℝ := fun s k => if k ∈ s then q' k else q k
  have hr : ∀ s k, 0 ≤ r s k ∧ r s k ≤ 1 := by
    intro s k; simp only [r]; split_ifs
    · exact hq' k
    · exact hq k
  have key : ∀ s, bexp q F ≤ bexp (r s) F := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [r]
    | insert a s ha ih =>
      refine ih.trans (bexp_mono_one a (r s) (r (insert a s)) (hr s) ?_ ?_ F hF)
      · intro k hk
        simp only [r, Finset.mem_insert, hk, false_or]
      · simp only [r, Finset.mem_insert, true_or, if_true, ha, if_false]
        exact hle a
  have := key Finset.univ
  simpa [r] using this

lemma bexp_anti {ι : Type*} [Fintype ι] [DecidableEq ι] (q q' : ι → ℝ)
    (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1) (hq' : ∀ k, 0 ≤ q' k ∧ q' k ≤ 1)
    (hle : ∀ k, q k ≤ q' k) (F : (ι → Bool) → ℝ) (hF : Antitone F) :
    bexp q' F ≤ bexp q F := by
  have := bexp_mono q q' hq hq' hle (fun ω => - F ω) (fun a b h => neg_le_neg (hF h))
  unfold bexp at *
  have e1 : ∑ ω : ι → Bool, (∏ k, bern (q k) (ω k)) * -F ω =
      - ∑ ω : ι → Bool, (∏ k, bern (q k) (ω k)) * F ω := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intros; ring
  have e2 : ∑ ω : ι → Bool, (∏ k, bern (q' k) (ω k)) * -F ω =
      - ∑ ω : ι → Bool, (∏ k, bern (q' k) (ω k)) * F ω := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intros; ring
  linarith

lemma bexp_const {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (c : ℝ) :
    bexp q (fun _ => c) = c := by
  unfold bexp
  rw [← Finset.sum_mul, sum_prod_bern, one_mul]

/-! ### The cascade -/

lemma sum_T_bern {n : ℕ} (c : Fin n → ℝ) :
    ∑ T : Fin n → Fin n → Bool, ∏ k : Fin n, ∏ j : Fin n, bern (c k) (T k j) = 1 := by
  have h := Fintype.prod_sum (fun k (t : Fin n → Bool) => ∏ j : Fin n, bern (c k) (t j))
  rw [← h]
  apply Finset.prod_eq_one
  intro k _
  have := sum_prod_bern (ι := Fin n) (fun _ => c k)
  exact this

/-- Transmission sum as a Bernoulli expectation over ordered pairs. -/
lemma sum_T_eq_bexp {n : ℕ} (c : Fin n → ℝ) (H : (Fin n → Fin n → Bool) → ℝ) :
    ∑ T : Fin n → Fin n → Bool, (∏ k : Fin n, ∏ j : Fin n, bern (c k) (T k j)) * H T =
      bexp (fun kj : Fin n × Fin n => c kj.1) (fun T' => H (Function.curry T')) := by
  unfold bexp
  have h := Equiv.sum_comp (Equiv.curry (Fin n) (Fin n) Bool).symm
    (fun ω : Fin n × Fin n → Bool =>
      (∏ k, bern ((fun kj : Fin n × Fin n => c kj.1) k) (ω k)) * H (Function.curry ω))
  rw [← h]
  apply Finset.sum_congr rfl
  intro T _
  simp only [Fintype.prod_prod_type]
  rfl

lemma cascadeInf_eq {n : ℕ} (G : SimpleGraph (Fin n)) (test : Fin n → ℝ) (β p : ℝ)
    (i : Fin n) :
    cascadeInf G test β p i = ∑ s : Fin n, ((1 : ℝ) / n) *
      bexp test (fun Z => bexp (fun kj : Fin n × Fin n => if Z kj.1 then β * p else β)
        (fun T' => if Relation.ReflTransGen
          (fun k j => G.Adj k j ∧ Function.curry T' k j = true) s i then 1 else 0)) := by
  unfold cascadeInf
  apply Finset.sum_congr rfl
  intro s _
  have hZ : ∀ Z : Fin n → Bool, ∑ T : Fin n → Fin n → Bool,
      (((1 : ℝ) / n) * (∏ k : Fin n, bern (test k) (Z k)) *
        (∏ k : Fin n, ∏ j : Fin n, bern (if Z k then β * p else β) (T k j))) *
        (if Relation.ReflTransGen (fun k j => G.Adj k j ∧ T k j = true) s i then 1 else 0) =
      ((1 : ℝ) / n) * ((∏ k : Fin n, bern (test k) (Z k)) *
        bexp (fun kj : Fin n × Fin n => if Z kj.1 then β * p else β)
        (fun T' => if Relation.ReflTransGen
          (fun k j => G.Adj k j ∧ Function.curry T' k j = true) s i then 1 else 0)) := by
    intro Z
    rw [← sum_T_eq_bexp (fun k => if Z k then β * p else β)
      (fun T => if Relation.ReflTransGen (fun k j => G.Adj k j ∧ T k j = true) s i
        then (1:ℝ) else 0), Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [Finset.sum_congr rfl (fun Z _ => hZ Z)]
  unfold bexp
  rw [Finset.mul_sum]

lemma reach_mono_T {n : ℕ} (G G' : SimpleGraph (Fin n)) (hG : G ≤ G')
    (T T' : Fin n → Fin n → Bool) (hT : ∀ k j, T k j = true → T' k j = true) (s i : Fin n)
    (h : Relation.ReflTransGen (fun k j => G.Adj k j ∧ T k j = true) s i) :
    Relation.ReflTransGen (fun k j => G'.Adj k j ∧ T' k j = true) s i :=
  Relation.ReflTransGen.mono (fun _ _ h => ⟨hG h.1, hT _ _ h.2⟩) s i h

lemma ind_mono {P Q : Prop} (h : P → Q) :
    (if P then (1:ℝ) else 0) ≤ (if Q then (1:ℝ) else 0) := by
  by_cases hp : P
  · simp [hp, h hp]
  · simp only [hp, if_false]; split_ifs <;> norm_num

lemma bexp_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    (F : (ι → Bool) → ℝ) (hF : ∀ ω, 0 ≤ F ω) : 0 ≤ bexp q F := by
  unfold bexp
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg
    (Finset.prod_nonneg (fun k _ => bern_nonneg (hq k).1 (hq k).2 _)) (hF ω))

lemma bexp_le_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    (F F' : (ι → Bool) → ℝ) (hF : ∀ ω, F ω ≤ F' ω) : bexp q F ≤ bexp q F' := by
  unfold bexp
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hF ω)
    (Finset.prod_nonneg (fun k _ => bern_nonneg (hq k).1 (hq k).2 _)))

lemma cascadeInf_mono_G {n : ℕ} (G G' : SimpleGraph (Fin n)) (hG : G ≤ G')
    (test : Fin n → ℝ) (htest : ∀ k, 0 ≤ test k ∧ test k ≤ 1) (β p : ℝ)
    (hβp : 0 ≤ β * p ∧ β * p ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (i : Fin n) :
    cascadeInf G test β p i ≤ cascadeInf G' test β p i := by
  rw [cascadeInf_eq, cascadeInf_eq]
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply bexp_le_of_le _ htest
  intro Z
  apply bexp_le_of_le
  · intro kj; split_ifs
    · exact hβp
    · exact hβ
  intro T
  exact ind_mono (reach_mono_T G G' hG _ _ (fun _ _ h => h) s i)

/-- Proposition 1 core: infection on a fixed graph is antitone in testing probabilities. -/
lemma cascadeInf_anti_test {n : ℕ} (G : SimpleGraph (Fin n))
    (test test' : Fin n → ℝ) (htest : ∀ k, 0 ≤ test k ∧ test k ≤ 1)
    (htest' : ∀ k, 0 ≤ test' k ∧ test' k ≤ 1) (hle : ∀ k, test k ≤ test' k) (β p : ℝ)
    (hβp : 0 ≤ β * p) (hpβ : β * p ≤ β) (hβ : β ≤ 1) (i : Fin n) :
    cascadeInf G test' β p i ≤ cascadeInf G test β p i := by
  rw [cascadeInf_eq, cascadeInf_eq]
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hc : ∀ Z : Fin n → Bool, ∀ kj : Fin n × Fin n,
      0 ≤ (if Z kj.1 then β * p else β) ∧ (if Z kj.1 then β * p else β) ≤ 1 := by
    intro Z kj; split_ifs
    · exact ⟨hβp, by linarith⟩
    · exact ⟨by linarith, hβ⟩
  apply bexp_anti _ _ htest htest' hle
  intro Z Z' hZ
  apply bexp_mono _ _ (hc Z') (hc Z)
  · intro kj
    have := hZ kj.1
    by_cases h1 : Z kj.1 = true
    · have h2 : Z' kj.1 = true := by
        cases h : Z' kj.1
        · rw [h1, h] at this; exact absurd this (by simp)
        · rfl
      simp [h1, h2]
    · simp only [h1, Bool.false_eq_true, if_false]
      split_ifs
      · exact hpβ
      · exact le_refl _
  · intro T T' hT
    apply ind_mono
    apply reach_mono_T G G le_rfl
    intro k j h
    have := hT (k, j)
    simp only [Function.curry] at h ⊢
    rw [h] at this
    cases h' : T' (k, j)
    · rw [h'] at this; exact absurd this (by simp)
    · rfl




lemma testProb_mem {n : ℕ} (P : Params) {α : ℝ × ℝ} (hα : α ∈ PolicySquare) (k : Fin n) :
    0 ≤ testProb P α k ∧ testProb P α k ≤ 1 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hα
  unfold testProb; split_ifs
  · exact ⟨h3, h4⟩
  · exact ⟨h1, h2⟩

lemma standing_bp {P : Params} (hP : P.Standing) :
    0 ≤ P.β * P.p ∧ P.β * P.p ≤ P.β ∧ P.β ≤ 1 ∧ 0 ≤ P.β := by
  obtain ⟨_, _, _, _, _, hb0, hb1, hp0, hp1, _⟩ := hP
  refine ⟨by positivity, by nlinarith, hb1, hb0.le⟩

theorem prop1 (P : Params) (hP : P.Standing) {n : ℕ}
    (G : SimpleGraph (Fin n)) (α α' : ℝ × ℝ)
    (hα : α ∈ PolicySquare) (hα' : α' ∈ PolicySquare)
    (hle : PolicyLe α α') (i : Fin n) :
    PinfG P G α' i ≤ PinfG P G α i := by
  obtain ⟨h1, h2, h3, h4⟩ := standing_bp hP
  unfold PinfG
  apply cascadeInf_anti_test G _ _ (testProb_mem P hα) (testProb_mem P hα') _ _ _ h1 h2 h3
  intro k
  unfold testProb; split_ifs
  · exact hle.2
  · exact hle.1

/-! ### Random graph as independent coins over ordered pairs -/

/-- Graph generated by coin outcomes on ordered pairs. -/
def mkG {n : ℕ} (f : Fin n × Fin n → Bool) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ (f (a, b) = true ∨ f (b, a) = true)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma mkG_adj {n : ℕ} (f : Fin n × Fin n → Bool) (a b : Fin n) :
    (mkG f).Adj a b ↔ a ≠ b ∧ (f (a, b) = true ∨ f (b, a) = true) := Iff.rfl

/-- Link probabilities on ordered pairs (only `a < b` pairs are live). -/
noncomputable def linkQ {n : ℕ} (P : Params) (x : Fin n → ℝ) : Fin n × Fin n → ℝ :=
  fun kj => if kj.1 < kj.2 then P.η * x kj.1 * x kj.2 else 0

lemma mkG_mono {n : ℕ} {f f' : Fin n × Fin n → Bool} (h : f ≤ f') : mkG f ≤ mkG f' := by
  intro a b hab
  rw [mkG_adj] at hab ⊢
  refine ⟨hab.1, ?_⟩
  have up : ∀ kj, f kj = true → f' kj = true := by
    intro kj hk
    have := h kj
    rw [hk] at this
    cases h' : f' kj
    · rw [h'] at this; exact absurd this (by simp)
    · rfl
  rcases hab.2 with h1 | h1
  · exact Or.inl (up _ h1)
  · exact Or.inr (up _ h1)

lemma Pinf_eq_bexp {n : ℕ} (P : Params) (x : Fin n → ℝ) (α : ℝ × ℝ) (i : Fin n) :
    Pinf P x α i = bexp (linkQ P x) (fun f => PinfG P (mkG f) α i) := by
  unfold Pinf bexp
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin n × Fin n → Bool)) mkG]
  apply Finset.sum_congr rfl
  intro G _
  let fG : Fin n × Fin n → Bool := fun kj => decide (kj.1 < kj.2 ∧ G.Adj kj.1 kj.2)
  have hfG : mkG fG = G := by
    ext a b
    simp only [mkG, fG]
    constructor
    · rintro ⟨hne, h | h⟩
      · simp at h; exact h.2
      · simp at h; exact h.2.symm
    · intro hab
      refine ⟨G.ne_of_adj hab, ?_⟩
      rcases lt_or_gt_of_ne (G.ne_of_adj hab) with h | h
      · left; simp [h, hab]
      · right; simp [h, hab.symm]
  rw [Finset.sum_eq_single_of_mem fG (by simp [hfG])]
  · simp only [hfG]
    congr 1
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro a _
    apply Finset.prod_congr rfl
    intro b _
    simp only [linkQ, fG]
    by_cases hab : a < b
    · simp [hab]
    · simp [hab, bern]
  · intro f hf hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have : (∏ k, bern (linkQ P x k) (f k)) = 0 := by
      obtain ⟨kj, hkj⟩ : ∃ kj, f kj ≠ fG kj := by
        by_contra hc; push_neg at hc; exact hne (funext hc)
      by_cases hlt : kj.1 < kj.2
      · -- then f kj = false and G.Adj, so f (kj.2, kj.1) = true
        cases hf' : f kj
        · have hadj : G.Adj kj.1 kj.2 := by
            have : fG kj = true := by
              rw [hf'] at hkj
              cases h : fG kj
              · rw [h] at hkj; exact absurd rfl hkj
              · rfl
            simp [fG] at this; exact this.2
          rw [← hf, mkG_adj] at hadj
          rcases hadj.2 with h | h
          · rw [hf'] at h; exact absurd h (by simp)
          · apply Finset.prod_eq_zero (Finset.mem_univ (kj.2, kj.1))
            simp [linkQ, not_lt.mpr hlt.le, h, bern]
        · exfalso
          have hadj : G.Adj kj.1 kj.2 := by
            rw [← hf, mkG_adj]
            exact ⟨ne_of_lt hlt, Or.inl hf'⟩
          apply hkj
          rw [hf']
          simp [fG, hlt, hadj]
      · apply Finset.prod_eq_zero (Finset.mem_univ kj)
        have hfk : f kj = true := by
          cases h : f kj
          · rw [h] at hkj
            exfalso; apply hkj
            simp [fG, hlt]
          · rfl
        simp [linkQ, hlt, hfk, bern]
    rw [this, zero_mul]

lemma linkQ_mem {n : ℕ} (P : Params) (hP : P.Standing) (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (kj : Fin n × Fin n) :
    0 ≤ linkQ P x kj ∧ linkQ P x kj ≤ 1 := by
  obtain ⟨_, _, _, hη0, hη1, _⟩ := hP
  unfold linkQ
  split_ifs
  · obtain ⟨a0, a1⟩ := hx kj.1
    obtain ⟨b0, b1⟩ := hx kj.2
    constructor
    · positivity
    · have : x kj.1 * x kj.2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg a0 b0]
  · exact ⟨le_rfl, zero_le_one⟩

theorem lemma1a (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (x y : Fin n → ℝ) (α : ℝ × ℝ) (hα : α ∈ PolicySquare)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1)
    (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1)
    (hxy : ∀ j, x j ≤ y j) (i : Fin n) :
    Pinf P x α i ≤ Pinf P y α i := by
  obtain ⟨h1, h2, h3, h4⟩ := standing_bp hP
  rw [Pinf_eq_bexp, Pinf_eq_bexp]
  apply bexp_mono _ _ (linkQ_mem P hP x hx) (linkQ_mem P hP y hy)
  · intro kj
    unfold linkQ
    split_ifs
    · have hη := hP.2.2.2.1
      obtain ⟨a0, _⟩ := hx kj.1
      obtain ⟨b0, _⟩ := hx kj.2
      have := mul_le_mul (hxy kj.1) (hxy kj.2) b0 (le_trans a0 (hxy kj.1))
      have := mul_le_mul_of_nonneg_left this hη.le
      nlinarith
    · exact le_rfl
  · intro f f' hff
    unfold PinfG
    exact cascadeInf_mono_G _ _ (mkG_mono hff) _ (testProb_mem P hα) _ _ ⟨h1, by linarith⟩
      ⟨h4, h3⟩ i

/-! ### Isolated agent -/

lemma cascadeInf_isolated {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (test : Fin n → ℝ)
    (β p : ℝ) (i : Fin n) (hiso : ∀ k, ¬ G.Adj k i) :
    cascadeInf G test β p i = (1 : ℝ) / n := by
  have hreach : ∀ (s : Fin n) (T : Fin n → Fin n → Bool),
      Relation.ReflTransGen (fun k j => G.Adj k j ∧ T k j = true) s i ↔ s = i := by
    intro s T
    constructor
    · intro h
      rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, _, hc⟩
      · exact h.symm
      · exact absurd hc.1 (hiso c)
    · rintro rfl; exact Relation.ReflTransGen.refl
  unfold cascadeInf
  simp only [hreach]
  rw [Finset.sum_eq_single i]
  · simp only [if_true, mul_one]
    have : ∀ Z : Fin n → Bool, ∑ T : Fin n → Fin n → Bool,
        (1 : ℝ) / n * (∏ k, bern (test k) (Z k)) *
          ∏ k : Fin n, ∏ j : Fin n, bern (if Z k then β * p else β) (T k j) =
        (1 : ℝ) / n * (∏ k, bern (test k) (Z k)) := by
      intro Z
      rw [← Finset.mul_sum, sum_T_bern, mul_one]
    rw [Finset.sum_congr rfl (fun Z _ => this Z), ← Finset.mul_sum, sum_prod_bern, mul_one]
  · intro s _ hs
    simp [hs]
  · simp

lemma Pinf_zero {n : ℕ} (hn : 0 < n) (P : Params) (x : Fin n → ℝ) (α : ℝ × ℝ) (i : Fin n)
    (hxi : x i = 0) : Pinf P x α i = (1 : ℝ) / n := by
  rw [Pinf_eq_bexp]
  unfold bexp
  have : ∀ f : Fin n × Fin n → Bool,
      (∏ k, bern (linkQ P x k) (f k)) * PinfG P (mkG f) α i =
      (∏ k, bern (linkQ P x k) (f k)) * ((1 : ℝ) / n) := by
    intro f
    by_cases hz : (∏ k, bern (linkQ P x k) (f k)) = 0
    · rw [hz, zero_mul, zero_mul]
    · congr 1
      unfold PinfG
      apply cascadeInf_isolated hn
      intro k hk
      rw [mkG_adj] at hk
      have hq0 : ∀ kj : Fin n × Fin n, (kj.1 = i ∨ kj.2 = i) → f kj = false := by
        intro kj hkj
        by_contra hc
        apply hz
        apply Finset.prod_eq_zero (Finset.mem_univ kj)
        have : f kj = true := by simpa using hc
        rcases hkj with h | h <;> simp [linkQ, bern, this, h, hxi]
      rcases hk.2 with h | h
      · rw [hq0 (k, i) (Or.inr rfl)] at h; exact absurd h (by simp)
      · rw [hq0 (i, k) (Or.inl rfl)] at h; exact absurd h (by simp)
  rw [Finset.sum_congr rfl (fun f _ => this f), ← Finset.sum_mul, sum_prod_bern, one_mul]

lemma PinfMix_zero {n : ℕ} (hn : 0 < n) (P : Params) (γ α : ℝ × ℝ) (i : Fin n) :
    PinfMix P γ α i 0 = (1 : ℝ) / n := by
  unfold PinfMix
  rw [Finset.sum_congr rfl (fun a _ => by rw [Pinf_zero hn P _ α i (by simp)]), ← Finset.sum_mul]
  have : ∑ a : Fin n → Bool, ∏ j : Fin n, (if j = i then (if a j then (1 : ℝ) else 0)
      else bern (stratProb P γ j) (a j)) = 1 := by
    rw [← Fintype.prod_sum (fun j (b : Bool) => if j = i then (if b then (1 : ℝ) else 0)
      else bern (stratProb P γ j) b)]
    apply Finset.prod_eq_one
    intro j _
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, bern]
  rw [this, one_mul]




/-! ### Concavity helpers on `[0,1]` -/

lemma concave_sum {U : Type*} (s : Finset U) (g : U → ℝ → ℝ)
    (hg : ∀ u ∈ s, ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (g u)) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (fun t => ∑ u ∈ s, g u t) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u hu
  have := (hg u hu).2 hx hy ha hb hab
  simpa only [smul_eq_mul] using this

lemma concave_mul_const (c : ℝ) (hc : 0 ≤ c) (g : ℝ → ℝ)
    (hg : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) g) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (fun t => c * g t) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have := hg.2 hx hy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have h2 := mul_le_mul_of_nonneg_left this hc
  nlinarith [h2]

lemma prod_one_sub_convex {κ : Type*} (B : Finset κ) (c : κ → ℝ)
    (hc : ∀ k, 0 ≤ c k ∧ c k ≤ 1) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t => ∏ k ∈ B, (1 - c k * t)) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ ∏ k ∈ B, (1 - c k * t)) ∧
    AntitoneOn (fun t => ∏ k ∈ B, (1 - c k * t)) (Set.Icc (0:ℝ) 1) := by
  induction B using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨convexOn_const 1 (convex_Icc 0 1), fun _ _ => zero_le_one, fun _ _ _ _ _ => le_rfl⟩
  | insert a B ha ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hlin : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t => 1 - c a * t) := by
      refine ⟨convex_Icc 0 1, ?_⟩
      intro x _ y _ p q _ _ hpq
      simp only [smul_eq_mul]
      apply le_of_eq
      linear_combination -hpq
    have hlin0 : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ 1 - c a * t := by
      intro t ht
      have := hc a
      nlinarith [ht.1, ht.2]
    have hlinA : AntitoneOn (fun t => 1 - c a * t) (Set.Icc (0:ℝ) 1) := by
      intro x _ y _ hxy
      have := (hc a).1
      show 1 - c a * y ≤ 1 - c a * x
      nlinarith
    have e : (fun t => ∏ k ∈ insert a B, (1 - c k * t)) =
        (fun t => 1 - c a * t) * (fun t => ∏ k ∈ B, (1 - c k * t)) := by
      funext t; simp [Finset.prod_insert ha]
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · apply hlin.mul ih1 hlin0 ih2
      intro x hx y hy hlt
      by_contra hcon
      push_neg at hcon
      have h1 : y ≤ x := by
        by_contra h; push_neg at h
        have := ih3 hx hy h.le
        simp only at this hlt
        linarith
      have := hlinA hy hx h1
      simp only at this hcon
      linarith
    · intro t ht
      rw [Finset.prod_insert ha]
      exact mul_nonneg (hlin0 t ht) (ih2 t ht)
    · intro x hx y hy hxy
      exact mul_le_mul (hlinA hx hy hxy) (ih3 hx hy hxy) (ih2 y hy) (hlin0 x hx)

lemma one_sub_prod_concave {κ : Type*} (B : Finset κ) (c : κ → ℝ)
    (hc : ∀ k, 0 ≤ c k ∧ c k ≤ 1) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (fun t => 1 - ∏ k ∈ B, (1 - c k * t)) := by
  have h := (prod_one_sub_convex B c hc).1
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have := h.2 hx hy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have e : a * (1 - ∏ k ∈ B, (1 - c k * x)) + b * (1 - ∏ k ∈ B, (1 - c k * y)) =
      1 - (a * ∏ k ∈ B, (1 - c k * x) + b * ∏ k ∈ B, (1 - c k * y)) := by
    linear_combination hab
  rw [e]
  linarith

/-! ### Bernoulli expectation algebra -/

lemma bexp_sum {ι U : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (s : Finset U)
    (g : U → (ι → Bool) → ℝ) :
    bexp q (fun ω => ∑ u ∈ s, g u ω) = ∑ u ∈ s, bexp q (g u) := by
  unfold bexp
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma bexp_mul_const {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (c : ℝ)
    (F : (ι → Bool) → ℝ) :
    bexp q (fun ω => c * F ω) = c * bexp q F := by
  unfold bexp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros; ring

/-- `P(some coin in B shows true) = 1 - ∏_{k ∈ B} (1 - q_k)`. -/
lemma bexp_or {κ : Type*} [Fintype κ] [DecidableEq κ] (q : κ → ℝ) (B : Finset κ) :
    bexp q (fun ω => if ∃ k ∈ B, ω k = true then 1 else 0) = 1 - ∏ k ∈ B, (1 - q k) := by
  have e : ∀ ω : κ → Bool, (if ∃ k ∈ B, ω k = true then (1:ℝ) else 0) =
      1 - ∏ k, (if k ∈ B then (if ω k then (0:ℝ) else 1) else 1) := by
    intro ω
    by_cases h : ∃ k ∈ B, ω k = true
    · obtain ⟨k, hk, hω⟩ := h
      rw [if_pos ⟨k, hk, hω⟩, Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk, hω])]
      ring
    · push_neg at h
      rw [if_neg (by push_neg; exact h), Finset.prod_eq_one]
      · ring
      · intro k _
        by_cases hk : k ∈ B
        · simp [hk, h k hk]
        · simp [hk]
  unfold bexp
  simp_rw [e, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, sum_prod_bern]
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k (b : Bool) => bern (q k) b *
      (if k ∈ B then (if b then (0:ℝ) else 1) else 1))]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => k ∈ B)]
  have h1 : ∏ k ∈ Finset.univ.filter (fun k => ¬ k ∈ B),
      ∑ b : Bool, bern (q k) b * (if k ∈ B then (if b then (0:ℝ) else 1) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    simp only [Finset.mem_filter] at hk
    simp [hk.2, bern]
  rw [h1, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.prod_congr rfl
  intro k hk
  simp [hk, bern]

lemma bexp_split {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (q : ι → ℝ) (F : (ι → Bool) → ℝ) :
    bexp q F = ∑ ω₂ : {k // ¬ p k} → Bool, (∏ k : {k // ¬ p k}, bern (q k) (ω₂ k)) *
      bexp (fun k : {k // p k} => q k)
        (fun ω₁ => F ((Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).symm (ω₁, ω₂))) := by
  unfold bexp
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).symm,
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω₂ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω₁ _
  rw [← Fintype.prod_subtype_mul_prod_subtype p]
  have h1 : ∀ k : {k // p k}, bern (q k)
      ((Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).symm (ω₁, ω₂) k) = bern (q k) (ω₁ k) := by
    intro k; simp [Equiv.piEquivPiSubtypeProd_symm_apply, k.2]
  have h2 : ∀ k : {k // ¬ p k}, bern (q k)
      ((Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).symm (ω₁, ω₂) k) = bern (q k) (ω₂ k) := by
    intro k; simp [Equiv.piEquivPiSubtypeProd_symm_apply, k.2]
  simp only [h1, h2]
  ring

/-! ### First-hit decomposition of reachability -/

lemma rtg_split {α : Type*} (r : α → α → Prop) (s i : α) :
    Relation.ReflTransGen r s i ↔
      s = i ∨ ∃ j, j ≠ i ∧
        Relation.ReflTransGen (fun k j => r k j ∧ k ≠ i ∧ j ≠ i) s j ∧ r j i := by
  constructor
  · intro h
    have key : ∀ y, Relation.ReflTransGen r s y → s = i ∨
        (y ≠ i ∧ Relation.ReflTransGen (fun k j => r k j ∧ k ≠ i ∧ j ≠ i) s y) ∨
        ∃ j, j ≠ i ∧ Relation.ReflTransGen (fun k j => r k j ∧ k ≠ i ∧ j ≠ i) s j ∧ r j i := by
      intro y hy
      induction hy with
      | refl =>
        by_cases hs : s = i
        · exact Or.inl hs
        · exact Or.inr (Or.inl ⟨hs, Relation.ReflTransGen.refl⟩)
      | @tail b c _ hbc ih =>
        rcases ih with h | ⟨hb, hp⟩ | h
        · exact Or.inl h
        · by_cases hc : c = i
          · subst hc; exact Or.inr (Or.inr ⟨b, hb, hp, hbc⟩)
          · exact Or.inr (Or.inl ⟨hc, hp.tail ⟨hbc, hb, hc⟩⟩)
        · exact Or.inr (Or.inr h)
    rcases key i h with h | ⟨h, _⟩ | h
    · exact Or.inl h
    · exact absurd rfl h
    · exact Or.inr h
  · rintro (rfl | ⟨j, _, hp, hr⟩)
    · exact Relation.ReflTransGen.refl
    · exact (Relation.ReflTransGen.mono (fun a b h => h.1) s j hp).tail hr




/-- Ordered pairs touching agent `i`. -/
def SI {n : ℕ} (i : Fin n) (k : Fin n × Fin n) : Prop := k.1 = i ∨ k.2 = i

/-- The endpoint of a pair other than `i`. -/
def otherE {n : ℕ} (i : Fin n) (k : Fin n × Fin n) : Fin n := if k.1 = i then k.2 else k.1

noncomputable def mergeI {n : ℕ} (i : Fin n) (ω₁ : {k // SI i k} → Bool)
    (ω₂ : {k // ¬ SI i k} → Bool) : Fin n × Fin n → Bool :=
  (Equiv.piEquivPiSubtypeProd (SI i) (fun _ => Bool)).symm (ω₁, ω₂)

lemma mergeI_in {n : ℕ} (i : Fin n) (ω₁ : {k // SI i k} → Bool)
    (ω₂ : {k // ¬ SI i k} → Bool) (kj : Fin n × Fin n) (h : SI i kj) :
    mergeI i ω₁ ω₂ kj = ω₁ ⟨kj, h⟩ := by
  simp [mergeI, Equiv.piEquivPiSubtypeProd_symm_apply, h]

lemma mergeI_out {n : ℕ} (i : Fin n) (ω₁ : {k // SI i k} → Bool)
    (ω₂ : {k // ¬ SI i k} → Bool) (kj : Fin n × Fin n) (h : ¬ SI i kj) :
    mergeI i ω₁ ω₂ kj = ω₂ ⟨kj, h⟩ := by
  simp [mergeI, Equiv.piEquivPiSubtypeProd_symm_apply, h]

lemma PinfG_eq {n : ℕ} (P : Params) (G : SimpleGraph (Fin n)) (α : ℝ × ℝ) (i : Fin n) :
    PinfG P G α i = ∑ s : Fin n, ∑ Z : Fin n → Bool, ∑ T : Fin n → Fin n → Bool,
      ((1 : ℝ) / n) * (∏ k : Fin n, bern (testProb P α k) (Z k)) *
        (∏ k : Fin n, ∏ j : Fin n, bern (if Z k then P.β * P.p else P.β) (T k j)) *
      (if Relation.ReflTransGen (fun k j => G.Adj k j ∧ T k j = true) s i then 1 else 0) := rfl

lemma linkQ_mem' (P : Params) (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) {n : ℕ} (x : Fin n → ℝ)
    (i : Fin n) (hx : ∀ j, j ≠ i → x j ∈ Set.Icc (0 : ℝ) 1) (k : {k // ¬ SI i k}) :
    0 ≤ linkQ P x k ∧ linkQ P x k ≤ 1 := by
  have h1 : k.1.1 ≠ i := fun h => k.2 (Or.inl h)
  have h2 : k.1.2 ≠ i := fun h => k.2 (Or.inr h)
  obtain ⟨a0, a1⟩ := hx _ h1
  obtain ⟨b0, b1⟩ := hx _ h2
  unfold linkQ
  split_ifs
  · constructor
    · positivity
    · have : x k.1.1 * x k.1.2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg a0 b0]
  · exact ⟨le_rfl, zero_le_one⟩

/-- The core: for a fixed source and transmission pattern, the probability over the random
links that `i` is reached is concave in `i`'s own activity. -/
lemma reach_concave (P : Params) (hP : P.Standing) {n : ℕ} (x : Fin n → ℝ) (i : Fin n)
    (hx : ∀ j, j ≠ i → x j ∈ Set.Icc (0 : ℝ) 1) (s : Fin n) (T : Fin n → Fin n → Bool) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => bexp (linkQ P (Function.update x i t))
      (fun f => if Relation.ReflTransGen (fun k j => (mkG f).Adj k j ∧ T k j = true) s i
        then 1 else 0)) := by
  obtain ⟨_, _, _, hη0, hη1, _⟩ := hP
  -- auxiliary objects
  let f0 : ({k // ¬ SI i k} → Bool) → Fin n × Fin n → Bool := fun ω₂ => mergeI i (fun _ => false) ω₂
  let A : ({k // ¬ SI i k} → Bool) → Fin n → Prop := fun ω₂ j => j ≠ i ∧
    Relation.ReflTransGen (fun k j => ((mkG (f0 ω₂)).Adj k j ∧ T k j = true) ∧ k ≠ i ∧ j ≠ i) s j ∧
    T j i = true
  let B : ({k // ¬ SI i k} → Bool) → Finset {k // SI i k} :=
    fun ω₂ => Finset.univ.filter (fun k => A ω₂ (otherE i k.1))
  let c : {k // SI i k} → ℝ := fun k => if k.1.1 < k.1.2 then P.η * x (otherE i k.1) else 0
  have hc : ∀ k, 0 ≤ c k ∧ c k ≤ 1 := by
    intro k
    simp only [c]
    split_ifs with hlt
    · have hne : otherE i k.1 ≠ i := by
        unfold otherE
        by_cases h1 : k.1.1 = i
        · rw [if_pos h1]; intro h2
          have : k.1.1 = k.1.2 := h1.trans h2.symm
          rw [this] at hlt; exact lt_irrefl _ hlt
        · rw [if_neg h1]; exact h1
      obtain ⟨h0, h1⟩ := hx _ hne
      exact ⟨by positivity, by nlinarith⟩
    · exact ⟨le_rfl, zero_le_one⟩
  -- coin probabilities
  have hq_out : ∀ t, ∀ k : {k // ¬ SI i k},
      linkQ P (Function.update x i t) k = linkQ P x k := by
    intro t k
    have h1 : k.1.1 ≠ i := fun h => k.2 (Or.inl h)
    have h2 : k.1.2 ≠ i := fun h => k.2 (Or.inr h)
    simp [linkQ, Function.update_of_ne h1, Function.update_of_ne h2]
  have hq_in : ∀ t, ∀ k : {k // SI i k},
      linkQ P (Function.update x i t) k = c k * t := by
    intro t k
    simp only [linkQ, c, otherE]
    by_cases hlt : k.1.1 < k.1.2
    · rw [if_pos hlt, if_pos hlt]
      rcases k.2 with h | h
      · have h2 : k.1.2 ≠ i := by intro h2; rw [h, h2] at hlt; exact lt_irrefl _ hlt
        rw [if_pos h, h, Function.update_self, Function.update_of_ne h2]; try ring
      · have h1 : k.1.1 ≠ i := by intro h1; rw [h1, h] at hlt; exact lt_irrefl _ hlt
        rw [if_neg h1, h, Function.update_self, Function.update_of_ne h1]; try ring
    · rw [if_neg hlt, if_neg hlt]; ring
  -- the indicator
  have hind : ∀ ω₂ ω₁, (if Relation.ReflTransGen
      (fun k j => (mkG (mergeI i ω₁ ω₂)).Adj k j ∧ T k j = true) s i then (1:ℝ) else 0) =
      if s = i then 1 else (if ∃ k ∈ B ω₂, ω₁ k = true then 1 else 0) := by
    intro ω₂ ω₁
    have hrel : (fun k j => ((mkG (mergeI i ω₁ ω₂)).Adj k j ∧ T k j = true) ∧ k ≠ i ∧ j ≠ i) =
        (fun k j => ((mkG (f0 ω₂)).Adj k j ∧ T k j = true) ∧ k ≠ i ∧ j ≠ i) := by
      funext k j
      apply propext
      have e : ∀ (a b : Fin n), a ≠ i → b ≠ i →
          mergeI i ω₁ ω₂ (a, b) = f0 ω₂ (a, b) := by
        intro a b ha hb
        have hns : ¬ SI i (a, b) := by
          rintro (h | h)
          · exact ha h
          · exact hb h
        simp only [f0]
        rw [mergeI_out _ _ _ _ hns, mergeI_out _ _ _ _ hns]
      constructor
      · rintro ⟨⟨hadj, hT⟩, hk, hj⟩
        rw [mkG_adj] at hadj
        refine ⟨⟨?_, hT⟩, hk, hj⟩
        rw [mkG_adj, ← e k j hk hj, ← e j k hj hk]
        exact hadj
      · rintro ⟨⟨hadj, hT⟩, hk, hj⟩
        rw [mkG_adj] at hadj
        refine ⟨⟨?_, hT⟩, hk, hj⟩
        rw [mkG_adj, e k j hk hj, e j k hj hk]
        exact hadj
    have hiff : Relation.ReflTransGen
        (fun k j => (mkG (mergeI i ω₁ ω₂)).Adj k j ∧ T k j = true) s i ↔
        s = i ∨ ∃ k ∈ B ω₂, ω₁ k = true := by
      rw [rtg_split, hrel]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨j, hj, hp, hadj, hT⟩
        rw [mkG_adj] at hadj
        rcases hadj.2 with h | h
        · -- coin on (j, i)
          have hs : SI i (j, i) := Or.inr rfl
          refine ⟨⟨(j, i), hs⟩, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            have ho : otherE i (j, i) = j := by simp [otherE, hj]
            show A ω₂ (otherE i (j, i))
            rw [ho]; exact ⟨hj, hp, hT⟩
          · rw [mergeI_in _ _ _ _ hs] at h; exact h
        · have hs : SI i (i, j) := Or.inl rfl
          refine ⟨⟨(i, j), hs⟩, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            have ho : otherE i (i, j) = j := by simp [otherE]
            show A ω₂ (otherE i (i, j))
            rw [ho]; exact ⟨hj, hp, hT⟩
          · rw [mergeI_in _ _ _ _ hs] at h; exact h
      · rintro ⟨k, hk, hω⟩
        obtain ⟨hj, hp, hT⟩ := (Finset.mem_filter.mp hk).2
        refine ⟨otherE i k.1, hj, hp, ?_, hT⟩
        rw [mkG_adj]
        refine ⟨hj, ?_⟩
        unfold otherE at hj ⊢
        by_cases h1 : k.1.1 = i
        · rw [if_pos h1] at hj ⊢
          right
          have : (i, k.1.2) = k.1 := Prod.ext h1.symm rfl
          rw [mergeI_in i ω₁ ω₂ (i, k.1.2) (Or.inl rfl)]
          have hk' : (⟨(i, k.1.2), Or.inl rfl⟩ : {k // SI i k}) = k := Subtype.ext this
          rw [hk']; exact hω
        · rw [if_neg h1] at hj ⊢
          left
          have h2 : k.1.2 = i := by
            rcases k.2 with h | h
            · exact absurd h h1
            · exact h
          have : (k.1.1, i) = k.1 := Prod.ext rfl h2.symm
          rw [mergeI_in i ω₁ ω₂ (k.1.1, i) (Or.inr rfl)]
          have hk' : (⟨(k.1.1, i), Or.inr rfl⟩ : {k // SI i k}) = k := Subtype.ext this
          rw [hk']; exact hω
    by_cases hs : s = i
    · rw [if_pos (hiff.2 (Or.inl hs)), if_pos hs]
    · rw [if_neg hs]
      by_cases hex : ∃ k ∈ B ω₂, ω₁ k = true
      · rw [if_pos (hiff.2 (Or.inr hex)), if_pos hex]
      · rw [if_neg (by rw [hiff]; push_neg; exact ⟨hs, by push_neg at hex; exact hex⟩),
          if_neg hex]
  -- rewrite the function
  have hfun : (fun t => bexp (linkQ P (Function.update x i t))
      (fun f => if Relation.ReflTransGen (fun k j => (mkG f).Adj k j ∧ T k j = true) s i
        then (1:ℝ) else 0)) =
      (fun t => ∑ ω₂ : {k // ¬ SI i k} → Bool,
        (∏ k : {k // ¬ SI i k}, bern (linkQ P x k) (ω₂ k)) *
        (if s = i then 1 else 1 - ∏ k ∈ B ω₂, (1 - c k * t))) := by
    funext t
    rw [bexp_split (SI i)]
    apply Finset.sum_congr rfl
    intro ω₂ _
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      rw [hq_out t k]
    · have h1 : (fun ω₁ : {k // SI i k} → Bool =>
          (if Relation.ReflTransGen (fun k j =>
            (mkG ((Equiv.piEquivPiSubtypeProd (SI i) fun _ => Bool).symm (ω₁, ω₂))).Adj k j ∧
              T k j = true) s i then (1:ℝ) else 0)) =
          (fun ω₁ => if s = i then 1 else (if ∃ k ∈ B ω₂, ω₁ k = true then 1 else 0)) := by
        funext ω₁
        exact hind ω₂ ω₁
      rw [h1]
      by_cases hs : s = i
      · simp only [hs, if_true]
        exact bexp_const _ 1
      · simp only [hs, if_false]
        rw [bexp_or]
        congr 1
        apply Finset.prod_congr rfl
        intro k _
        rw [hq_in t k]
  rw [hfun]
  apply concave_sum
  intro ω₂ _
  apply concave_mul_const
  · exact Finset.prod_nonneg (fun k _ => bern_nonneg (linkQ_mem' P hη0 hη1 x i hx k).1
      (linkQ_mem' P hη0 hη1 x i hx k).2 _)
  · by_cases hs : s = i
    · simp only [hs, if_true]
      exact concaveOn_const 1 (convex_Icc 0 1)
    · simp only [hs, if_false]
      exact one_sub_prod_concave (B ω₂) c hc



theorem lemma1b (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (α : ℝ × ℝ) (hα : α ∈ PolicySquare) (i : Fin n)
    (hx : ∀ j, j ≠ i → x j ∈ Set.Icc (0 : ℝ) 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t => Pinf P (Function.update x i t) α i) := by
  obtain ⟨h1, h2, h3, h4⟩ := standing_bp hP
  have e : (fun t => Pinf P (Function.update x i t) α i) = fun t =>
      ∑ s : Fin n, ∑ Z : Fin n → Bool, ∑ T : Fin n → Fin n → Bool,
        ((1 : ℝ) / n) * (∏ k : Fin n, bern (testProb P α k) (Z k)) *
          (∏ k : Fin n, ∏ j : Fin n, bern (if Z k then P.β * P.p else P.β) (T k j)) *
        bexp (linkQ P (Function.update x i t))
          (fun f => if Relation.ReflTransGen (fun k j => (mkG f).Adj k j ∧ T k j = true) s i
            then 1 else 0) := by
    funext t
    rw [Pinf_eq_bexp]
    simp only [PinfG_eq]
    simp_rw [bexp_sum, bexp_mul_const]
  rw [e]
  apply concave_sum; intro s _
  apply concave_sum; intro Z _
  apply concave_sum; intro T _
  apply concave_mul_const
  · have hZ : 0 ≤ ∏ k : Fin n, bern (testProb P α k) (Z k) :=
      Finset.prod_nonneg (fun k _ => bern_nonneg (testProb_mem P hα k).1 (testProb_mem P hα k).2 _)
    have hT : 0 ≤ ∏ k : Fin n, ∏ j : Fin n, bern (if Z k then P.β * P.p else P.β) (T k j) := by
      apply Finset.prod_nonneg; intro k _
      apply Finset.prod_nonneg; intro j _
      split_ifs
      · exact bern_nonneg h1 (by linarith) _
      · exact bern_nonneg h4 h3 _
    positivity
  · exact reach_concave P hP x i hx s T

theorem lemma2' (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (α : ℝ × ℝ) (hα : α ∈ PolicySquare) (i : Fin n)
    (hx : ∀ j, j ≠ i → x j ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hbest : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      pureUtil P (Function.update x i s) α i ≤ pureUtil P (Function.update x i t) α i) :
    t = 0 ∨ t = 1 ∨
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        pureUtil P (Function.update x i s) α i = pureUtil P (Function.update x i t) α i := by
  have hcc := lemma1b P hP hn x α hα i hx
  set f : ℝ → ℝ := fun s => pureUtil P (Function.update x i s) α i with hf
  have hfe : ∀ s, f s = val P i * s - Pinf P (Function.update x i s) α i - P.c * testProb P α i := by
    intro s; simp [hf, pureUtil]
  -- convexity inequality for f
  have hconv : ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ v ∈ Set.Icc (0:ℝ) 1, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → f (a * u + b * v) ≤ a * f u + b * f v := by
    intro u hu v hv a b ha hb hab
    have := hcc.2 hu hv ha hb hab
    simp only [smul_eq_mul] at this
    rw [hfe, hfe, hfe]
    have e : val P i * (a * u + b * v) = a * (val P i * u) + b * (val P i * v) := by ring
    have e2 : P.c * testProb P α i = a * (P.c * testProb P α i) + b * (P.c * testProb P α i) := by
      rw [← add_mul, hab, one_mul]
    nlinarith
  by_cases h0 : t = 0
  · exact Or.inl h0
  by_cases h1 : t = 1
  · exact Or.inr (Or.inl h1)
  right; right
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
  intro s hs
  apply le_antisymm (hbest s hs)
  show f t ≤ f s
  have hf1 : f 1 ≤ f t := hbest 1 ⟨zero_le_one, le_rfl⟩
  have hf0 : f 0 ≤ f t := hbest 0 ⟨le_rfl, zero_le_one⟩
  rcases lt_trichotomy s t with hst | hst | hst
  · have hs1 : 0 < 1 - s := by linarith
    set a := (1 - t) / (1 - s)
    set b := (t - s) / (1 - s)
    have ha : 0 < a := div_pos (by linarith) hs1
    have hb : 0 ≤ b := div_nonneg (by linarith) hs1.le
    have hab : a + b = 1 := by
      simp only [a, b]; field_simp; ring
    have hpt : a * s + b * 1 = t := by
      simp only [a, b]; field_simp; ring
    have := hconv s hs 1 ⟨zero_le_one, le_rfl⟩ a b ha.le hb hab
    rw [hpt] at this
    have k := mul_le_mul_of_nonneg_left hf1 hb
    have k2 : a * f t = f t - b * f t := by linear_combination (f t) * hab
    have : a * f t ≤ a * f s := by linarith
    exact le_of_mul_le_mul_left this ha
  · rw [hst]
  · have hs0 : 0 < s := by linarith
    set a := (s - t) / s
    set b := t / s
    have hb : 0 < b := div_pos ht0 hs0
    have ha : 0 ≤ a := div_nonneg (by linarith) hs0.le
    have hab : a + b = 1 := by
      simp only [a, b]; field_simp; ring
    have hpt : a * 0 + b * s = t := by
      simp only [a, b]; field_simp; ring
    have := hconv 0 ⟨le_rfl, zero_le_one⟩ s hs a b ha hb.le hab
    rw [hpt] at this
    have k := mul_le_mul_of_nonneg_left hf0 ha
    have k2 : b * f t = f t - a * f t := by linear_combination (f t) * hab
    have : b * f t ≤ b * f s := by linarith
    exact le_of_mul_le_mul_left this hb


end TestDistancing.Equilibrium

open TestDistancing.Equilibrium

theorem solution (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (α : ℝ × ℝ) (hα : α ∈ PolicySquare) (i : Fin n)
    (hx : ∀ j, j ≠ i → x j ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hbest : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      pureUtil P (Function.update x i s) α i ≤ pureUtil P (Function.update x i t) α i) :
    t = 0 ∨ t = 1 ∨
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        pureUtil P (Function.update x i s) α i = pureUtil P (Function.update x i t) α i :=
  lemma2' P hP hn x α hα i hx t ht hbest
