-- Prove2me | solution 1 for TestDistancing.Equilibrium.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:18:27.322811+00:00
-- url     : https://prove2.me/submissions/2b44a96c-385a-4a67-a24d-702369c5a6f9

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


end TestDistancing.Equilibrium

open TestDistancing.Equilibrium

theorem solution (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (α α' : ℝ × ℝ)
    (hα : α ∈ PolicySquare) (hα' : α' ∈ PolicySquare)
    (hle : PolicyLe α α') (i : Fin n) :
    PinfG P G α' i ≤ PinfG P G α i :=
  prop1 P hP G α α' hα hα' hle i
