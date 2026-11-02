-- Prove2me | solution 1 for TestDistancing.Equilibrium.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:54:20.849343+00:00
-- url     : https://prove2.me/submissions/d20c35ba-d6c8-4a93-900e-663d2f6490b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model
import Theorems.Thm_TestDistancing_Equilibrium_proposition_2
import Theorems.Thm_TestDistancing_Equilibrium_regions_cover
import Theorems.Thm_TestDistancing_Equilibrium_eq_9
import Theorems.Thm_TestDistancing_Equilibrium_eq_10
import Theorems.Thm_TestDistancing_Equilibrium_gammaL_mono
import Theorems.Thm_TestDistancing_Equilibrium_proposition_1
import Theorems.Thm_TestDistancing_Equilibrium_lemma_1_a
import Theorems.Thm_TestDistancing_Equilibrium_lemma_1_b
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




/-! ### Strict monotonicity tools -/

lemma bexp_ge_single {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ)
    (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1) (F : (ι → Bool) → ℝ) (hF : ∀ ω, 0 ≤ F ω) (ω : ι → Bool) :
    (∏ k, bern (q k) (ω k)) * F ω ≤ bexp q F := by
  unfold bexp
  exact Finset.single_le_sum (f := fun ω => (∏ k, bern (q k) (ω k)) * F ω)
    (fun ω _ => mul_nonneg (Finset.prod_nonneg (fun k _ => bern_nonneg (hq k).1 (hq k).2 _))
      (hF ω)) (Finset.mem_univ ω)

lemma bexp_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ)
    (F G : (ι → Bool) → ℝ) : bexp q F - bexp q G = bexp q (fun ω => F ω - G ω) := by
  unfold bexp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros; ring

lemma bexp_strict_one {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (q q' : ι → ℝ)
    (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1) (hoff : ∀ k, k ≠ a → q' k = q k) (ha : q a < q' a)
    (F : (ι → Bool) → ℝ) (hF : Monotone F) (ω₀ : ι → Bool)
    (hpos : ∀ k, k ≠ a → 0 < bern (q k) (ω₀ k))
    (hgap : F (Function.update ω₀ a false) < F (Function.update ω₀ a true)) :
    bexp q F < bexp q' F := by
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
  -- the special term
  set ω₁ := Function.update ω₀ a true with hω₁
  have hfl1 : fl ω₁ = Function.update ω₀ a false := by
    simp [fl, ω₁]
  have hD1 : 0 < D ω₁ := by
    simp only [hDdef]
    apply Finset.prod_pos
    intro k hk
    have hka := Finset.ne_of_mem_erase hk
    simp only [ω₁, Function.update_of_ne hka]
    exact hpos k hka
  have hspecial : 0 < g ω₁ + g (fl ω₁) := by
    simp only [hgdef, hDfl]
    have h1 : ω₁ a = true := by simp [ω₁]
    have h2 : fl ω₁ a = false := by simp [fl, h1]
    rw [h1, h2, hfl1]
    simp only [if_true, Bool.false_eq_true, if_false]
    have : 0 < D ω₁ * (F ω₁ - F (Function.update ω₀ a false)) :=
      mul_pos hD1 (by simp only [ω₁]; linarith)
    linarith
  have hpos' : 0 < ∑ ω, g ω := by
    have h2 : 2 * ∑ ω, g ω = ∑ ω, (g ω + g (fl ω)) := by
      rw [Finset.sum_add_distrib, hsum]; ring
    have := Finset.single_le_sum (f := fun ω => g ω + g (fl ω))
      (fun ω _ => hterm ω) (Finset.mem_univ ω₁)
    linarith
  have : 0 < (q' a - q a) * ∑ ω, g ω := mul_pos (by linarith) hpos'
  linarith



lemma bexp_zero_prob {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ)
    (hq : ∀ k, q k = 0) (H : (ι → Bool) → ℝ) : bexp q H = H (fun _ => false) := by
  unfold bexp
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp [hq, bern]
  · intro ω _ hω
    obtain ⟨k, hk⟩ : ∃ k, ω k ≠ false := by
      by_contra hc; push_neg at hc; exact hω (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ k)]
    · ring
    · have : ω k = true := by simpa using hk
      simp [hq, bern, this]
  · simp

/-- Strict gain from adding a direct link from an otherwise isolated node. -/
lemma cascade_gap {n : ℕ} (G0 G1 : SimpleGraph (Fin n)) (hG : G0 ≤ G1) (w l : Fin n)
    (hwl : w ≠ l) (hadj : G1.Adj w l) (hiso : ∀ k, ¬ G0.Adj w k)
    (test : Fin n → ℝ) (htest : ∀ k, 0 ≤ test k ∧ test k ≤ 1) (htw : test w < 1)
    (β p : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hβp : 0 ≤ β * p) (hβp1 : β * p ≤ β) :
    cascadeInf G0 test β p l < cascadeInf G1 test β p l := by
  have hn : 0 < n := Fin.pos w
  unfold cascadeInf
  set C : Fin n → (Fin n → Bool) → (Fin n → Fin n → Bool) → ℝ := fun s Z T =>
    ((1 : ℝ) / n) * (∏ k : Fin n, bern (test k) (Z k)) *
      (∏ k : Fin n, ∏ j : Fin n, bern (if Z k then β * p else β) (T k j)) with hC
  have hCnn : ∀ s Z T, 0 ≤ C s Z T := by
    intro s Z T
    simp only [hC]
    apply mul_nonneg (mul_nonneg (by positivity)
      (Finset.prod_nonneg (fun k _ => bern_nonneg (htest k).1 (htest k).2 _)))
    apply Finset.prod_nonneg; intro k _
    apply Finset.prod_nonneg; intro j _
    split_ifs
    · exact bern_nonneg hβp (by linarith) _
    · exact bern_nonneg hβ0.le hβ1 _
  set I : SimpleGraph (Fin n) → Fin n → (Fin n → Fin n → Bool) → ℝ := fun G s T =>
    if Relation.ReflTransGen (fun k j => G.Adj k j ∧ T k j = true) s l then 1 else 0 with hI
  have hImono : ∀ s T, I G0 s T ≤ I G1 s T := by
    intro s T
    exact ind_mono (reach_mono_T G0 G1 hG T T (fun _ _ h => h) s l)
  have hlhs : (∑ s : Fin n, ∑ Z : Fin n → Bool, ∑ T : Fin n → Fin n → Bool,
      ((1 : ℝ) / n) * (∏ k : Fin n, bern (test k) (Z k)) *
        (∏ k : Fin n, ∏ j : Fin n, bern (if Z k then β * p else β) (T k j)) *
      (if Relation.ReflTransGen (fun k j => G1.Adj k j ∧ T k j = true) s l then 1 else 0)) -
      (∑ s : Fin n, ∑ Z : Fin n → Bool, ∑ T : Fin n → Fin n → Bool,
      ((1 : ℝ) / n) * (∏ k : Fin n, bern (test k) (Z k)) *
        (∏ k : Fin n, ∏ j : Fin n, bern (if Z k then β * p else β) (T k j)) *
      (if Relation.ReflTransGen (fun k j => G0.Adj k j ∧ T k j = true) s l then 1 else 0)) =
      ∑ s, ∑ Z, ∑ T, C s Z T * (I G1 s T - I G0 s T) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro Z _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro T _
    simp only [hC, hI]; ring
  -- special configuration
  let Zs : Fin n → Bool := fun k => decide (test k = 1)
  let cZ : Fin n → ℝ := fun k => if Zs k then β * p else β
  let Ts : Fin n → Fin n → Bool := fun k _ => decide (0 < cZ k)
  have hZw : Zs w = false := by simp [Zs, ne_of_lt htw]
  have hTwl : Ts w l = true := by simp [Ts, cZ, hZw, hβ0]
  have hCpos : 0 < C w Zs Ts := by
    simp only [hC]
    apply mul_pos (mul_pos (by positivity) ?_) ?_
    · apply Finset.prod_pos; intro k _
      by_cases hk : test k = 1
      · simp [Zs, hk, bern]
      · have : test k < 1 := lt_of_le_of_ne (htest k).2 hk
        simp [Zs, hk, bern]; linarith
    · apply Finset.prod_pos; intro k _
      apply Finset.prod_pos; intro j _
      have hc0 : 0 ≤ cZ k := by
        simp only [cZ]; split_ifs
        · exact hβp
        · exact hβ0.le
      by_cases hc : 0 < cZ k
      · have : Ts k j = true := by simp [Ts, hc]
        rw [this]; simp only [bern, if_true]; exact hc
      · have h0 : cZ k = 0 := le_antisymm (not_lt.mp hc) hc0
        have : Ts k j = false := by simp [Ts, hc]
        rw [this]
        show 0 < bern (if Zs k then β * p else β) false
        have : (if Zs k then β * p else β) = 0 := h0
        rw [this]; simp [bern]
  have hgap : I G1 w Ts - I G0 w Ts = 1 := by
    have h1 : I G1 w Ts = 1 := by
      simp only [hI]
      rw [if_pos (Relation.ReflTransGen.single ⟨hadj, hTwl⟩)]
    have h0 : I G0 w Ts = 0 := by
      simp only [hI]
      rw [if_neg]
      intro h
      rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
      · exact hwl h
      · exact hiso c hc.1
    rw [h1, h0]; ring
  have hterm : ∀ s Z T, 0 ≤ C s Z T * (I G1 s T - I G0 s T) :=
    fun s Z T => mul_nonneg (hCnn s Z T) (by linarith [hImono s T])
  have hpos : 0 < ∑ s, ∑ Z, ∑ T, C s Z T * (I G1 s T - I G0 s T) := by
    have e1 : C w Zs Ts * (I G1 w Ts - I G0 w Ts) ≤
        ∑ T, C w Zs T * (I G1 w T - I G0 w T) :=
      Finset.single_le_sum (f := fun T => C w Zs T * (I G1 w T - I G0 w T))
        (fun T _ => hterm w Zs T) (Finset.mem_univ Ts)
    have e2 : ∑ T, C w Zs T * (I G1 w T - I G0 w T) ≤
        ∑ Z, ∑ T, C w Z T * (I G1 w T - I G0 w T) :=
      Finset.single_le_sum (f := fun Z => ∑ T, C w Z T * (I G1 w T - I G0 w T))
        (fun Z _ => Finset.sum_nonneg (fun T _ => hterm w Z T)) (Finset.mem_univ Zs)
    have e3 : ∑ Z, ∑ T, C w Z T * (I G1 w T - I G0 w T) ≤
        ∑ s, ∑ Z, ∑ T, C s Z T * (I G1 s T - I G0 s T) :=
      Finset.single_le_sum (f := fun s => ∑ Z, ∑ T, C s Z T * (I G1 s T - I G0 s T))
        (fun s _ => Finset.sum_nonneg (fun Z _ => Finset.sum_nonneg (fun T _ => hterm s Z T)))
        (Finset.mem_univ w)
    rw [hgap, mul_one] at e1
    linarith
  linarith

lemma zeroS_merge {n : ℕ} (w : Fin n) (ω₁ : {k // SI w k} → Bool) (ω₂ : {k // ¬ SI w k} → Bool) :
    (fun k => if SI w k then false else mergeI w ω₁ ω₂ k) = mergeI w (fun _ => false) ω₂ := by
  funext k
  by_cases h : SI w k
  · rw [if_pos h, mergeI_in _ _ _ _ h]
  · rw [if_neg h, mergeI_out _ _ _ _ h, mergeI_out _ _ _ _ h]

/-- Strict gain in infection when another agent becomes active. -/
lemma Pinf_strict_other (P : Params) (hP : P.Standing) {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (α : ℝ × ℝ) (hα : α ∈ PolicySquare)
    (l w : Fin n) (hwl : w ≠ l) (hxl : x l = 1) (hxw : x w = 1)
    (htw : testProb P α w < 1) :
    Pinf P (Function.update x w 0) α l < Pinf P x α l := by
  obtain ⟨h1, h2, h3, h4⟩ := standing_bp hP
  have hβ0 : 0 < P.β := hP.2.2.2.2.2.1
  have hη0 : 0 < P.η := hP.2.2.2.1
  set F : (Fin n × Fin n → Bool) → ℝ := fun f => PinfG P (mkG f) α l with hF
  set zero : (Fin n × Fin n → Bool) → (Fin n × Fin n → Bool) :=
    fun f k => if SI w k then false else f k with hzero
  have hx0 : ∀ j, Function.update x w 0 j ∈ Set.Icc (0:ℝ) 1 := by
    intro j
    by_cases hj : j = w
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact hx j
  -- the zeroed representation
  have hrep : Pinf P (Function.update x w 0) α l = bexp (linkQ P x) (fun f => F (zero f)) := by
    rw [Pinf_eq_bexp, bexp_split (SI w), bexp_split (SI w)]
    apply Finset.sum_congr rfl
    intro ω₂ _
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      have e1 : k.1.1 ≠ w := fun h => k.2 (Or.inl h)
      have e2 : k.1.2 ≠ w := fun h => k.2 (Or.inr h)
      simp [linkQ, Function.update_of_ne e1, Function.update_of_ne e2]
    · rw [bexp_zero_prob]
      · have : (fun ω₁ : {k // SI w k} → Bool =>
            F (zero ((Equiv.piEquivPiSubtypeProd (SI w) fun _ => Bool).symm (ω₁, ω₂)))) =
            fun _ => F (mergeI w (fun _ => false) ω₂) := by
          funext ω₁
          have := zeroS_merge w ω₁ ω₂
          simp only [hzero]
          unfold mergeI at this ⊢
          rw [this]
        rw [this, bexp_const]
        rfl
      · intro k
        simp only [linkQ]
        split_ifs
        · rcases k.2 with h | h
          · rw [h]; simp
          · rw [h]; simp
        · rfl
  rw [hrep, Pinf_eq_bexp]
  have hq := linkQ_mem P hP x hx
  -- difference
  have hFmono : ∀ f, F (zero f) ≤ F f := by
    intro f
    simp only [hF]
    unfold PinfG
    apply cascadeInf_mono_G _ _ _ _ (testProb_mem P hα) _ _ ⟨h1, by linarith⟩ ⟨h4, h3⟩ l
    apply mkG_mono
    intro k
    simp only [hzero]
    split_ifs
    · exact Bool.false_le _
    · exact le_rfl
  suffices 0 < bexp (linkQ P x) (fun f => F f - F (zero f)) by
    rw [← bexp_sub] at this; linarith
  let fs : Fin n × Fin n → Bool := fun k => decide (0 < linkQ P x k)
  have hws : 0 < ∏ k, bern (linkQ P x k) (fs k) := by
    apply Finset.prod_pos; intro k _
    by_cases hk : 0 < linkQ P x k
    · simp [fs, hk, bern]
    · have h0 : linkQ P x k = 0 := le_antisymm (not_lt.mp hk) (hq k).1
      simp [fs, hk, bern, h0]
  have hgap : 0 < F fs - F (zero fs) := by
    simp only [hF]
    unfold PinfG
    have := cascade_gap (mkG (zero fs)) (mkG fs) (mkG_mono (by
        intro k; simp only [hzero]; split_ifs
        · exact Bool.false_le _
        · exact le_rfl)) w l hwl ?_ ?_ (testProb P α) (testProb_mem P hα) htw P.β P.p hβ0 h3 h1 h2
    · linarith
    · rw [mkG_adj]
      refine ⟨hwl, ?_⟩
      rcases lt_or_gt_of_ne hwl with h | h
      · left
        simp [fs, linkQ, h, hxl, hxw, hη0]
      · right
        simp [fs, linkQ, h, hxl, hxw, hη0]
    · intro k hk
      rw [mkG_adj] at hk
      rcases hk.2 with h | h
      · simp [hzero, SI] at h
      · simp [hzero, SI] at h
  have := bexp_ge_single (linkQ P x) hq (fun f => F f - F (zero f))
    (fun f => by linarith [hFmono f]) fs
  have : 0 < (∏ k, bern (linkQ P x k) (fs k)) * (F fs - F (zero fs)) := mul_pos hws hgap
  linarith




lemma PinfMix_eq_bexp {n : ℕ} (P : Params) (γ α : ℝ × ℝ) (i : Fin n) (xi : ℝ) :
    PinfMix P γ α i xi = bexp (fun j => if j = i then 1 else stratProb P γ j)
      (fun a => Pinf P (Function.update (profileOf a) i xi) α i) := by
  unfold PinfMix bexp
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = i
  · simp only [hj, if_true]; cases a i <;> simp [bern]
  · simp only [hj, if_false]

lemma stratProb_mem {n : ℕ} (P : Params) {γ : ℝ × ℝ}
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (j : Fin n) :
    0 ≤ stratProb P γ j ∧ stratProb P γ j ≤ 1 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hγ
  unfold stratProb; split_ifs
  · exact ⟨h3, h4⟩
  · exact ⟨h1, h2⟩

lemma profile_mem {n : ℕ} (a : Fin n → Bool) (i : Fin n) (xi : ℝ)
    (hxi : xi ∈ Set.Icc (0 : ℝ) 1) (j : Fin n) :
    Function.update (profileOf a) i xi j ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hj : j = i
  · subst hj; simpa using hxi
  · rw [Function.update_of_ne hj]; unfold profileOf; split_ifs <;> simp

lemma netWeight_nonneg {n : ℕ} (P : Params) (hP : P.Standing) (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (G : SimpleGraph (Fin n)) : 0 ≤ netWeight P x G := by
  unfold netWeight
  apply Finset.prod_nonneg; intro a _
  apply Finset.prod_nonneg; intro b _
  split_ifs with hab
  · have := linkQ_mem P hP x hx (a, b)
    simp only [linkQ, hab, if_true] at this
    exact bern_nonneg this.1 this.2 _
  · exact zero_le_one

lemma Pinf_anti_alpha (P : Params) (hP : P.Standing) {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (α α' : ℝ × ℝ) (hα : α ∈ PolicySquare)
    (hα' : α' ∈ PolicySquare) (hle : PolicyLe α α') (i : Fin n) :
    Pinf P x α' i ≤ Pinf P x α i := by
  unfold Pinf
  apply Finset.sum_le_sum
  intro G _
  exact mul_le_mul_of_nonneg_left (prop1 P hP G α α' hα hα' hle i) (netWeight_nonneg P hP x hx G)

lemma PinfMix_anti_alpha (P : Params) (hP : P.Standing) {n : ℕ} (γ : ℝ × ℝ)
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (α α' : ℝ × ℝ)
    (hα : α ∈ PolicySquare) (hα' : α' ∈ PolicySquare) (hle : PolicyLe α α') (i : Fin n)
    (xi : ℝ) (hxi : xi ∈ Set.Icc (0 : ℝ) 1) :
    PinfMix P γ α' i xi ≤ PinfMix P γ α i xi := by
  rw [PinfMix_eq_bexp, PinfMix_eq_bexp]
  apply bexp_le_of_le
  · intro j; split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact stratProb_mem P hγ j
  intro a
  exact Pinf_anti_alpha P hP _ (profile_mem a i xi hxi) α α' hα hα' hle i

/-- Strict increase of a low agent's infection in the low-type mixing probability. -/
lemma PinfMix_strict_gL (P : Params) (hP : P.Standing) {n : ℕ} (α : ℝ × ℝ)
    (hα : α ∈ PolicySquare) (hαL : α.1 < 1) (g g' : ℝ) (hg' : 0 ≤ g') (hlt : g' < g)
    (hg : g ≤ 1) (l l' : Fin n) (hl : ¬ IsHigh P l) (hl' : ¬ IsHigh P l') (hne : l' ≠ l) :
    PinfMix P (g', 1) α l 1 < PinfMix P (g, 1) α l 1 := by
  rw [PinfMix_eq_bexp, PinfMix_eq_bexp]
  set F : (Fin n → Bool) → ℝ := fun a => Pinf P (Function.update (profileOf a) l 1) α l with hF
  have hFm : Monotone F := by
    intro a b hab
    apply lemma1a P hP (Fin.pos l) _ _ α hα (profile_mem a l 1 ⟨zero_le_one, le_rfl⟩)
      (profile_mem b l 1 ⟨zero_le_one, le_rfl⟩)
    intro j
    by_cases hj : j = l
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      unfold profileOf
      cases ha : a j <;> cases hb : b j
      · simp
      · simp
      · have := hab j; rw [ha, hb] at this; exact absurd this (by simp)
      · simp
  set q' : Fin n → ℝ := fun j => if j = l then 1 else stratProb P (g', 1) j with hq'
  set q : Fin n → ℝ := fun j => if j = l then 1 else stratProb P (g, 1) j with hq
  set qm : Fin n → ℝ := fun j => if j = l' then q' j else q j with hqm
  have hγ' : ((g', 1) : ℝ × ℝ) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨hg', by linarith⟩, ⟨zero_le_one, le_rfl⟩⟩
  have hγ : ((g, 1) : ℝ × ℝ) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨by linarith, hg⟩, ⟨zero_le_one, le_rfl⟩⟩
  have hq'm : ∀ k, 0 ≤ q' k ∧ q' k ≤ 1 := by
    intro k; simp only [hq']; split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact stratProb_mem P hγ' k
  have hqm' : ∀ k, 0 ≤ q k ∧ q k ≤ 1 := by
    intro k; simp only [hq]; split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact stratProb_mem P hγ k
  have hqmm : ∀ k, 0 ≤ qm k ∧ qm k ≤ 1 := by
    intro k; simp only [hqm]; split_ifs
    · exact hq'm k
    · exact hqm' k
  have hsp : ∀ k : Fin n, stratProb P (g', 1) k ≤ stratProb P (g, 1) k := by
    intro k; unfold stratProb; split_ifs
    · exact le_rfl
    · exact hlt.le
  have step1 : bexp q' F ≤ bexp qm F := by
    apply bexp_mono _ _ hq'm hqmm _ F hFm
    intro k
    simp only [hqm]
    split_ifs with hk
    · exact le_rfl
    · simp only [hq', hq]; split_ifs
      · exact le_rfl
      · exact hsp k
  have step2 : bexp qm F < bexp q F := by
    apply bexp_strict_one l' qm q hqmm
    · intro k hk; simp only [hqm, hk, if_false]
    · simp only [hqm, if_true, hq', hq, if_neg hne, stratProb, hl', if_false]
      exact hlt
    · exact hFm
    · intro k hk
      show 0 < bern (qm k) true
      simp only [bern, if_true, hqm, if_neg hk, hq, stratProb]
      split_ifs with h1 h2
      · exact zero_lt_one
      · exact zero_lt_one
      · linarith
    · -- the gap
      simp only [hF]
      have e1 : Function.update (profileOf (Function.update (fun _ => true) l' false)) l (1:ℝ) =
          Function.update (Function.update (profileOf (fun _ => true)) l 1) l' 0 := by
        funext j
        by_cases hjl : j = l
        · subst hjl; simp [Function.update_of_ne (Ne.symm hne)]
        · by_cases hjl' : j = l'
          · subst hjl'; simp [hjl, profileOf]
          · simp [hjl, hjl', profileOf]
      have e2 : Function.update (profileOf (Function.update (fun _ => true) l' true)) l (1:ℝ) =
          Function.update (profileOf (fun _ => true)) l 1 := by
        congr 2
        funext j; by_cases h : j = l' <;> simp [h]
      rw [e1, e2]
      apply Pinf_strict_other P hP _ (profile_mem _ l 1 ⟨zero_le_one, le_rfl⟩) α hα l l' hne
      · simp
      · rw [Function.update_of_ne hne]; simp [profileOf]
      · simp only [testProb, hl', if_false]; exact hαL
  linarith

lemma interior_policy {S : Set (ℝ × ℝ)} (hS : S ⊆ PolicySquare) {α : ℝ × ℝ}
    (h : α ∈ interior S) : α ∈ PolicySquare ∧ 0 < α.1 ∧ α.1 < 1 ∧ 0 < α.2 ∧ α.2 < 1 := by
  have h1 : α ∈ interior PolicySquare := interior_mono hS h
  unfold PolicySquare at h1
  rw [interior_prod_eq, interior_Icc] at h1
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := h1
  exact ⟨hS (interior_subset h), a, b, c, d⟩

lemma A2_sub {P : Params} {n : ℕ} : A2 P n ⊆ PolicySquare := fun _ h => h.1

/-- Enough low agents for large `n`. -/
lemma many_low (P : Params) (hP : P.Standing) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n → ⌈P.rH * n⌉₊ + 2 ≤ n := by
  have hr0 : 0 < P.rH := hP.2.2.2.2.2.2.2.2.2.2.1
  have hr1 : P.rH < 1 := hP.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨⌈3 / (1 - P.rH)⌉₊ + 1, Nat.succ_pos _, ?_⟩
  intro n hn
  have h1 : (3 / (1 - P.rH) : ℝ) ≤ n := by
    have := Nat.le_ceil (3 / (1 - P.rH))
    have h2 : ((⌈3 / (1 - P.rH)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have h3 : 3 ≤ (1 - P.rH) * n := by
    rw [div_le_iff₀ (by linarith)] at h1; linarith
  have h4 : (⌈P.rH * n⌉₊ : ℝ) < P.rH * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have h5 : ((⌈P.rH * n⌉₊ + 2 : ℕ) : ℝ) < n + 1 := by push_cast; nlinarith
  have : ⌈P.rH * n⌉₊ + 2 < n + 1 := by exact_mod_cast h5
  omega

theorem gammaL_mono' (P : Params) (hP : P.Standing) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n →
      ∀ α α' : ℝ × ℝ, α ∈ interior (A2 P n) → α' ∈ interior (A2 P n) →
      PolicyLe α α' → ∀ g g' : ℝ,
      (∀ l : Fin n, ¬ IsHigh P l →
        PinfMix P (g, 1) α l 1 = (1 : ℝ) / n + P.vL) →
      (∀ l : Fin n, ¬ IsHigh P l →
        PinfMix P (g', 1) α' l 1 = (1 : ℝ) / n + P.vL) →
      g ∈ Set.Icc (0 : ℝ) 1 → g' ∈ Set.Icc (0 : ℝ) 1 → g ≤ g' := by
  obtain ⟨M, hM0, hM⟩ := many_low P hP
  refine ⟨M, hM0, ?_⟩
  intro n hn α α' hα hα' hle g g' hgm hgm' hg hg'
  have hcard := hM n hn
  obtain ⟨hαS, -, hαL, -, -⟩ := interior_policy A2_sub hα
  obtain ⟨hα'S, -, -, -, -⟩ := interior_policy A2_sub hα'
  by_contra hcon
  push_neg at hcon
  let l : Fin n := ⟨n - 1, by omega⟩
  let l' : Fin n := ⟨n - 2, by omega⟩
  have hl : ¬ IsHigh P l := by
    unfold IsHigh; simp only [l]; omega
  have hl' : ¬ IsHigh P l' := by
    unfold IsHigh; simp only [l']; omega
  have hne : l' ≠ l := by
    intro h; have := congrArg Fin.val h; simp only [l, l'] at this; omega
  have e1 := hgm l hl
  have e2 := hgm' l hl
  have c1 := PinfMix_anti_alpha P hP (g', 1) ⟨⟨hg'.1, hg'.2⟩, ⟨zero_le_one, le_rfl⟩⟩ α α' hαS hα'S
    hle l 1 ⟨zero_le_one, le_rfl⟩
  have c2 := PinfMix_strict_gL P hP α hαS hαL g g' hg'.1 hcon hg.2 l l' hl hl' hne
  linarith




lemma bexp_det {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ)
    (hq : ∀ k, q k = 0 ∨ q k = 1) (H : (ι → Bool) → ℝ) :
    bexp q H = H (fun k => decide (q k = 1)) := by
  unfold bexp
  rw [Finset.sum_eq_single (fun k => decide (q k = 1))]
  · rw [Finset.prod_eq_one, one_mul]
    intro k _
    rcases hq k with h | h <;> simp [h, bern]
  · intro ω _ hω
    obtain ⟨k, hk⟩ : ∃ k, ω k ≠ decide (q k = 1) := by
      by_contra hc; push_neg at hc; exact hω (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ k)]
    · ring
    · rcases hq k with h | h
      · have : ω k = true := by
          cases hw : ω k
          · rw [hw] at hk; simp [h] at hk
          · rfl
        simp [h, bern, this]
      · have : ω k = false := by
          cases hw : ω k
          · rfl
          · rw [hw] at hk; simp [h] at hk
        simp [h, bern, this]
  · simp

lemma bexp_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (F : (ι → Bool) → ℝ) :
    bexp q (fun ω => - F ω) = - bexp q F := by
  unfold bexp
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intros; ring

lemma bexp_lt_of_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ)
    (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1) (F G : (ι → Bool) → ℝ) (hle : ∀ ω, F ω ≤ G ω)
    (ω₀ : ι → Bool) (hw : 0 < ∏ k, bern (q k) (ω₀ k)) (hlt : F ω₀ < G ω₀) :
    bexp q F < bexp q G := by
  have h1 := bexp_ge_single q hq (fun ω => G ω - F ω) (fun ω => by linarith [hle ω]) ω₀
  have h2 := bexp_sub q G F
  have : 0 < (∏ k, bern (q k) (ω₀ k)) * (G ω₀ - F ω₀) := mul_pos hw (by linarith)
  linarith

lemma pos_weight {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1) :
    0 < ∏ k, bern (q k) (decide (0 < q k)) := by
  apply Finset.prod_pos; intro k _
  by_cases hk : 0 < q k
  · simp [hk, bern]
  · have h0 : q k = 0 := le_antisymm (not_lt.mp hk) (hq k).1
    simp [hk, bern, h0]

lemma pos_weight1 {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ k, 0 ≤ q k ∧ q k ≤ 1) :
    0 < ∏ k, bern (q k) (decide (q k = 1)) := by
  apply Finset.prod_pos; intro k _
  by_cases hk : q k = 1
  · simp [hk, bern]
  · have : q k < 1 := lt_of_le_of_ne (hq k).2 hk
    simp [hk, bern]; linarith

/-- The transmission layer is antitone in the testing outcomes. -/
lemma R_anti {n : ℕ} (G : SimpleGraph (Fin n)) (s i : Fin n) (β p : ℝ)
    (hβp : 0 ≤ β * p) (hpβ : β * p ≤ β) (hβ : β ≤ 1) :
    Antitone (fun Z : Fin n → Bool => bexp (fun kj : Fin n × Fin n => if Z kj.1 then β * p else β)
      (fun T' => if Relation.ReflTransGen
        (fun k j => G.Adj k j ∧ Function.curry T' k j = true) s i then (1:ℝ) else 0)) := by
  have hc : ∀ Z : Fin n → Bool, ∀ kj : Fin n × Fin n,
      0 ≤ (if Z kj.1 then β * p else β) ∧ (if Z kj.1 then β * p else β) ≤ 1 := by
    intro Z kj; split_ifs
    · exact ⟨hβp, by linarith⟩
    · exact ⟨by linarith, hβ⟩
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

/-- Strict decrease in the testing probability of a neighbour (fixed graph). -/
lemma cascade_strict_test {n : ℕ} (G : SimpleGraph (Fin n)) (w i : Fin n) (hwi : w ≠ i)
    (hadj : G.Adj w i) (test test' : Fin n → ℝ) (ht : ∀ k, 0 ≤ test k ∧ test k ≤ 1)
    (ht' : ∀ k, 0 ≤ test' k ∧ test' k ≤ 1) (hle : ∀ k, test k ≤ test' k)
    (hlt : test w < test' w) (β p : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hp0 : 0 ≤ p)
    (hp1 : p < 1) :
    cascadeInf G test' β p i < cascadeInf G test β p i := by
  have hn : 0 < n := Fin.pos w
  have hβp : 0 ≤ β * p := by positivity
  have hpβ : β * p < β := by nlinarith
  rw [cascadeInf_eq, cascadeInf_eq]
  set R : Fin n → (Fin n → Bool) → ℝ := fun s Z =>
    bexp (fun kj : Fin n × Fin n => if Z kj.1 then β * p else β)
      (fun T' => if Relation.ReflTransGen
        (fun k j => G.Adj k j ∧ Function.curry T' k j = true) s i then (1:ℝ) else 0) with hR
  have hRa : ∀ s, Antitone (R s) := fun s => R_anti G s i β p hβp hpβ.le hβ1
  apply Finset.sum_lt_sum
  · intro s _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact bexp_anti _ _ ht ht' hle _ (hRa s)
  refine ⟨w, Finset.mem_univ _, ?_⟩
  apply mul_lt_mul_of_pos_left _ (by positivity)
  set qm : Fin n → ℝ := fun k => if k = w then test w else test' k with hqm
  have hqmm : ∀ k, 0 ≤ qm k ∧ qm k ≤ 1 := by
    intro k; simp only [hqm]; split_ifs
    · exact ht w
    · exact ht' k
  have weak : bexp qm (R w) ≤ bexp test (R w) := by
    apply bexp_anti _ _ ht hqmm _ _ (hRa w)
    intro k; simp only [hqm]; split_ifs with h
    · rw [h]
    · exact hle k
  suffices strict : bexp test' (R w) < bexp qm (R w) by linarith
  have key := bexp_strict_one w qm test' hqmm (by intro k hk; simp [hqm, hk])
    (by simp [hqm]; exact hlt) (fun Z => - R w Z) (fun a b h => neg_le_neg (hRa w h))
    (fun k => decide (qm k = 1)) ?_ ?_
  · rw [bexp_neg, bexp_neg] at key; linarith
  · intro k _
    by_cases hk : qm k = 1
    · simp [hk, bern]
    · have : qm k < 1 := lt_of_le_of_ne (hqmm k).2 hk
      simp [hk, bern]; linarith
  · -- gap in the transmission layer
    simp only [neg_lt_neg_iff]
    set Zt := Function.update (fun k => decide (qm k = 1)) w true
    set Zf := Function.update (fun k => decide (qm k = 1)) w false
    have hZt : Zt w = true := by simp [Zt]
    have hZf : Zf w = false := by simp [Zf]
    have hZo : ∀ k, k ≠ w → Zt k = Zf k := by
      intro k hk; simp [Zt, Zf, Function.update_of_ne hk]
    set q1 : Fin n × Fin n → ℝ := fun kj => if Zt kj.1 then β * p else β
    set q3 : Fin n × Fin n → ℝ := fun kj => if Zf kj.1 then β * p else β
    set q2 : Fin n × Fin n → ℝ := fun kj => if kj = (w, i) then β else q1 kj
    have hq1 : ∀ kj, 0 ≤ q1 kj ∧ q1 kj ≤ 1 := by
      intro kj; simp only [q1]; split_ifs
      · exact ⟨hβp, by linarith⟩
      · exact ⟨hβ0.le, hβ1⟩
    have hq2 : ∀ kj, 0 ≤ q2 kj ∧ q2 kj ≤ 1 := by
      intro kj; simp only [q2]; split_ifs
      · exact ⟨hβ0.le, hβ1⟩
      · exact hq1 kj
    have hq3 : ∀ kj, 0 ≤ q3 kj ∧ q3 kj ≤ 1 := by
      intro kj; simp only [q3]; split_ifs
      · exact ⟨hβp, by linarith⟩
      · exact ⟨hβ0.le, hβ1⟩
    set Fr : (Fin n × Fin n → Bool) → ℝ := fun T' => if Relation.ReflTransGen
        (fun k j => G.Adj k j ∧ Function.curry T' k j = true) w i then (1:ℝ) else 0 with hFr
    have hFrm : Monotone Fr := by
      intro T T' hT
      apply ind_mono
      apply reach_mono_T G G le_rfl
      intro k j h
      have := hT (k, j)
      simp only [Function.curry] at h ⊢
      rw [h] at this
      cases h' : T' (k, j)
      · rw [h'] at this; exact absurd this (by simp)
      · rfl
    show bexp q1 Fr < bexp q3 Fr
    have s1 : bexp q1 Fr < bexp q2 Fr := by
      apply bexp_strict_one (w, i) q1 q2 hq1 (by intro k hk; simp [q2, hk])
        (by simp [q2, q1, hZt]; exact hpβ) Fr hFrm
        (fun kj => if kj.1 = w then false else decide (q1 kj = 1))
      · intro k hk
        by_cases hkw : k.1 = w
        · have hq1k : q1 k = β * p := by simp only [q1, hkw, hZt, if_true]
          show 0 < bern (q1 k) (if k.1 = w then false else decide (q1 k = 1))
          rw [if_pos hkw, hq1k]
          simp only [bern, Bool.false_eq_true, if_false]
          linarith
        · show 0 < bern (q1 k) (if k.1 = w then false else decide (q1 k = 1))
          rw [if_neg hkw]
          by_cases h1 : q1 k = 1
          · simp [h1, bern]
          · have : q1 k < 1 := lt_of_le_of_ne (hq1 k).2 h1
            simp [h1, bern]; linarith
      · have hTv : Fr (Function.update (fun kj => if kj.1 = w then false else decide (q1 kj = 1))
            (w, i) true) = 1 := by
          simp only [hFr]
          rw [if_pos (Relation.ReflTransGen.single ⟨hadj, by simp [Function.curry]⟩)]
        have hFv : Fr (Function.update (fun kj => if kj.1 = w then false else decide (q1 kj = 1))
            (w, i) false) = 0 := by
          simp only [hFr]
          rw [if_neg]
          intro h
          rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
          · exact hwi h
          · have := hc.2
            simp only [Function.curry] at this
            by_cases hci : (w, c) = (w, i)
            · rw [Function.update_apply, if_pos hci] at this; exact absurd this (by simp)
            · rw [Function.update_apply, if_neg hci] at this; simp at this
        rw [hTv, hFv]; norm_num
    have s2 : bexp q2 Fr ≤ bexp q3 Fr := by
      apply bexp_mono _ _ hq2 hq3 _ Fr hFrm
      intro kj
      simp only [q2, q1, q3]
      by_cases hkw : kj.1 = w
      · have e1 : Zf kj.1 = false := by rw [hkw]; exact hZf
        split_ifs <;> simp_all <;> linarith
      · rw [hZo kj.1 hkw]
        split_ifs <;> simp_all
    linarith




lemma mkG_all_link {n : ℕ} (P : Params) (hP : P.Standing) (x : Fin n → ℝ) (w i : Fin n)
    (hwi : w ≠ i) (hxi : x i = 1) (hxw : x w = 1) :
    (mkG (fun k => decide (0 < linkQ P x k))).Adj w i := by
  have hη0 : 0 < P.η := hP.2.2.2.1
  rw [mkG_adj]
  refine ⟨hwi, ?_⟩
  rcases lt_or_gt_of_ne hwi with h | h
  · left; simp [linkQ, h, hxi, hxw, hη0]
  · right; simp [linkQ, h, hxi, hxw, hη0]

/-- Strict decrease of infection in the testing probability of an active neighbour. -/
lemma Pinf_strict_alpha (P : Params) (hP : P.Standing) {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (α α' : ℝ × ℝ) (hα : α ∈ PolicySquare)
    (hα' : α' ∈ PolicySquare) (hle : PolicyLe α α') (w i : Fin n) (hwi : w ≠ i)
    (hxi : x i = 1) (hxw : x w = 1) (hlt : testProb P α w < testProb P α' w) :
    Pinf P x α' i < Pinf P x α i := by
  obtain ⟨_, _, _, _, _, hβ0, hβ1, hp0, hp1, _⟩ := id hP
  rw [Pinf_eq_bexp, Pinf_eq_bexp]
  have hq := linkQ_mem P hP x hx
  apply bexp_lt_of_lt _ hq _ _ (fun f => prop1 P hP _ α α' hα hα' hle i)
    (fun k => decide (0 < linkQ P x k)) (pos_weight _ hq)
  unfold PinfG
  apply cascade_strict_test _ w i hwi (mkG_all_link P hP x w i hwi hxi hxw) _ _
    (testProb_mem P hα) (testProb_mem P hα') _ hlt P.β P.p hβ0 hβ1 hp0 hp1
  intro k; unfold testProb; split_ifs
  · exact hle.2
  · exact hle.1

lemma mixq_mem {n : ℕ} (P : Params) {γ : ℝ × ℝ}
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (i : Fin n) (j : Fin n) :
    0 ≤ (if j = i then (1:ℝ) else stratProb P γ j) ∧
      (if j = i then (1:ℝ) else stratProb P γ j) ≤ 1 := by
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · exact stratProb_mem P hγ j

/-- Strict decrease of the mixed infection probability in the testing of an agent that is
active with positive probability. -/
lemma PinfMix_strict_alpha (P : Params) (hP : P.Standing) {n : ℕ} (γ : ℝ × ℝ)
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (α α' : ℝ × ℝ)
    (hα : α ∈ PolicySquare) (hα' : α' ∈ PolicySquare) (hle : PolicyLe α α') (w i : Fin n)
    (hwi : w ≠ i) (hpos : 0 < stratProb P γ w) (hlt : testProb P α w < testProb P α' w) :
    PinfMix P γ α' i 1 < PinfMix P γ α i 1 := by
  rw [PinfMix_eq_bexp, PinfMix_eq_bexp]
  have hq := mixq_mem P hγ i
  apply bexp_lt_of_lt _ hq _ _
    (fun a => Pinf_anti_alpha P hP _ (profile_mem a i 1 ⟨zero_le_one, le_rfl⟩) α α' hα hα' hle i)
    _ (pos_weight _ hq)
  apply Pinf_strict_alpha P hP _ (profile_mem _ i 1 ⟨zero_le_one, le_rfl⟩) α α' hα hα' hle w i hwi
  · simp
  · rw [Function.update_of_ne hwi]
    simp [profileOf, hwi, hpos]
  · exact hlt

/-- Strict increase of the mixed infection probability in another agent's activity. -/
lemma PinfMix_strict_g (P : Params) (hP : P.Standing) {n : ℕ} (γ γ' : ℝ × ℝ)
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (hγ' : γ' ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (hsp : ∀ j : Fin n, stratProb P γ' j ≤ stratProb P γ j) (α : ℝ × ℝ)
    (hα : α ∈ PolicySquare) (w i : Fin n) (hwi : w ≠ i)
    (hlt : stratProb P γ' w < stratProb P γ w) (htw : testProb P α w < 1) :
    PinfMix P γ' α i 1 < PinfMix P γ α i 1 := by
  rw [PinfMix_eq_bexp, PinfMix_eq_bexp]
  set F : (Fin n → Bool) → ℝ := fun a => Pinf P (Function.update (profileOf a) i 1) α i with hF
  have hFm : Monotone F := by
    intro a b hab
    apply lemma1a P hP (Fin.pos i) _ _ α hα (profile_mem a i 1 ⟨zero_le_one, le_rfl⟩)
      (profile_mem b i 1 ⟨zero_le_one, le_rfl⟩)
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      unfold profileOf
      cases ha : a j <;> cases hb : b j
      · simp
      · simp
      · have := hab j; rw [ha, hb] at this; exact absurd this (by simp)
      · simp
  set q' : Fin n → ℝ := fun j => if j = i then 1 else stratProb P γ' j with hq'
  set q : Fin n → ℝ := fun j => if j = i then 1 else stratProb P γ j with hq
  set qm : Fin n → ℝ := fun j => if j = w then q' j else q j with hqm
  have hq'm := mixq_mem P hγ' i
  have hqm' := mixq_mem P hγ i
  have hqmm : ∀ k, 0 ≤ qm k ∧ qm k ≤ 1 := by
    intro k; simp only [hqm]; split_ifs
    · exact hq'm k
    · exact hqm' k
  have step1 : bexp q' F ≤ bexp qm F := by
    apply bexp_mono _ _ hq'm hqmm _ F hFm
    intro k
    show q' k ≤ qm k
    by_cases hk : k = w
    · simp [hqm, hk]
    · have : qm k = q k := by simp [hqm, hk]
      rw [this]
      simp only [hq', hq]
      by_cases hki : k = i
      · simp [hki]
      · simp only [hki, if_false]; exact hsp k
  have step2 : bexp qm F < bexp q F := by
    apply bexp_strict_one w qm q hqmm
    · intro k hk; simp only [hqm, hk, if_false]
    · show qm w < q w
      simp only [hqm, if_true, hq', hq, if_neg hwi]
      exact hlt
    · exact hFm
    · intro k hk
      by_cases h0 : 0 < qm k
      · show 0 < bern (qm k) (decide (0 < qm k))
        simp [h0, bern]
      · have : qm k = 0 := le_antisymm (not_lt.mp h0) (hqmm k).1
        show 0 < bern (qm k) (decide (0 < qm k))
        simp [h0, bern, this]
    · simp only [hF]
      set a₀ : Fin n → Bool := fun k => decide (0 < qm k)
      have e1 : Function.update (profileOf (Function.update a₀ w false)) i (1:ℝ) =
          Function.update (Function.update (profileOf (Function.update a₀ w true)) i 1) w 0 := by
        funext j
        by_cases hji : j = i
        · subst hji; simp [Function.update_of_ne (Ne.symm hwi)]
        · by_cases hjw : j = w
          · subst hjw; simp [hji, profileOf]
          · simp [hji, hjw, profileOf]
      rw [e1]
      apply Pinf_strict_other P hP _ (profile_mem _ i 1 ⟨zero_le_one, le_rfl⟩) α hα i w hwi
      · simp
      · rw [Function.update_of_ne hwi]; simp [profileOf]
      · exact htw
  linarith

/-- An agent all of whose potential partners are inactive is infected only as the source. -/
lemma Pinf_alone {n : ℕ} (P : Params) (x : Fin n → ℝ) (α : ℝ × ℝ) (i : Fin n)
    (hx : ∀ j, j ≠ i → x j = 0) : Pinf P x α i = (1 : ℝ) / n := by
  have hn : 0 < n := Fin.pos i
  rw [Pinf_eq_bexp, bexp_zero_prob]
  · unfold PinfG
    apply cascadeInf_isolated hn
    intro k hk
    rw [mkG_adj] at hk
    simp at hk
  · intro k
    unfold linkQ
    split_ifs with h
    · by_cases h1 : k.1 = i
      · have h2 : k.2 ≠ i := by intro h2; rw [h1, h2] at h; exact lt_irrefl _ h
        rw [hx _ h2]; ring
      · rw [hx _ h1]; ring
    · rfl

/-- The deterministic profile of a pure symmetric strategy, with the agent herself active. -/
noncomputable def detProf {n : ℕ} (P : Params) (γ : ℝ × ℝ) (i : Fin n) : Fin n → ℝ :=
  fun j => if j = i ∨ stratProb P γ j = 1 then 1 else 0

lemma PinfMix_det {n : ℕ} (P : Params) (γ α : ℝ × ℝ) (i : Fin n)
    (hpure : ∀ j : Fin n, stratProb P γ j = 0 ∨ stratProb P γ j = 1) :
    PinfMix P γ α i 1 = Pinf P (detProf P γ i) α i := by
  rw [PinfMix_eq_bexp, bexp_det]
  · congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [detProf]
    · rw [Function.update_of_ne hj]
      simp [detProf, profileOf, hj]
  · intro j
    by_cases hj : j = i
    · simp [hj]
    · simp only [hj, if_false]; exact hpure j

lemma detProf_mem {n : ℕ} (P : Params) (γ : ℝ × ℝ) (i : Fin n) (j : Fin n) :
    detProf P γ i j ∈ Set.Icc (0 : ℝ) 1 := by
  unfold detProf; split_ifs <;> simp

lemma eqInf_one {n : ℕ} (P : Params) (γ α : ℝ × ℝ) (i : Fin n) (h : stratProb P γ i = 1) :
    eqInf P γ α i = PinfMix P γ α i 1 := by
  unfold eqInf; rw [h]; ring

lemma eqInf_zero {n : ℕ} (P : Params) (γ α : ℝ × ℝ) (i : Fin n) (h : stratProb P γ i = 0) :
    eqInf P γ α i = (1 : ℝ) / n := by
  unfold eqInf; rw [h, PinfMix_zero (Fin.pos i)]; ring

/-- Equilibrium inequality for an agent playing activity one with certainty. -/
lemma eq_one_ineq {n : ℕ} (P : Params) (γ α : ℝ × ℝ) (heq : IsSymEq P n γ α) (i : Fin n)
    (h : stratProb P γ i = 1) : PinfMix P γ α i 1 ≤ (1 : ℝ) / n + val P i := by
  have := heq.2 i 0 ⟨le_rfl, zero_le_one⟩
  rw [h] at this
  unfold expUtil at this
  rw [PinfMix_zero (Fin.pos i)] at this
  linarith

/-- Equilibrium inequality for an agent playing activity zero with certainty. -/
lemma eq_zero_ineq {n : ℕ} (P : Params) (γ α : ℝ × ℝ) (heq : IsSymEq P n γ α) (i : Fin n)
    (h : stratProb P γ i = 0) : (1 : ℝ) / n + val P i ≤ PinfMix P γ α i 1 := by
  have := heq.2 i 1 ⟨zero_le_one, le_rfl⟩
  rw [h] at this
  unfold expUtil at this
  rw [PinfMix_zero (Fin.pos i)] at this
  linarith




/-- Proposition 1 lifted to the random graph (uses the platform's `proposition_1`). -/
lemma Pinf_anti (P : Params) (hP : P.Standing) {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (α α' : ℝ × ℝ) (hα : α ∈ PolicySquare)
    (hα' : α' ∈ PolicySquare) (hle : PolicyLe α α') (i : Fin n) :
    Pinf P x α' i ≤ Pinf P x α i := by
  unfold Pinf
  apply Finset.sum_le_sum
  intro G _
  exact mul_le_mul_of_nonneg_left (proposition_1 P hP (Fin.pos i) G α α' hα hα' hle i)
    (netWeight_nonneg P hP x hx G)

lemma many_high (P : Params) (hP : P.Standing) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n → 2 ≤ ⌈P.rH * n⌉₊ := by
  have hr0 : 0 < P.rH := hP.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⌈2 / P.rH⌉₊ + 1, Nat.succ_pos _, ?_⟩
  intro n hn
  have h1 : (2 / P.rH : ℝ) < n := by
    have := Nat.le_ceil (2 / P.rH)
    have h2 : ((⌈2 / P.rH⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have h3 : 2 < P.rH * n := by
    rw [div_lt_iff₀ hr0] at h1; linarith
  have : 1 < ⌈P.rH * n⌉₊ := Nat.lt_ceil.mpr (by push_cast; linarith)
  omega

lemma detProf_11 {n : ℕ} (P : Params) (i : Fin n) : detProf P (1, 1) i = prof P 1 1 := by
  funext j; simp [detProf, prof, stratProb]

lemma detProf_01_low {n : ℕ} (P : Params) (l : Fin n) :
    detProf P (0, 1) l = Function.update (prof P 1 0) l 1 := by
  funext j
  by_cases hj : j = l
  · subst hj; simp [detProf]
  · rw [Function.update_of_ne hj]
    simp only [detProf, prof, stratProb, hj, false_or]
    split_ifs <;> simp_all

lemma detProf_01_high {n : ℕ} (P : Params) (h : Fin n) (hh : IsHigh P h) :
    detProf P (0, 1) h = prof P 1 0 := by
  funext j
  by_cases hj : j = h
  · subst hj; simp [detProf, prof, hh]
  · simp only [detProf, prof, stratProb, hj, false_or]
    split_ifs <;> simp_all

lemma pure_11 {n : ℕ} (P : Params) (j : Fin n) :
    stratProb P (1, 1) j = 0 ∨ stratProb P (1, 1) j = 1 := by
  right; simp [stratProb]

lemma pure_01 {n : ℕ} (P : Params) (j : Fin n) :
    stratProb P (0, 1) j = 0 ∨ stratProb P (0, 1) j = 1 := by
  unfold stratProb; split_ifs <;> simp

lemma pure_00 {n : ℕ} (P : Params) (j : Fin n) :
    stratProb P (0, 0) j = 0 ∨ stratProb P (0, 0) j = 1 := by
  left; unfold stratProb; split_ifs <;> rfl

lemma sq_of_sub {S : Set (ℝ × ℝ)} (hS : S ⊆ PolicySquare) {α : ℝ × ℝ} (h : α ∈ S) :
    α ∈ PolicySquare := hS h

lemma A1_sub {P : Params} {n : ℕ} : A1 P n ⊆ PolicySquare := fun _ h => h.1
lemma A3_sub {P : Params} {n : ℕ} : A3 P n ⊆ PolicySquare := fun _ h => h.1
lemma A4_sub {P : Params} {n : ℕ} : A4 P n ⊆ PolicySquare := fun _ h => h.1

/-! ### Part (a) and (c): pure regions -/

lemma part_a (P : Params) (hP : P.Standing) {n : ℕ} (α α' γ γ' : ℝ × ℝ)
    (hα : α ∈ PolicySquare) (hα' : α' ∈ PolicySquare) (hle : PolicyLe α α')
    (hγ : γ = (1, 1)) (hγ' : γ' = (1, 1)) (i : Fin n) :
    eqInf P γ' α' i ≤ eqInf P γ α i := by
  subst hγ hγ'
  have hs : stratProb P (1, 1) i = 1 := by simp [stratProb]
  rw [eqInf_one P _ _ i hs, eqInf_one P _ _ i hs, PinfMix_det P _ _ i (pure_11 P),
    PinfMix_det P _ _ i (pure_11 P)]
  exact Pinf_anti P hP _ (detProf_mem P _ i) α α' hα hα' hle i

lemma part_c (P : Params) (hP : P.Standing) {n : ℕ} (α α' γ γ' : ℝ × ℝ)
    (hα : α ∈ PolicySquare) (hα' : α' ∈ PolicySquare) (hle : PolicyLe α α')
    (hγ : γ = (0, 1)) (hγ' : γ' = (0, 1)) (i : Fin n) :
    eqInf P γ' α' i ≤ eqInf P γ α i := by
  subst hγ hγ'
  by_cases hi : IsHigh P i
  · have hs : stratProb P (0, 1) i = 1 := by simp [stratProb, hi]
    rw [eqInf_one P _ _ i hs, eqInf_one P _ _ i hs, PinfMix_det P _ _ i (pure_01 P),
      PinfMix_det P _ _ i (pure_01 P)]
    exact Pinf_anti P hP _ (detProf_mem P _ i) α α' hα hα' hle i
  · have hs : stratProb P (0, 1) i = 0 := by simp [stratProb, hi]
    rw [eqInf_zero P _ _ i hs, eqInf_zero P _ _ i hs]

/-! ### Part (b): low-type mixing region -/

lemma A2_indiff (P : Params) (hP : P.Standing) {n : ℕ} (α : ℝ × ℝ) (hα : α ∈ A2 P n)
    (g : ℝ) (hg : g ∈ Set.Icc (0 : ℝ) 1) (heq : IsSymEq P n (g, 1) α) (l h : Fin n)
    (hl : ¬ IsHigh P l) (hh : IsHigh P h) :
    PinfMix P (g, 1) α l 1 = (1 : ℝ) / n + P.vL := by
  have hn : 0 < n := Fin.pos l
  have hvl : val P l = P.vL := by simp [val, hl]
  rcases eq_or_lt_of_le hg.1 with h0 | h0
  · -- g = 0
    subst h0
    have e1 := eq_zero_ineq P _ α heq l (by simp [stratProb, hl])
    rw [hvl] at e1
    rw [PinfMix_det P _ _ l (pure_01 P), detProf_01_low] at e1 ⊢
    have := (hα.2 l h hl hh).2.1
    linarith
  rcases eq_or_lt_of_le hg.2 with h1 | h1
  · -- g = 1
    subst h1
    have e1 := eq_one_ineq P _ α heq l (by simp [stratProb, hl])
    rw [hvl] at e1
    rw [PinfMix_det P _ _ l (pure_11 P), detProf_11] at e1 ⊢
    have := (hα.2 l h hl hh).1
    linarith
  · exact (eq_9 P hP hn α hα.1 g h0 h1 heq l hl).1

lemma eqInf_of_indiff {n : ℕ} (P : Params) (γ α : ℝ × ℝ) (i : Fin n) (v : ℝ)
    (h : PinfMix P γ α i 1 = (1 : ℝ) / n + v) :
    eqInf P γ α i = stratProb P γ i * v + (1 : ℝ) / n := by
  unfold eqInf
  rw [h, PinfMix_zero (Fin.pos i)]; ring

lemma ball_down2 {S : Set (ℝ × ℝ)} {α : ℝ × ℝ} (h : α ∈ interior S) :
    ∃ ε > 0, ((α.1, α.2 - ε) : ℝ × ℝ) ∈ S := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  refine ⟨ε / 2, by positivity, hball ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  simp only [dist_self, Real.dist_eq]
  rw [max_lt_iff]
  constructor
  · exact hε
  · rw [show α.2 - ε / 2 - α.2 = -(ε / 2) by ring, abs_neg, abs_of_pos (by positivity)]
    linarith

lemma A2_interior_g_pos (P : Params) (hP : P.Standing) {n : ℕ} (α : ℝ × ℝ)
    (hα : α ∈ interior (A2 P n)) (g : ℝ) (hg : g ∈ Set.Icc (0 : ℝ) 1)
    (heq : IsSymEq P n (g, 1) α) (l h : Fin n) (hl : ¬ IsHigh P l) (hh : IsHigh P h) :
    0 < g := by
  rcases eq_or_lt_of_le hg.1 with h0 | h0
  · exfalso
    subst h0
    have hA := interior_subset hα
    have e1 := A2_indiff P hP α hA 0 hg heq l h hl hh
    rw [PinfMix_det P _ _ l (pure_01 P), detProf_01_low] at e1
    obtain ⟨ε, hε, hmem⟩ := ball_down2 hα
    have h2 := (hmem.2 l h hl hh).2.1
    have hne : h ≠ l := by intro e; rw [e] at hh; exact hl hh
    have hlt := Pinf_strict_alpha P hP (Function.update (prof P 1 0) l 1)
      (by intro j; by_cases hj : j = l
          · subst hj; simp
          · rw [Function.update_of_ne hj]; unfold prof; split_ifs <;> simp)
      (α.1, α.2 - ε) α hmem.1 hA.1 ⟨le_rfl, by simp; linarith⟩ h l hne (by simp)
      (by rw [Function.update_of_ne hne]; simp [prof, hh])
      (by simp [testProb, hh]; linarith)
    linarith
  · exact h0

lemma A2_interior_vL_pos (P : Params) (hP : P.Standing) {n : ℕ} (α : ℝ × ℝ)
    (hα : α ∈ interior (A2 P n)) (l h : Fin n) (hl : ¬ IsHigh P l) (hh : IsHigh P h) :
    0 < P.vL := by
  have hn : 0 < n := Fin.pos l
  obtain ⟨hαS, -, -, -, hα2⟩ := interior_policy A2_sub hα
  have hA := interior_subset hα
  have h1 := (hA.2 l h hl hh).2.1
  have hne : h ≠ l := by intro e; rw [e] at hh; exact hl hh
  set x := Function.update (prof P 1 0) l 1 with hx
  have hxm : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j; by_cases hj : j = l
    · subst hj; simp [hx]
    · rw [hx, Function.update_of_ne hj]; unfold prof; split_ifs <;> simp
  have h2 := Pinf_strict_other P hP x hxm α hαS l h hne (by simp [hx])
    (by rw [hx, Function.update_of_ne hne]; simp [prof, hh]) (by simp [testProb, hh]; exact hα2)
  have hxm' : ∀ j, Function.update x h 0 j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j; by_cases hj : j = h
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact hxm j
  have h3 := lemma_1_a P hP hn (Function.update (Function.update x h 0) l 0)
    (Function.update x h 0) α hαS
    (by intro j; by_cases hj : j = l
        · subst hj; simp
        · rw [Function.update_of_ne hj]; exact hxm' j) hxm'
    (by intro j; by_cases hj : j = l
        · subst hj; simp [Function.update_of_ne hne.symm, hx]
        · rw [Function.update_of_ne hj]) l
  rw [Pinf_zero hn P _ α l (by simp)] at h3
  linarith

/-- Part (b). -/
lemma part_b (P : Params) (hP : P.Standing) {n : ℕ} (hn : 0 < n)
    (hgL : ∀ α α' : ℝ × ℝ, α ∈ interior (A2 P n) → α' ∈ interior (A2 P n) →
      PolicyLe α α' → ∀ g g' : ℝ,
      (∀ l : Fin n, ¬ IsHigh P l → PinfMix P (g, 1) α l 1 = (1 : ℝ) / n + P.vL) →
      (∀ l : Fin n, ¬ IsHigh P l → PinfMix P (g', 1) α' l 1 = (1 : ℝ) / n + P.vL) →
      g ∈ Set.Icc (0 : ℝ) 1 → g' ∈ Set.Icc (0 : ℝ) 1 → g ≤ g')
    (h0 : Fin n) (hh0 : IsHigh P h0) (l0 l1 : Fin n) (hl0 : ¬ IsHigh P l0)
    (hl1 : ¬ IsHigh P l1) (hl01 : l0 ≠ l1)
    (α α' : ℝ × ℝ) (hα : α ∈ interior (A2 P n)) (hα' : α' ∈ interior (A2 P n))
    (hle : PolicyLe α α') (hne : α ≠ α') (g g' : ℝ) (hg : g ∈ Set.Icc (0 : ℝ) 1)
    (hg' : g' ∈ Set.Icc (0 : ℝ) 1) (heq : IsSymEq P n (g, 1) α)
    (heq' : IsSymEq P n (g', 1) α') (l : Fin n) (hl : ¬ IsHigh P l) :
    eqInf P (g, 1) α l < eqInf P (g', 1) α' l := by
  have hA := interior_subset hα
  have hA' := interior_subset hα'
  obtain ⟨hαS, -, -, -, -⟩ := interior_policy A2_sub hα
  obtain ⟨hα'S, -, -, -, -⟩ := interior_policy A2_sub hα'
  have I1 : ∀ l : Fin n, ¬ IsHigh P l → PinfMix P (g, 1) α l 1 = (1 : ℝ) / n + P.vL :=
    fun l hl => A2_indiff P hP α hA g hg heq l h0 hl hh0
  have I2 : ∀ l : Fin n, ¬ IsHigh P l → PinfMix P (g', 1) α' l 1 = (1 : ℝ) / n + P.vL :=
    fun l hl => A2_indiff P hP α' hA' g' hg' heq' l h0 hl hh0
  have hgg : g ≤ g' := hgL α α' hα hα' hle g g' I1 I2 hg hg'
  have hgpos : 0 < g := A2_interior_g_pos P hP α hα g hg heq l h0 hl hh0
  have hvL : 0 < P.vL := A2_interior_vL_pos P hP α hα l h0 hl hh0
  have hlt : g < g' := by
    rcases eq_or_lt_of_le hgg with he | he
    · exfalso
      subst he
      have hγ : ((g, 1) : ℝ × ℝ) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
        ⟨hg, ⟨zero_le_one, le_rfl⟩⟩
      have hcases : α.1 < α'.1 ∨ α.2 < α'.2 := by
        by_contra hc
        push_neg at hc
        exact hne (Prod.ext (le_antisymm hle.1 hc.1) (le_antisymm hle.2 hc.2))
      rcases hcases with hc | hc
      · -- another low agent
        obtain ⟨w, hw, hwl⟩ : ∃ w : Fin n, ¬ IsHigh P w ∧ w ≠ l := by
          by_cases h : l0 = l
          · exact ⟨l1, hl1, fun e => hl01 (h.trans e.symm)⟩
          · exact ⟨l0, hl0, h⟩
        have := PinfMix_strict_alpha P hP (g, 1) hγ α α' hαS hα'S hle w l hwl
          (by simp [stratProb, hw]; exact hgpos) (by simp [testProb, hw]; exact hc)
        rw [I1 l hl, I2 l hl] at this
        linarith
      · have hwl : h0 ≠ l := by intro e; rw [e] at hh0; exact hl hh0
        have := PinfMix_strict_alpha P hP (g, 1) hγ α α' hαS hα'S hle h0 l hwl
          (by simp [stratProb, hh0]) (by simp [testProb, hh0]; exact hc)
        rw [I1 l hl, I2 l hl] at this
        linarith
    · exact he
  rw [eqInf_of_indiff P _ _ l _ (I1 l hl), eqInf_of_indiff P _ _ l _ (I2 l hl)]
  simp only [stratProb, hl, if_false]
  nlinarith

/-! ### Part (d): high-type mixing region -/

lemma A4_indiff (P : Params) (hP : P.Standing) {n : ℕ} (α : ℝ × ℝ) (hα : α ∈ A4 P n)
    (g : ℝ) (hg : g ∈ Set.Icc (0 : ℝ) 1) (heq : IsSymEq P n (0, g) α) (l h : Fin n)
    (hl : ¬ IsHigh P l) (hh : IsHigh P h) :
    0 < g ∧ PinfMix P (0, g) α h 1 = (1 : ℝ) / n + P.vH := by
  have hn : 0 < n := Fin.pos l
  have hvh : val P h = P.vH := by simp [val, hh]
  have hvH : 0 < P.vH := lt_of_le_of_lt hP.1 hP.2.1
  rcases eq_or_lt_of_le hg.1 with h0 | h0
  · exfalso
    subst h0
    have e1 := eq_zero_ineq P _ α heq h (by simp [stratProb, hh])
    rw [hvh, PinfMix_det P _ _ h (pure_00 P), Pinf_alone] at e1
    · linarith
    · intro j hj; simp [detProf, hj, stratProb]
  refine ⟨h0, ?_⟩
  rcases eq_or_lt_of_le hg.2 with h1 | h1
  · subst h1
    have e1 := eq_one_ineq P _ α heq h (by simp [stratProb, hh])
    rw [hvh] at e1
    rw [PinfMix_det P _ _ h (pure_01 P), detProf_01_high P h hh] at e1 ⊢
    have := (hα.2 l h hl hh).2
    linarith
  · exact (eq_10 P hP hn α hα.1 g h0 h1 heq h hh).1

lemma part_d (P : Params) (hP : P.Standing) {n : ℕ}
    (h0 h1 : Fin n) (hh0 : IsHigh P h0) (hh1 : IsHigh P h1) (h01 : h0 ≠ h1)
    (l0 : Fin n) (hl0 : ¬ IsHigh P l0)
    (α α' : ℝ × ℝ) (hα : α ∈ interior (A4 P n)) (hα' : α' ∈ interior (A4 P n))
    (hle : PolicyLe α α') (g g' : ℝ) (hg : g ∈ Set.Icc (0 : ℝ) 1)
    (hg' : g' ∈ Set.Icc (0 : ℝ) 1) (heq : IsSymEq P n (0, g) α)
    (heq' : IsSymEq P n (0, g') α') :
    (∀ h : Fin n, IsHigh P h →
      eqInf P (0, g) α h ≤ eqInf P (0, g') α' h ∧
      (α.2 < α'.2 → eqInf P (0, g) α h < eqInf P (0, g') α' h)) ∧
    (∀ l : Fin n, ¬ IsHigh P l →
      eqInf P (0, g) α l = (1 : ℝ) / n ∧ eqInf P (0, g') α' l = (1 : ℝ) / n) := by
  have hA := interior_subset hα
  have hA' := interior_subset hα'
  obtain ⟨hαS, -, -, -, hα2⟩ := interior_policy A4_sub hα
  obtain ⟨hα'S, -, -, -, -⟩ := interior_policy A4_sub hα'
  have hvH : 0 < P.vH := lt_of_le_of_lt hP.1 hP.2.1
  refine ⟨?_, ?_⟩
  · intro h hh
    obtain ⟨gpos, I1⟩ := A4_indiff P hP α hA g hg heq l0 h hl0 hh
    obtain ⟨gpos', I2⟩ := A4_indiff P hP α' hA' g' hg' heq' l0 h hl0 hh
    obtain ⟨w, hw, hwh⟩ : ∃ w : Fin n, IsHigh P w ∧ w ≠ h := by
      by_cases e : h0 = h
      · exact ⟨h1, hh1, fun e' => h01 (e.trans e'.symm)⟩
      · exact ⟨h0, hh0, e⟩
    have hγ : ((0, g) : ℝ × ℝ) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨⟨le_rfl, zero_le_one⟩, hg⟩
    have hγ' : ((0, g') : ℝ × ℝ) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨⟨le_rfl, zero_le_one⟩, hg'⟩
    have hgg : g ≤ g' := by
      by_contra hc
      push_neg at hc
      have c1 := PinfMix_anti_alpha P hP (0, g') hγ' α α' hαS hα'S hle h 1
        ⟨zero_le_one, le_rfl⟩
      have c2 := PinfMix_strict_g P hP (0, g) (0, g') hγ hγ'
        (by intro j; unfold stratProb; split_ifs
            · exact hc.le
            · exact le_rfl) α hαS w h hwh (by simp [stratProb, hw]; exact hc)
        (by simp [testProb, hw]; exact hα2)
      rw [I1] at c2; rw [I2] at c1
      linarith
    have hs : stratProb P (0, g) h = g := by simp [stratProb, hh]
    have hs' : stratProb P (0, g') h = g' := by simp [stratProb, hh]
    rw [eqInf_of_indiff P _ _ h _ I1, eqInf_of_indiff P _ _ h _ I2, hs, hs']
    refine ⟨by nlinarith, ?_⟩
    intro h2
    have hlt : g < g' := by
      rcases eq_or_lt_of_le hgg with he | he
      · exfalso
        subst he
        have := PinfMix_strict_alpha P hP (0, g) hγ α α' hαS hα'S hle w h hwh
          (by simp [stratProb, hw]; exact gpos) (by simp [testProb, hw]; exact h2)
        rw [I1, I2] at this
        linarith
      · exact he
    nlinarith
  · intro l hl
    have hs : ∀ g : ℝ, stratProb P (0, g) l = 0 := by intro g; simp [stratProb, hl]
    exact ⟨eqInf_zero P _ _ l (hs g), eqInf_zero P _ _ l (hs g')⟩




/-! ### Continuity -/

lemma continuous_bern {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f)
    (b : Bool) : Continuous (fun z => bern (f z) b) := by
  cases b
  · simp only [bern, Bool.false_eq_true, if_false]; exact continuous_const.sub hf
  · simp only [bern, if_true]; exact hf

lemma continuous_testProb {X : Type*} [TopologicalSpace X] {n : ℕ} (P : Params)
    {f : X → ℝ × ℝ} (hf : Continuous f) (k : Fin n) :
    Continuous (fun z => testProb P (f z) k) := by
  unfold testProb; split_ifs
  · exact continuous_snd.comp hf
  · exact continuous_fst.comp hf

lemma continuous_stratProb {X : Type*} [TopologicalSpace X] {n : ℕ} (P : Params)
    {f : X → ℝ × ℝ} (hf : Continuous f) (k : Fin n) :
    Continuous (fun z => stratProb P (f z) k) := by
  unfold stratProb; split_ifs
  · exact continuous_snd.comp hf
  · exact continuous_fst.comp hf

lemma continuous_Pinf {X : Type*} [TopologicalSpace X] {n : ℕ} (P : Params)
    (x : Fin n → ℝ) {f : X → ℝ × ℝ} (hf : Continuous f) (i : Fin n) :
    Continuous (fun z => Pinf P x (f z) i) := by
  unfold Pinf PinfG cascadeInf
  apply continuous_finset_sum; intro G _
  apply continuous_const.mul
  apply continuous_finset_sum; intro s _
  apply continuous_finset_sum; intro Z _
  apply continuous_finset_sum; intro T _
  apply Continuous.mul _ continuous_const
  apply Continuous.mul _ continuous_const
  apply continuous_const.mul
  apply continuous_finset_prod; intro k _
  exact continuous_bern (continuous_testProb P hf k) _

lemma continuous_PinfMix {n : ℕ} (P : Params) (i : Fin n) (xi : ℝ) :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => PinfMix P z.1 z.2 i xi) := by
  have hfst : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1) := continuous_fst
  have hsnd : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2) := continuous_snd
  unfold PinfMix
  apply continuous_finset_sum; intro a _
  apply Continuous.mul
  · apply continuous_finset_prod; intro j _
    by_cases hj : j = i
    · simp only [hj, if_true]; exact continuous_const
    · simp only [hj, if_false]; exact continuous_bern (continuous_stratProb P hfst j) _
  · exact continuous_Pinf P _ hsnd i

lemma continuous_eqInf {n : ℕ} (P : Params) (i : Fin n) :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => eqInf P z.1 z.2 i) := by
  have hfst : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1) := continuous_fst
  unfold eqInf
  have h1 := continuous_stratProb P hfst i
  exact (h1.mul (continuous_PinfMix P i 1)).add
    ((continuous_const.sub h1).mul (continuous_PinfMix P i 0))

lemma continuous_expUtil {n : ℕ} (P : Params) (i : Fin n) (xi : ℝ) :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => expUtil P z.1 z.2 i xi) := by
  have hsnd : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2) := continuous_snd
  unfold expUtil
  exact (continuous_const.sub (continuous_PinfMix P i xi)).sub
    (continuous_const.mul (continuous_testProb P hsnd i))

/-- The equilibrium relation is closed under limits. -/
lemma IsSymEq_limit {n : ℕ} (P : Params) (u : ℕ → (ℝ × ℝ) × (ℝ × ℝ))
    (z : (ℝ × ℝ) × (ℝ × ℝ)) (hu : Filter.Tendsto u Filter.atTop (nhds z))
    (heq : ∀ k, IsSymEq P n (u k).1 (u k).2) : IsSymEq P n z.1 z.2 := by
  refine ⟨?_, ?_⟩
  · have hc : IsClosed (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
      isClosed_Icc.prod isClosed_Icc
    exact hc.mem_of_tendsto ((continuous_fst.tendsto z).comp hu)
      (Filter.Eventually.of_forall (fun k => (heq k).1))
  · intro i xi hxi
    have hL := ((continuous_expUtil P i xi).tendsto z).comp hu
    have hfst : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1) := continuous_fst
    have hs := (continuous_stratProb P hfst i)
    have hRc : Continuous (fun w : (ℝ × ℝ) × (ℝ × ℝ) => stratProb P w.1 i * expUtil P w.1 w.2 i 1 +
        (1 - stratProb P w.1 i) * expUtil P w.1 w.2 i 0) :=
      (hs.mul (continuous_expUtil P i 1)).add
        ((continuous_const.sub hs).mul (continuous_expUtil P i 0))
    have hR := (hRc.tendsto z).comp hu
    exact le_of_tendsto_of_tendsto' hL hR (fun k => (heq k).2 i xi hxi)

/-- The policy regions are closed. -/
lemma region_closed_aux {n : ℕ} (A : Set (ℝ × ℝ)) (P : Params)
    (Q : (ℝ × ℝ) → Fin n → Fin n → Prop)
    (hA : A = {α | α ∈ PolicySquare ∧ ∀ l h : Fin n, ¬ IsHigh P l → IsHigh P h → Q α l h})
    (hQ : ∀ l h : Fin n, ∀ u : ℕ → ℝ × ℝ, ∀ α, Filter.Tendsto u Filter.atTop (nhds α) →
      (∀ k, Q (u k) l h) → Q α l h) :
    IsClosed A := by
  rw [← closure_subset_iff_isClosed]
  intro α hα
  rw [mem_closure_iff_seq_limit] at hα
  obtain ⟨u, hu, hlim⟩ := hα
  rw [hA] at hu ⊢
  refine ⟨?_, ?_⟩
  · exact (isClosed_Icc.prod isClosed_Icc).mem_of_tendsto hlim
      (Filter.Eventually.of_forall (fun k => (hu k).1))
  · intro l h hl hh
    exact hQ l h u α hlim (fun k => (hu k).2 l h hl hh)

lemma lim_le {n : ℕ} (P : Params) (x : Fin n → ℝ) (i : Fin n) (c : ℝ) (u : ℕ → ℝ × ℝ)
    (α : ℝ × ℝ) (hlim : Filter.Tendsto u Filter.atTop (nhds α))
    (h : ∀ k, Pinf P x (u k) i ≤ c) : Pinf P x α i ≤ c :=
  le_of_tendsto' (((continuous_Pinf P x continuous_id i).tendsto α).comp hlim) h

lemma lim_ge {n : ℕ} (P : Params) (x : Fin n → ℝ) (i : Fin n) (c : ℝ) (u : ℕ → ℝ × ℝ)
    (α : ℝ × ℝ) (hlim : Filter.Tendsto u Filter.atTop (nhds α))
    (h : ∀ k, c ≤ Pinf P x (u k) i) : c ≤ Pinf P x α i :=
  ge_of_tendsto' (((continuous_Pinf P x continuous_id i).tendsto α).comp hlim) h

lemma A1_closed (P : Params) (n : ℕ) : IsClosed (A1 P n) := by
  apply region_closed_aux _ P _ rfl
  intro l h u α hlim hk
  exact ⟨lim_le P _ l _ u α hlim (fun k => (hk k).1), lim_le P _ h _ u α hlim (fun k => (hk k).2)⟩

lemma A2_closed (P : Params) (n : ℕ) : IsClosed (A2 P n) := by
  apply region_closed_aux _ P _ rfl
  intro l h u α hlim hk
  exact ⟨lim_ge P _ l _ u α hlim (fun k => (hk k).1), lim_le P _ l _ u α hlim (fun k => (hk k).2.1),
    lim_le P _ h _ u α hlim (fun k => (hk k).2.2)⟩

lemma A3_closed (P : Params) (n : ℕ) : IsClosed (A3 P n) := by
  apply region_closed_aux _ P _ rfl
  intro l h u α hlim hk
  exact ⟨lim_ge P _ l _ u α hlim (fun k => (hk k).1), lim_ge P _ l _ u α hlim (fun k => (hk k).2.1),
    lim_le P _ h _ u α hlim (fun k => (hk k).2.2)⟩

lemma A4_closed (P : Params) (n : ℕ) : IsClosed (A4 P n) := by
  apply region_closed_aux _ P _ rfl
  intro l h u α hlim hk
  exact ⟨lim_ge P _ l _ u α hlim (fun k => (hk k).1), lim_ge P _ h _ u α hlim (fun k => (hk k).2)⟩

/-- Continuity of the equilibrium infection probability at a policy with a unique
equilibrium. -/
lemma continuity_of_unique {n : ℕ} (P : Params) (α γ : ℝ × ℝ) (heq : IsSymEq P n γ α)
    (huniq : ∀ γ' : ℝ × ℝ, IsSymEq P n γ' α → γ' = γ) (i : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ α' ∈ PolicySquare, dist α' α < δ →
      ∀ γ' : ℝ × ℝ, IsSymEq P n γ' α' →
        |eqInf P γ' α' i - eqInf P γ α i| < ε := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ α' : ℝ × ℝ, ∃ γ' : ℝ × ℝ, dist α' α < 1 / ((k : ℝ) + 1) ∧
      IsSymEq P n γ' α' ∧ ε ≤ |eqInf P γ' α' i - eqInf P γ α i| := by
    intro k
    obtain ⟨α', _, hd, γ', he, hge⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨α', γ', hd, he, hge⟩
  choose a g hd he hge using hseq
  have hmem : ∀ k, g k ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := fun k => (he k).1
  obtain ⟨γs, _, φ, hφ, hlimg⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hmem
  have hlima : Filter.Tendsto (a ∘ φ) Filter.atTop (nhds α) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h1 : Filter.Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact h0.comp hφ.tendsto_atTop
    apply squeeze_zero (fun k => dist_nonneg) _ h1
    intro k
    exact (hd (φ k)).le
  have hlim : Filter.Tendsto (fun k => ((g ∘ φ) k, (a ∘ φ) k)) Filter.atTop (nhds (γs, α)) :=
    hlimg.prodMk_nhds hlima
  have hsym : IsSymEq P n γs α :=
    IsSymEq_limit P (fun k => ((g ∘ φ) k, (a ∘ φ) k)) (γs, α) hlim (fun k => he (φ k))
  have hγs : γs = γ := huniq γs hsym
  subst hγs
  have hc := ((continuous_eqInf P i).tendsto (γs, α)).comp hlim
  have hev := (Metric.tendsto_nhds.mp hc) ε hε
  obtain ⟨k, hk⟩ := hev.exists
  have := hge (φ k)
  simp only [Function.comp, Real.dist_eq] at hk
  linarith

/-! ### Existence at pure profiles -/

lemma PinfMix_concave_ineq (P : Params) (hP : P.Standing) {n : ℕ} (γ α : ℝ × ℝ)
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (hα : α ∈ PolicySquare) (i : Fin n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * PinfMix P γ α i 0 + t * PinfMix P γ α i 1 ≤ PinfMix P γ α i t := by
  have hn : 0 < n := Fin.pos i
  rw [PinfMix_eq_bexp, PinfMix_eq_bexp, PinfMix_eq_bexp]
  unfold bexp
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hw : 0 ≤ ∏ k, bern (if k = i then (1:ℝ) else stratProb P γ k) (a k) :=
    Finset.prod_nonneg (fun k _ => bern_nonneg (mixq_mem P hγ i k).1 (mixq_mem P hγ i k).2 _)
  have hc := lemma_1_b P hP hn (profileOf a) α hα i
    (by intro j _; unfold profileOf; split_ifs <;> simp)
  have := hc.2 (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    (show (0:ℝ) ≤ 1 - t by linarith [ht.2]) ht.1 (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one] at this
  simp only
  nlinarith [mul_le_mul_of_nonneg_left this hw]

lemma eq_of_pure (P : Params) (hP : P.Standing) {n : ℕ} (γ α : ℝ × ℝ)
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (hα : α ∈ PolicySquare)
    (hpure : ∀ j : Fin n, stratProb P γ j = 0 ∨ stratProb P γ j = 1)
    (h1 : ∀ i : Fin n, stratProb P γ i = 1 → PinfMix P γ α i 1 ≤ (1 : ℝ) / n + val P i)
    (h0 : ∀ i : Fin n, stratProb P γ i = 0 → (1 : ℝ) / n + val P i ≤ PinfMix P γ α i 1) :
    IsSymEq P n γ α := by
  refine ⟨hγ, ?_⟩
  intro i xi hxi
  have hc := PinfMix_concave_ineq P hP γ α hγ hα i xi hxi
  have hz := PinfMix_zero (Fin.pos i) P γ α i
  unfold expUtil
  rcases hpure i with hs | hs
  · have := h0 i hs
    rw [hs]
    nlinarith [hxi.1, hxi.2]
  · have := h1 i hs
    rw [hs]
    nlinarith [hxi.1, hxi.2]




/-! ### Certain non-transmitters are irrelevant (the corner `p = 0`, `α_L = 1`) -/

lemma zeroW_rep (P : Params) {n : ℕ} (x : Fin n → ℝ) (α : ℝ × ℝ) (w l : Fin n) :
    Pinf P (Function.update x w 0) α l = bexp (linkQ P x)
      (fun f => PinfG P (mkG (fun k => if SI w k then false else f k)) α l) := by
  rw [Pinf_eq_bexp, bexp_split (SI w), bexp_split (SI w)]
  apply Finset.sum_congr rfl
  intro ω₂ _
  congr 1
  · apply Finset.prod_congr rfl
    intro k _
    have e1 : k.1.1 ≠ w := fun h => k.2 (Or.inl h)
    have e2 : k.1.2 ≠ w := fun h => k.2 (Or.inr h)
    simp [linkQ, Function.update_of_ne e1, Function.update_of_ne e2]
  · rw [bexp_zero_prob]
    · have : (fun ω₁ : {k // SI w k} → Bool =>
          PinfG P (mkG (fun k => if SI w k then false else
            ((Equiv.piEquivPiSubtypeProd (SI w) fun _ => Bool).symm (ω₁, ω₂)) k)) α l) =
          fun _ => PinfG P (mkG (mergeI w (fun _ => false) ω₂)) α l := by
        funext ω₁
        have := zeroS_merge w ω₁ ω₂
        unfold mergeI at this ⊢
        rw [this]
      rw [this, bexp_const]
      rfl
    · intro k
      simp only [linkQ]
      split_ifs
      · rcases k.2 with h | h
        · rw [h]; simp
        · rw [h]; simp
      · rfl

lemma path_avoid {n : ℕ} (G G' : SimpleGraph (Fin n)) (w : Fin n)
    (hGG : ∀ a b, a ≠ w → b ≠ w → G.Adj a b → G'.Adj a b) (T : Fin n → Fin n → Bool)
    (hT : ∀ j, T w j = false) (s i : Fin n) (hiw : i ≠ w)
    (h : Relation.ReflTransGen (fun k j => G.Adj k j ∧ T k j = true) s i) :
    Relation.ReflTransGen (fun k j => G'.Adj k j ∧ T k j = true) s i := by
  have key : ∀ c, Relation.ReflTransGen (fun k j => G.Adj k j ∧ T k j = true) s c →
      Relation.ReflTransGen (fun k j => G'.Adj k j ∧ T k j = true) s c ∨ c = w := by
    intro c hc
    induction hc with
    | refl => exact Or.inl Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      have hbw : b ≠ w := by
        intro e; rw [e, hT c] at hbc; exact absurd hbc.2 (by simp)
      rcases ih with ih | ih
      · by_cases hcw : c = w
        · exact Or.inr hcw
        · exact Or.inl (ih.tail ⟨hGG b c hbw hcw hbc.1, hbc.2⟩)
      · exact absurd ih hbw
  rcases key i h with h | h
  · exact h
  · exact absurd h hiw

lemma cascade_noTx {n : ℕ} (G G' : SimpleGraph (Fin n)) (w i : Fin n) (hiw : i ≠ w)
    (hGG : ∀ a b, a ≠ w → b ≠ w → G.Adj a b → G'.Adj a b) (test : Fin n → ℝ)
    (htest : ∀ k, 0 ≤ test k ∧ test k ≤ 1) (htw : test w = 1) (β p : ℝ) (hp : p = 0)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    cascadeInf G test β p i ≤ cascadeInf G' test β p i := by
  unfold cascadeInf
  apply Finset.sum_le_sum; intro s _
  apply Finset.sum_le_sum; intro Z _
  apply Finset.sum_le_sum; intro T _
  have hZnn : 0 ≤ ∏ k, bern (test k) (Z k) :=
    Finset.prod_nonneg (fun k _ => bern_nonneg (htest k).1 (htest k).2 _)
  have hTnn : 0 ≤ ∏ k : Fin n, ∏ j : Fin n, bern (if Z k then β * p else β) (T k j) := by
    apply Finset.prod_nonneg; intro k _
    apply Finset.prod_nonneg; intro j _
    split_ifs
    · rw [hp, mul_zero]; exact bern_nonneg le_rfl zero_le_one _
    · exact bern_nonneg hβ0 hβ1 _
  by_cases hgood : Z w = true ∧ ∀ j, T w j = false
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact ind_mono (path_avoid G G' w hGG T hgood.2 s i hiw)
  · have hzero : (∏ k, bern (test k) (Z k)) *
        (∏ k : Fin n, ∏ j : Fin n, bern (if Z k then β * p else β) (T k j)) = 0 := by
      by_cases hZ : Z w = true
      · have : ∃ j, T w j = true := by
          by_contra hc; push_neg at hc
          exact hgood ⟨hZ, fun j => by simpa using hc j⟩
        obtain ⟨j, hj⟩ := this
        apply mul_eq_zero_of_right
        apply Finset.prod_eq_zero (Finset.mem_univ w)
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [hZ, hj, bern, hp]
      · apply mul_eq_zero_of_left
        apply Finset.prod_eq_zero (Finset.mem_univ w)
        have : Z w = false := by simpa using hZ
        simp [this, bern, htw]
    have e : ∀ c : ℝ, ((1 : ℝ) / n * (∏ k, bern (test k) (Z k)) *
        (∏ k : Fin n, ∏ j : Fin n, bern (if Z k then β * p else β) (T k j))) * c = 0 := by
      intro c
      rw [mul_assoc ((1:ℝ) / n), hzero]; ring
    rw [e, e]

lemma Pinf_noTx (P : Params) (hP : P.Standing) {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (α : ℝ × ℝ) (hα : α ∈ PolicySquare) (w i : Fin n)
    (hiw : i ≠ w) (hp : P.p = 0) (htw : testProb P α w = 1) :
    Pinf P x α i ≤ Pinf P (Function.update x w 0) α i := by
  obtain ⟨h1, h2, h3, h4⟩ := standing_bp hP
  rw [zeroW_rep, Pinf_eq_bexp]
  apply bexp_le_of_le _ (linkQ_mem P hP x hx)
  intro f
  unfold PinfG
  apply cascade_noTx _ _ w i hiw _ _ (testProb_mem P hα) htw _ _ hp h4 h3
  intro a b ha hb hab
  rw [mkG_adj] at hab ⊢
  have hns : ∀ c d, c ≠ w → d ≠ w → ¬ SI w (c, d) := by
    rintro c d hc hd (h | h)
    · exact hc h
    · exact hd h
  refine ⟨hab.1, ?_⟩
  simp only [if_neg (hns a b ha hb), if_neg (hns b a hb ha)]
  exact hab.2

lemma corner_low (P : Params) (hP : P.Standing) {n : ℕ} (α : ℝ × ℝ) (hα : α ∈ PolicySquare)
    (hp : P.p = 0) (h1 : α.1 = 1) (l : Fin n) (hl : ¬ IsHigh P l) :
    Pinf P (prof P 1 1) α l ≤ Pinf P (Function.update (prof P 1 0) l 1) α l := by
  set S : Finset (Fin n) := Finset.univ.filter (fun j => ¬ IsHigh P j ∧ j ≠ l) with hS
  let xT : Finset (Fin n) → Fin n → ℝ := fun T j => if j ∈ T then 0 else 1
  have hxT : ∀ T j, xT T j ∈ Set.Icc (0 : ℝ) 1 := by
    intro T j; simp only [xT]; split_ifs <;> simp
  have key : ∀ T : Finset (Fin n), T ⊆ S → Pinf P (xT ∅) α l ≤ Pinf P (xT T) α l := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact le_rfl
    | insert a T ha ih =>
      intro hsub
      have haS : a ∈ S := hsub (Finset.mem_insert_self a T)
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at haS
      have e : xT (insert a T) = Function.update (xT T) a 0 := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [xT]
        · simp [xT, hj, Function.update_of_ne hj]
      rw [e]
      exact (ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))).trans
        (Pinf_noTx P hP _ (hxT T) α hα a l (Ne.symm haS.2) hp
          (by simp [testProb, haS.1, h1]))
  have e0 : xT ∅ = prof P 1 1 := by funext j; simp [xT, prof]
  have eS : xT S = Function.update (prof P 1 0) l 1 := by
    funext j
    by_cases hj : j = l
    · subst hj; simp [xT, hS]
    · rw [Function.update_of_ne hj]
      by_cases hh : IsHigh P j
      · simp [xT, hS, hh, prof]
      · simp [xT, hS, hh, hj, prof]
  rw [← e0, ← eS]
  exact key S (subset_refl S)




theorem thm1 (P : Params) (hP : P.Standing) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n →
      (∀ α ∈ PolicySquare, ∃ γ : ℝ × ℝ, IsSymEq P n γ α) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A1 P n) → α' ∈ interior (A1 P n) →
        PolicyLe α α' → IsSymEq P n γ α → IsSymEq P n γ' α' →
        ∀ i : Fin n, eqInf P γ' α' i ≤ eqInf P γ α i) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A2 P n) → α' ∈ interior (A2 P n) →
        PolicyLe α α' → α ≠ α' →
        IsSymEq P n γ α → IsSymEq P n γ' α' →
        ∀ l : Fin n, ¬ IsHigh P l → eqInf P γ α l < eqInf P γ' α' l) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A3 P n) → α' ∈ interior (A3 P n) →
        PolicyLe α α' → IsSymEq P n γ α → IsSymEq P n γ' α' →
        ∀ i : Fin n, eqInf P γ' α' i ≤ eqInf P γ α i) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A4 P n) → α' ∈ interior (A4 P n) →
        PolicyLe α α' → IsSymEq P n γ α → IsSymEq P n γ' α' →
        (∀ h : Fin n, IsHigh P h →
          eqInf P γ α h ≤ eqInf P γ' α' h ∧
          (α.2 < α'.2 → eqInf P γ α h < eqInf P γ' α' h)) ∧
        (∀ l : Fin n, ¬ IsHigh P l →
          eqInf P γ α l = (1 : ℝ) / n ∧
          eqInf P γ' α' l = (1 : ℝ) / n)) ∧
      (∀ α ∈ PolicySquare,
        (α ∈ frontier (A1 P n) ∨ α ∈ frontier (A2 P n) ∨
          α ∈ frontier (A3 P n) ∨ α ∈ frontier (A4 P n)) →
        (P.p = 0 → α.1 < 1) →
        ∀ γ : ℝ × ℝ, IsSymEq P n γ α → ∀ (i : Fin n) (ε : ℝ), 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ ∀ α' ∈ PolicySquare, dist α' α < δ →
            ∀ γ' : ℝ × ℝ, IsSymEq P n γ' α' →
              |eqInf P γ' α' i - eqInf P γ α i| < ε) := by
  obtain ⟨Mp, hMp0, hMp⟩ := proposition_2 P hP
  obtain ⟨Mc, hMc0, hMc⟩ := regions_cover P hP
  obtain ⟨Mg, hMg0, hMg⟩ := gammaL_mono P hP
  obtain ⟨Ml, hMl0, hMl⟩ := many_low P hP
  obtain ⟨Mh, hMh0, hMh⟩ := many_high P hP
  refine ⟨Mp + Mc + Mg + Ml + Mh, by omega, ?_⟩
  intro n hn
  obtain ⟨pa, pb, pc, pd⟩ := hMp n (by omega)
  have hcov := hMc n (by omega)
  have hgL := hMg n (by omega)
  have hlow := hMl n (by omega)
  have hhigh := hMh n (by omega)
  have hnpos : 0 < n := by omega
  let l0 : Fin n := ⟨n - 1, by omega⟩
  let l1 : Fin n := ⟨n - 2, by omega⟩
  let h0 : Fin n := ⟨0, hnpos⟩
  let h1 : Fin n := ⟨1, by omega⟩
  have hl0 : ¬ IsHigh P l0 := by unfold IsHigh; simp only [l0]; omega
  have hl1 : ¬ IsHigh P l1 := by unfold IsHigh; simp only [l1]; omega
  have hh0 : IsHigh P h0 := by unfold IsHigh; simp only [h0]; omega
  have hh1 : IsHigh P h1 := by unfold IsHigh; simp only [h1]; omega
  have hl01 : l0 ≠ l1 := by
    intro e; have := congrArg Fin.val e; simp only [l0, l1] at this; omega
  have hh01 : h0 ≠ h1 := by
    intro e; have := congrArg Fin.val e; simp only [h0, h1] at this; omega
  have hvL : ∀ i : Fin n, ¬ IsHigh P i → val P i = P.vL := fun i hi => by simp [val, hi]
  have hvH : ∀ i : Fin n, IsHigh P i → val P i = P.vH := fun i hi => by simp [val, hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- existence
    intro α hα
    by_cases hc : P.p = 0 → α.1 < 1
    · rcases hcov α hα with hA | hA | hA | hA
      · exact ⟨(1, 1), (pa α hA hc (1, 1)).mpr rfl⟩
      · obtain ⟨g, _, hg⟩ := pb α hA hc
        exact ⟨(g, 1), (hg (g, 1)).mpr rfl⟩
      · exact ⟨(0, 1), (pc α hA hc (0, 1)).mpr rfl⟩
      · obtain ⟨g, _, hg⟩ := pd α hA
        exact ⟨(0, g), (hg (0, g)).mpr rfl⟩
    · push_neg at hc
      obtain ⟨hp0, hα1⟩ := hc
      have hαL : α.1 = 1 := le_antisymm hα.1.2 hα1
      have h01 : ((0, 1) : ℝ × ℝ) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
        ⟨⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩⟩
      have h11 : ((1, 1) : ℝ × ℝ) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
        ⟨⟨zero_le_one, le_rfl⟩, ⟨zero_le_one, le_rfl⟩⟩
      -- the profile (0,1) is an equilibrium when lows weakly prefer 0 and highs weakly prefer 1
      have eq01 : (∀ l : Fin n, ¬ IsHigh P l →
          P.vL + (1 : ℝ) / n ≤ Pinf P (Function.update (prof P 1 0) l 1) α l) →
          (∀ h : Fin n, IsHigh P h → Pinf P (prof P 1 0) α h ≤ P.vH + (1 : ℝ) / n) →
          ∃ γ : ℝ × ℝ, IsSymEq P n γ α := by
        intro hL hH
        refine ⟨(0, 1), eq_of_pure P hP (0, 1) α h01 hα (pure_01 P) ?_ ?_⟩
        · intro i hi
          have hih : IsHigh P i := by
            by_contra hc; simp [stratProb, hc] at hi
          rw [PinfMix_det P _ _ i (pure_01 P), detProf_01_high P i hih, hvH i hih]
          linarith [hH i hih]
        · intro i hi
          have hil : ¬ IsHigh P i := by
            intro hc; simp [stratProb, hc] at hi
          rw [PinfMix_det P _ _ i (pure_01 P), detProf_01_low P i, hvL i hil]
          linarith [hL i hil]
      rcases hcov α hα with hA | hA | hA | hA
      · refine ⟨(1, 1), eq_of_pure P hP (1, 1) α h11 hα (pure_11 P) ?_ ?_⟩
        · intro i _
          rw [PinfMix_det P _ _ i (pure_11 P), detProf_11]
          by_cases hi : IsHigh P i
          · rw [hvH i hi]; linarith [(hA.2 l0 i hl0 hi).2]
          · rw [hvL i hi]; linarith [(hA.2 i h0 hi hh0).1]
        · intro i hi; simp [stratProb] at hi
      · apply eq01
        · intro l hl
          exact ((hA.2 l h0 hl hh0).1).trans (corner_low P hP α hα hp0 hαL l hl)
        · intro h hh; exact (hA.2 l0 h hl0 hh).2.2
      · apply eq01
        · intro l hl; exact (hA.2 l h0 hl hh0).2.1
        · intro h hh; exact (hA.2 l0 h hl0 hh).2.2
      · obtain ⟨g, _, hg⟩ := pd α hA
        exact ⟨(0, g), (hg (0, g)).mpr rfl⟩
  · -- part (a)
    intro α α' γ γ' hα hα' hle heq heq' i
    obtain ⟨hαS, -, hαL, -, -⟩ := interior_policy A1_sub hα
    obtain ⟨hα'S, -, hα'L, -, -⟩ := interior_policy A1_sub hα'
    have hγ := (pa α (interior_subset hα) (fun _ => hαL) γ).mp heq
    have hγ' := (pa α' (interior_subset hα') (fun _ => hα'L) γ').mp heq'
    exact part_a P hP α α' γ γ' hαS hα'S hle hγ hγ' i
  · -- part (b)
    intro α α' γ γ' hα hα' hle hne heq heq' l hl
    obtain ⟨_, -, hαL, -, -⟩ := interior_policy A2_sub hα
    obtain ⟨_, -, hα'L, -, -⟩ := interior_policy A2_sub hα'
    obtain ⟨g, hg, hgi⟩ := pb α (interior_subset hα) (fun _ => hαL)
    obtain ⟨g', hg', hgi'⟩ := pb α' (interior_subset hα') (fun _ => hα'L)
    have hγ := (hgi γ).mp heq
    have hγ' := (hgi' γ').mp heq'
    subst hγ hγ'
    exact part_b P hP hnpos hgL h0 hh0 l0 l1 hl0 hl1 hl01 α α' hα hα' hle hne g g' hg hg'
      heq heq' l hl
  · -- part (c)
    intro α α' γ γ' hα hα' hle heq heq' i
    obtain ⟨hαS, -, hαL, -, -⟩ := interior_policy A3_sub hα
    obtain ⟨hα'S, -, hα'L, -, -⟩ := interior_policy A3_sub hα'
    have hγ := (pc α (interior_subset hα) (fun _ => hαL) γ).mp heq
    have hγ' := (pc α' (interior_subset hα') (fun _ => hα'L) γ').mp heq'
    exact part_c P hP α α' γ γ' hαS hα'S hle hγ hγ' i
  · -- part (d)
    intro α α' γ γ' hα hα' hle heq heq'
    obtain ⟨g, hg, hgi⟩ := pd α (interior_subset hα)
    obtain ⟨g', hg', hgi'⟩ := pd α' (interior_subset hα')
    have hγ := (hgi γ).mp heq
    have hγ' := (hgi' γ').mp heq'
    subst hγ hγ'
    exact part_d P hP h0 h1 hh0 hh1 hh01 l0 hl0 α α' hα hα' hle g g' hg hg' heq heq'
  · -- continuity at the boundaries
    intro α _ hfr hcorner γ heq i ε hε
    have huniq : ∀ γ' : ℝ × ℝ, IsSymEq P n γ' α → γ' = γ := by
      intro γ' h'
      rcases hfr with hf | hf | hf | hf
      · have hA : α ∈ A1 P n := (A1_closed P n).frontier_subset hf
        rw [(pa α hA hcorner γ').mp h', (pa α hA hcorner γ).mp heq]
      · have hA : α ∈ A2 P n := (A2_closed P n).frontier_subset hf
        obtain ⟨g, _, hg⟩ := pb α hA hcorner
        rw [(hg γ').mp h', (hg γ).mp heq]
      · have hA : α ∈ A3 P n := (A3_closed P n).frontier_subset hf
        rw [(pc α hA hcorner γ').mp h', (pc α hA hcorner γ).mp heq]
      · have hA : α ∈ A4 P n := (A4_closed P n).frontier_subset hf
        obtain ⟨g, _, hg⟩ := pd α hA
        rw [(hg γ').mp h', (hg γ).mp heq]
    exact continuity_of_unique P α γ heq huniq i ε hε


end TestDistancing.Equilibrium

open TestDistancing.Equilibrium

theorem solution (P : Params) (hP : P.Standing) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n →
      (∀ α ∈ PolicySquare, ∃ γ : ℝ × ℝ, IsSymEq P n γ α) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A1 P n) → α' ∈ interior (A1 P n) →
        PolicyLe α α' → IsSymEq P n γ α → IsSymEq P n γ' α' →
        ∀ i : Fin n, eqInf P γ' α' i ≤ eqInf P γ α i) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A2 P n) → α' ∈ interior (A2 P n) →
        PolicyLe α α' → α ≠ α' →
        IsSymEq P n γ α → IsSymEq P n γ' α' →
        ∀ l : Fin n, ¬ IsHigh P l → eqInf P γ α l < eqInf P γ' α' l) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A3 P n) → α' ∈ interior (A3 P n) →
        PolicyLe α α' → IsSymEq P n γ α → IsSymEq P n γ' α' →
        ∀ i : Fin n, eqInf P γ' α' i ≤ eqInf P γ α i) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A4 P n) → α' ∈ interior (A4 P n) →
        PolicyLe α α' → IsSymEq P n γ α → IsSymEq P n γ' α' →
        (∀ h : Fin n, IsHigh P h →
          eqInf P γ α h ≤ eqInf P γ' α' h ∧
          (α.2 < α'.2 → eqInf P γ α h < eqInf P γ' α' h)) ∧
        (∀ l : Fin n, ¬ IsHigh P l →
          eqInf P γ α l = (1 : ℝ) / n ∧
          eqInf P γ' α' l = (1 : ℝ) / n)) ∧
      (∀ α ∈ PolicySquare,
        (α ∈ frontier (A1 P n) ∨ α ∈ frontier (A2 P n) ∨
          α ∈ frontier (A3 P n) ∨ α ∈ frontier (A4 P n)) →
        (P.p = 0 → α.1 < 1) →
        ∀ γ : ℝ × ℝ, IsSymEq P n γ α → ∀ (i : Fin n) (ε : ℝ), 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ ∀ α' ∈ PolicySquare, dist α' α < δ →
            ∀ γ' : ℝ × ℝ, IsSymEq P n γ' α' →
              |eqInf P γ' α' i - eqInf P γ α i| < ε) :=
  thm1 P hP
