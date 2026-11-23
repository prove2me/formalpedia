-- Prove2me | solution 1 for SmallSecretLWE.Classical.fact_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T06:21:13.092259+00:00
-- url     : https://prove2.me/submissions/09d37e62-b437-4cb8-bd4e-35d66a19b695

import Mathlib

open scoped Classical

noncomputable def esymA {S : Type*} (p : S → ℝ) (s : Finset S) (k : ℕ) : ℝ :=
  ∑ T ∈ s.powersetCard k, ∏ i ∈ T, p i

lemma esymA_zero {S : Type*} (p : S → ℝ) (s : Finset S) : esymA p s 0 = 1 := by
  simp [esymA]

lemma esymA_insert {S : Type*} (p : S → ℝ) (s : Finset S) (x : S) (hx : x ∉ s) (k : ℕ) :
    esymA p (insert x s) (k+1) = esymA p s (k+1) + p x * esymA p s k := by
  unfold esymA
  rw [Finset.powersetCard_succ_insert hx, Finset.sum_union, Finset.sum_image, Finset.mul_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.prod_insert]
    intro h
    exact hx (Finset.mem_powersetCard.1 hT |>.1 h)
  · intro A hA B hB hAB
    have hA' := Finset.mem_powersetCard.1 hA
    have hB' := Finset.mem_powersetCard.1 hB
    have h1 : x ∉ A := fun h => hx (hA'.1 h)
    have h2 : x ∉ B := fun h => hx (hB'.1 h)
    have := congrArg (Finset.erase · x) hAB
    simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this
  · rw [Finset.disjoint_left]
    intro T h1 h2
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 h2
    have := (Finset.mem_powersetCard.1 h1).1 (Finset.mem_insert_self x A)
    exact hx this

lemma esymA_nonneg {S : Type*} (p : S → ℝ) (hp : ∀ i, 0 ≤ p i) (s : Finset S) (k : ℕ) :
    0 ≤ esymA p s k :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun i _ => hp i

lemma esymA_congr {S : Type*} (p q : S → ℝ) (s : Finset S) (h : ∀ i ∈ s, p i = q i) (k : ℕ) :
    esymA p s k = esymA q s k := by
  unfold esymA
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.prod_congr rfl
  intro i hi
  exact h i ((Finset.mem_powersetCard.1 hT).1 hi)

lemma esymA_two {S : Type*} (p : S → ℝ) (s : Finset S) (a b : S) (ha : a ∉ s) (hb : b ∉ s)
    (hab : a ≠ b) (k : ℕ) :
    esymA p (insert a (insert b s)) (k+2) =
      esymA p s (k+2) + (p a + p b) * esymA p s (k+1) + p a * p b * esymA p s k := by
  have hb' : b ∉ s := hb
  have ha' : a ∉ insert b s := by simp [ha, hab]
  rw [esymA_insert p _ a ha', esymA_insert p _ b hb', esymA_insert p _ b hb']
  ring

lemma esymA_one {S : Type*} (p : S → ℝ) (s : Finset S) (a b : S) (ha : a ∉ s) (hb : b ∉ s)
    (hab : a ≠ b) :
    esymA p (insert a (insert b s)) 1 = esymA p s 1 + (p a + p b) := by
  have ha' : a ∉ insert b s := by simp [ha, hab]
  rw [esymA_insert p _ a ha', esymA_insert p _ b hb]
  simp only [esymA_zero]
  ring

lemma esymA_smooth {S : Type*} [Fintype S] (p q : S → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (a b : S) (hab : a ≠ b) (hrest : ∀ i, i ≠ a → i ≠ b → p i = q i)
    (hsum : p a + p b = q a + q b) (hprod : p a * p b ≤ q a * q b) (k : ℕ) :
    esymA p Finset.univ k ≤ esymA q Finset.univ k := by
  set s : Finset S := (Finset.univ.erase b).erase a with hs
  have hu : (Finset.univ : Finset S) = insert a (insert b s) := by
    ext i; by_cases h1 : i = a <;> by_cases h2 : i = b <;> simp [hs, h1, h2]
  have ha : a ∉ s := by simp [hs]
  have hb : b ∉ s := by simp [hs]
  have hc : ∀ j, esymA p s j = esymA q s j := fun j =>
    esymA_congr p q s (fun i hi => hrest i (by intro h; simp [hs, h] at hi)
      (by intro h; simp [hs, h] at hi)) j
  rw [hu]
  rcases k with _ | _ | k
  · simp [esymA_zero]
  · rw [esymA_one p s a b ha hb hab, esymA_one q s a b ha hb hab, hc, hsum]
  · rw [esymA_two p s a b ha hb hab, esymA_two q s a b ha hb hab, hc, hc, hc, hsum]
    have := esymA_nonneg q hq s k
    have h2 : esymA q s k = esymA p s k := (hc k).symm
    have := esymA_nonneg p hp s k
    rw [← hc]
    nlinarith [mul_le_mul_of_nonneg_right hprod this]

lemma maclaurinA {S : Type*} [Fintype S] [Nonempty S] (k : ℕ) :
    ∀ (m : ℕ) (p : S → ℝ), (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      (Finset.univ.filter (fun i : S => p i ≠ 1 / (Fintype.card S : ℝ))).card = m →
      esymA p (Finset.univ : Finset S) k ≤ esymA (fun _ : S => 1 / (Fintype.card S : ℝ)) (Finset.univ : Finset S) k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p hp hsum hm
  set c : ℝ := 1 / (Fintype.card S : ℝ) with hc
  have hn : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  by_cases hall : ∀ i, p i = c
  · have : p = fun _ => c := funext hall
    rw [this]
  push Not at hall
  obtain ⟨i0, hi0⟩ := hall
  have hsumc : ∑ i : S, c = 1 := by
    simp [hc]
  have hex_gt : ∃ a, c < p a := by
    by_contra h
    push Not at h
    have : ∑ i, p i < ∑ i : S, c := by
      apply Finset.sum_lt_sum (fun i _ => h i)
      exact ⟨i0, Finset.mem_univ _, lt_of_le_of_ne (h i0) hi0⟩
    linarith
  have hex_lt : ∃ b, p b < c := by
    by_contra h
    push Not at h
    have : ∑ i : S, c < ∑ i, p i := by
      apply Finset.sum_lt_sum (fun i _ => h i)
      obtain ⟨a, ha⟩ := hex_gt
      exact ⟨a, Finset.mem_univ _, ha⟩
    linarith
  obtain ⟨a, ha⟩ := hex_gt
  obtain ⟨b, hb⟩ := hex_lt
  have hab : a ≠ b := by rintro rfl; linarith
  set q : S → ℝ := Function.update (Function.update p a c) b (p a + p b - c) with hq
  have hqa : q a = c := by simp [hq, Function.update_of_ne hab]
  have hqb : q b = p a + p b - c := by simp [hq]
  have hqr : ∀ i, i ≠ a → i ≠ b → q i = p i := by
    intro i h1 h2; simp [hq, Function.update_of_ne h1, Function.update_of_ne h2]
  have hqnn : ∀ i, 0 ≤ q i := by
    intro i
    by_cases h1 : i = a
    · subst h1; rw [hqa]; positivity
    by_cases h2 : i = b
    · subst h2; rw [hqb]; linarith [hp i, hp a]
    rw [hqr i h1 h2]; exact hp i
  have hqsum : ∑ i, q i = 1 := by
    rw [← hsum]
    have e : ∀ r : S → ℝ, ∑ i, r i = r a + r b + ∑ i ∈ (Finset.univ.erase a).erase b, r i := by
      intro r
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase (Finset.univ.erase a) _
        (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩)]
      ring
    rw [e q, e p, hqa, hqb]
    have : ∑ i ∈ (Finset.univ.erase a).erase b, q i = ∑ i ∈ (Finset.univ.erase a).erase b, p i :=
      Finset.sum_congr rfl fun i hi => hqr i (by simp at hi; exact hi.2) (by simp at hi; exact hi.1)
    rw [this]; ring
  have hlt : (Finset.univ.filter (fun i : S => q i ≠ c)).card < m := by
    rw [← hm]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨a, ?_, ?_⟩
      · simp [ha.ne']
      · simp [hqa]
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_cases h1 : i = a
      · subst h1; exact ha.ne'
      by_cases h2 : i = b
      · subst h2; exact hb.ne
      rwa [hqr i h1 h2] at hi
  have := ih _ hlt q hqnn hqsum rfl
  refine le_trans (esymA_smooth p q hp hqnn a b hab (fun i h1 h2 => (hqr i h1 h2).symm) ?_ ?_ k) this
  · rw [hqa, hqb]; ring
  · rw [hqa, hqb]; nlinarith

noncomputable def injSum {S : Type*} [Fintype S] (w : S → ℝ) (L : ℕ) : ℝ :=
  ∑ x : Fin L → S, if Function.Injective x then ∏ i, w (x i) else 0

lemma card_inj_fiber {S : Type*} [Fintype S] (L : ℕ) (T : Finset S) (hT : T.card = L) :
    ((Finset.univ.filter (fun x : Fin L → S => Function.Injective x)).filter
      (fun x => Finset.univ.image x = T)).card = L.factorial := by
  have h1 : ((Finset.univ.filter (fun x : Fin L → S => Function.Injective x)).filter
      (fun x => Finset.univ.image x = T)) =
      Finset.univ.filter (fun x : Fin L → S => Function.Injective x ∧ ∀ i, x i ∈ T) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, h2⟩
      refine ⟨h, fun i => ?_⟩
      rw [← h2]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    · rintro ⟨h, h2⟩
      refine ⟨h, ?_⟩
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 ha
        exact h2 i
      · rw [Finset.card_image_of_injective _ h, hT]; simp
  rw [h1, ← Fintype.card_subtype]
  have e : {x : Fin L → S // Function.Injective x ∧ ∀ i, x i ∈ T} ≃ (Fin L ↪ T) :=
    { toFun := fun x => ⟨fun i => ⟨x.1 i, x.2.2 i⟩, fun i j hij => x.2.1 (by simpa using hij)⟩
      invFun := fun e => ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij),
        fun i => (e i).2⟩
      left_inv := fun x => rfl
      right_inv := fun e => rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq]
  simp [hT]
  exact Nat.descFactorial_self L

lemma injSum_eq {S : Type*} [Fintype S] (w : S → ℝ) (L : ℕ) :
    injSum w L = (L.factorial : ℝ) * esymA w Finset.univ L := by
  unfold injSum esymA
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise_of_maps_to
    (g := fun x : Fin L → S => Finset.univ.image x) (t := Finset.powersetCard L Finset.univ)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    have hTc : T.card = L := (Finset.mem_powersetCard.1 hT).2
    have : ∀ x ∈ (Finset.univ.filter (fun x : Fin L → S => Function.Injective x)).filter
        (fun x => Finset.univ.image x = T), ∏ i, w (x i) = ∏ a ∈ T, w a := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [← hx.2, Finset.prod_image (fun i _ j _ h => hx.1 h)]
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_inj_fiber L T hTc]
    simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ hx]; simp

lemma sum_all {S : Type*} [Fintype S] (w : S → ℝ) (L : ℕ) :
    ∑ x : Fin L → S, ∏ i, w (x i) = (∑ a, w a) ^ L := by
  have := Finset.prod_univ_sum (fun _ : Fin L => (Finset.univ : Finset S)) (fun _ a => w a)
  simp only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

lemma noninj_eq {S : Type*} [Fintype S] (w : S → ℝ) (L : ℕ) :
    (∑ x : Fin L → S, if ¬ Function.Injective x then ∏ i, w (x i) else 0) =
      (∑ a, w a) ^ L - injSum w L := by
  rw [← sum_all, injSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : Function.Injective x <;> simp [h]

lemma prod_eq_desc {S : Type*} [Fintype S] [Nonempty S] (L : ℕ) :
    ∏ j ∈ Finset.Icc 1 (L - 1), (1 - (j : ℝ) / Fintype.card S) =
      ((Fintype.card S).descFactorial L : ℝ) / (Fintype.card S : ℝ) ^ L := by
  set n := Fintype.card S with hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have key : ∀ m : ℕ, ∏ j ∈ Finset.range m, (1 - (j : ℝ) / n) =
      (n.descFactorial m : ℝ) / (n : ℝ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
      by_cases hm : m ≤ n
      · rw [Nat.cast_mul, Nat.cast_sub hm]
        field_simp
        ring
      · have : n.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
        simp [this]
  rcases L with _ | L
  · simp
  · rw [← key, show Finset.Icc 1 (L + 1 - 1) = Finset.Ico 1 (L+1) by ext; simp,
      Finset.prod_Ico_eq_prod_range, Finset.prod_range_succ']
    simp [add_comm]

lemma injSum_unif {S : Type*} [Fintype S] [Nonempty S] (L : ℕ) :
    injSum (fun _ : S => 1 / (Fintype.card S : ℝ)) L =
      ((Fintype.card S).descFactorial L : ℝ) / (Fintype.card S : ℝ) ^ L := by
  unfold injSum
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have : (Finset.univ.filter (fun x : Fin L → S => Function.Injective x)).card =
      (Fintype.card S).descFactorial L := by
    rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin L) S),
      Fintype.card_embedding_eq]
    simp
  rw [this, div_pow, one_pow]
  field_simp

theorem solution {S : Type*} [Fintype S] (D : PMF S) (L : ℕ) :
    (∑ x : Fin L → S, if ¬ Function.Injective x then ((1 : ℝ) / Fintype.card S) ^ L else 0) ≤
      (∑ x : Fin L → S, if ¬ Function.Injective x then ∏ i, (D (x i)).toReal else 0) ∧
    (∑ x : Fin L → S, if ¬ Function.Injective x then ((1 : ℝ) / Fintype.card S) ^ L else 0) =
      1 - ∏ j ∈ Finset.Icc 1 (L - 1), (1 - (j : ℝ) / Fintype.card S) := by
  haveI : Nonempty S := ⟨(D.support_nonempty).some⟩
  set c : ℝ := 1 / (Fintype.card S : ℝ) with hc
  have hn : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hcs : ∑ _a : S, c = 1 := by simp [hc]
  have hU : (∑ x : Fin L → S, if ¬ Function.Injective x then c ^ L else 0) =
      (∑ a : S, c) ^ L - injSum (fun _ : S => c) L := by
    rw [← noninj_eq]
    apply Finset.sum_congr rfl
    intro x _
    simp [Finset.prod_const]
  rw [hU, hcs, injSum_unif, ← prod_eq_desc]
  refine ⟨?_, by simp⟩
  have hDs : ∑ a, (D a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top D a)]
    have := D.tsum_coe
    rw [tsum_fintype] at this
    rw [this]; simp
  have hle : injSum (fun a => (D a).toReal) L ≤ injSum (fun _ : S => c) L := by
    rw [injSum_eq, injSum_eq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact maclaurinA L _ _ (fun a => ENNReal.toReal_nonneg) hDs rfl
  have hu : injSum (fun _ : S => c) L = ∏ j ∈ Finset.Icc 1 (L - 1), (1 - (j : ℝ) / Fintype.card S) :=
    (injSum_unif L).trans (prod_eq_desc L).symm
  rw [noninj_eq (fun a => (D a).toReal), hDs]
  simp only [one_pow]
  linarith
