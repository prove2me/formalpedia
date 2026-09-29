-- Prove2me | solution 1 for SetCoverThreshold.SetCover.prop_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:01:49.256265+00:00
-- url     : https://prove2.me/submissions/c0b5ed62-e59a-4b9b-9d86-3e5bb055b8e7

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

namespace SetCoverThreshold.SetCover

open Formula5

theorem aux_p43_3M (φ : Formula5) : 3 * φ.M = 5 * φ.n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin φ.M × Fin 3)))
    (t := (Finset.univ : Finset (Fin φ.n))) (f := fun cp => (φ.clause cp.1 cp.2).2) (by simp)
  have h2 : ∑ v : Fin φ.n, (Finset.univ.filter
      (fun cp : Fin φ.M × Fin 3 => (φ.clause cp.1 cp.2).2 = v)).card = ∑ _v : Fin φ.n, 5 :=
    Finset.sum_congr rfl (fun v _ => φ.five v)
  rw [h2] at h
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Finset.sum_const,
    smul_eq_mul] at h
  linarith

theorem aux_p43_count (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (i : Fin k)
    (q : Fin ℓ → φ.QCoord) (hq : ∀ j, (q j).isLeft = code i j) :
    (Finset.univ.filter (fun r : φ.RandomString ℓ => φ.question code r i = q)).card =
      3 ^ (Finset.univ.filter (fun j => code i j = true)).card *
        5 ^ (Finset.univ.filter (fun j => ¬ code i j = true)).card := by
  classical
  have hS : Finset.univ.filter (fun r : φ.RandomString ℓ => φ.question code r i = q) =
      Fintype.piFinset (fun j => Finset.univ.filter (fun cp : Fin φ.M × Fin 3 =>
        (if code i j then Sum.inl cp.1 else Sum.inr (φ.var cp.1 cp.2)) = q j)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j; rw [← h]; rfl
    · intro h; funext j; exact h j
  rw [hS, Fintype.card_piFinset]
  have hj : ∀ j, (Finset.univ.filter (fun cp : Fin φ.M × Fin 3 =>
        (if code i j then Sum.inl cp.1 else Sum.inr (φ.var cp.1 cp.2)) = q j)).card =
        if code i j = true then 3 else 5 := by
    intro j
    have h := hq j
    cases hc : code i j
    · rw [hc] at h
      obtain ⟨v, hv⟩ : ∃ v, q j = Sum.inr v := by
        cases h' : q j with
        | inl c => rw [h'] at h; simp at h
        | inr v => exact ⟨v, rfl⟩
      simp only [hv, Bool.false_eq_true, if_false, Sum.inr.injEq]
      exact φ.five v
    · rw [hc] at h
      obtain ⟨c, hcq⟩ : ∃ c, q j = Sum.inl c := by
        cases h' : q j with
        | inl c => exact ⟨c, rfl⟩
        | inr v => rw [h'] at h; simp at h
      simp only [hcq, if_true, Sum.inl.injEq]
      rw [show (Finset.univ.filter (fun cp : Fin φ.M × Fin 3 => cp.1 = c)) =
        ({c} : Finset (Fin φ.M)) ×ˢ (Finset.univ : Finset (Fin 3)) by
          ext ⟨c', p'⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
            Finset.mem_singleton, and_true]]
      simp
  rw [Finset.prod_congr rfl (fun j _ => hj j), Finset.prod_ite]
  simp

theorem aux_p43_countQ (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (i : Fin k)
    (q : Fin ℓ → φ.QCoord) (hq : ∀ j, (q j).isLeft = code i j) :
    (Finset.univ.filter (fun r : φ.RandomString ℓ => φ.question code r i = q)).card *
        φ.numQuestions ℓ = Fintype.card (φ.RandomString ℓ) := by
  classical
  rw [aux_p43_count φ code i q hq]
  have h1 := hcode.1 i
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => code i j = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  have ht' : (Finset.univ.filter (fun j => ¬ code i j = true)).card =
      (Finset.univ.filter (fun j => code i j = true)).card := by omega
  rw [ht']
  generalize (Finset.univ.filter (fun j => code i j = true)).card = t at h1 h2 ⊢
  have hl2 : ℓ / 2 = t := by omega
  have h3 := aux_p43_3M φ
  simp only [numQuestions, hl2, Fintype.card_pi, Fintype.card_prod, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ]
  rw [← h1, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
  congr 1
  have e : 3 * 5 * (φ.n * φ.M) = 3 * φ.M * (5 * φ.n) := by ring
  rw [e, ← h3]
  ring

theorem aux_p43_sumw (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (𝒞 : Finset (φ.SetIdx code)) :
    (∑ r, φ.weight code 𝒞 r) * φ.numQuestions ℓ = 𝒞.card * Fintype.card (φ.RandomString ℓ) := by
  classical
  have : ∑ r, φ.weight code 𝒞 r = ∑ x ∈ 𝒞, (Finset.univ.filter
      (fun r : φ.RandomString ℓ => φ.question code r x.1 = x.2.1.1)).card := by
    simp only [weight, Finset.card_filter]
    exact Finset.sum_comm
  rw [this, Finset.sum_mul,
    Finset.sum_congr rfl (fun x _ => aux_p43_countQ φ code hcode x.1 x.2.1.1 x.2.1.2)]
  simp

theorem aux_p43_collide (φ : Formula5) {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d)
    (𝒞 : Finset (φ.SetIdx code)) (hcov : φ.IsSCCover code P 𝒞)
    (r : φ.RandomString ℓ) (hw : φ.weight code 𝒞 r < d) :
    ∃ x ∈ 𝒞, ∃ y ∈ 𝒞, x.1 ≠ y.1 ∧ φ.question code r x.1 = x.2.1.1 ∧
      φ.question code r y.1 = y.2.1.1 ∧
      φ.inducedAssignment code r x.1 x.2.2.1 = φ.inducedAssignment code r y.1 y.2.2.1 := by
  classical
  by_contra hcon
  push Not at hcon
  let F : Finset (Fin (2 ^ ℓ) × Fin k) :=
    (𝒞.filter (fun x => φ.question code r x.1 = x.2.1.1)).image
      (fun x => (labelEquiv ℓ (φ.inducedAssignment code r x.1 x.2.2.1), x.1))
  have h1 : ∀ u ∈ F, ∀ v ∈ F, u.1 = v.1 → u = v := by
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    rw [Finset.mem_filter] at hx hy
    have hind := (labelEquiv ℓ).injective huv
    by_cases hxy : x.1 = y.1
    · exact Prod.ext huv hxy
    · exact absurd hind (hcon x hx.1 y hy.1 hxy hx.2 hy.2)
  have h2 : ∀ b : Fin m, ∃ u ∈ F, (P r).part b u.1 = u.2 := by
    intro b
    obtain ⟨x, hx, hmem⟩ := hcov (r, b)
    simp only [scSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hx, hmem.1⟩), hmem.2⟩
  have h3 := (P r).cover_bound F h1 h2
  have h4 : F.card ≤ φ.weight code 𝒞 r := Finset.card_image_le
  omega

/-- A canonical default answer. -/
def aux_p43_dflt (φ : Formula5) {ℓ : ℕ} (q : Fin ℓ → φ.QCoord) : Fin ℓ → Fin 3 → Bool :=
  fun j => match q j with
    | Sum.inl c => fun p => (φ.clause c p).1
    | Sum.inr _ => fun _ => false

theorem aux_p43_dflt_spec (φ : Formula5) {ℓ : ℕ} (q : Fin ℓ → φ.QCoord) :
    ∀ j, φ.CoordCanonical (q j) (aux_p43_dflt φ q j) := by
  intro j
  unfold aux_p43_dflt
  cases q j with
  | inl c => exact ⟨0, rfl⟩
  | inr v => exact ⟨rfl, rfl⟩

/-- The strategy induced by a selector. -/
def aux_p43_strat (φ : Formula5) {ℓ k : ℕ}
    (σ : Fin k × (Fin ℓ → φ.QCoord) → Fin ℓ → Fin 3 → Bool) : φ.KStrategy ℓ k :=
  fun i q => (⟨if ∀ j, φ.CoordCanonical (q j) (σ (i, q) j) then σ (i, q) else aux_p43_dflt φ q,
    by
      split_ifs with h
      · exact h
      · exact aux_p43_dflt_spec φ q⟩ :
      { a : Fin ℓ → Fin 3 → Bool // ∀ j, φ.CoordCanonical (q j) (a j) })

theorem aux_p43_strat_val (φ : Formula5) {ℓ k : ℕ}
    (σ : Fin k × (Fin ℓ → φ.QCoord) → Fin ℓ → Fin 3 → Bool) (i : Fin k) (q : Fin ℓ → φ.QCoord)
    (h : ∀ j, φ.CoordCanonical (q j) (σ (i, q) j)) :
    (aux_p43_strat φ σ i q).1 = σ (i, q) := by
  show (if ∀ j, φ.CoordCanonical (q j) (σ (i, q) j) then σ (i, q) else aux_p43_dflt φ q) = σ (i, q)
  rw [if_pos h]

/-- Raw answers present in the cover for a prover/question pair. -/
def aux_p43_T (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (𝒞 : Finset (φ.SetIdx code)) (iq : Fin k × (Fin ℓ → φ.QCoord)) :
    Finset (Fin ℓ → Fin 3 → Bool) :=
  (𝒞.filter (fun x => x.1 = iq.1 ∧ x.2.1.1 = iq.2)).image (fun x => x.2.2.1)

def aux_p43_T' (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (𝒞 : Finset (φ.SetIdx code)) (iq : Fin k × (Fin ℓ → φ.QCoord)) :
    Finset (Fin ℓ → Fin 3 → Bool) :=
  if (aux_p43_T φ code 𝒞 iq).Nonempty then aux_p43_T φ code 𝒞 iq else {aux_p43_dflt φ iq.2}

theorem aux_p43_T'_nonempty (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool)
    (𝒞 : Finset (φ.SetIdx code)) (iq : Fin k × (Fin ℓ → φ.QCoord)) :
    (aux_p43_T' φ code 𝒞 iq).Nonempty := by
  unfold aux_p43_T'
  split_ifs with h
  · exact h
  · exact Finset.singleton_nonempty _

theorem aux_p43_pi1 {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (T : ι → Finset β) (p : ι) (a : β) :
    (Fintype.piFinset T).card = (T p).card * (Fintype.piFinset (Function.update T p {a})).card := by
  rw [Fintype.card_piFinset, Fintype.card_piFinset]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (T j).card) (Finset.mem_univ p)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (Function.update T p {a} j).card)
    (Finset.mem_univ p)]
  simp only [Function.update_self, Finset.card_singleton, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem aux_p43_pi2 {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (T : ι → Finset β) (p₁ p₂ : ι) (hp : p₁ ≠ p₂) (a b : β) (ha : a ∈ T p₁) (hb : b ∈ T p₂) :
    (Fintype.piFinset T).card ≤ (T p₁).card * (T p₂).card *
      ((Fintype.piFinset T).filter (fun σ => σ p₁ = a ∧ σ p₂ = b)).card := by
  have e1 := aux_p43_pi1 T p₁ a
  have e2 := aux_p43_pi1 (Function.update T p₁ {a}) p₂ b
  rw [Function.update_of_ne hp.symm] at e2
  rw [e1, e2, mul_assoc]
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro σ hσ
  rw [Fintype.mem_piFinset] at hσ
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun j => ?_, ?_, ?_⟩
  · have := hσ j
    by_cases h2 : j = p₂
    · subst h2
      simp only [Function.update_self, Finset.mem_singleton] at this
      rw [this]; exact hb
    · by_cases h1 : j = p₁
      · subst h1
        simp only [Function.update_of_ne h2, Function.update_self, Finset.mem_singleton] at this
        rw [this]; exact ha
      · simpa only [Function.update_of_ne h1, Function.update_of_ne h2] using this
  · have := hσ p₁
    simpa only [Function.update_of_ne hp, Function.update_self, Finset.mem_singleton] using this
  · have := hσ p₂
    simpa only [Function.update_self, Finset.mem_singleton] using this

theorem aux_p43_main (φ : Formula5) (ℓ k m d : ℕ) (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d)
    (δ : ℝ) (hδ : 0 < δ) (hd : (1 - δ / 2) * k * Real.log m ≤ d)
    (𝒞 : Finset (φ.SetIdx code)) (hcov : φ.IsSCCover code P 𝒞)
    (h𝒞 : (𝒞.card : ℝ) ≤ (1 - δ) * k * φ.numQuestions ℓ * Real.log m) :
    ∃ A : φ.KStrategy ℓ k, 2 * δ / (k * Real.log m) ^ 2 ≤ φ.weakAcceptFrac code A := by
  classical
  have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hK0 : 0 ≤ (k : ℝ) * Real.log m := mul_nonneg (Nat.cast_nonneg _) hlog
  rcases hK0.eq_or_lt with hK | hK
  · refine ⟨aux_p43_strat φ (fun iq => aux_p43_dflt φ iq.2), ?_⟩
    rw [← hK]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
    unfold weakAcceptFrac
    positivity
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (k : ℝ) * Real.log m := ⟨_, rfl⟩
  rw [← hKdef] at hK ⊢
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = Fintype.card (φ.RandomString ℓ) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = φ.numQuestions ℓ := ⟨_, rfl⟩
  have hRpos : 0 < R := by
    rw [hRdef]; exact Fintype.card_pos_iff.2 ⟨fun _ => (⟨0, φ.M_pos⟩, 0)⟩
  have hn : 0 < φ.n := by have := aux_p43_3M φ; have := φ.M_pos; omega
  have hQpos : 0 < Q := by
    rw [hQdef]; unfold numQuestions; have := φ.M_pos; positivity
  have hsumw : ((∑ r, φ.weight code 𝒞 r : ℕ) : ℝ) * Q = 𝒞.card * R := by
    rw [hQdef, hRdef]; exact_mod_cast aux_p43_sumw φ code hcode 𝒞
  have hC : (𝒞.card : ℝ) ≤ (1 - δ) * K * Q := by
    rw [hKdef, hQdef]; linarith [h𝒞]
  -- Markov
  obtain ⟨G, hG⟩ : ∃ G : Finset (φ.RandomString ℓ), G = Finset.univ.filter
      (fun r => (φ.weight code 𝒞 r : ℝ) < (1 - δ / 2) * K) := ⟨_, rfl⟩
  have hGcard : (δ / 2) * R ≤ G.card := by
    obtain ⟨B, hB⟩ : ∃ B : Finset (φ.RandomString ℓ), B = Finset.univ.filter
      (fun r => ¬ ((φ.weight code 𝒞 r : ℝ) < (1 - δ / 2) * K)) := ⟨_, rfl⟩
    have h1 : ((∑ r, φ.weight code 𝒞 r : ℕ) : ℝ) =
        ∑ r ∈ G, (φ.weight code 𝒞 r : ℝ) + ∑ r ∈ B, (φ.weight code 𝒞 r : ℝ) := by
      rw [hG, hB]; push_cast; rw [Finset.sum_filter_add_sum_filter_not]
    have h2 : 0 ≤ ∑ r ∈ G, (φ.weight code 𝒞 r : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have h3 : (B.card : ℝ) * ((1 - δ / 2) * K) ≤ ∑ r ∈ B, (φ.weight code 𝒞 r : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro r hr
      rw [hB, Finset.mem_filter] at hr
      exact not_lt.1 hr.2
    have h4 : (G.card : ℝ) + B.card = R := by
      rw [hG, hB, hRdef]
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := Finset.univ) _
    have h5 : ((∑ r, φ.weight code 𝒞 r : ℕ) : ℝ) ≤ (1 - δ) * K * R := by
      have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQpos
      have hR' : (0 : ℝ) ≤ R := by positivity
      have : ((∑ r, φ.weight code 𝒞 r : ℕ) : ℝ) * Q ≤ (1 - δ) * K * R * Q := by
        rw [hsumw]; nlinarith
      exact le_of_mul_le_mul_right this hQ'
    have h6 : (B.card : ℝ) * (1 - δ / 2) * K ≤ (1 - δ) * R * K := by nlinarith
    have h7 : (B.card : ℝ) * (1 - δ / 2) ≤ (1 - δ) * R := le_of_mul_le_mul_right h6 hK
    have hB' : (B.card : ℝ) = R - G.card := by linarith
    rw [hB'] at h7
    have hGδ : 0 ≤ (G.card : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    nlinarith
  -- selectors
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Finset (Fin k × (Fin ℓ → φ.QCoord) → Fin ℓ → Fin 3 → Bool),
      Ω = Fintype.piFinset (aux_p43_T' φ code 𝒞) := ⟨_, rfl⟩
  have hΩne : Ω.Nonempty := by
    rw [hΩ, Fintype.piFinset_nonempty]; exact fun iq => aux_p43_T'_nonempty φ code 𝒞 iq
  have hr' : ∀ r ∈ G, 4 * (Ω.card : ℝ) ≤
      (Ω.filter (fun σ => φ.WeakAccept code (aux_p43_strat φ σ) r)).card * K ^ 2 := by
    intro r hrG
    rw [hG, Finset.mem_filter] at hrG
    have hwr : (φ.weight code 𝒞 r : ℝ) < (1 - δ / 2) * K := hrG.2
    have hwd : φ.weight code 𝒞 r < d := by
      have : (φ.weight code 𝒞 r : ℝ) < d := lt_of_lt_of_le hwr (by rw [hKdef]; linarith [hd])
      exact_mod_cast this
    obtain ⟨x, hx, y, hy, hne, hxq, hyq, heq⟩ := aux_p43_collide φ code P 𝒞 hcov r hwd
    have hp : ((x.1, φ.question code r x.1) : Fin k × (Fin ℓ → φ.QCoord)) ≠
        (y.1, φ.question code r y.1) := fun h => hne (congrArg Prod.fst h)
    have hxT : x.2.2.1 ∈ aux_p43_T φ code 𝒞 (x.1, φ.question code r x.1) :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hx, rfl, hxq.symm⟩)
    have hyT : y.2.2.1 ∈ aux_p43_T φ code 𝒞 (y.1, φ.question code r y.1) :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hy, rfl, hyq.symm⟩)
    have hT1 : aux_p43_T' φ code 𝒞 (x.1, φ.question code r x.1) =
        aux_p43_T φ code 𝒞 (x.1, φ.question code r x.1) := by
      unfold aux_p43_T'; rw [if_pos ⟨_, hxT⟩]
    have hT2 : aux_p43_T' φ code 𝒞 (y.1, φ.question code r y.1) =
        aux_p43_T φ code 𝒞 (y.1, φ.question code r y.1) := by
      unfold aux_p43_T'; rw [if_pos ⟨_, hyT⟩]
    have hpi := aux_p43_pi2 (aux_p43_T' φ code 𝒞) _ _ hp x.2.2.1 y.2.2.1
      (hT1 ▸ hxT) (hT2 ▸ hyT)
    rw [hT1, hT2, ← hΩ] at hpi
    have hmono : (Ω.filter (fun σ => σ (x.1, φ.question code r x.1) = x.2.2.1 ∧
        σ (y.1, φ.question code r y.1) = y.2.2.1)).card ≤
        (Ω.filter (fun σ => φ.WeakAccept code (aux_p43_strat φ σ) r)).card := by
      apply Finset.card_le_card
      intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      obtain ⟨hσΩ, hσ1, hσ2⟩ := hσ
      refine ⟨hσΩ, x.1, y.1, hne, ?_⟩
      have c1 : ∀ j, φ.CoordCanonical (φ.question code r x.1 j)
          (σ (x.1, φ.question code r x.1) j) := by
        intro j; rw [hσ1, hxq]; exact x.2.2.2 j
      have c2 : ∀ j, φ.CoordCanonical (φ.question code r y.1 j)
          (σ (y.1, φ.question code r y.1) j) := by
        intro j; rw [hσ2, hyq]; exact y.2.2.2 j
      unfold Consistent
      rw [aux_p43_strat_val φ σ x.1 _ c1, aux_p43_strat_val φ σ y.1 _ c2, hσ1, hσ2]
      exact heq
    have hcardT : (aux_p43_T φ code 𝒞 (x.1, φ.question code r x.1)).card +
        (aux_p43_T φ code 𝒞 (y.1, φ.question code r y.1)).card ≤ φ.weight code 𝒞 r := by
      have hdisj : Disjoint (𝒞.filter (fun z => z.1 = x.1 ∧ z.2.1.1 = φ.question code r x.1))
          (𝒞.filter (fun z => z.1 = y.1 ∧ z.2.1.1 = φ.question code r y.1)) := by
        rw [Finset.disjoint_filter]; intro z _ h1 h2; exact hne (h1.1.symm.trans h2.1)
      have hsub : (𝒞.filter (fun z => z.1 = x.1 ∧ z.2.1.1 = φ.question code r x.1)) ∪
          (𝒞.filter (fun z => z.1 = y.1 ∧ z.2.1.1 = φ.question code r y.1)) ⊆
          𝒞.filter (fun z => φ.question code r z.1 = z.2.1.1) := by
        intro z hz
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hz
        rw [Finset.mem_filter]
        rcases hz with ⟨hz, h1, h2⟩ | ⟨hz, h1, h2⟩
        · exact ⟨hz, by rw [h2, h1]⟩
        · exact ⟨hz, by rw [h2, h1]⟩
      calc _ ≤ (𝒞.filter (fun z => z.1 = x.1 ∧ z.2.1.1 = φ.question code r x.1)).card +
            (𝒞.filter (fun z => z.1 = y.1 ∧ z.2.1.1 = φ.question code r y.1)).card :=
            Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ = ((𝒞.filter (fun z => z.1 = x.1 ∧ z.2.1.1 = φ.question code r x.1)) ∪
            (𝒞.filter (fun z => z.1 = y.1 ∧ z.2.1.1 = φ.question code r y.1))).card :=
            (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ _ := Finset.card_le_card hsub
    generalize (aux_p43_T φ code 𝒞 (x.1, φ.question code r x.1)).card = t₁ at hpi hcardT
    generalize (aux_p43_T φ code 𝒞 (y.1, φ.question code r y.1)).card = t₂ at hpi hcardT
    generalize (Ω.filter (fun σ => φ.WeakAccept code (aux_p43_strat φ σ) r)).card = c at hmono ⊢
    have e1 : (Ω.card : ℝ) ≤ t₁ * t₂ * c := by
      exact_mod_cast hpi.trans (Nat.mul_le_mul_left _ hmono)
    have e2 : (t₁ : ℝ) + t₂ ≤ φ.weight code 𝒞 r := by exact_mod_cast hcardT
    have e3 : (φ.weight code 𝒞 r : ℝ) ≤ K := by nlinarith
    have ht1 : (0 : ℝ) ≤ t₁ := Nat.cast_nonneg _
    have ht2 : (0 : ℝ) ≤ t₂ := Nat.cast_nonneg _
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    have e4 : 4 * ((t₁ : ℝ) * t₂) ≤ K ^ 2 := by
      nlinarith [sq_nonneg ((t₁ : ℝ) - t₂),
        mul_nonneg (sub_nonneg.2 (e2.trans e3)) (by positivity : (0 : ℝ) ≤ K + t₁ + t₂)]
    nlinarith [mul_le_mul_of_nonneg_right e4 hc0]
  have hswap : ∑ σ ∈ Ω, (Finset.univ.filter
      (fun r => φ.WeakAccept code (aux_p43_strat φ σ) r)).card =
      ∑ r, (Ω.filter (fun σ => φ.WeakAccept code (aux_p43_strat φ σ) r)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hsum : ∑ σ ∈ Ω, 2 * δ * R / K ^ 2 ≤ ∑ σ ∈ Ω, ((Finset.univ.filter
      (fun r => φ.WeakAccept code (aux_p43_strat φ σ) r)).card : ℝ) := by
    rw [← Nat.cast_sum, hswap, Nat.cast_sum, Finset.sum_const, nsmul_eq_mul]
    have hK2 : 0 < K ^ 2 := by positivity
    calc (Ω.card : ℝ) * (2 * δ * R / K ^ 2) = ((δ / 2) * R) * (4 * Ω.card / K ^ 2) := by
          field_simp; ring
      _ ≤ G.card * (4 * Ω.card / K ^ 2) := by gcongr
      _ = ∑ r ∈ G, (4 * Ω.card / K ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ G, ((Ω.filter (fun σ => φ.WeakAccept code (aux_p43_strat φ σ) r)).card : ℝ) :=
          Finset.sum_le_sum (fun r hr => by rw [div_le_iff₀ hK2]; linarith [hr' r hr])
      _ ≤ ∑ r, ((Ω.filter (fun σ => φ.WeakAccept code (aux_p43_strat φ σ) r)).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.cast_nonneg _)
  obtain ⟨σ, -, hle⟩ := Finset.exists_le_of_sum_le hΩne hsum
  refine ⟨aux_p43_strat φ σ, ?_⟩
  unfold weakAcceptFrac
  rw [← hRdef, le_div_iff₀ (by exact_mod_cast hRpos)]
  calc 2 * δ / K ^ 2 * R = 2 * δ * R / K ^ 2 := by ring
    _ ≤ _ := hle

end SetCoverThreshold.SetCover

open SetCoverThreshold.SetCover

theorem solution (φ : Formula5) (ℓ k m d : ℕ) (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d)
    (δ : ℝ) (hδ : 0 < δ) (hd : (1 - δ / 2) * k * Real.log m ≤ d)
    (𝒞 : Finset (φ.SetIdx code)) (hcov : φ.IsSCCover code P 𝒞)
    (h𝒞 : (𝒞.card : ℝ) ≤ (1 - δ) * k * φ.numQuestions ℓ * Real.log m) :
    ∃ A : φ.KStrategy ℓ k, 2 * δ / (k * Real.log m) ^ 2 ≤ φ.weakAcceptFrac code A :=
  aux_p43_main φ ℓ k m d code hcode P δ hδ hd 𝒞 hcov h𝒞
