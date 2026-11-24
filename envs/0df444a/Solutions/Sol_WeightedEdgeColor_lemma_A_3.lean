-- Prove2me | solution 1 for WeightedEdgeColor.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:41:11.271723+00:00
-- url     : https://prove2.me/submissions/1b41cdfe-0e20-4f74-bfbb-76fb58f7e540

import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace WECLemmaA3

variable {J Q : Type} [Fintype J] {O : J → Type} [∀ j, Fintype (O j)]

/-- load -/
noncomputable def L (a : (Σ j, O j) → Q → ℝ) (x : (Σ j, O j) → ℝ) (q : Q) : ℝ :=
  ∑ k, a k q * x k

/-- upper bound on the final load: all options still alive used fully -/
noncomputable def U (a : (Σ j, O j) → Q → ℝ) (x : (Σ j, O j) → ℝ) (q : Q) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => 0 < x k), a k q

/-- fractional coordinates -/
noncomputable def Fr (x : (Σ j, O j) → ℝ) : Finset (Σ j, O j) :=
  Finset.univ.filter (fun k => 0 < x k ∧ x k < 1)

structure Good (a : (Σ j, O j) → Q → ℝ) (b : Q → ℝ) (τ : ℝ) (x : (Σ j, O j) → ℝ) : Prop where
  bnd : ∀ k, 0 ≤ x k ∧ x k ≤ 1
  job : ∀ j, ∑ o, x ⟨j, o⟩ = 1
  cons : ∀ q, L a x q ≤ b q ∨ U a x q ≤ b q + 2 * τ

theorem sum_fiber (f : (Σ j, O j) → ℝ) (j : J) :
    ∑ k ∈ Finset.univ.filter (fun k : (Σ j, O j) => k.1 = j), f k = ∑ o, f ⟨j, o⟩ := by
  rw [Finset.sum_filter, Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'; simp [hj']
  · simp

theorem L_le_U (a : (Σ j, O j) → Q → ℝ) (x : (Σ j, O j) → ℝ) (ha : ∀ k q, 0 ≤ a k q)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) (q : Q) : L a x q ≤ U a x q := by
  unfold L U
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with h
  · have := ha k q; nlinarith [hx k]
  · have : x k = 0 := le_antisymm (not_lt.mp h) (hx k).1
    simp [this]

/-- base case: integral point -/
theorem base (a : (Σ j, O j) → Q → ℝ) (b : Q → ℝ) (τ : ℝ) (x : (Σ j, O j) → ℝ)
    (ha : ∀ k q, 0 ≤ a k q) (hτ : 0 ≤ τ) (_hb : ∀ q, 0 ≤ b q)
    (hg : Good a b τ x) (h0 : Fr x = ∅) :
    ∃ σ : ∀ j, O j, ∀ q, ∑ j, a ⟨j, σ j⟩ q ≤ b q + 2 * τ := by
  have h01 : ∀ k, x k = 0 ∨ x k = 1 := by
    intro k
    have hk : k ∉ Fr x := by rw [h0]; simp
    simp only [Fr, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hk
    rcases (hg.bnd k).1.eq_or_lt with h | h
    · left; exact h.symm
    · right; exact le_antisymm (hg.bnd k).2 (hk h)
  have hex : ∀ j, ∃ o, x ⟨j, o⟩ = 1 := by
    intro j
    by_contra hne
    push Not at hne
    have : ∑ o, x ⟨j, o⟩ = 0 := by
      apply Finset.sum_eq_zero
      intro o _
      rcases h01 ⟨j, o⟩ with h | h
      · exact h
      · exact absurd h (hne o)
    rw [hg.job j] at this; norm_num at this
  choose σ hσ using hex
  refine ⟨σ, fun q => ?_⟩
  have h1 : ∑ j, a ⟨j, σ j⟩ q ≤ L a x q := by
    unfold L
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro j _
    have : a ⟨j, σ j⟩ q = a ⟨j, σ j⟩ q * x ⟨j, σ j⟩ := by rw [hσ j, mul_one]
    rw [this]
    exact Finset.single_le_sum (f := fun o => a ⟨j, o⟩ q * x ⟨j, o⟩)
      (fun o _ => mul_nonneg (ha _ _) (hg.bnd _).1) (Finset.mem_univ (σ j))
  have h2 := L_le_U a x ha hg.bnd q
  rcases hg.cons q with h | h <;> linarith

/-- the hitting-time lemma -/
theorem hit (x d : (Σ j, O j) → ℝ) (F : Finset (Σ j, O j))
    (hF : ∀ k ∈ F, 0 < x k ∧ x k < 1) (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hd0 : ∀ k ∉ F, d k = 0) (hne : ∃ k ∈ F, d k ≠ 0) :
    ∃ t : ℝ, (∀ k, 0 ≤ x k + t * d k ∧ x k + t * d k ≤ 1) ∧
      ∃ k ∈ F, x k + t * d k = 0 ∨ x k + t * d k = 1 := by
  set D := F.filter (fun k => d k ≠ 0)
  have hD : D.Nonempty := by
    obtain ⟨k, hk, hdk⟩ := hne
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hdk⟩⟩
  let h : (Σ j, O j) → ℝ := fun k => if 0 < d k then (1 - x k) / d k else (- x k) / d k
  have hpos : ∀ k ∈ D, 0 < h k := by
    intro k hk
    obtain ⟨hkF, hdk⟩ := Finset.mem_filter.mp hk
    have hxk := hF k hkF
    simp only [h]
    split_ifs with hd
    · exact div_pos (by linarith) hd
    · have : d k < 0 := lt_of_le_of_ne (not_lt.mp hd) hdk
      exact div_pos_of_neg_of_neg (by linarith) this
  obtain ⟨k₀, hk₀, hmin⟩ := D.exists_min_image h hD
  refine ⟨h k₀, fun k => ?_, k₀, (Finset.mem_filter.mp hk₀).1, ?_⟩
  · have ht := hpos k₀ hk₀
    by_cases hkF : k ∈ F
    · by_cases hdk : d k = 0
      · simp [hdk, hx k]
      · have hkD : k ∈ D := Finset.mem_filter.mpr ⟨hkF, hdk⟩
        have hle := hmin k hkD
        simp only [h] at hle ⊢
        have hxk := hF k hkF
        rcases lt_or_gt_of_ne hdk with hneg | hpos'
        · rw [if_neg (not_lt.mpr hneg.le)] at hle
          rw [le_div_iff_of_neg hneg] at hle
          constructor
          · linarith
          · nlinarith
        · rw [if_pos hpos'] at hle
          rw [le_div_iff₀ hpos'] at hle
          constructor
          · nlinarith
          · linarith
    · rw [hd0 k hkF]; simp [hx k]
  · have hdk := (Finset.mem_filter.mp hk₀).2
    simp only [h]
    split_ifs with hd
    · right; field_simp; ring
    · left; field_simp; ring


noncomputable def ext (F : Finset (Σ j, O j)) (d : F → ℝ) (k : Σ j, O j) : ℝ :=
  if h : k ∈ F then d ⟨k, h⟩ else 0

theorem ext_add (F : Finset (Σ j, O j)) (d₁ d₂ : F → ℝ) (k : Σ j, O j) :
    ext F (d₁ + d₂) k = ext F d₁ k + ext F d₂ k := by
  unfold ext; split_ifs <;> simp

theorem ext_smul (F : Finset (Σ j, O j)) (c : ℝ) (d : F → ℝ) (k : Σ j, O j) :
    ext F (c • d) k = c * ext F d k := by
  unfold ext; split_ifs <;> simp

theorem ext_out (F : Finset (Σ j, O j)) (d : F → ℝ) (k : Σ j, O j) (hk : k ∉ F) :
    ext F d k = 0 := by
  unfold ext; rw [dif_neg hk]

/-- The constraint map whose kernel gives the move direction. -/
noncomputable def cmap (a : (Σ j, O j) → Q → ℝ) (F : Finset (Σ j, O j)) (Jf : Finset J)
    (Qa : Finset Q) : (F → ℝ) →ₗ[ℝ] ((Jf → ℝ) × (Qa → ℝ)) where
  toFun d := (fun j => ∑ o, ext F d ⟨j.1, o⟩, fun q => ∑ k, a k q.1 * ext F d k)
  map_add' d₁ d₂ := by
    ext j
    · simp [ext_add, Finset.sum_add_distrib]
    · simp [ext_add, mul_add, Finset.sum_add_distrib]
  map_smul' c d := by
    ext j
    · simp [ext_smul, Finset.mul_sum]
    · simp only [ext_smul, RingHom.id_apply, Prod.smul_mk, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring

theorem step (a : (Σ j, O j) → Q → ℝ) (b : Q → ℝ) (τ : ℝ) (x : (Σ j, O j) → ℝ)
    (ha : ∀ k q, 0 ≤ a k q ∧ a k q ≤ τ) (s : (Σ j, O j) → Finset Q)
    (hs : ∀ k, (s k).card ≤ 2 ∧ ∀ q ∉ s k, a k q = 0)
    (hτ : 0 ≤ τ) (hb : ∀ q, 0 ≤ b q)
    (hg : Good a b τ x) (hne : (Fr x).Nonempty) :
    ∃ x', Good a b τ x' ∧ (Fr x').card < (Fr x).card := by
  set F := Fr x with hFdef
  have hF : ∀ k ∈ F, 0 < x k ∧ x k < 1 := fun k hk => by
    simpa [F, Fr] using hk
  set Jf : Finset J := Finset.univ.filter (fun j => ∃ o, (⟨j, o⟩ : Σ j, O j) ∈ F)
  set Qrel : Finset Q := Finset.univ.biUnion s
  set Qa : Finset Q := Qrel.filter (fun q => ¬ U a x q ≤ b q + 2 * τ)
  -- (i) the jobs
  have hjob1 : ∀ j ∈ Jf, ∑ k ∈ F.filter (fun k => k.1 = j), x k = 1 := by
    intro j hj
    obtain ⟨o₀, ho₀⟩ := (Finset.mem_filter.mp hj).2
    have hfull : ∑ k ∈ Finset.univ.filter (fun k : (Σ j, O j) => k.1 = j), x k = 1 := by
      rw [sum_fiber]; exact hg.job j
    rw [← hfull]
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_filter] at hk ⊢; exact ⟨Finset.mem_univ _, hk.2⟩
    · intro k hk hkF
      have hk1 : k.1 = j := (Finset.mem_filter.mp hk).2
      have hkF' : k ∉ F := fun h => hkF (Finset.mem_filter.mpr ⟨h, hk1⟩)
      have hx01 : x k = 0 ∨ x k = 1 := by
        have : ¬ (0 < x k ∧ x k < 1) := fun h => hkF' (by simp [F, Fr, h])
        rcases (hg.bnd k).1.eq_or_lt with h | h
        · left; exact h.symm
        · right; exact le_antisymm (hg.bnd k).2 (not_lt.mp (fun h' => this ⟨h, h'⟩))
      rcases hx01 with h | h
      · exact h
      · exfalso
        have hne' : k ≠ ⟨j, o₀⟩ := fun h' => hkF' (h' ▸ ho₀)
        have hsub : ({k, ⟨j, o₀⟩} : Finset (Σ j, O j)) ⊆
            Finset.univ.filter (fun k : (Σ j, O j) => k.1 = j) := by
          intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl <;> simp [hk1]
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => (hg.bnd m).1)
        rw [Finset.sum_pair hne', hfull, h] at this
        have := (hF _ ho₀).1
        linarith
  have hJ : (Jf.card : ℝ) = ∑ k ∈ F, x k := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := Jf) (g := Sigma.fst)]
    · rw [Finset.sum_congr rfl hjob1]; simp
    · intro k hk
      simp only [Jf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k.2, hk⟩
  -- (ii) the active constraints
  have hS : ∀ q ∈ Qa, 2 < ∑ k ∈ F.filter (fun k => a k q ≠ 0), (1 - x k) := by
    intro q hq
    have hnot := (Finset.mem_filter.mp hq).2
    have hL : L a x q ≤ b q := (hg.cons q).resolve_right hnot
    have hUL : U a x q - L a x q ≤ τ * ∑ k ∈ F.filter (fun k => a k q ≠ 0), (1 - x k) := by
      unfold U L
      rw [show F.filter (fun k => a k q ≠ 0) = Finset.univ.filter (fun k => k ∈ F ∧ a k q ≠ 0) by
        ext; simp]
      rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro k _
      have hak := ha k q
      have hxk := hg.bnd k
      by_cases hk : k ∈ F
      · have := hF k hk
        rw [if_pos this.1]
        by_cases ha0 : a k q ≠ 0
        · rw [if_pos ⟨hk, ha0⟩]; nlinarith
        · have hnF : ¬ (k ∈ F ∧ a k q ≠ 0) := fun h => ha0 h.2
          rw [if_neg hnF]; push Not at ha0; rw [ha0]; simp
      · have hnF : ¬ (k ∈ F ∧ a k q ≠ 0) := fun h => hk h.1
        rw [if_neg hnF]
        by_cases h0 : 0 < x k
        · rw [if_pos h0]
          have : x k = 1 := by
            by_contra h1
            exact hk (by simp [F, Fr, h0, lt_of_le_of_ne hxk.2 h1])
          rw [this]; simp
        · rw [if_neg h0]
          have : x k = 0 := le_antisymm (not_lt.mp h0) hxk.1
          rw [this]; simp
    have : 2 * τ < τ * ∑ k ∈ F.filter (fun k => a k q ≠ 0), (1 - x k) := by
      push Not at hnot; linarith
    by_contra hle
    push Not at hle
    nlinarith
  have hQ : (Qa.card : ℝ) < ∑ k ∈ F, (1 - x k) := by
    have hpos : 0 < ∑ k ∈ F, (1 - x k) :=
      Finset.sum_pos (fun k hk => by linarith [(hF k hk).2]) hne
    rcases Qa.eq_empty_or_nonempty with hQe | hQne
    · rw [hQe]; simpa using hpos
    · have h1 : ∑ q ∈ Qa, (2 : ℝ) < ∑ q ∈ Qa, ∑ k ∈ F.filter (fun k => a k q ≠ 0), (1 - x k) :=
        Finset.sum_lt_sum_of_nonempty hQne hS
      have h2 : ∑ q ∈ Qa, ∑ k ∈ F.filter (fun k => a k q ≠ 0), (1 - x k)
          = ∑ k ∈ F, (1 - x k) * ((Qa.filter (fun q => a k q ≠ 0)).card : ℝ) := by
        simp_rw [Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      have h3 : ∑ k ∈ F, (1 - x k) * ((Qa.filter (fun q => a k q ≠ 0)).card : ℝ)
          ≤ ∑ k ∈ F, (1 - x k) * 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hc : (Qa.filter (fun q => a k q ≠ 0)).card ≤ 2 := by
          refine le_trans (Finset.card_le_card ?_) (hs k).1
          intro q hq
          by_contra hqs
          exact (Finset.mem_filter.mp hq).2 ((hs k).2 q hqs)
        have : ((Qa.filter (fun q => a k q ≠ 0)).card : ℝ) ≤ 2 := by exact_mod_cast hc
        have := (hF k hk).2
        nlinarith
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      rw [← Finset.sum_mul] at h3
      nlinarith
  have hcount : Jf.card + Qa.card < F.card := by
    have : (Jf.card : ℝ) + Qa.card < F.card := by
      have hsum : ∑ k ∈ F, x k + ∑ k ∈ F, (1 - x k) = F.card := by
        rw [← Finset.sum_add_distrib]; simp
      linarith
    exact_mod_cast this
  -- the kernel
  have hrank : Module.finrank ℝ ((Jf → ℝ) × (Qa → ℝ)) < Module.finrank ℝ (F → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card]
    simpa using hcount
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := cmap a F Jf Qa) hrank
  obtain ⟨d, hdker, hd0⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker] at hdker
  have hdj : ∀ j ∈ Jf, ∑ o, ext F d ⟨j, o⟩ = 0 := by
    intro j hj
    have := congrArg (fun p => p.1 ⟨j, hj⟩) hdker
    simpa [cmap] using this
  have hdq : ∀ q ∈ Qa, ∑ k, a k q * ext F d k = 0 := by
    intro q hq
    have := congrArg (fun p => p.2 ⟨q, hq⟩) hdker
    simpa [cmap] using this
  have hdne : ∃ k ∈ F, ext F d k ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hd0
    funext k
    have := hall k.1 k.2
    simpa [ext] using this
  obtain ⟨t, ht, k₀, hk₀F, hk₀⟩ := hit x (ext F d) F hF hg.bnd (ext_out F d) hdne
  set x' : (Σ j, O j) → ℝ := fun k => x k + t * ext F d k with hx'
  have hsame : ∀ k ∉ F, x' k = x k := by
    intro k hk; simp [x', ext_out F d k hk]
  refine ⟨x', ⟨ht, ?_, ?_⟩, ?_⟩
  · intro j
    simp only [x']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hg.job j]
    by_cases hj : j ∈ Jf
    · rw [hdj j hj]; ring
    · have : ∀ o, ext F d ⟨j, o⟩ = 0 := by
        intro o
        apply ext_out
        intro h
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, o, h⟩)
      simp [this]
  · intro q
    by_cases hU : U a x q ≤ b q + 2 * τ
    · right
      refine le_trans ?_ hU
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        by_contra h0
        have hx0 : x k = 0 := le_antisymm (not_lt.mp h0) (hg.bnd k).1
        have hkF : k ∉ F := fun h => by have := (hF k h).1; linarith
        rw [hsame k hkF, hx0] at hk
        exact lt_irrefl _ hk
      · intro k _ _; exact (ha k q).1
    · left
      have hqrel : q ∈ Qrel := by
        by_contra hq
        apply hU
        have : ∀ k, a k q = 0 := by
          intro k
          apply (hs k).2
          intro hqk
          exact hq (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hqk⟩)
        have : U a x q = 0 := by unfold U; simp [this]
        rw [this]; linarith [hb q]
      have hqa : q ∈ Qa := Finset.mem_filter.mpr ⟨hqrel, hU⟩
      have hL : L a x' q = L a x q := by
        unfold L
        simp only [x', mul_add, Finset.sum_add_distrib]
        have : ∑ k, a k q * (t * ext F d k) = t * ∑ k, a k q * ext F d k := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        rw [this, hdq q hqa]; ring
      rw [hL]
      exact (hg.cons q).resolve_right hU
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨k₀, hk₀F, ?_⟩
      intro h
      simp only [Fr, Finset.mem_filter, Finset.mem_univ, true_and] at h
      rcases hk₀ with h' | h' <;> (simp only [x'] at h; linarith [h.1, h.2])
    · intro k hk
      by_contra hkF
      simp only [Fr, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [hsame k hkF] at hk
      exact hkF (by simp [F, Fr, hk])

theorem main (a : (Σ j, O j) → Q → ℝ) (b : Q → ℝ) (τ : ℝ)
    (ha : ∀ k q, 0 ≤ a k q ∧ a k q ≤ τ) (s : (Σ j, O j) → Finset Q)
    (hs : ∀ k, (s k).card ≤ 2 ∧ ∀ q ∉ s k, a k q = 0)
    (hτ : 0 ≤ τ) (hb : ∀ q, 0 ≤ b q) :
    ∀ n : ℕ, ∀ x, (Fr x).card = n → Good a b τ x →
      ∃ σ : ∀ j, O j, ∀ q, ∑ j, a ⟨j, σ j⟩ q ≤ b q + 2 * τ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn hg
    rcases (Fr x).eq_empty_or_nonempty with h0 | hne
    · exact base a b τ x (fun k q => (ha k q).1) hτ hb hg h0
    · obtain ⟨x', hg', hlt⟩ := step a b τ x ha s hs hτ hb hg hne
      exact ih _ (hn ▸ hlt) x' rfl hg'

end WECLemmaA3

theorem solution (J Q : Type) [Fintype J] (O : J → Type) [∀ j, Fintype (O j)]
    (p : ∀ j, O j → ℝ) (amt : ∀ j, O j → Q → ℝ) (τ : ℝ)
    (hp : ∀ j o, 0 ≤ p j o) (hp1 : ∀ j, ∑ o, p j o = 1)
    (hamt : ∀ j o q, 0 ≤ amt j o q ∧ amt j o q ≤ τ)
    (htwo : ∀ j o, ∃ s : Finset Q, s.card ≤ 2 ∧ ∀ q ∉ s, amt j o q = 0)
    (hτ : 0 ≤ τ) :
    ∃ σ : ∀ j, O j, ∀ q, ∑ j, amt j (σ j) q ≤ (∑ j, ∑ o, p j o * amt j o q) + 2 * τ := by
  let a : (Σ j, O j) → Q → ℝ := fun k q => amt k.1 k.2 q
  let x : (Σ j, O j) → ℝ := fun k => p k.1 k.2
  choose s hs using fun k : (Σ j, O j) => htwo k.1 k.2
  let b : Q → ℝ := fun q => WECLemmaA3.L a x q
  have hb : ∀ q, b q = ∑ j, ∑ o, p j o * amt j o q := by
    intro q
    simp only [b, WECLemmaA3.L, a, x]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro o _; ring
  have hg : WECLemmaA3.Good a b τ x := by
    refine ⟨fun k => ⟨hp _ _, ?_⟩, hp1, fun q => Or.inl le_rfl⟩
    rw [← hp1 k.1]
    exact Finset.single_le_sum (f := p k.1) (fun o _ => hp _ _) (Finset.mem_univ _)
  have hb0 : ∀ q, 0 ≤ b q := by
    intro q
    rw [hb]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun o _ =>
      mul_nonneg (hp _ _) (hamt _ _ _).1))
  obtain ⟨σ, hσ⟩ := WECLemmaA3.main a b τ (fun k q => hamt k.1 k.2 q) s hs hτ hb0 _ x rfl hg
  exact ⟨σ, fun q => by rw [← hb q]; exact hσ q⟩
