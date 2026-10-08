-- Prove2me | solution 1 for TalagrandConc.Assignment.lemma_10_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:28:45.911995+00:00
-- url     : https://prove2.me/submissions/accb5b89-ed9e-4849-a6c2-f1607b3649f0

import Mathlib
import Definitions.Def_TalagrandConc_Assignment_Basic



namespace TalagrandConc.Assignment

open Classical

/-- A walk of length `n` from `a` to `b` along the relation `(x, τ y) ∈ D`. -/
def IsWalk {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (a b : Fin N) (n : ℕ)
    (c : ℕ → Fin N) : Prop :=
  c 0 = a ∧ c n = b ∧ ∀ ℓ, ℓ < n → (c ℓ, τ (c (ℓ + 1))) ∈ D

def fwd {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (S : Set (Fin N)) :
    Set (Fin N) :=
  {b | ∃ a ∈ S, (a, τ b) ∈ D}

def bwd {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (T : Set (Fin N)) :
    Set (Fin N) :=
  {a | ∃ b ∈ T, (a, τ b) ∈ D}

lemma fwd_eq_preimage {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N))
    (S : Set (Fin N)) : fwd D τ S = τ ⁻¹' nbhd D S := by
  ext b; simp [fwd, nbhd]

lemma ncard_fwd {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N))
    (S : Set (Fin N)) : (fwd D τ S).ncard = (nbhd D S).ncard := by
  rw [fwd_eq_preimage]
  have : τ ⁻¹' nbhd D S = τ.symm '' nbhd D S := by
    ext x; simp [Equiv.symm_apply_eq]
  rw [this]
  exact Set.ncard_image_of_injective _ τ.symm.injective

lemma ncard_le_N {N : ℕ} (S : Set (Fin N)) : S.ncard ≤ N := by
  have := Set.ncard_le_card S
  simpa using this

lemma fwd_expand {N : ℕ} {D : Set (Fin N × Fin N)} {α : ℝ} (hD : IsExpanding N α D)
    (τ : Equiv.Perm (Fin N)) (S : Set (Fin N)) :
    min (α * S.ncard) ((N : ℝ) / 2) ≤ ((fwd D τ S).ncard : ℝ) := by
  obtain ⟨hα, h⟩ := hD
  rw [ncard_fwd]
  rcases le_or_gt (S.ncard : ℝ) ((N : ℝ) / 2) with h1 | h1
  · exact (h S).1 h1
  · have h2 := (h S).2 h1.le
    refine le_trans (min_le_right _ _) (le_trans ?_ h2)
    have hS : (S.ncard : ℝ) ≤ N := by exact_mod_cast ncard_le_N S
    have ha : 1 / α ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hα
    have := mul_le_mul_of_nonneg_right ha (sub_nonneg.2 hS)
    linarith

lemma bwd_expand {N : ℕ} {D : Set (Fin N × Fin N)} {α : ℝ} (hD : IsExpanding N α D)
    (τ : Equiv.Perm (Fin N)) (T : Set (Fin N)) :
    min (α * T.ncard) ((N : ℝ) / 2) ≤ ((bwd D τ T).ncard : ℝ) := by
  obtain ⟨hα, h⟩ := hD
  set S := (bwd D τ T)ᶜ with hSdef
  have hsub : fwd D τ S ⊆ Tᶜ := by
    rintro b ⟨a, haS, hab⟩ hbT
    exact haS ⟨b, hbT, hab⟩
  have hcard : (fwd D τ S).ncard + T.ncard ≤ N := by
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_add_ncard_compl T
    simp only [Nat.card_fin] at h2
    omega
  have hSc : S.ncard + (bwd D τ T).ncard = N := by
    have := Set.ncard_add_ncard_compl (bwd D τ T)
    simp only [Nat.card_fin] at this
    rw [add_comm]; exact this
  have hcardR : ((fwd D τ S).ncard : ℝ) + T.ncard ≤ N := by exact_mod_cast hcard
  have hScR : (S.ncard : ℝ) + (bwd D τ T).ncard = N := by exact_mod_cast hSc
  rcases le_or_gt (S.ncard : ℝ) ((N : ℝ) / 2) with h1 | h1
  · exact le_trans (min_le_right _ _) (by linarith)
  · have h2 := (h S).2 h1.le
    rw [ncard_fwd] at hcardR
    refine le_trans (min_le_left _ _) ?_
    have hα0 : 0 < α := by linarith
    have hT : (T.ncard : ℝ) ≤ (1 / α) * (bwd D τ T).ncard := by
      have : (1 / α) * ((N : ℝ) - S.ncard) = (1 / α) * (bwd D τ T).ncard := by
        congr 1; linarith
      linarith
    calc α * T.ncard ≤ α * ((1 / α) * (bwd D τ T).ncard) :=
          mul_le_mul_of_nonneg_left hT hα0.le
      _ = (bwd D τ T).ncard := by field_simp

lemma walk_single {N : ℕ} {D : Set (Fin N × Fin N)} {τ : Equiv.Perm (Fin N)} {a b : Fin N}
    (h : (a, τ b) ∈ D) : ∃ c, IsWalk D τ a b 1 c := by
  refine ⟨fun ℓ => if ℓ = 0 then a else b, by simp, by simp, ?_⟩
  intro ℓ hℓ
  have : ℓ = 0 := by omega
  subst this
  simpa using h

lemma walk_refl {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (a : Fin N) :
    ∃ c, IsWalk D τ a a 0 c :=
  ⟨fun _ => a, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

lemma walk_concat {N : ℕ} {D : Set (Fin N × Fin N)} {τ : Equiv.Perm (Fin N)} {a b d : Fin N}
    {n1 n2 : ℕ} {c1 c2 : ℕ → Fin N} (h1 : IsWalk D τ a b n1 c1) (h2 : IsWalk D τ b d n2 c2) :
    ∃ c, IsWalk D τ a d (n1 + n2) c := by
  obtain ⟨h10, h1n, h1e⟩ := h1
  obtain ⟨h20, h2n, h2e⟩ := h2
  refine ⟨fun ℓ => if ℓ ≤ n1 then c1 ℓ else c2 (ℓ - n1), by simp [h10], ?_, ?_⟩
  · dsimp only
    by_cases hn2 : n2 = 0
    · subst hn2; simp [h1n, ← h2n, h20]
    · rw [if_neg (by omega)]
      have : n1 + n2 - n1 = n2 := by omega
      rw [this, h2n]
  · intro ℓ hℓ
    dsimp only
    by_cases hl : ℓ < n1
    · rw [if_pos hl.le, if_pos (by omega)]
      exact h1e ℓ hl
    · by_cases hl2 : ℓ = n1
      · subst hl2
        rw [if_pos le_rfl, if_neg (by omega), h1n, ← h20]
        have : ℓ + 1 - ℓ = 1 := by omega
        rw [this]
        exact h2e 0 (by omega)
      · rw [if_neg (by omega), if_neg (by omega)]
        have : ℓ + 1 - n1 = (ℓ - n1) + 1 := by omega
        rw [this]
        exact h2e (ℓ - n1) (by omega)

/-- Points reachable from `i` by a walk of length at most `k`. -/
def FwdSet {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (i : Fin N) (k : ℕ) :
    Set (Fin N) :=
  {b | ∃ n, n ≤ k ∧ ∃ c, IsWalk D τ i b n c}

/-- Points from which `i` is reachable by a walk of length at most `k`. -/
def BwdSet {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (i : Fin N) (k : ℕ) :
    Set (Fin N) :=
  {a | ∃ n, n ≤ k ∧ ∃ c, IsWalk D τ a i n c}

lemma fwd_FwdSet {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (i : Fin N)
    (k : ℕ) : ∀ b ∈ fwd D τ (FwdSet D τ i k), ∃ n, 1 ≤ n ∧ n ≤ k + 1 ∧ ∃ c, IsWalk D τ i b n c := by
  rintro b ⟨a, ⟨n, hn, c, hc⟩, hab⟩
  obtain ⟨c1, hc1⟩ := walk_single hab
  obtain ⟨c', hc'⟩ := walk_concat hc hc1
  exact ⟨n + 1, by omega, by omega, c', hc'⟩

lemma bwd_BwdSet {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (i : Fin N)
    (k : ℕ) : ∀ a ∈ bwd D τ (BwdSet D τ i k), ∃ n, 1 ≤ n ∧ n ≤ k + 1 ∧ ∃ c, IsWalk D τ a i n c := by
  rintro a ⟨b, ⟨n, hn, c, hc⟩, hab⟩
  obtain ⟨c1, hc1⟩ := walk_single hab
  obtain ⟨c', hc'⟩ := walk_concat hc1 hc
  exact ⟨1 + n, by omega, by omega, c', hc'⟩

lemma fwd_FwdSet_subset {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (i : Fin N)
    (k : ℕ) : fwd D τ (FwdSet D τ i k) ⊆ FwdSet D τ i (k + 1) := by
  intro b hb
  obtain ⟨n, _, hn, c, hc⟩ := fwd_FwdSet D τ i k b hb
  exact ⟨n, hn, c, hc⟩

lemma bwd_BwdSet_subset {N : ℕ} (D : Set (Fin N × Fin N)) (τ : Equiv.Perm (Fin N)) (i : Fin N)
    (k : ℕ) : bwd D τ (BwdSet D τ i k) ⊆ BwdSet D τ i (k + 1) := by
  intro b hb
  obtain ⟨n, _, hn, c, hc⟩ := bwd_BwdSet D τ i k b hb
  exact ⟨n, hn, c, hc⟩

lemma min_step {N : ℕ} {α x : ℝ} (hα : 2 ≤ α) (k : ℕ) (hx : min (α ^ k) ((N : ℝ) / 2) ≤ x) :
    min (α ^ (k + 1)) ((N : ℝ) / 2) ≤ min (α * x) ((N : ℝ) / 2) := by
  have hα0 : 0 ≤ α := by linarith
  rcases le_total (α ^ k) ((N : ℝ) / 2) with h | h
  · rw [min_eq_left h] at hx
    refine le_min (le_trans (min_le_left _ _) ?_) (min_le_right _ _)
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left hx hα0
  · rw [min_eq_right h] at hx
    refine le_min (le_trans (min_le_right _ _) ?_) (min_le_right _ _)
    have : 0 ≤ (N : ℝ) / 2 := by positivity
    nlinarith

lemma ncard_FwdSet {N : ℕ} {D : Set (Fin N × Fin N)} {α : ℝ} (hD : IsExpanding N α D)
    (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    ∀ k, min (α ^ k) ((N : ℝ) / 2) ≤ ((FwdSet D τ i k).ncard : ℝ) := by
  intro k
  induction k with
  | zero =>
    have hi : i ∈ FwdSet D τ i 0 := ⟨0, le_rfl, walk_refl D τ i⟩
    have : 1 ≤ (FwdSet D τ i 0).ncard := by
      rw [Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero]
      exact Set.nonempty_iff_ne_empty.1 ⟨i, hi⟩
    refine le_trans (min_le_left _ _) ?_
    simp only [pow_zero]
    exact_mod_cast this
  | succ k ih =>
    have h1 := min_step hD.1 k ih
    have h2 := fwd_expand hD τ (FwdSet D τ i k)
    have h3 : ((fwd D τ (FwdSet D τ i k)).ncard : ℝ) ≤ (FwdSet D τ i (k + 1)).ncard := by
      exact_mod_cast Set.ncard_le_ncard (fwd_FwdSet_subset D τ i k)
    linarith

lemma ncard_BwdSet {N : ℕ} {D : Set (Fin N × Fin N)} {α : ℝ} (hD : IsExpanding N α D)
    (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    ∀ k, min (α ^ k) ((N : ℝ) / 2) ≤ ((BwdSet D τ i k).ncard : ℝ) := by
  intro k
  induction k with
  | zero =>
    have hi : i ∈ BwdSet D τ i 0 := ⟨0, le_rfl, walk_refl D τ i⟩
    have : 1 ≤ (BwdSet D τ i 0).ncard := by
      rw [Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero]
      exact Set.nonempty_iff_ne_empty.1 ⟨i, hi⟩
    refine le_trans (min_le_left _ _) ?_
    simp only [pow_zero]
    exact_mod_cast this
  | succ k ih =>
    have h1 := min_step hD.1 k ih
    have h2 := bwd_expand hD τ (BwdSet D τ i k)
    have h3 : ((bwd D τ (BwdSet D τ i k)).ncard : ℝ) ≤ (BwdSet D τ i (k + 1)).ncard := by
      exact_mod_cast Set.ncard_le_ncard (bwd_BwdSet_subset D τ i k)
    linarith

/-- Shortcutting a closed walk at a repeated vertex. -/
lemma walk_shortcut {N : ℕ} {D : Set (Fin N × Fin N)} {τ : Equiv.Perm (Fin N)} {i : Fin N}
    {n : ℕ} {c : ℕ → Fin N} (hc : IsWalk D τ i i n c) {a b : ℕ} (hab : a < b) (hb : b < n)
    (heq : c a = c b) : ∃ c', IsWalk D τ i i (n - (b - a)) c' := by
  obtain ⟨h0, hn, he⟩ := hc
  refine ⟨fun ℓ => if ℓ ≤ a then c ℓ else c (ℓ + (b - a)), by simp [h0], ?_, ?_⟩
  · dsimp only
    rw [if_neg (by omega)]
    have : n - (b - a) + (b - a) = n := by omega
    rw [this, hn]
  · intro ℓ hℓ
    dsimp only
    by_cases h1 : ℓ < a
    · rw [if_pos h1.le, if_pos (by omega)]
      exact he ℓ (by omega)
    · by_cases h2 : ℓ = a
      · subst h2
        rw [if_pos le_rfl, if_neg (by omega), heq]
        have : ℓ + 1 + (b - ℓ) = b + 1 := by omega
        rw [this]
        exact he b hb
      · rw [if_neg (by omega), if_neg (by omega)]
        have : ℓ + 1 + (b - a) = ℓ + (b - a) + 1 := by omega
        rw [this]
        exact he _ (by omega)

theorem lemma_10_1_core {N : ℕ} (D : Set (Fin N × Fin N)) (α : ℝ) (hD : IsExpanding N α D)
    (m : ℕ) (hm : 1 ≤ m) (hαm : (N : ℝ) / 2 ≤ α ^ m) (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 * m ∧ ∃ c : ℕ → Fin N, c 0 = i ∧ c n = i ∧
      (∀ a b : ℕ, a < n → b < n → c a = c b → a = b) ∧
      ∀ ℓ : ℕ, ℓ < n → (c ℓ, τ (c (ℓ + 1))) ∈ D := by
  have hα := hD.1
  -- a closed walk of length in [1, 2m]
  have hclosed : ∃ n, 1 ≤ n ∧ n ≤ 2 * m ∧ ∃ c, IsWalk D τ i i n c := by
    set G := fwd D τ (FwdSet D τ i (m - 1)) with hGdef
    set H := bwd D τ (BwdSet D τ i (m - 1)) with hHdef
    have hpow : α ^ m = α * α ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hhalf : ∀ x : ℝ, min (α ^ (m - 1)) ((N : ℝ) / 2) ≤ x →
        (N : ℝ) / 2 ≤ min (α * x) ((N : ℝ) / 2) := by
      intro x hx
      refine le_min ?_ le_rfl
      rcases le_total (α ^ (m - 1)) ((N : ℝ) / 2) with h | h
      · rw [min_eq_left h] at hx
        calc (N : ℝ) / 2 ≤ α ^ m := hαm
          _ = α * α ^ (m - 1) := hpow
          _ ≤ α * x := mul_le_mul_of_nonneg_left hx (by linarith)
      · rw [min_eq_right h] at hx
        have : 0 ≤ (N : ℝ) / 2 := by positivity
        nlinarith
    have hG : (N : ℝ) / 2 ≤ G.ncard :=
      le_trans (hhalf _ (ncard_FwdSet hD τ i (m - 1))) (fwd_expand hD τ _)
    have hH : (N : ℝ) / 2 ≤ H.ncard :=
      le_trans (hhalf _ (ncard_BwdSet hD τ i (m - 1))) (bwd_expand hD τ _)
    have hGmem : ∀ b ∈ G, ∃ n, 1 ≤ n ∧ n ≤ m ∧ ∃ c, IsWalk D τ i b n c := by
      intro b hb
      obtain ⟨n, h1, h2, c, hc⟩ := fwd_FwdSet D τ i (m - 1) b hb
      exact ⟨n, h1, by omega, c, hc⟩
    have hHmem : ∀ a ∈ H, ∃ n, 1 ≤ n ∧ n ≤ m ∧ ∃ c, IsWalk D τ a i n c := by
      intro a ha
      obtain ⟨n, h1, h2, c, hc⟩ := bwd_BwdSet D τ i (m - 1) a ha
      exact ⟨n, h1, by omega, c, hc⟩
    by_cases hGH : (G ∩ H).Nonempty
    · obtain ⟨j, hjG, hjH⟩ := hGH
      obtain ⟨n1, h11, h12, c1, hc1⟩ := hGmem j hjG
      obtain ⟨n2, h21, h22, c2, hc2⟩ := hHmem j hjH
      obtain ⟨c, hc⟩ := walk_concat hc1 hc2
      exact ⟨n1 + n2, by omega, by omega, c, hc⟩
    · have hdisj : Disjoint G H :=
        Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hGH)
      have hunion : (G ∪ H).ncard = G.ncard + H.ncard := Set.ncard_union_eq hdisj
      have hi : i ∈ G ∪ H := by
        by_contra hi
        have hsub : G ∪ H ⊆ ({i} : Set (Fin N))ᶜ := by
          intro x hx hxi
          rw [Set.mem_singleton_iff] at hxi
          exact hi (hxi ▸ hx)
        have h1 := Set.ncard_le_ncard hsub
        have h2 := Set.ncard_add_ncard_compl ({i} : Set (Fin N))
        rw [Set.ncard_singleton, Nat.card_fin] at h2
        have h3 : (N : ℝ) ≤ G.ncard + H.ncard := by linarith
        have h4 : N ≤ G.ncard + H.ncard := by exact_mod_cast h3
        omega
      rcases hi with h | h
      · obtain ⟨n, h1, h2, c, hc⟩ := hGmem i h
        exact ⟨n, h1, by omega, c, hc⟩
      · obtain ⟨n, h1, h2, c, hc⟩ := hHmem i h
        exact ⟨n, h1, by omega, c, hc⟩
  have hex : ∃ n, 1 ≤ n ∧ ∃ c, IsWalk D τ i i n c := by
    obtain ⟨n, h1, _, c, hc⟩ := hclosed
    exact ⟨n, h1, c, hc⟩
  have hspec := Nat.find_spec hex
  obtain ⟨hn1, c, hc⟩ := hspec
  refine ⟨Nat.find hex, hn1, ?_, c, hc.1, hc.2.1, ?_, hc.2.2⟩
  · obtain ⟨n0, h1, h2, c0, hc0⟩ := hclosed
    exact le_trans (Nat.find_min' hex ⟨h1, c0, hc0⟩) h2
  · intro a b ha hb hab
    by_contra hne
    have key : ∀ a b : ℕ, a < b → b < Nat.find hex → c a = c b → False := by
      intro a b hlt hb heq
      obtain ⟨c', hc'⟩ := walk_shortcut hc hlt hb heq
      exact Nat.find_min hex (show Nat.find hex - (b - a) < Nat.find hex by omega)
        ⟨by omega, c', hc'⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a b h hb hab
    · exact key b a h ha hab.symm

end TalagrandConc.Assignment

open TalagrandConc.Assignment


theorem solution {N : ℕ} (D : Set (Fin N × Fin N)) (α : ℝ) (hD : IsExpanding N α D)
    (m : ℕ) (hm : 1 ≤ m) (hαm : (N : ℝ) / 2 ≤ α ^ m) (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 * m ∧ ∃ c : ℕ → Fin N, c 0 = i ∧ c n = i ∧
      (∀ a b : ℕ, a < n → b < n → c a = c b → a = b) ∧
      ∀ ℓ : ℕ, ℓ < n → (c ℓ, τ (c (ℓ + 1))) ∈ D := by
  exact lemma_10_1_core D α hD m hm hαm τ i
