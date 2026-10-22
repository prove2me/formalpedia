-- Prove2me | solution 1 for PosetSecretary.LowerBound.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:39:21.436969+00:00
-- url     : https://prove2.me/submissions/13256a71-f1c4-443e-9f34-4b27aeafa5a5

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_LowerBound_Setting

set_option autoImplicit false
open PosetSecretary.LowerBound

theorem psl_le_iff (ω k : ℕ) (a b : ChainsPoset ω k) : a ≤ b ↔ a.1 = b.1 ∧ a.2.val ≤ b.2.val := by
  obtain ⟨i, x⟩ := a
  obtain ⟨i', y⟩ := b
  constructor
  · intro h
    cases h with
    | fiber _ _ _ h2 => exact ⟨rfl, h2⟩
  · rintro ⟨h1, h2⟩
    simp only at h1
    subst h1
    exact (Sigma.mk_le_mk_iff).2 h2

theorem psl_width (ω k : ℕ) (hk : 1 ≤ k) :
    AppliedComb.Posets.width (ChainsPoset ω k) = ω := by
  classical
  unfold AppliedComb.Posets.width
  apply le_antisymm
  · apply Finset.sup_le
    intro A hA
    rw [Finset.mem_filter] at hA
    have hA' := hA.2
    have : A.card ≤ (Finset.univ : Finset (Fin ω)).card := by
      apply Finset.card_le_card_of_injOn (fun x => x.1)
      · intro x _; simp
      · intro x hx y hy hxy
        by_contra hne
        have hxy' : x.1 = y.1 := hxy
        rcases le_total x.2.val y.2.val with h | h
        · exact hA' (by exact_mod_cast hx) (by exact_mod_cast hy) hne ((psl_le_iff ω k x y).2 ⟨hxy', h⟩)
        · exact hA' (by exact_mod_cast hy) (by exact_mod_cast hx) (Ne.symm hne) ((psl_le_iff ω k y x).2 ⟨hxy'.symm, h⟩)
    simpa using this
  · have hmem : (Finset.univ.image (fun i : Fin ω => (⟨i, ⟨0, hk⟩⟩ : ChainsPoset ω k))) ∈
        (Finset.univ : Finset (Finset (ChainsPoset ω k))).filter
          (fun A : Finset (ChainsPoset ω k) => IsAntichain (· ≤ ·) (A : Set (ChainsPoset ω k))) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx y hy hne hle
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      rw [psl_le_iff] at hle
      apply hne
      have := hle.1
      simp only at this
      rw [this]
    have hc : (Finset.univ.image (fun i : Fin ω => (⟨i, ⟨0, hk⟩⟩ : ChainsPoset ω k))).card = ω := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j h
        simpa using h
    calc ω = _ := hc.symm
      _ ≤ _ := Finset.le_sup (f := Finset.card) hmem

theorem psl_expectedScore_eq (ω k : ℕ) (μ : Finset (ChainsPoset ω k) → ℝ) (w : ChainsPoset ω k → ℝ) :
    expectedScore μ w = ∑ a, selProb μ a * w a := by
  classical
  unfold expectedScore selProb
  simp only [Finset.sum_mul]
  have : ∀ s : Finset (ChainsPoset ω k), μ s * ∑ a ∈ s, w a =
      ∑ a, if a ∈ s then μ s * w a else 0 := by
    intro s
    rw [Finset.mul_sum, ← Finset.sum_filter]
    congr 1
    ext a; simp
  simp only [this]
  rw [Finset.sum_comm]
  congr 1
  ext a
  rw [← Finset.sum_filter]

theorem psl_selProb_nonneg (ω k : ℕ) (μ : Finset (ChainsPoset ω k) → ℝ) (hμ : IsSelectionRule k μ)
    (a : ChainsPoset ω k) : 0 ≤ selProb μ a :=
  Finset.sum_nonneg (fun s _ => hμ.1 s)

theorem psl_selProb_le_one (ω k : ℕ) (μ : Finset (ChainsPoset ω k) → ℝ) (hμ : IsSelectionRule k μ)
    (a : ChainsPoset ω k) : selProb μ a ≤ 1 := by
  unfold selProb
  calc ∑ s ∈ Finset.univ.filter (fun s => a ∈ s), μ s ≤ ∑ s, μ s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun s _ _ => hμ.1 s)
    _ = 1 := hμ.2.1

theorem psl_sum_selProb_le (ω k : ℕ) (μ : Finset (ChainsPoset ω k) → ℝ) (hμ : IsSelectionRule k μ) :
    ∑ a, selProb μ a ≤ k := by
  have h := psl_expectedScore_eq ω k μ (fun _ => 1)
  simp only [mul_one] at h
  rw [← h]
  unfold expectedScore
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc ∑ s, μ s * (s.card : ℝ) ≤ ∑ s, μ s * (k : ℝ) := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : k < s.card
        · rw [hμ.2.2 s hs]; simp
        · have : (s.card : ℝ) ≤ k := by exact_mod_cast (not_lt.1 hs)
          exact mul_le_mul_of_nonneg_left this (hμ.1 s)
    _ = k := by rw [← Finset.sum_mul, hμ.2.1, one_mul]

theorem psl_exists_chain (ω k : ℕ) (hω : 1 ≤ ω)
    (μ : Finset (ChainsPoset ω k) → ℝ) (hμ : IsSelectionRule k μ) :
    ∃ i : Fin ω, ∑ j : Fin k, selProb μ ⟨i, j⟩ ≤ (k : ℝ) / ω := by
  have h1 := psl_sum_selProb_le ω k μ hμ
  rw [Fintype.sum_sigma] at h1
  have hne : (Finset.univ : Finset (Fin ω)).Nonempty := ⟨⟨0, hω⟩, Finset.mem_univ _⟩
  have h2 : ∑ i : Fin ω, ∑ j : Fin k, selProb μ ⟨i, j⟩ ≤ ∑ _i : Fin ω, (k : ℝ) / ω := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (ω : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ this]
    exact h1
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hne h2
  exact ⟨i, hi⟩

theorem psl_opt_eq (ω k : ℕ) (hk : 1 ≤ k) (i₀ : Fin ω) (M : ℝ) (hM : 0 < M)
    (w : ChainsPoset ω k → ℝ)
    (hlight : ∀ (i : Fin ω) (j : Fin k), i ≠ i₀ → 0 ≤ w ⟨i, j⟩ ∧ w ⟨i, j⟩ < M / (2 * k))
    (hheavy : ∀ j : Fin k, |w ⟨i₀, j⟩ - M / k| < M / (2 * k))
    (hsum : ∑ j : Fin k, (w ⟨i₀, j⟩ - M / k) = 0) :
    PosetSecretary.ProxyLabel.opt w k = M := by
  classical
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℝ := M / (2 * k) with hc
  let H : Finset (ChainsPoset ω k) :=
    Finset.univ.map ⟨fun j : Fin k => (⟨i₀, j⟩ : ChainsPoset ω k), fun a b h => by simpa using h⟩
  have hHmem : ∀ x : ChainsPoset ω k, x ∈ H ↔ x.1 = i₀ := by
    rintro ⟨i, j⟩
    simp only [H, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j', hj'⟩
      exact (congrArg Sigma.fst hj').symm
    · intro h
      have h' : i = i₀ := h
      subst h'
      exact ⟨j, rfl⟩
  have hHcard : H.card = k := by simp [H]
  have hHsum : ∑ x ∈ H, w x = M := by
    simp only [H, Finset.sum_map]
    show ∑ j : Fin k, w ⟨i₀, j⟩ = M
    have h1 : ∑ j : Fin k, (w ⟨i₀, j⟩ - M / k) = ∑ j : Fin k, w ⟨i₀, j⟩ - k * (M / k) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [h1] at hsum
    have : (k : ℝ) * (M / k) = M := by field_simp
    linarith
  have hheavy' : ∀ x ∈ H, c ≤ w x := by
    intro x hx
    rw [hHmem] at hx
    obtain ⟨i, j⟩ := x
    simp only at hx
    subst hx
    have := (abs_lt.1 (hheavy j)).1
    have e : M / k - M / (2 * k) = c := by rw [hc]; field_simp; ring
    linarith
  have hlight' : ∀ x, x ∉ H → w x ≤ c := by
    intro x hx
    rw [hHmem] at hx
    obtain ⟨i, j⟩ := x
    exact (hlight i j hx).2.le
  have hupper : ∀ S : Finset (ChainsPoset ω k), S.card ≤ k → ∑ x ∈ S, w x ≤ M := by
    intro S hS
    have e1 : ∑ x ∈ S, w x = ∑ x ∈ S.filter (· ∈ H), w x + ∑ x ∈ S.filter (· ∉ H), w x :=
      (Finset.sum_filter_add_sum_filter_not S (· ∈ H) w).symm
    have e2 : ∑ x ∈ H, w x = ∑ x ∈ S.filter (· ∈ H), w x + ∑ x ∈ H \ S, w x := by
      have : H = S.filter (· ∈ H) ∪ (H \ S) := by
        ext x; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]; tauto
      conv_lhs => rw [this]
      rw [Finset.sum_union]
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_filter, Finset.mem_sdiff] at hx hx'
      exact hx'.2 hx.1
    have h3 : ∑ x ∈ S.filter (· ∉ H), w x ≤ ((S.filter (· ∉ H)).card : ℝ) * c := by
      calc ∑ x ∈ S.filter (· ∉ H), w x ≤ ∑ _x ∈ S.filter (· ∉ H), c :=
            Finset.sum_le_sum (fun x hx => hlight' x (Finset.mem_filter.1 hx).2)
        _ = _ := by simp
    have h4 : ((H \ S).card : ℝ) * c ≤ ∑ x ∈ H \ S, w x := by
      calc ((H \ S).card : ℝ) * c = ∑ _x ∈ H \ S, c := by simp
        _ ≤ _ := Finset.sum_le_sum (fun x hx => hheavy' x (Finset.mem_sdiff.1 hx).1)
    have h5 : (S.filter (· ∉ H)).card + (S.filter (· ∈ H)).card = S.card :=
      by have := Finset.card_filter_add_card_filter_not (s := S) (fun x => x ∈ H); omega
    have h6 : (H \ S).card + (S.filter (· ∈ H)).card = k := by
      have : S.filter (· ∈ H) = H ∩ S := by
        ext x; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
      have h' := Finset.card_inter_add_card_sdiff H S
      rw [this]; omega
    have h7 : (S.filter (· ∉ H)).card ≤ (H \ S).card := by omega
    have h7' : ((S.filter (· ∉ H)).card : ℝ) ≤ (H \ S).card := by exact_mod_cast h7
    have hcpos : 0 ≤ c := by rw [hc]; positivity
    have : ((S.filter (· ∉ H)).card : ℝ) * c ≤ ((H \ S).card : ℝ) * c :=
      mul_le_mul_of_nonneg_right h7' hcpos
    linarith
  unfold PosetSecretary.ProxyLabel.opt
  apply le_antisymm
  · apply Finset.sup'_le
    intro S hS
    rw [Finset.mem_filter] at hS
    exact hupper S hS.2
  · rw [← hHsum]
    exact Finset.le_sup' (fun S => ∑ a ∈ S, w a)
      (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), hHcard.le⟩)

theorem psl_lt_iff (ω k : ℕ) (a b : ChainsPoset ω k) : a < b ↔ a.1 = b.1 ∧ a.2.val < b.2.val := by
  rw [lt_iff_le_not_ge, psl_le_iff, psl_le_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    by_contra h
    exact h3 ⟨h1.symm, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, h2.le⟩, ?_⟩
    rintro ⟨_, h4⟩
    omega

theorem psl_divmod (k i j i' j' : ℕ) (hj : j < k) (hj' : j' < k) (h : i * k + j = i' * k + j') :
    i = i' ∧ j = j' := by
  have hk : 0 < k := by omega
  have h1 : (i * k + j) / k = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hj, zero_add]
  have h2 : (i' * k + j') / k = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hj', zero_add]
  have : i = i' := by rw [← h1, ← h2, h]
  subst this
  exact ⟨rfl, by omega⟩

theorem psl_sum_dev (k : ℕ) : ∑ j : Fin k, (2 * (j : ℝ) - ((k : ℝ) - 1)) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℝ)) k]
  have h := Finset.sum_range_id_mul_two k
  have h' : (∑ i ∈ Finset.range k, (i : ℝ)) * 2 = (k : ℝ) * ((k : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have := congrArg (fun n : ℕ => (n : ℝ)) h
      simp only [Nat.cast_mul, Nat.cast_sum] at this
      rw [Nat.cast_sub hk] at this
      simpa using this
  linarith

theorem psl_perturbation (ω k : ℕ) (hk : 1 ≤ k) (hω : 1 ≤ ω)
    (μ : Finset (ChainsPoset ω k) → ℝ) (hμ : IsSelectionRule k μ) (i₀ : Fin ω)
    (hi₀ : ∑ j : Fin k, selProb μ ⟨i₀, j⟩ ≤ (k : ℝ) / ω) (M : ℝ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ChainsPoset ω k → ℝ, PosetSecretary.ProxyLabel.IsConsistentScoring w ∧
      PosetSecretary.ProxyLabel.opt w k = M ∧
      expectedScore μ w ≤ (1 + ε) * PosetSecretary.ProxyLabel.opt w k / ω := by
  classical
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hωpos : (0 : ℝ) < ω := by exact_mod_cast hω
  set σ : ℝ := min (M / (4 * k)) (ε * M / (ω * k)) with hσdef
  have hσpos : 0 < σ := lt_min (by positivity) (by positivity)
  have hσ1 : σ ≤ M / (4 * k) := min_le_left _ _
  have hσ2 : σ ≤ ε * M / (ω * k) := min_le_right _ _
  set X : ℝ := (k : ℝ) * ω + k + 1 with hX
  have hXpos : 0 < X := by positivity
  set τ : ℝ := σ / X with hτ
  have hτpos : 0 < τ := by positivity
  have hτX : τ * X = σ := by rw [hτ]; field_simp
  have hkX : (k : ℝ) ≤ X := by nlinarith
  have hM4 : M / (4 * k) < M / (2 * k) := by
    apply div_lt_div_of_pos_left hM (by positivity); linarith
  have hM4' : M / (4 * k) = M / k / 4 := by field_simp
  have hM2' : M / (2 * k) = M / k / 2 := by field_simp
  let w : ChainsPoset ω k → ℝ := fun x =>
    if x.1 = i₀ then M / k + τ * (2 * (x.2 : ℝ) - ((k : ℝ) - 1)) else τ * ((x.1 : ℝ) * k + x.2 + 1)
  have hwH : ∀ j : Fin k, w ⟨i₀, j⟩ = M / k + τ * (2 * (j : ℝ) - ((k : ℝ) - 1)) := by
    intro j; simp [w]
  have hwL : ∀ (i : Fin ω) (j : Fin k), i ≠ i₀ → w ⟨i, j⟩ = τ * ((i : ℝ) * k + j + 1) := by
    intro i j hi; simp [w, hi]
  have hj : ∀ j : Fin k, (j : ℝ) + 1 ≤ k := by
    intro j; have : (j : ℕ) + 1 ≤ k := j.2; exact_mod_cast this
  have hi : ∀ i : Fin ω, (i : ℝ) + 1 ≤ ω := by
    intro i; have : (i : ℕ) + 1 ≤ ω := i.2; exact_mod_cast this
  have hj0 : ∀ j : Fin k, (0 : ℝ) ≤ j := fun j => by positivity
  have hi0 : ∀ i : Fin ω, (0 : ℝ) ≤ i := fun i => by positivity
  -- bounds
  have hdev : ∀ j : Fin k, |τ * (2 * (j : ℝ) - ((k : ℝ) - 1))| ≤ σ := by
    intro j
    rw [abs_mul, abs_of_pos hτpos]
    have : |2 * (j : ℝ) - ((k : ℝ) - 1)| ≤ k := by
      rw [abs_le]; constructor <;> nlinarith [hj j, hj0 j]
    calc τ * |2 * (j : ℝ) - ((k : ℝ) - 1)| ≤ τ * X := by
          apply mul_le_mul_of_nonneg_left (this.trans hkX) hτpos.le
      _ = σ := hτX
  have hlightb : ∀ (i : Fin ω) (j : Fin k), 0 < τ * ((i : ℝ) * k + j + 1) ∧ τ * ((i : ℝ) * k + j + 1) ≤ σ := by
    intro i j
    constructor
    · have : 0 < (i : ℝ) * k + j + 1 := by positivity
      positivity
    · rw [← hτX]
      apply mul_le_mul_of_nonneg_left _ hτpos.le
      have h1 := hi i
      have h2 := hj j
      have h3 : ((i : ℝ) + 1) * k ≤ ω * k := mul_le_mul_of_nonneg_right h1 hkpos.le
      nlinarith
  have hσM : σ < M / k / 2 := by
    have : M / k / 4 < M / k / 2 := by
      have : 0 < M / k := by positivity
      linarith
    linarith
  have hopt : PosetSecretary.ProxyLabel.opt w k = M := by
    apply psl_opt_eq ω k hk i₀ M hM w
    · intro i j hij
      rw [hwL i j hij]
      refine ⟨(hlightb i j).1.le, ?_⟩
      have := (hlightb i j).2
      rw [hM2']; linarith
    · intro j
      rw [hwH]
      rw [show M / k + τ * (2 * (j : ℝ) - ((k : ℝ) - 1)) - M / k = τ * (2 * (j : ℝ) - ((k : ℝ) - 1)) by ring]
      have := hdev j
      rw [hM2']; linarith
    · have : ∀ j : Fin k, w ⟨i₀, j⟩ - M / k = τ * (2 * (j : ℝ) - ((k : ℝ) - 1)) := by
        intro j; rw [hwH]; ring
      simp only [this]
      rw [← Finset.mul_sum, psl_sum_dev, mul_zero]
  refine ⟨w, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- nonneg
    rintro ⟨i, j⟩
    by_cases h : i = i₀
    · subst h
      have := hwH j
      have h2 := (abs_le.1 (hdev j)).1
      have h3 : 0 < M / k := by positivity
      show 0 ≤ w ⟨i, j⟩
      rw [this]; linarith
    · show 0 ≤ w ⟨i, j⟩
      rw [hwL i j h]; exact (hlightb i j).1.le
  · -- injective
    rintro ⟨i, j⟩ ⟨i', j'⟩ hxy
    have h3 : 0 < M / k := by positivity
    by_cases h1 : i = i₀ <;> by_cases h2 : i' = i₀
    · subst h1; subst h2
      rw [hwH, hwH] at hxy
      have : (j : ℝ) = j' := by
        have := mul_left_cancel₀ hτpos.ne' (by linarith : τ * (2 * (j : ℝ) - ((k : ℝ) - 1)) = τ * (2 * (j' : ℝ) - ((k : ℝ) - 1)))
        linarith
      have : j = j' := Fin.ext (by exact_mod_cast this)
      subst this; rfl
    · subst h1
      exfalso
      rw [hwH, hwL i' j' h2] at hxy
      have h4 := (abs_le.1 (hdev j)).1
      have h5 := (hlightb i' j').2
      linarith
    · subst h2
      exfalso
      rw [hwL i j h1, hwH] at hxy
      have h4 := (abs_le.1 (hdev j')).1
      have h5 := (hlightb i j).2
      linarith
    · rw [hwL i j h1, hwL i' j' h2] at hxy
      have h4 : (i : ℝ) * k + j + 1 = (i' : ℝ) * k + j' + 1 := mul_left_cancel₀ hτpos.ne' hxy
      have h5 : (i : ℕ) * k + j = (i' : ℕ) * k + j' := by
        have : ((i : ℕ) * k + j : ℕ) = (((i' : ℕ) * k + j' : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      obtain ⟨e1, e2⟩ := psl_divmod k i j i' j' j.2 j'.2 h5
      have e1' : i = i' := Fin.ext e1
      have e2' : j = j' := Fin.ext e2
      subst e1'; subst e2'; rfl
  · -- strict mono
    rintro ⟨i, j⟩ ⟨i', j'⟩ hlt
    rw [psl_lt_iff] at hlt
    obtain ⟨e1, e2⟩ := hlt
    simp only at e1 e2
    subst e1
    have e2' : (j : ℝ) < j' := by exact_mod_cast e2
    by_cases h : i = i₀
    · subst h
      rw [hwH, hwH]
      have := mul_lt_mul_of_pos_left (by linarith : 2 * (j : ℝ) - ((k : ℝ) - 1) < 2 * (j' : ℝ) - ((k : ℝ) - 1)) hτpos
      linarith
    · rw [hwL i j h, hwL i j' h]
      apply mul_lt_mul_of_pos_left _ hτpos
      linarith
  · refine ⟨?_, ?_⟩
    · exact hopt
    · rw [hopt, psl_expectedScore_eq]
      have hb : ∀ a : ChainsPoset ω k, w a ≤ (if a.1 = i₀ then M / k else 0) + σ := by
        rintro ⟨i, j⟩
        by_cases h : i = i₀
        · subst h
          rw [hwH]
          have := (abs_le.1 (hdev j)).2
          simp only [if_true]; linarith
        · rw [hwL i j h]
          have := (hlightb i j).2
          simp only [h, if_false]; linarith
      have hsp0 := psl_selProb_nonneg ω k μ hμ
      calc ∑ a, selProb μ a * w a ≤ ∑ a, selProb μ a * ((if a.1 = i₀ then M / k else 0) + σ) :=
            Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hb a) (hsp0 a))
        _ = (∑ a, selProb μ a * (if a.1 = i₀ then M / k else 0)) + σ * ∑ a, selProb μ a := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro a _; ring
        _ ≤ M / k * ((k : ℝ) / ω) + σ * k := by
            have e1 : ∑ a, selProb μ a * (if a.1 = i₀ then M / k else 0) =
                M / k * ∑ j : Fin k, selProb μ ⟨i₀, j⟩ := by
              rw [Fintype.sum_sigma]
              simp only [mul_ite, mul_zero]
              have e : ∀ i : Fin ω, (∑ j : Fin k, if i = i₀ then selProb μ ⟨i, j⟩ * (M / k) else 0) =
                  if i = i₀ then (∑ j : Fin k, selProb μ ⟨i, j⟩) * (M / k) else 0 := by
                intro i
                split_ifs
                · rw [Finset.sum_mul]
                · simp
              simp only [e]
              rw [Finset.sum_ite_eq' Finset.univ i₀]
              simp only [Finset.mem_univ, if_true]
              ring
            rw [e1]
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hi₀ (by positivity)
            · exact mul_le_mul_of_nonneg_left (psl_sum_selProb_le ω k μ hμ) hσpos.le
        _ ≤ (1 + ε) * M / ω := by
            have e2 : M / k * ((k : ℝ) / ω) = M / ω := by field_simp
            have e3 : σ * k ≤ ε * M / ω := by
              calc σ * k ≤ ε * M / (ω * k) * k := mul_le_mul_of_nonneg_right hσ2 hkpos.le
                _ = ε * M / ω := by field_simp
            rw [e2]
            have : (1 + ε) * M / ω = M / ω + ε * M / ω := by ring
            rw [this]; linarith

theorem solution (k ω : ℕ) (hk : 1 ≤ k) (hω : 1 ≤ ω) :
    ∃ (β : Type) (_ : PartialOrder β) (_ : Fintype β) (_ : DecidableEq β),
      AppliedComb.Posets.width β = ω ∧
      ∀ μ : Finset β → ℝ, IsSelectionRule k μ →
        ∀ ε : ℝ, 0 < ε →
          ∃ w : β → ℝ, PosetSecretary.ProxyLabel.IsConsistentScoring w ∧ 0 < PosetSecretary.ProxyLabel.opt w k ∧
            expectedScore μ w ≤ (1 + ε) * PosetSecretary.ProxyLabel.opt w k / ω := by
  refine ⟨ChainsPoset ω k, inferInstance, inferInstance, inferInstance, psl_width ω k hk, ?_⟩
  intro μ hμ ε hε
  obtain ⟨i, hi⟩ := psl_exists_chain ω k hω μ hμ
  obtain ⟨w, h1, h2, h3⟩ := psl_perturbation ω k hk hω μ hμ i hi 1 one_pos ε hε
  exact ⟨w, h1, by rw [h2]; exact one_pos, h3⟩
