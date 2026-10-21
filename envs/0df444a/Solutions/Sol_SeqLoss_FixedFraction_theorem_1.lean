-- Prove2me | solution 1 for SeqLoss.FixedFraction.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:58:28.516984+00:00
-- url     : https://prove2.me/submissions/31af32e2-4782-4d53-b891-987489887aa4

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

set_option autoImplicit false
open SeqLoss.FixedFraction

theorem slf_homog (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hadd : Additive φ) (n : ℕ) (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ) (α : ℝ) (hα : 0 ≤ α) :
    φ n (α • ℓ) = α • φ n ℓ := by
  have hsm : ∀ (c : ℝ) (m : Fin n → ℝ), 0 ≤ c → IsLoss m → IsLoss (c • m) := by
    intro c m hc hm i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hc (hm i)
  have hz : IsLoss (0 : Fin n → ℝ) := fun i => le_rfl
  have h0 : φ n 0 = 0 := by
    have := hadd n 0 0 hz hz
    simpa using this
  have hnat : ∀ m : ℕ, ∀ ℓ' : Fin n → ℝ, IsLoss ℓ' → φ n ((m : ℝ) • ℓ') = (m : ℝ) • φ n ℓ' := by
    intro m ℓ' hℓ'
    induction m with
    | zero => simp [h0]
    | succ m ih =>
      push_cast
      rw [add_smul, one_smul, hadd n _ _ (hsm _ _ (Nat.cast_nonneg m) hℓ') hℓ', ih, add_smul, one_smul]
  have hrat : ∀ p q : ℕ, 0 < q → φ n (((p : ℝ) / q) • ℓ) = ((p : ℝ) / q) • φ n ℓ := by
    intro p q hq
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have h1 := hnat q (((p : ℝ) / q) • ℓ) (hsm _ _ (by positivity) hℓ)
    have e : (q : ℝ) • (((p : ℝ) / q) • ℓ) = (p : ℝ) • ℓ := by
      rw [smul_smul]; congr 1; field_simp
    rw [e, hnat p ℓ hℓ] at h1
    apply smul_right_injective (Fin n → ℝ) hq0
    simp only []
    rw [← h1, smul_smul]
    congr 1
    field_simp
  rcases hα.eq_or_lt with h | hαpos
  · subst h; simp [h0]
  have hl' : IsLoss (α • ℓ) := hsm _ _ hα hℓ
  -- rational approximations
  set r : ℕ → ℝ := fun k => (⌊α * ((k : ℝ) + 1)⌋₊ : ℝ) / ((k : ℝ) + 1) with hr
  have hk : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hr_le : ∀ k : ℕ, r k ≤ α := by
    intro k
    rw [hr]; simp only []
    rw [div_le_iff₀ (hk k)]
    exact Nat.floor_le (by positivity)
  have hr_ge : ∀ k : ℕ, α - 1 / ((k : ℝ) + 1) ≤ r k := by
    intro k
    rw [hr]; simp only []
    have h := Nat.lt_floor_add_one (α * ((k : ℝ) + 1))
    rw [le_div_iff₀ (hk k), sub_mul, one_div, inv_mul_cancel₀ (hk k).ne']
    linarith
  have hr_tend : Filter.Tendsto r Filter.atTop (nhds α) := by
    have hup : Filter.Tendsto (fun k : ℕ => α - 1 / ((k : ℝ) + 1)) Filter.atTop (nhds (α - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hup tendsto_const_nhds hr_ge hr_le
  have ha_tend : Filter.Tendsto (fun k => r k / α) Filter.atTop (nhds 1) := by
    have := hr_tend.div_const α
    rwa [div_self hαpos.ne'] at this
  have hcont := (hφ n (α • ℓ) hl').2
  have hlim1 : Filter.Tendsto (fun k => φ n ((r k / α) • (α • ℓ))) Filter.atTop (nhds (φ n (α • ℓ))) :=
    hcont.comp ha_tend
  have hlim2 : Filter.Tendsto (fun k => φ n ((r k / α) • (α • ℓ))) Filter.atTop (nhds (α • φ n ℓ)) := by
    have : ∀ k, φ n ((r k / α) • (α • ℓ)) = r k • φ n ℓ := by
      intro k
      have e : (r k / α) • (α • ℓ) = (((⌊α * ((k : ℝ) + 1)⌋₊ : ℕ) : ℝ) / (((k + 1 : ℕ)) : ℝ)) • ℓ := by
        rw [smul_smul, div_mul_cancel₀ _ hαpos.ne']
        simp only [hr]
        push_cast
        rfl
      rw [e, hrat _ (k + 1) (by omega)]
      simp only [hr]
      push_cast
      rfl
    simp_rw [this]
    exact hr_tend.smul_const _
  exact tendsto_nhds_unique hlim1 hlim2


theorem slf_notliable (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ))
    (hφ : IsRule φ) (hzt : ZeroTruncation φ) (n : ℕ) (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ)
    (h i : Fin n) (hhi : h < i) (hsingle : ∀ j, j ≠ h → ℓ j = 0) :
    φ n ℓ i = 0 := by
  obtain ⟨hnn, hpre, htot⟩ := (hφ n ℓ hℓ).1
  have hlt : h.val + 1 < n := by
    have := hhi; rw [Fin.lt_def] at this; have := i.isLt; omega
  have hp := hpre h.val hlt
  have hL : ∑ j, ℓ j = ℓ h := by
    rw [Finset.sum_eq_single h]
    · intro j _ hj; exact hsingle j hj
    · intro hh; exact absurd (Finset.mem_univ h) hh
  have hpre' : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ h.val), ℓ j = ℓ h := by
    rw [Finset.sum_eq_single h]
    · intro j _ hj; exact hsingle j hj
    · intro hh; exact absurd (by simp) hh
  rw [hpre'] at hp
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j.val ≤ h.val)] at htot
  rw [hL] at htot
  have hrest : ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val ≤ h.val), φ n ℓ j ≤ 0 := by linarith
  have hi' : i ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val ≤ h.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact hhi
  have := Finset.single_le_sum (f := φ n ℓ) (fun j _ => hnn j) hi'
  linarith [hnn i]


theorem slf_isLoss_elem (n : ℕ) : IsLoss (elem n) := by
  intro i; unfold elem; split_ifs <;> norm_num

theorem slf_sum_elem (n : ℕ) (hn : 1 ≤ n) : ∑ i, elem n i = 1 := by
  rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
  · simp [elem]; omega
  · intro j _ hj
    have : j.val ≠ n - 1 := fun h => hj (Fin.ext h)
    unfold elem
    rw [if_neg (by omega)]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem slf_phi2_e3 (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hmp : MergingProof φ) : φ 3 (elem 3) 1 = 0 := by
  obtain ⟨h1, h2⟩ := hmp
  have e3 := (hφ 3 (elem 3) (slf_isLoss_elem 3)).1
  have e2 := (hφ 2 (elem 2) (slf_isLoss_elem 2)).1
  obtain ⟨nn3, -, t3⟩ := e3
  obtain ⟨nn2, -, t2⟩ := e2
  rw [slf_sum_elem 3 (by norm_num), Fin.sum_univ_three] at t3
  rw [slf_sum_elem 2 (by norm_num), Fin.sum_univ_two] at t2
  have a0 := nn3 0
  have a1 := nn3 1
  have a2 := nn3 2
  exact le_antisymm (by linarith) a1

/-- first-component of `e_m` is non-increasing in m (for m ≥ 3 index 1 goes down) -/
theorem slf_B (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) :
    ∀ m : ℕ, 3 ≤ m → ∀ i : Fin m, i.val = 1 → φ m (elem m) i ≤ 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro i hi
    have : i = 1 := Fin.ext (by simpa using hi)
    subst this
    exact (slf_phi2_e3 φ hφ hmp).le
  | succ m hm ih =>
    intro i hi
    have h := (hpm m 2 (by norm_num) (by omega) ⟨1, by omega⟩ ⟨m - 1, by omega⟩ (by simp) (by simp; omega)).1
    have hi' : i = (⟨1, by omega⟩ : Fin m).castSucc := Fin.ext (by simpa using hi)
    rw [hi']
    exact h.trans (ih ⟨1, by omega⟩ rfl)

theorem slf_C (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hpm : PopulationMonotone φ)
    (n : ℕ) (k : Fin n) (hk : 1 ≤ k.val) :
    φ (n + 1) (elem (n + 1)) k.succ ≤ φ n (elem n) k := by
  have hn : 1 < n := by have := k.isLt; omega
  exact (hpm n 1 le_rfl hn ⟨0, by omega⟩ k (by simp) (by omega)).2

theorem slf_inter (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) :
    ∀ (n : ℕ) (i : Fin n), 1 ≤ i.val → i.val + 1 < n → φ n (elem n) i = 0 := by
  have S : ∀ c n : ℕ, ∀ i : Fin (n + 1), i.val = c + 1 → i.val + 1 < n + 1 →
      φ (n + 1) (elem (n + 1)) i ≤ 0 := by
    intro c
    induction c with
    | zero =>
      intro n i hi hin
      exact slf_B φ hφ hpm hmp (n + 1) (by omega) i hi
    | succ c ih =>
      intro n i hi hin
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hk : c + 1 < n' + 1 := by omega
      have hi' : i = (⟨c + 1, hk⟩ : Fin (n' + 1)).succ := Fin.ext (by simpa using hi)
      rw [hi']
      refine (slf_C φ hpm (n' + 1) ⟨c + 1, hk⟩ (by simp)).trans ?_
      exact ih n' ⟨c + 1, hk⟩ rfl (by simp; omega)
  intro n i h1 h2
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, i.val = c + 1 := ⟨i.val - 1, by omega⟩
  exact le_antisymm (S c n' i hc h2) ((hφ _ (elem _) (slf_isLoss_elem _)).1.1 i)
theorem slf_ab_sum (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) (n : ℕ) (hn : 2 ≤ n) :
    φ n (elem n) ⟨0, by omega⟩ + φ n (elem n) ⟨n - 1, by omega⟩ = 1 := by
  have t := (hφ n (elem n) (slf_isLoss_elem n)).1.2.2
  rw [slf_sum_elem n (by omega)] at t
  rw [← t]
  symm
  apply Finset.sum_eq_add (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
  · intro h; have := congrArg Fin.val h; simp at this; omega
  · intro c _ hc
    apply slf_inter φ hφ hpm hmp
    · by_contra hcon
      apply hc.1
      exact Fin.ext (by simp; omega)
    · by_contra hcon
      apply hc.2
      exact Fin.ext (by simp; omega)
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem slf_endpoints (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) (n : ℕ) (hn : 2 ≤ n) :
    φ n (elem n) ⟨0, by omega⟩ = φ 2 (elem 2) 0 ∧
    φ n (elem n) ⟨n - 1, by omega⟩ = φ 2 (elem 2) 1 := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ n hn ih =>
    have h1 := (hpm n 1 le_rfl (by omega) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ (by simp) (by simp; omega)).1
    have h2 := (hpm n 1 le_rfl (by omega) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ (by simp) (by simp; omega)).2
    have s1 := slf_ab_sum φ hφ hpm hmp n hn
    have s2 := slf_ab_sum φ hφ hpm hmp (n + 1) (by omega)
    have e1 : (⟨0, by omega⟩ : Fin (n + 1)) = (⟨0, by omega⟩ : Fin n).castSucc := rfl
    have e2 : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = (⟨n - 1, by omega⟩ : Fin n).succ :=
      Fin.ext (by simp; omega)
    rw [e1] at s2 ⊢
    rw [e2] at s2 ⊢
    constructor
    · linarith [ih.1]
    · linarith [ih.2]
theorem slf_ff_elem (lam : ℝ) (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    fixedFraction lam n (elem n) i =
      if i.val = 0 then 1 - lam else if i.val + 1 = n then lam else 0 := by
  unfold fixedFraction
  rw [slf_sum_elem n (by omega)]
  by_cases h0 : i.val = 0
  · have : ¬ (i.val + 1 = n) := by omega
    have hn1 : ¬ (1 = n) := by omega
    simp [elem, h0, this, hn1]
  · by_cases h1 : i.val + 1 = n
    · simp [elem, h0, h1]
    · simp [elem, h0, h1]

theorem slf_ffinter (lam : ℝ) (n : ℕ) (hn : 2 ≤ n) (i : Fin n) (h1 : 1 ≤ i.val) (h2 : i.val + 1 < n) :
    fixedFraction lam n (elem n) i = 0 := by
  rw [slf_ff_elem lam n hn]
  rw [if_neg (by omega), if_neg (by omega)]
theorem slf_prop2 (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) :
    (PopulationMonotone φ ∧ MergingProof φ) ↔
    ∃ lam ∈ Set.Icc (0:ℝ) 1, ∀ n : ℕ, φ n (elem n) = fixedFraction lam n (elem n) := by
  constructor
  · rintro ⟨hpm, hmp⟩
    have hs := slf_ab_sum φ hφ hpm hmp 2 le_rfl
    have n0 := (hφ 2 (elem 2) (slf_isLoss_elem 2)).1.1 0
    have n1 := (hφ 2 (elem 2) (slf_isLoss_elem 2)).1.1 1
    have hs' : φ 2 (elem 2) 0 + φ 2 (elem 2) 1 = 1 := hs
    refine ⟨φ 2 (elem 2) 1, ⟨n1, by linarith⟩, ?_⟩
    intro n
    funext i
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact i.elim0
      · have t := (hφ 1 (elem 1) (slf_isLoss_elem 1)).1.2.2
        rw [slf_sum_elem 1 le_rfl] at t
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at t
        rw [t]
        simp [fixedFraction, elem]
    · rw [slf_ff_elem _ n hn]
      obtain ⟨e0, e1⟩ := slf_endpoints φ hφ hpm hmp n hn
      by_cases h0 : i.val = 0
      · rw [if_pos h0]
        have : i = ⟨0, by omega⟩ := Fin.ext h0
        rw [this, e0]; linarith
      · rw [if_neg h0]
        by_cases h1 : i.val + 1 = n
        · rw [if_pos h1]
          have : i = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [this, e1]
        · rw [if_neg h1]
          exact slf_inter φ hφ hpm hmp n i (by omega) (by omega)
  · rintro ⟨lam, ⟨hl0, hl1⟩, h⟩
    constructor
    · intro n j hj1 hjn i k hi hk
      have hn2 : 2 ≤ n := by omega
      have e1 := h (n + 1)
      have e2 := h n
      have c1 : ∀ x : Fin (n + 1), φ (n + 1) (elem (n + 1)) x =
          if x.val = 0 then 1 - lam else if x.val + 1 = n + 1 then lam else 0 := by
        intro x; rw [e1, slf_ff_elem lam (n + 1) (by omega)]
      have c2 : ∀ x : Fin n, φ n (elem n) x =
          if x.val = 0 then 1 - lam else if x.val + 1 = n then lam else 0 := by
        intro x; rw [e2, slf_ff_elem lam n hn2]
      constructor
      · rw [c1, c2]
        simp only [Fin.val_castSucc]
        by_cases h0 : i.val = 0
        · simp [h0]
        · have hA : ¬ (i.val + 1 = n + 1) := by omega
          have hB : ¬ (i.val + 1 = n) := by omega
          rw [if_neg h0, if_neg h0, if_neg hA, if_neg hB]
      · rw [c1, c2]
        simp only [Fin.val_succ]
        have hk0 : ¬ (k.val = 0) := by omega
        have hk0' : ¬ (k.val + 1 = 0) := by omega
        rw [if_neg hk0', if_neg hk0]
        by_cases hl : k.val + 1 = n
        · rw [if_pos (by omega : k.val + 1 + 1 = n + 1), if_pos hl]
        · rw [if_neg (by omega : ¬ (k.val + 1 + 1 = n + 1)), if_neg hl]
    · have e3 := h 3
      have e2 := h 2
      have c3 : ∀ x : Fin 3, φ 3 (elem 3) x =
          if x.val = 0 then 1 - lam else if x.val + 1 = 3 then lam else 0 := by
        intro x; rw [e3, slf_ff_elem lam 3 (by omega)]
      have c2 : ∀ x : Fin 2, φ 2 (elem 2) x =
          if x.val = 0 then 1 - lam else if x.val + 1 = 2 then lam else 0 := by
        intro x; rw [e2, slf_ff_elem lam 2 le_rfl]
      constructor
      · rw [c3, c3, c2]; simp
      · rw [c3, c3, c2]; simp


noncomputable def slfUnit (n j : ℕ) : Fin n → ℝ := fun x => if x.val = j then 1 else 0

lemma slf_unit_loss (n j : ℕ) : IsLoss (slfUnit n j) := by
  intro x; unfold slfUnit; split_ifs <;> norm_num

lemma slf_add_loss {n : ℕ} {ℓ ℓ' : Fin n → ℝ} (h : IsLoss ℓ) (h' : IsLoss ℓ') : IsLoss (ℓ + ℓ') :=
  fun i => add_nonneg (h i) (h' i)

lemma slf_snoc_loss {n : ℕ} {ℓ : Fin n → ℝ} (h : IsLoss ℓ) :
    IsLoss (Fin.snoc ℓ 0 : Fin (n + 1) → ℝ) := by
  intro x
  refine Fin.lastCases ?_ (fun y => ?_) x
  · simp
  · simp [Fin.snoc_castSucc]; exact h y

lemma slf_unit_zt (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hzt : ZeroTruncation φ) (j : ℕ) :
    ∀ n (hn : j + 1 ≤ n) (i : Fin n) (hi : i.val ≤ j),
      φ n (slfUnit n j) i = φ (j + 1) (elem (j + 1)) ⟨i.val, by omega⟩ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro i hi
    have : slfUnit (j + 1) j = elem (j + 1) := by
      funext x; simp [slfUnit, elem]
    rw [this]
  | succ n hn ih =>
    intro i hi
    have hlt : i.val < n := by omega
    have hu : slfUnit (n + 1) j = (Fin.snoc (slfUnit n j) 0 : Fin (n + 1) → ℝ) := by
      funext x
      refine Fin.lastCases ?_ (fun y => ?_) x
      · simp [slfUnit]; omega
      · simp [slfUnit, Fin.snoc_castSucc]
    show φ (n + 1) (slfUnit (n + 1) j) (⟨i.val, hlt⟩ : Fin n).castSucc = _
    rw [hu, hzt n (slfUnit n j) (slf_unit_loss n j) ⟨i.val, hlt⟩]
    exact ih ⟨i.val, hlt⟩ hi

lemma slf_sum_additive (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hadd : Additive φ) (n : ℕ)
    {ι : Type} (s : Finset ι) (f : ι → (Fin n → ℝ)) (hf : ∀ k ∈ s, IsLoss (f k)) :
    φ n (∑ k ∈ s, f k) = ∑ k ∈ s, φ n (f k) := by
  classical
  have h0 : φ n 0 = 0 := by
    have := hadd n 0 0 (fun i => le_rfl) (fun i => le_rfl)
    simpa using this
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : IsLoss (∑ k ∈ s, f k) := by
      intro i
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg (fun k hk => hf k (Finset.mem_insert_of_mem hk) i)
    rw [hadd n _ _ (hf a (Finset.mem_insert_self a s)) hs, ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))]

lemma slf_forward (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) (hadd : Additive φ)
    (hzt : ZeroTruncation φ) (n : ℕ) (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ) (i : Fin n) :
    φ n ℓ i = ∑ j : Fin n,
        if h : i ≤ j then ℓ j * φ (j.val + 1) (elem (j.val + 1)) ⟨i.val, Nat.lt_succ_of_le h⟩
        else 0 := by
  have hdec : ∑ j : Fin n, ℓ j • slfUnit n j.val = ℓ := by
    funext x
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp [slfUnit]
    · intro j _ hj
      have : x.val ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [slfUnit, this]
    · intro h; exact absurd (Finset.mem_univ x) h
  have hstep : φ n ℓ i = ∑ j : Fin n, ℓ j * φ n (slfUnit n j.val) i := by
    conv_lhs => rw [← hdec]
    rw [slf_sum_additive φ hadd n Finset.univ _ (fun k _ => by
      intro x; simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (hℓ k) (slf_unit_loss n _ x))]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [slf_homog φ hφ hadd n _ (slf_unit_loss n _) (ℓ j) (hℓ j)]
    simp
  rw [hstep]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i ≤ j
  · rw [dif_pos hij]
    congr 1
    exact slf_unit_zt φ hzt j.val n (by omega) i (Fin.le_def.mp hij)
  · rw [dif_neg hij]
    have : φ n (slfUnit n j.val) i = 0 := by
      apply slf_notliable φ hφ hzt n _ (slf_unit_loss n _) j i (not_le.1 hij)
      intro k hk
      have : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp [slfUnit, this]
    rw [this]; simp

lemma slf_backward (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ))
    (hform : ∀ n (ℓ : Fin n → ℝ), IsLoss ℓ → ∀ i : Fin n, φ n ℓ i = ∑ j : Fin n,
        if h : i ≤ j then ℓ j * φ (j.val + 1) (elem (j.val + 1)) ⟨i.val, Nat.lt_succ_of_le h⟩
        else 0) : Additive φ ∧ ZeroTruncation φ := by
  constructor
  · intro n ℓ ℓ' h h'
    funext i
    rw [Pi.add_apply, hform n _ (slf_add_loss h h') i, hform n ℓ h i, hform n ℓ' h' i,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i ≤ j
    · simp [hij, add_mul]
    · simp [hij]
  · intro n ℓ hℓ i
    rw [hform (n + 1) _ (slf_snoc_loss hℓ) i.castSucc, hform n ℓ hℓ i, Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc]

theorem slf_prop1 (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) :
    (Additive φ ∧ ZeroTruncation φ) ↔
    ∀ n (ℓ : Fin n → ℝ), IsLoss ℓ → ∀ i : Fin n,
      φ n ℓ i = ∑ j : Fin n,
        if h : i ≤ j then ℓ j * φ (j.val + 1) (elem (j.val + 1)) ⟨i.val, Nat.lt_succ_of_le h⟩
        else 0 := by
  constructor
  · rintro ⟨hadd, hzt⟩ n ℓ hℓ i
    exact slf_forward φ hφ hadd hzt n ℓ hℓ i
  · intro h
    exact slf_backward φ h


lemma slf_ff_val (lam : ℝ) (n : ℕ) (ℓ : Fin n → ℝ) (i : Fin n) :
    fixedFraction lam n ℓ i = lam * ℓ i + if i.val = 0 then (1 - lam) * ∑ j, ℓ j else 0 := rfl

theorem solution (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) :
    (Additive φ ∧ ZeroTruncation φ ∧ MergingProof φ ∧ PopulationMonotone φ) ↔
    ∃ lam ∈ Set.Icc (0:ℝ) 1,
      ∀ n (ℓ : Fin n → ℝ), IsLoss ℓ → φ n ℓ = fixedFraction lam n ℓ := by
  constructor
  · rintro ⟨hadd, hzt, hmp, hpm⟩
    obtain ⟨lam, hlam, hel⟩ := (slf_prop2 φ hφ).1 ⟨hpm, hmp⟩
    refine ⟨lam, hlam, fun n ℓ hℓ => ?_⟩
    funext i
    rw [slf_forward φ hφ hadd hzt n ℓ hℓ i, slf_ff_val]
    have hterm : ∀ j : Fin n,
        (if h : i ≤ j then ℓ j * φ (j.val + 1) (elem (j.val + 1)) ⟨i.val, Nat.lt_succ_of_le h⟩
          else 0) =
        lam * (if j = i then ℓ j else 0) + (if i.val = 0 then (1 - lam) * ℓ j else 0) := by
      intro j
      by_cases hij : i ≤ j
      · rw [dif_pos hij]
        have h1 := congrFun (hel (j.val + 1)) ⟨i.val, Nat.lt_succ_of_le hij⟩
        rw [h1, slf_ff_val, slf_sum_elem (j.val + 1) (by omega)]
        have hij' : i.val ≤ j.val := Fin.le_def.mp hij
        by_cases hji : j = i
        · subst hji
          by_cases h0 : j.val = 0
          · simp [elem, h0]; ring
          · simp [elem, h0]; ring
        · have hne : i.val + 1 ≠ j.val + 1 := fun h => hji (Fin.ext (by omega)).symm
          have : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
          by_cases h0 : i.val = 0
          · have hj0 : j.val ≠ 0 := fun h => this (by omega)
            simp [elem, h0, hji, this, hj0]; ring
          · simp [elem, h0, hji, this]
      · rw [dif_neg hij]
        have hji : j ≠ i := fun h => hij (h ▸ le_rfl)
        have h0 : i.val ≠ 0 := by
          have := not_le.1 hij
          rw [Fin.lt_def] at this
          omega
        simp [hji, h0]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]
    by_cases h0 : i.val = 0
    · simp [h0, ← Finset.mul_sum]
    · simp [h0]
  · rintro ⟨lam, hlam, hform⟩
    have hadd : Additive φ := by
      intro n ℓ ℓ' h h'
      rw [hform n _ (slf_add_loss h h'), hform n ℓ h, hform n ℓ' h']
      funext i
      simp only [fixedFraction, Pi.add_apply, Finset.sum_add_distrib]
      split_ifs <;> ring
    have hzt : ZeroTruncation φ := by
      intro n ℓ hℓ i
      rw [hform (n + 1) _ (slf_snoc_loss hℓ), hform n ℓ hℓ]
      simp only [fixedFraction, Fin.coe_castSucc, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, add_zero]
    obtain ⟨hpm, hmp⟩ := (slf_prop2 φ hφ).2 ⟨lam, hlam, fun n => hform n (elem n) (slf_isLoss_elem n)⟩
    exact ⟨hadd, hzt, hmp, hpm⟩
