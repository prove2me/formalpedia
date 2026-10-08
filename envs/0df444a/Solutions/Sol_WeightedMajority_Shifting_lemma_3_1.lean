-- Prove2me | solution 1 for WeightedMajority.Shifting.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:01:27.09491+00:00
-- url     : https://prove2.me/submissions/d3f98413-0e29-40ed-975e-dfdc4195d760

import Mathlib
import Definitions.Def_WeightedMajority_Shifting_WML



namespace WeightedMajority.Shifting

open Finset

lemma wml_pos {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam) : ∀ k, k ≤ T → ∀ i, 0 < w k i := by
  intro k
  induction k with
  | zero => intro _ i; exact hrun.init_pos i
  | succ k ih =>
    intro hk i
    have := hrun.update ⟨k, by omega⟩
    simp only at this
    rw [this]
    have h := ih (by omega) i
    unfold wmlUpdate
    split_ifs
    · positivity
    · exact h

lemma wml_total_nonneg {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam) (k : ℕ) (hk : k ≤ T) : 0 ≤ totalWeight (w k) :=
  Finset.sum_nonneg (fun i _ => (wml_pos hβ0 hrun k hk i).le)

lemma ratio_core {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam) (t : Fin T) (hmis : lam t ≠ ρ t) :
    totalWeight (w ((t : ℕ) + 1)) ≤ uFactor β γ * totalWeight (w t) := by
  have hW : 0 ≤ totalWeight (w t) := wml_total_nonneg hβ0 hrun t (by omega)
  have hpred := hrun.predict t
  have hupd := hrun.update t
  generalize hl : lam t = l at *
  generalize hr : ρ t = r at *
  generalize ha : w t = a at *
  have hb : ∀ b : Bool, b = r ↔ ¬ b = l := by
    revert hmis; intro hmis; intro b; cases b <;> cases l <;> cases r <;> simp at hmis ⊢
  obtain ⟨h1, h2⟩ := hpred
  have hq : voteWeight a (x t) r ≤ voteWeight a (x t) l := by
    by_contra hc
    have hc := not_le.1 hc
    cases l <;> cases r
    · exact absurd rfl hmis
    · exact absurd (h2 hc) (by simp)
    · exact absurd (h1 hc) (by simp)
    · exact absurd rfl hmis
  have hsplit : voteWeight a (x t) l + voteWeight a (x t) r = totalWeight a := by
    unfold voteWeight totalWeight
    have : univ.filter (fun i => x t i = r) = univ.filter (fun i => ¬ x t i = l) :=
      Finset.filter_congr (fun i _ => hb _)
    rw [this]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  set W := totalWeight a with hWdef
  -- pointwise bound
  have hpt : ∀ i ∈ univ.filter (fun i => x t i = l),
      a i ≤ (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) + γ / n * W := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    have hxr : x t i ≠ r := by
      intro h; exact (hb _).1 h hi
    by_cases hc : (γ / (n : ℝ)) * W < a i
    · rw [if_pos ⟨hmis, hxr, hc⟩]
      have : 0 ≤ γ / n * W := by positivity
      linarith
    · rw [if_neg (fun h => hc h.2.2)]; push_neg at hc; linarith
  have hsum := Finset.sum_le_sum hpt
  have hn : 0 < n ∨ n = 0 := by omega
  have hcard : ∑ i ∈ univ.filter (fun i => x t i = l), (γ / n * W) ≤ γ * W := by
    rcases hn with hn | hn
    · rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((univ.filter (fun i => x t i = l)).card : ℝ) ≤ n := by
        have := Finset.card_filter_le (univ : Finset (Fin n)) (fun i => x t i = l)
        simpa using this
      have hnr : (0:ℝ) < n := by exact_mod_cast hn
      have : 0 ≤ γ / n * W := by positivity
      calc _ ≤ (n:ℝ) * (γ / n * W) := mul_le_mul_of_nonneg_right hc this
        _ = γ * W := by field_simp
    · subst hn
      simp
      positivity
  rw [Finset.sum_add_distrib] at hsum
  have hite : ∑ i ∈ univ.filter (fun i => x t i = l),
      (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0)
      = ∑ i, (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hx : x t i = l
    · simp [hx]
    · have hxr : x t i = r := (hb _).2 hx
      simp [hxr]
  have hpt2 : ∀ i, wmlUpdate β γ a (x t) r l i = a i - (1 - β) *
      (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) := by
    intro i
    simp only [wmlUpdate, ← hWdef]
    split_ifs <;> ring
  have hnew : totalWeight (w ((t : ℕ) + 1)) = W - (1 - β) *
      ∑ i, (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) := by
    rw [hupd]
    unfold totalWeight
    simp only [hpt2]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; rfl
  rw [hnew]
  rw [hite] at hsum
  have hu : uFactor β γ = (1 + β) / 2 + (1 - β) * γ := rfl
  rw [hu]
  have h1β : 0 < 1 - β := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (show W / 2 - γ * W ≤ ∑ i, (if (l ≠ r ∧ x t i ≠ r ∧ (γ / (n : ℝ)) * W < a i) then a i else 0) by
    unfold voteWeight at hq hsplit; linarith) h1β.le]


lemma wml_mono {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam) (t : Fin T) (i : Fin n) :
    β * w t i ≤ w ((t : ℕ) + 1) i ∧ w ((t : ℕ) + 1) i ≤ w t i := by
  have hp := wml_pos hβ0 hrun t (by omega) i
  rw [hrun.update t]
  unfold wmlUpdate
  split_ifs
  · exact ⟨le_rfl, by nlinarith⟩
  · exact ⟨by nlinarith, le_rfl⟩

lemma floor_core {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam)
    (hfloor : ∀ i, β * γ / (n : ℝ) * totalWeight (w 0) ≤ w 0 i) :
    ∀ k, k ≤ T → ∀ i, β * γ / (n : ℝ) * totalWeight (w k) ≤ w k i := by
  intro k
  induction k with
  | zero => intro _; exact hfloor
  | succ k ih =>
    intro hk i
    have hkT : k < T := by omega
    set t : Fin T := ⟨k, hkT⟩
    have hWle : totalWeight (w (k+1)) ≤ totalWeight (w k) :=
      Finset.sum_le_sum (fun j _ => (wml_mono hβ0 hβ1 hrun t j).2)
    have hc : 0 ≤ β * γ / (n : ℝ) := by positivity
    have h0 := ih (by omega) i
    have hupd := hrun.update t
    have hi : w (k+1) i = wmlUpdate β γ (w k) (x t) (ρ t) (lam t) i := by
      rw [hupd]
    rw [hi]
    unfold wmlUpdate
    split_ifs with hcond
    · have h3 := hcond.2.2
      have : β * (γ / (n:ℝ) * totalWeight (w k)) < β * w k i := by nlinarith
      calc β * γ / (n : ℝ) * totalWeight (w (k+1)) ≤ β * γ / (n : ℝ) * totalWeight (w k) :=
            mul_le_mul_of_nonneg_left hWle hc
        _ = β * (γ / (n:ℝ) * totalWeight (w k)) := by ring
        _ ≤ _ := this.le
    · calc β * γ / (n : ℝ) * totalWeight (w (k+1)) ≤ β * γ / (n : ℝ) * totalWeight (w k) :=
            mul_le_mul_of_nonneg_left hWle hc
        _ ≤ _ := h0

def cnt {n T : ℕ} (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (i : Fin n) (k : ℕ) : ℕ :=
  (univ.filter (fun t : Fin T => (t : ℕ) < k ∧ x t i ≠ ρ t)).card

lemma cnt_succ {n T : ℕ} (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (i : Fin n) (k : ℕ)
    (hk : k < T) :
    (x ⟨k, hk⟩ i = ρ ⟨k, hk⟩ → cnt x ρ i (k+1) = cnt x ρ i k) ∧
    (x ⟨k, hk⟩ i ≠ ρ ⟨k, hk⟩ → cnt x ρ i (k+1) = cnt x ρ i k + 1) := by
  constructor
  · intro h
    unfold cnt
    congr 1
    ext t
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
      · exact h3
      · exfalso; apply h2; have : t = ⟨k, hk⟩ := Fin.ext h3
        rw [this]; exact h
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · intro h
    unfold cnt
    have : univ.filter (fun t : Fin T => (t : ℕ) < k + 1 ∧ x t i ≠ ρ t) =
        insert ⟨k, hk⟩ (univ.filter (fun t : Fin T => (t : ℕ) < k ∧ x t i ≠ ρ t)) := by
      ext t
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
        · exact Or.inr ⟨h3, h2⟩
        · exact Or.inl (Fin.ext h3)
      · rintro (h1 | ⟨h1, h2⟩)
        · subst h1; exact ⟨by simp, h⟩
        · exact ⟨by omega, h2⟩
    rw [this, Finset.card_insert_of_notMem]
    simp

lemma member_core {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam) (i : Fin n) :
    ∀ k, k ≤ T → β ^ (cnt x ρ i k) * w 0 i ≤ w k i := by
  intro k
  induction k with
  | zero =>
    intro _
    have : cnt x ρ i 0 = 0 := by simp [cnt]
    simp [this]
  | succ k ih =>
    intro hk
    have hkT : k < T := by omega
    have h0 := ih (by omega)
    have hm := wml_mono hβ0 hβ1 hrun ⟨k, hkT⟩ i
    simp only at hm
    obtain ⟨c1, c2⟩ := cnt_succ x ρ i k hkT
    by_cases hx : x ⟨k, hkT⟩ i = ρ ⟨k, hkT⟩
    · rw [c1 hx]
      have : w (k+1) i = w k i := by
        rw [hrun.update ⟨k, hkT⟩]
        unfold wmlUpdate
        rw [if_neg]
        rintro ⟨_, h, _⟩; exact h hx
      rw [this]; exact h0
    · rw [c2 hx, pow_succ]
      have : 0 < β ^ cnt x ρ i k * w 0 i := by
        have := hrun.init_pos i; positivity
      nlinarith

lemma main_core {n T : ℕ} (hn : 0 < n) {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam)
    (hfloor : ∀ i, β * γ / (n : ℝ) * totalWeight (w 0) ≤ w 0 i) :
    (masterMistakes ρ lam : ℝ) ≤
        (Real.log ((n : ℝ) / (β * γ)) + (bestMistakesOn x ρ 0 T : ℝ) * Real.log (1 / β)) /
          Real.log (1 / uFactor β γ) ∧
      ∀ i, β * γ / (n : ℝ) * totalWeight (w T) ≤ w T i := by
  refine ⟨?_, floor_core hβ0 hβ1 hγ0.le hrun hfloor T le_rfl⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i : Fin n => memberMistakesOn x ρ 0 T i)
  have hbest : bestMistakesOn x ρ 0 T = cnt x ρ i T := by
    unfold bestMistakesOn
    rw [← hi]
    unfold memberMistakesOn cnt
    congr 1
    ext t; simp
  set m := cnt x ρ i T
  set M := masterMistakes ρ lam
  have hu1 : uFactor β γ < 1 := by unfold uFactor; nlinarith
  have hu0 : 0 < uFactor β γ := by unfold uFactor; nlinarith
  have hlogu : 0 < Real.log (1 / uFactor β γ) := Real.log_pos (by rw [lt_div_iff₀ hu0]; linarith)
  rw [le_div_iff₀ hlogu, hbest]
  -- total weight bound
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hW0 : 0 < totalWeight (w 0) :=
    Finset.sum_pos (fun i _ => hrun.init_pos i) ⟨⟨0, hn⟩, mem_univ _⟩
  have hWM : ∀ k, k ≤ T → totalWeight (w k) ≤
      uFactor β γ ^ (univ.filter (fun t : Fin T => (t : ℕ) < k ∧ lam t ≠ ρ t)).card *
        totalWeight (w 0) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkT : k < T := by omega
      have h0 := ih (by omega)
      by_cases hm : lam ⟨k, hkT⟩ = ρ ⟨k, hkT⟩
      · have heq : totalWeight (w (k+1)) = totalWeight (w k) := by
          unfold totalWeight
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hrun.update ⟨k, hkT⟩]
          unfold wmlUpdate
          rw [if_neg]
          rintro ⟨h, _⟩; exact h hm
        have hc : (univ.filter (fun t : Fin T => (t : ℕ) < k + 1 ∧ lam t ≠ ρ t)) =
            (univ.filter (fun t : Fin T => (t : ℕ) < k ∧ lam t ≠ ρ t)) := by
          ext t
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨?_, h2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
            · exact h3
            · exfalso; apply h2; have : t = ⟨k, hkT⟩ := Fin.ext h3
              rw [this]; exact hm
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        rw [hc, heq]; exact h0
      · have hr := ratio_core hβ0 hβ1 hγ0.le hγ1 x ρ w lam hrun ⟨k, hkT⟩ hm
        simp only at hr
        have hc : (univ.filter (fun t : Fin T => (t : ℕ) < k + 1 ∧ lam t ≠ ρ t)) =
            insert ⟨k, hkT⟩ (univ.filter (fun t : Fin T => (t : ℕ) < k ∧ lam t ≠ ρ t)) := by
          ext t
          simp only [mem_filter, mem_univ, true_and, mem_insert]
          constructor
          · rintro ⟨h1, h2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
            · exact Or.inr ⟨h3, h2⟩
            · exact Or.inl (Fin.ext h3)
          · rintro (h1 | ⟨h1, h2⟩)
            · subst h1; exact ⟨by simp, hm⟩
            · exact ⟨by omega, h2⟩
        rw [hc, Finset.card_insert_of_notMem (by simp), pow_succ]
        calc totalWeight (w (k+1)) ≤ uFactor β γ * totalWeight (w k) := hr
          _ ≤ uFactor β γ * (uFactor β γ ^ _ * totalWeight (w 0)) :=
              mul_le_mul_of_nonneg_left h0 hu0.le
          _ = _ := by ring
  have hMcard : (univ.filter (fun t : Fin T => (t : ℕ) < T ∧ lam t ≠ ρ t)).card = M := by
    unfold M masterMistakes
    congr 1
    ext t; simp
  have hWT := hWM T le_rfl
  rw [hMcard] at hWT
  have hmem := member_core hβ0 hβ1 hrun i T le_rfl
  have hle : w T i ≤ totalWeight (w T) :=
    Finset.single_le_sum (f := fun j => w T j)
      (fun j _ => (wml_pos hβ0 hrun T le_rfl j).le) (mem_univ i)
  have hf0 := hfloor i
  -- combine: β^m * (βγ/n W0) ≤ u^M W0
  have hkey : β ^ m * (β * γ / n * totalWeight (w 0)) ≤ uFactor β γ ^ M * totalWeight (w 0) := by
    calc β ^ m * (β * γ / n * totalWeight (w 0)) ≤ β ^ m * w 0 i :=
          mul_le_mul_of_nonneg_left hf0 (by positivity)
      _ ≤ w T i := hmem
      _ ≤ _ := hle
      _ ≤ _ := hWT
  have hkey2 : β ^ m * (β * γ / n) ≤ uFactor β γ ^ M := by
    have : (β ^ m * (β * γ / n)) * totalWeight (w 0) ≤ uFactor β γ ^ M * totalWeight (w 0) := by
      linarith
    exact le_of_mul_le_mul_right this hW0
  have hpos : 0 < β ^ m * (β * γ / n) := by positivity
  have hlog := Real.log_le_log hpos hkey2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_div (by positivity) (by positivity), Real.log_mul hβ0.ne' hγ0.ne', Real.log_pow] at hlog
  have e1 : Real.log (1 / β) = - Real.log β := by rw [one_div, Real.log_inv]
  have e2 : Real.log (1 / uFactor β γ) = - Real.log (uFactor β γ) := by rw [one_div, Real.log_inv]
  have e3 : Real.log ((n:ℝ) / (β * γ)) = Real.log n - (Real.log β + Real.log γ) := by
    rw [Real.log_div hnr.ne' (by positivity), Real.log_mul hβ0.ne' hγ0.ne']
  rw [e1, e2, e3]
  nlinarith [hlog]

end WeightedMajority.Shifting

open WeightedMajority.Shifting


theorem solution {n T : ℕ} (hn : 0 < n) {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam)
    (hfloor : ∀ i, β * γ / (n : ℝ) * totalWeight (w 0) ≤ w 0 i) :
    (masterMistakes ρ lam : ℝ) ≤
        (Real.log ((n : ℝ) / (β * γ)) + (bestMistakesOn x ρ 0 T : ℝ) * Real.log (1 / β)) /
          Real.log (1 / uFactor β γ) ∧
      ∀ i, β * γ / (n : ℝ) * totalWeight (w T) ≤ w T i := by
  exact main_core hn hβ0 hβ1 hγ0 hγ1 x ρ w lam hrun hfloor
