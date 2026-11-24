-- Prove2me | solution 1 for PartialResampling.pra_sums
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:47:46.563608+00:00
-- url     : https://prove2.me/submissions/9c6807f7-d8a7-4ff7-91e5-dc8535d4eee5

import Mathlib
import Theorems.Thm_PartialResampling_pra_exists

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace PRAsym

variable {I : Type} [DecidableEq I]

/-- elementary symmetric sum -/
noncomputable def esym (b : I → ℝ) (U : Finset I) (d : ℕ) : ℝ :=
  ∑ S ∈ U.powersetCard d, ∏ i ∈ S, b i

theorem esym_zero (b : I → ℝ) (U : Finset I) : esym b U 0 = 1 := by
  simp [esym]

theorem sum_filter_mem_eq (b : I → ℝ) (U : Finset I) (u : I) (hu : u ∈ U) (d : ℕ) :
    ∑ S ∈ (U.powersetCard (d + 1)).filter (fun S => u ∈ S), ∏ i ∈ S, b i =
      b u * esym b (U.erase u) d := by
  unfold esym
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun S => S.erase u) (fun S => insert u S) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.erase_subset_erase u hS.1.1, ?_⟩
    rw [Finset.card_erase_of_mem hS.2, hS.1.2]; rfl
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    have hnot : u ∉ S := fun h => by
      have := hS.1 h; simp at this
    refine ⟨⟨Finset.insert_subset hu (hS.1.trans (Finset.erase_subset u U)), ?_⟩,
      Finset.mem_insert_self _ _⟩
    rw [Finset.card_insert_of_notMem hnot, hS.2]
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter] at hS
    exact Finset.insert_erase hS.2
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
    have hnot : u ∉ S := fun h => by
      have := hS.1 h; simp at this
    exact Finset.erase_insert hnot
  · intro S hS
    simp only [Finset.mem_filter] at hS
    rw [Finset.mul_prod_erase S b hS.2]

theorem esym_succ_mul (b : I → ℝ) (U : Finset I) (d : ℕ) :
    ((d : ℝ) + 1) * esym b U (d + 1) = ∑ u ∈ U, b u * esym b (U.erase u) d := by
  have h1 : ((d : ℝ) + 1) * esym b U (d + 1) =
      ∑ S ∈ U.powersetCard (d + 1), ∑ u ∈ S, ∏ i ∈ S, b i := by
    unfold esym
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    rw [Finset.sum_const, (Finset.mem_powersetCard.mp hS).2, nsmul_eq_mul]
    push_cast; ring
  rw [h1]
  rw [Finset.sum_comm' (t' := U) (s' := fun u => (U.powersetCard (d + 1)).filter (fun S => u ∈ S))]
  · refine Finset.sum_congr rfl (fun u hu => sum_filter_mem_eq b U u hu d)
  · intro S u
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h1 h3⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, _⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem esym_nonneg (b : I → ℝ) (hb : ∀ i, 0 ≤ b i) (U : Finset I) (d : ℕ) : 0 ≤ esym b U d :=
  Finset.sum_nonneg (fun S _ => Finset.prod_nonneg (fun i _ => hb i))

theorem esym_mono (b : I → ℝ) (hb : ∀ i, 0 ≤ b i) (V U : Finset I) (hVU : V ⊆ U) (d : ℕ) :
    esym b V d ≤ esym b U d :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.powersetCard_mono hVU)
    (fun S _ _ => Finset.prod_nonneg (fun i _ => hb i))

theorem esym_upper (b : I → ℝ) (hb : ∀ i, 0 ≤ b i) :
    ∀ (d : ℕ) (U : Finset I), (d.factorial : ℝ) * esym b U d ≤ (∑ i ∈ U, b i) ^ d
  | 0, U => by simp [esym_zero]
  | d + 1, U => by
    have IH := esym_upper b hb d
    have key := esym_succ_mul b U d
    calc ((d + 1).factorial : ℝ) * esym b U (d + 1)
        = (d.factorial : ℝ) * (((d : ℝ) + 1) * esym b U (d + 1)) := by
          rw [Nat.factorial_succ]; push_cast; ring
      _ = ∑ u ∈ U, b u * ((d.factorial : ℝ) * esym b (U.erase u) d) := by
          rw [key, Finset.mul_sum]; refine Finset.sum_congr rfl (fun u _ => by ring)
      _ ≤ ∑ u ∈ U, b u * (∑ i ∈ U, b i) ^ d := by
          refine Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left ?_ (hb u))
          refine le_trans ?_ (IH U)
          exact mul_le_mul_of_nonneg_left (esym_mono b hb _ _ (Finset.erase_subset u U) d)
            (by positivity)
      _ = (∑ i ∈ U, b i) ^ (d + 1) := by rw [← Finset.sum_mul, pow_succ]; ring

theorem esym_lower (b : I → ℝ) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    ∀ (d : ℕ) (U : Finset I), (d : ℝ) ≤ (∑ i ∈ U, b i) + 1 →
      ∏ j ∈ range d, ((∑ i ∈ U, b i) - j) ≤ (d.factorial : ℝ) * esym b U d
  | 0, U, _ => by simp [esym_zero]
  | d + 1, U, hd => by
    have IH := esym_lower b hb d
    set s := ∑ i ∈ U, b i with hs
    have hsd : (d : ℝ) ≤ s := by push_cast at hd; linarith
    have key := esym_succ_mul b U d
    calc ∏ j ∈ range (d + 1), (s - j) = s * ∏ j ∈ range d, (s - 1 - j) := by
          rw [Finset.prod_range_succ', mul_comm]
          congr 1
          · simp
          · refine Finset.prod_congr rfl (fun j _ => by push_cast; ring)
      _ = ∑ u ∈ U, b u * ∏ j ∈ range d, (s - 1 - j) := by rw [hs, Finset.sum_mul]
      _ ≤ ∑ u ∈ U, b u * ((d.factorial : ℝ) * esym b (U.erase u) d) := by
          refine Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left ?_ (hb u).1)
          have hse : ∑ i ∈ U.erase u, b i = s - b u := by
            rw [hs, ← Finset.sum_erase_add U b hu]; ring
          refine le_trans ?_ (IH (U.erase u) (by rw [hse]; linarith [(hb u).2]))
          rw [hse]
          refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_)
          · have : (j : ℝ) + 1 ≤ d := by
              have := Finset.mem_range.mp hj; exact_mod_cast this
            linarith
          · linarith [(hb u).2]
      _ = ((d + 1).factorial : ℝ) * esym b U (d + 1) := by
          rw [Nat.factorial_succ]; push_cast
          rw [mul_comm ((d : ℝ) + 1), mul_assoc, key, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun u _ => by ring)

end PRAsym


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset PRAsym

namespace PRAsums

variable {I : Type} [Fintype I] [DecidableEq I] {Ω : I → Type} [∀ i, Fintype (Ω i)]
  [∀ i, DecidableEq (Ω i)]

def supp (Y : ∀ i, Option (Ω i)) : Finset I := univ.filter (fun i => (Y i).isSome)

theorem sum_atoms_fiber (h : ∀ i, Ω i → ℝ) (S : Finset I) :
    ∑ Y ∈ univ.filter (fun Y : (∀ i, Option (Ω i)) => supp Y = S), ∏ i, (Y i).elim 1 (h i) =
      ∏ i ∈ S, ∑ ω, h i ω := by
  classical
  let g : ∀ i, Option (Ω i) → ℝ := fun i o => if (o.isSome ↔ i ∈ S) then o.elim 1 (h i) else 0
  have hpt : ∀ Y : (∀ i, Option (Ω i)), (if supp Y = S then ∏ i, (Y i).elim 1 (h i) else 0) =
      ∏ i, g i (Y i) := by
    intro Y
    split_ifs with hY
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      have : ((Y i).isSome ↔ i ∈ S) := by rw [← hY]; simp [supp]
      simp only [g, if_pos this]
    · have : ∃ i, ¬ ((Y i).isSome ↔ i ∈ S) := by
        by_contra hc
        push_neg at hc
        exact hY (by ext i; simp [supp, hc i])
      obtain ⟨i, hi⟩ := this
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [g, if_neg hi])
  rw [Finset.sum_filter]
  simp_rw [hpt]
  rw [← Fintype.prod_sum g]
  have hg : ∀ i, ∑ o, g i o = if i ∈ S then ∑ ω, h i ω else 1 := by
    intro i
    rw [Fintype.sum_option]
    by_cases hi : i ∈ S <;> simp [g, hi]
  simp_rw [hg]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem sum_atoms_card (h : ∀ i, Ω i → ℝ) (d : ℕ) :
    ∑ Y : (∀ i, Option (Ω i)), (if (supp Y).card = d then ∏ i, (Y i).elim 1 (h i) else 0) =
      esym (fun i => ∑ ω, h i ω) univ d := by
  classical
  rw [← Finset.sum_fiberwise (s := univ) (g := supp)]
  unfold esym
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  rw [Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← sum_atoms_fiber h S]
  split_ifs with hS
  · refine Finset.sum_congr rfl (fun Y hY => ?_)
    rw [(Finset.mem_filter.mp hY).2, if_pos hS]
  · refine Finset.sum_eq_zero (fun Y hY => ?_)
    rw [(Finset.mem_filter.mp hY).2, if_neg hS]

theorem sum_atoms_card_mem (h : ∀ i, Ω i → ℝ) (d : ℕ) (u : I) :
    ∑ Y : (∀ i, Option (Ω i)), (if (supp Y).card = d + 1 ∧ (Y u).isSome then
        ∏ i, (Y i).elim 1 (h i) else 0) =
      (∑ ω, h u ω) * esym (fun i => ∑ ω, h i ω) (univ.erase u) d := by
  classical
  rw [← sum_filter_mem_eq (fun i => ∑ ω, h i ω) univ u (Finset.mem_univ u) d]
  rw [← Finset.sum_fiberwise (s := univ) (g := supp)]
  rw [Finset.sum_filter, Finset.powersetCard_eq_filter, Finset.sum_filter, Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← sum_atoms_fiber h S]
  by_cases hS : S.card = d + 1 ∧ u ∈ S
  · rw [if_pos hS.1, if_pos hS.2]
    refine Finset.sum_congr rfl (fun Y hY => ?_)
    have hY' := (Finset.mem_filter.mp hY).2
    have hu : (Y u).isSome := by
      have : u ∈ supp Y := by rw [hY']; exact hS.2
      simpa [supp] using this
    rw [if_pos ⟨by rw [hY']; exact hS.1, hu⟩]
  · have : ∀ Y ∈ univ.filter (fun Y : (∀ i, Option (Ω i)) => supp Y = S),
        (if (supp Y).card = d + 1 ∧ (Y u).isSome then ∏ i, (Y i).elim 1 (h i) else 0) = 0 := by
      intro Y hY
      have hY' := (Finset.mem_filter.mp hY).2
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hS
      refine ⟨by rw [← hY']; exact h1, ?_⟩
      rw [← hY']; simpa [supp] using h2
    rw [Finset.sum_eq_zero this]
    by_cases h1 : S.card = d + 1
    · rw [if_pos h1, if_neg (fun h2 => hS ⟨h1, h2⟩)]
    · rw [if_neg h1]

theorem prod_elim_mul (f g : ∀ i, Ω i → ℝ) (Y : ∀ i, Option (Ω i)) :
    (∏ i, (Y i).elim 1 (f i)) * ∏ i, (Y i).elim 1 (g i) = ∏ i, (Y i).elim 1 (fun ω => f i ω * g i ω) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases Y i <;> simp

theorem prod_elim_const (c : ℝ) (Y : ∀ i, Option (Ω i)) :
    ∏ i, (Y i).elim 1 (fun _ : Ω i => c) = c ^ (supp Y).card := by
  unfold supp
  rw [← Finset.prod_const (s := univ.filter (fun i => (Y i).isSome)) c, Finset.prod_filter]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases Y i <;> simp

theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

end PRAsums

open PRAsym PRAsums in
theorem solution {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
    (Ω : I → Type) [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp : ∀ i ω, 0 < p i ω) (hp1 : ∀ i, ∑ ω, p i ω = 1)
    (a : T → ∀ i, Ω i → ℝ) (ha : ∀ t i ω, 0 ≤ a t i ω ∧ a t i ω ≤ 1)
    (τ : T → ℝ) (d : T → ℕ) (hd : ∀ t, 1 ≤ d t ∧ (d t : ℝ) ≤ τ t)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hS : ∀ t, (Λ * ∑ i, ∑ ω, p i ω * a t i ω) ^ d t ≤
      (∏ j ∈ Finset.range (d t), (τ t - j)) / 4)
    (hG : ∀ i, ∑ t, (d t : ℝ) * (Λ * ∑ ω, p i ω * a t i ω) *
        (Λ * ∑ u, ∑ ω, p u ω * a t u ω) ^ (d t - 1) / ∏ j ∈ Finset.range (d t), (τ t - j) ≤
      Real.log Λ / 2) :
    ∃ z : ∀ i, Ω i, ∀ t, ∑ i, a t i (z i) < τ t := by
  classical
  set ff : T → ℝ := fun t => ∏ j ∈ Finset.range (d t), (τ t - j) with hff_def
  have hfac_pos : ∀ t j, j ∈ Finset.range (d t) → 0 < τ t - j := by
    intro t j hj
    have := Finset.mem_range.mp hj
    have h1 : (j : ℝ) + 1 ≤ d t := by exact_mod_cast this
    linarith [(hd t).2]
  have hff : ∀ t, 0 < ff t := fun t => Finset.prod_pos (fun j hj => hfac_pos t j hj)
  -- per-variable expected loads
  set m : T → I → ℝ := fun t i => Λ * ∑ ω, p i ω * a t i ω with hm_def
  have hm0 : ∀ t i, 0 ≤ m t i := fun t i => mul_nonneg (by linarith)
    (Finset.sum_nonneg (fun ω _ => mul_nonneg (hp i ω).le (ha t i ω).1))
  have hmsum : ∀ t, ∑ i, m t i = Λ * ∑ i, ∑ ω, p i ω * a t i ω := fun t => by
    rw [Finset.mul_sum]
  let q : T → (∀ i, Option (Ω i)) → ℝ := fun t Y =>
    if (supp Y).card = d t then ((d t).factorial : ℝ) / ff t * ∏ i, (Y i).elim 1 (a t i) else 0
  let lamY : (∀ i, Option (Ω i)) → ℝ := fun Y => ∏ i, (Y i).elim 1 (fun ω => Λ * p i ω)
  let μ : T → (∀ i, Option (Ω i)) → ℝ := fun t Y => 2 * q t Y * lamY Y
  have hq : ∀ t Y, 0 ≤ q t Y := by
    intro t Y
    simp only [q]
    split_ifs
    · refine mul_nonneg (div_nonneg (by positivity) (hff t).le) (Finset.prod_nonneg (fun i _ => ?_))
      cases Y i <;> simp [(ha t i _).1]
    · exact le_rfl
  have hlam0 : ∀ Y, 0 ≤ lamY Y := by
    intro Y
    refine Finset.prod_nonneg (fun i _ => ?_)
    cases Y i <;> simp; exact mul_nonneg (by linarith) (hp i _).le
  have hμ : ∀ t Y, 0 ≤ μ t Y := fun t Y => mul_nonneg (mul_nonneg (by norm_num) (hq t Y)) (hlam0 Y)
  -- μ as an atom sum
  have hμ_eq : ∀ t Y, μ t Y = if (supp Y).card = d t then
      2 * ((d t).factorial : ℝ) / ff t * ∏ i, (Y i).elim 1 (fun ω => a t i ω * (Λ * p i ω)) else 0 := by
    intro t Y
    show 2 * q t Y * lamY Y = _
    by_cases hc : (supp Y).card = d t
    · rw [if_pos hc]
      have hq' : q t Y = ((d t).factorial : ℝ) / ff t * ∏ i, (Y i).elim 1 (a t i) := if_pos hc
      rw [hq']
      have : lamY Y = ∏ i, (Y i).elim 1 (fun ω => Λ * p i ω) := rfl
      rw [this, mul_assoc 2, mul_assoc (_ / _), prod_elim_mul, ← mul_assoc, mul_div_assoc]
    · rw [if_neg hc]
      have hq' : q t Y = 0 := if_neg hc
      rw [hq']; ring
  -- S bound
  have hSum : ∀ t, ∑ Y, μ t Y ≤ 1 / 2 := by
    intro t
    simp_rw [hμ_eq]
    have e : ∀ Y : (∀ i, Option (Ω i)), (if (supp Y).card = d t then
        2 * ((d t).factorial : ℝ) / ff t * ∏ i, (Y i).elim 1 (fun ω => a t i ω * (Λ * p i ω)) else 0) =
        2 * ((d t).factorial : ℝ) / ff t * (if (supp Y).card = d t then
          ∏ i, (Y i).elim 1 (fun ω => a t i ω * (Λ * p i ω)) else 0) := by
      intro Y; split_ifs <;> simp
    simp_rw [e]
    rw [← Finset.mul_sum, sum_atoms_card]
    have hx : (fun i => ∑ ω, a t i ω * (Λ * p i ω)) = m t := by
      funext i; simp only [hm_def, Finset.mul_sum]; refine Finset.sum_congr rfl (fun ω _ => by ring)
    rw [hx]
    have hup := esym_upper (m t) (hm0 t) (d t) univ
    rw [hmsum] at hup
    have hS' := hS t
    have hfft := hff t
    rw [show (2 * ((d t).factorial : ℝ) / ff t) * esym (m t) univ (d t) =
      2 * (((d t).factorial : ℝ) * esym (m t) univ (d t)) / ff t by ring]
    rw [div_le_iff₀ hfft]
    have : ff t = ∏ j ∈ Finset.range (d t), (τ t - j) := rfl
    rw [this] at hfft ⊢
    linarith
  -- G bound
  have hGsum : ∀ i, ∑ t, ∑ Y, (if (Y i).isSome then μ t Y else 0) ≤ Real.log Λ := by
    intro i
    have h1 : ∀ t, ∑ Y, (if (Y i).isSome then μ t Y else 0) ≤
        2 * ((d t : ℝ) * m t i * (∑ u, m t u) ^ (d t - 1) / ff t) := by
      intro t
      obtain ⟨d', hd'⟩ : ∃ d', d t = d' + 1 := ⟨d t - 1, by have := (hd t).1; omega⟩
      have e : ∀ Y : (∀ i, Option (Ω i)), (if (Y i).isSome then μ t Y else 0) =
          2 * ((d t).factorial : ℝ) / ff t * (if (supp Y).card = d' + 1 ∧ (Y i).isSome then
            ∏ u, (Y u).elim 1 (fun ω => a t u ω * (Λ * p u ω)) else 0) := by
        intro Y
        rw [hμ_eq, ← hd']
        by_cases h1 : (Y i).isSome <;> by_cases h2 : (supp Y).card = d t <;> simp [h1, h2]
      simp_rw [e]
      rw [← Finset.mul_sum, sum_atoms_card_mem]
      have hx : (fun i => ∑ ω, a t i ω * (Λ * p i ω)) = m t := by
        funext i; simp only [hm_def, Finset.mul_sum]; refine Finset.sum_congr rfl (fun ω _ => by ring)
      rw [hx]
      have hmi_eq : (∑ ω, a t i ω * (Λ * p i ω)) = m t i := by
        simp only [hm_def, Finset.mul_sum]; refine Finset.sum_congr rfl (fun ω _ => by ring)
      rw [hmi_eq]
      have hup := esym_upper (m t) (hm0 t) d' univ
      have hmono := esym_mono (m t) (hm0 t) (univ.erase i) univ (Finset.erase_subset _ _) d'
      have hfft := hff t
      have hdd : d t - 1 = d' := by omega
      rw [hdd, hd']
      have hfac : ((d' + 1).factorial : ℝ) = (d' + 1 : ℝ) * (d'.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfac]
      rw [show ∀ x y : ℝ, 2 * (x / y) = (2 * x) / y from fun x y => by ring]
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hfft]
      push_cast
      have hmi := hm0 t i
      have hE := esym_nonneg (m t) (hm0 t) (univ.erase i) d'
      calc 2 * ((d' + 1 : ℝ) * (d'.factorial : ℝ)) * (m t i * esym (m t) (univ.erase i) d')
          = 2 * (d' + 1 : ℝ) * m t i * ((d'.factorial : ℝ) * esym (m t) (univ.erase i) d') := by ring
        _ ≤ 2 * (d' + 1 : ℝ) * m t i * ((d'.factorial : ℝ) * esym (m t) univ d') := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (by positivity)) ?_
          positivity
        _ ≤ 2 * (d' + 1 : ℝ) * m t i * (∑ u, m t u) ^ d' := by
          refine mul_le_mul_of_nonneg_left hup ?_; positivity
        _ = 2 * ((d' + 1 : ℝ) * m t i * (∑ u, m t u) ^ d') := by ring
    refine le_trans (Finset.sum_le_sum (fun t _ => h1 t)) ?_
    rw [← Finset.mul_sum]
    have := hG i
    simp_rw [hmsum]
    simp only [hm_def] at this ⊢
    linarith
  suffices H : (∀ (t : T) (z : ∀ i, Ω i), τ t ≤ ∑ i, a t i (z i) →
      1 ≤ ∑ Y, q t Y * ∏ i, (Y i).elim 1 (fun ω => if z i = ω then 1 else 0)) ∧
      (∀ k Y, (∏ i, (Y i).elim 1 (p i)) * q k Y *
        ∏ ℓ ∈ Finset.univ.filter (fun ℓ : (∀ i, Option (Ω i)) × T =>
          ℓ.2 = k ∨ ∃ i, (Y i).isSome ∧ (ℓ.1 i).isSome), (1 + μ ℓ.2 ℓ.1) ≤ μ k Y) by
    obtain ⟨z, hz⟩ := PartialResampling.pra_exists Ω p hp hp1 (fun t z => τ t ≤ ∑ i, a t i (z i))
      q hq H.1 μ hμ H.2
    exact ⟨z, fun t => lt_of_not_ge (hz t)⟩
  refine ⟨?_, ?_⟩
  · -- hitting
    intro t z hb
    have e : ∀ Y : (∀ i, Option (Ω i)), q t Y * ∏ i, (Y i).elim 1 (fun ω => if z i = ω then 1 else 0) =
        ((d t).factorial : ℝ) / ff t * (if (supp Y).card = d t then
          ∏ i, (Y i).elim 1 (fun ω => a t i ω * (if z i = ω then 1 else 0)) else 0) := by
      intro Y
      simp only [q]
      split_ifs
      · rw [mul_assoc, prod_elim_mul]
      · simp
    simp_rw [e]
    rw [← Finset.mul_sum, sum_atoms_card]
    have hx : (fun i => ∑ ω, a t i ω * (if z i = ω then 1 else 0)) = fun i => a t i (z i) := by
      funext i; simp
    rw [hx]
    have hlow := esym_lower (fun i => a t i (z i)) (fun i => ha t i (z i)) (d t) univ
      (by linarith [(hd t).2])
    have hmono : ff t ≤ ∏ j ∈ Finset.range (d t), ((∑ i, a t i (z i)) - j) :=
      Finset.prod_le_prod (fun j hj => (hfac_pos t j hj).le) (fun j _ => by linarith)
    rw [div_mul_eq_mul_div, le_div_iff₀ (hff t), one_mul]
    linarith
  · -- criterion
    intro k Y
    by_cases hc : (supp Y).card = d k
    · set N := Finset.univ.filter (fun ℓ : (∀ i, Option (Ω i)) × T =>
        ℓ.2 = k ∨ ∃ i, (Y i).isSome ∧ (ℓ.1 i).isSome) with hN
      have hsumN : ∑ ℓ ∈ N, μ ℓ.2 ℓ.1 ≤ 1 / 2 + (d k : ℝ) * Real.log Λ := by
        have hpt : ∀ ℓ : (∀ i, Option (Ω i)) × T, (if ℓ ∈ N then μ ℓ.2 ℓ.1 else 0) ≤
            (if ℓ.2 = k then μ ℓ.2 ℓ.1 else 0) +
              ∑ i ∈ supp Y, (if (ℓ.1 i).isSome then μ ℓ.2 ℓ.1 else 0) := by
          intro ℓ
          have hnn : 0 ≤ ∑ i ∈ supp Y, (if (ℓ.1 i).isSome then μ ℓ.2 ℓ.1 else 0) :=
            Finset.sum_nonneg (fun i _ => by split_ifs; exact hμ _ _; exact le_rfl)
          by_cases hℓ : ℓ ∈ N
          · rw [if_pos hℓ]
            rw [hN, Finset.mem_filter] at hℓ
            rcases hℓ.2 with h | ⟨i, hi, hi'⟩
            · rw [if_pos h]; linarith
            · have hiY : i ∈ supp Y := by simp [supp, hi]
              have : μ ℓ.2 ℓ.1 ≤ ∑ i ∈ supp Y, (if (ℓ.1 i).isSome then μ ℓ.2 ℓ.1 else 0) := by
                have := Finset.single_le_sum (f := fun i => if (ℓ.1 i).isSome then μ ℓ.2 ℓ.1 else 0)
                  (fun i _ => by split_ifs; exact hμ _ _; exact le_rfl) hiY
                simpa [hi'] using this
              have h0 : 0 ≤ (if ℓ.2 = k then μ ℓ.2 ℓ.1 else 0) := by
                split_ifs; exact hμ _ _; exact le_rfl
              linarith
          · rw [if_neg hℓ]
            have h0 : 0 ≤ (if ℓ.2 = k then μ ℓ.2 ℓ.1 else 0) := by
              split_ifs; exact hμ _ _; exact le_rfl
            linarith
        have hsplit : ∑ ℓ ∈ N, μ ℓ.2 ℓ.1 ≤ (∑ ℓ : (∀ i, Option (Ω i)) × T,
            (if ℓ.2 = k then μ ℓ.2 ℓ.1 else 0)) + ∑ i ∈ supp Y, ∑ ℓ : (∀ i, Option (Ω i)) × T,
              (if (ℓ.1 i).isSome then μ ℓ.2 ℓ.1 else 0) := by
          rw [Finset.sum_comm, ← Finset.sum_add_distrib]
          calc ∑ ℓ ∈ N, μ ℓ.2 ℓ.1 = ∑ ℓ, (if ℓ ∈ N then μ ℓ.2 ℓ.1 else 0) := by
                rw [Finset.sum_ite_mem, Finset.univ_inter]
            _ ≤ _ := Finset.sum_le_sum (fun ℓ _ => hpt ℓ)
        have hA : ∑ ℓ : (∀ i, Option (Ω i)) × T, (if ℓ.2 = k then μ ℓ.2 ℓ.1 else 0) =
            ∑ Y', μ k Y' := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun Y' _ => ?_)
          rw [Finset.sum_ite_eq' univ k (fun k' => μ k' Y')]; simp
        have hB : ∀ i, ∑ ℓ : (∀ i, Option (Ω i)) × T, (if (ℓ.1 i).isSome then μ ℓ.2 ℓ.1 else 0) =
            ∑ t, ∑ Y', (if (Y' i).isSome then μ t Y' else 0) := by
          intro i; rw [Fintype.sum_prod_type, Finset.sum_comm]
        rw [hA] at hsplit
        simp_rw [hB] at hsplit
        have h3 : ∑ i ∈ supp Y, ∑ t, ∑ Y', (if (Y' i).isSome then μ t Y' else 0) ≤
            ∑ i ∈ supp Y, Real.log Λ := Finset.sum_le_sum (fun i _ => hGsum i)
        rw [Finset.sum_const, hc, nsmul_eq_mul] at h3
        linarith [hSum k]
      have hprod : ∏ ℓ ∈ N, (1 + μ ℓ.2 ℓ.1) ≤ 2 * Λ ^ (d k) := by
        calc ∏ ℓ ∈ N, (1 + μ ℓ.2 ℓ.1) ≤ ∏ ℓ ∈ N, Real.exp (μ ℓ.2 ℓ.1) :=
              Finset.prod_le_prod (fun ℓ _ => by linarith [hμ ℓ.2 ℓ.1])
                (fun ℓ _ => by linarith [Real.add_one_le_exp (μ ℓ.2 ℓ.1)])
          _ = Real.exp (∑ ℓ ∈ N, μ ℓ.2 ℓ.1) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp (1 / 2 + (d k : ℝ) * Real.log Λ) := Real.exp_le_exp.mpr hsumN
          _ = Real.exp (1 / 2) * Λ ^ (d k) := by
              rw [Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity)]
          _ ≤ 2 * Λ ^ (d k) := mul_le_mul_of_nonneg_right exp_half_le_two (by positivity)
      have hqY : 0 ≤ q k Y := hq k Y
      have hpA : 0 ≤ ∏ i, (Y i).elim 1 (p i) := Finset.prod_nonneg (fun i _ => by
        cases Y i <;> simp [(hp i _).le])
      calc (∏ i, (Y i).elim 1 (p i)) * q k Y * ∏ ℓ ∈ N, (1 + μ ℓ.2 ℓ.1)
          ≤ (∏ i, (Y i).elim 1 (p i)) * q k Y * (2 * Λ ^ (d k)) :=
            mul_le_mul_of_nonneg_left hprod (mul_nonneg hpA hqY)
        _ = μ k Y := by
            show _ = 2 * q k Y * lamY Y
            have : lamY Y = (∏ i, (Y i).elim 1 (fun _ : Ω i => Λ)) * ∏ i, (Y i).elim 1 (p i) := by
              rw [prod_elim_mul]
            rw [this, prod_elim_const, hc]; ring
    · have hq0 : q k Y = 0 := by simp only [q]; rw [if_neg hc]
      have hμ0 : μ k Y = 0 := by simp only [μ]; rw [hq0]; ring
      rw [hq0, hμ0]; simp
