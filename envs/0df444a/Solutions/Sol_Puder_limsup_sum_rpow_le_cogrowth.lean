-- Prove2me | solution 1 for Puder.limsup_sum_rpow_le_cogrowth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T10:18:04.484265+00:00
-- url     : https://prove2.me/submissions/4ace19e5-31fe-40ed-93f8-abef02ee2202

import Mathlib
import Definitions.Def_StrongConv

section
open Filter
namespace Puder.Cog
variable {k : ℕ}
/-! q218 Blueprint: Puder's extended cogrowth formula (Theorem 4.4) for the Cayley graph of `F_k`,
and the bridge between non-backtracking letter sequences and reduced words. -/
/-- The generator a letter stands for: `inl x ↦ x`, `inr x ↦ x⁻¹`. -/
def gen : Fin k ⊕ Fin k → FreeGroup (Fin k)
  | Sum.inl x => FreeGroup.of x
  | Sum.inr x => (FreeGroup.of x)⁻¹

/-- The endpoint in `F_k` of the walk spelled by a letter sequence. -/
noncomputable def word {t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : FreeGroup (Fin k) :=
  StrongConv.wordFree (List.ofFn fun j => some (i j))

/-- Non-backtracking: no letter is followed by its inverse. -/
def NB {t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : Prop :=
  ∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap

instance {t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : Decidable (NB i) := by
  unfold NB; infer_instance

/-- `ν_h(r)`: the sum of `h` over the endpoints of the non-backtracking walks of length `r`. -/
noncomputable def S (h : FreeGroup (Fin k) → ℝ) (r : ℕ) : ℝ :=
  ∑ i : Fin r → Fin k ⊕ Fin k with NB i, h (word i)

/-- One step of the walk: `(A h)(g) = ∑_a h(g · a)`. -/
noncomputable def A (h : FreeGroup (Fin k) → ℝ) (g : FreeGroup (Fin k)) : ℝ :=
  ∑ a : Fin k ⊕ Fin k, h (g * gen a)

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog
/-! q218 Part A: the combinatorial lemmas of the Blueprint `Puder.Cog`, proved. -/
/-! ### Helpers -/
theorem word_eq {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    word i = (List.ofFn fun j => gen (i j)).prod := by
  unfold word StrongConv.wordFree
  rw [List.map_ofFn]
  congr 2
  funext j
  simp only [Function.comp]
  rcases i j with x | x <;> rfl

theorem word_zero {k : ℕ} (i : Fin 0 → Fin k ⊕ Fin k) : word i = 1 := by
  simp [word_eq]

theorem word_snoc {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) (a : Fin k ⊕ Fin k) :
    word (Fin.snoc i a : Fin (t + 1) → Fin k ⊕ Fin k) = word i * gen a := by
  rw [word_eq, word_eq, List.ofFn_succ']
  simp

theorem gen_mul_swap {k : ℕ} (a : Fin k ⊕ Fin k) : gen a * gen a.swap = 1 := by
  rcases a with x | x <;> simp [gen]

theorem sum_snoc {k r : ℕ} (f : (Fin (r + 1) → Fin k ⊕ Fin k) → ℝ) :
    ∑ j, f j = ∑ i : Fin r → Fin k ⊕ Fin k, ∑ a, f (Fin.snoc i a) := by
  rw [← (Fin.snocEquiv fun _ => Fin k ⊕ Fin k).sum_comp, Fintype.sum_prod_type_right]
  rfl

theorem NB_of_le_one {k t : ℕ} (ht : t ≤ 1) (i : Fin t → Fin k ⊕ Fin k) : NB i := by
  intro j hj
  omega

theorem NB_snoc_succ {k r : ℕ} (i : Fin (r + 1) → Fin k ⊕ Fin k) (a : Fin k ⊕ Fin k) :
    NB (Fin.snoc i a : Fin (r + 2) → Fin k ⊕ Fin k) ↔ NB i ∧ a ≠ (i (Fin.last r)).swap := by
  simp only [NB]
  constructor
  · intro H
    refine ⟨fun j hj => ?_, ?_⟩
    · have := H ⟨j, by omega⟩ (by simp; omega)
      simpa [Fin.snoc, hj, j.isLt] using this
    · have := H ⟨r, by omega⟩ (by simp)
      simpa [Fin.snoc, Fin.last] using this
  · rintro ⟨H, ha⟩ j hj
    have hj' : (j : ℕ) < r + 1 := by simp at hj; omega
    by_cases h2 : (j : ℕ) + 1 < r + 1
    · have := H ⟨j, hj'⟩ h2
      simp [Fin.snoc, h2, hj']
      exact this
    · have hjr : (j : ℕ) = r := by omega
      have e : (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r := rfl
      simp [Fin.snoc, hjr]
      convert ha using 4
      ext
      simp [hjr]

theorem S_eq {k : ℕ} (h : FreeGroup (Fin k) → ℝ) (r : ℕ) :
    S h r = ∑ i : Fin r → Fin k ⊕ Fin k, if NB i then h (word i) else 0 :=
  Finset.sum_filter _ _

theorem S_A {k : ℕ} (h : FreeGroup (Fin k) → ℝ) (r : ℕ) :
    S (A h) r = ∑ i : Fin r → Fin k ⊕ Fin k, ∑ a,
      if NB i then h (word (Fin.snoc i a : Fin (r + 1) → Fin k ⊕ Fin k)) else 0 := by
  rw [S_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [A, word_snoc]

theorem sum_ne {k : ℕ} (c : Fin k ⊕ Fin k) (x : ℝ) :
    ∑ b : Fin k ⊕ Fin k, (if b ≠ c then x else 0) = (2 * k - 1) * x := by
  have : ∑ b : Fin k ⊕ Fin k, (if b ≠ c then x else 0) =
      ∑ _b : Fin k ⊕ Fin k, x - ∑ b : Fin k ⊕ Fin k, (if b = c then x else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp_all
  rw [this]
  simp
  ring

theorem S_A_succ {k : ℕ} (h : FreeGroup (Fin k) → ℝ) (r : ℕ) :
    S (A h) (r + 1) = S h (r + 2) + ∑ i' : Fin r → Fin k ⊕ Fin k, ∑ b,
      if NB (Fin.snoc i' b : Fin (r + 1) → Fin k ⊕ Fin k) then h (word i') else 0 := by
  have hinit : ∀ i : Fin (r + 1) → Fin k ⊕ Fin k, word i * gen (i (Fin.last r)).swap =
      word (Fin.init i) := by
    intro i
    have hw : word i = word (Fin.init i) * gen (i (Fin.last r)) := by
      rw [← word_snoc, Fin.snoc_init_self]
    rw [hw, mul_assoc, gen_mul_swap, mul_one]
  have h2 : ∑ i' : Fin r → Fin k ⊕ Fin k, ∑ b,
      (if NB (Fin.snoc i' b : Fin (r + 1) → Fin k ⊕ Fin k) then h (word i') else 0) =
      ∑ i : Fin (r + 1) → Fin k ⊕ Fin k, if NB i then h (word (Fin.init i)) else 0 := by
    rw [sum_snoc (r := r)]
    simp [Fin.init_snoc]
  rw [h2, S_A, S_eq, sum_snoc (r := r + 1), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : NB i
  · simp only [hi, if_true, NB_snoc_succ, true_and, word_snoc]
    set c := (i (Fin.last r)).swap
    have : ∑ a : Fin k ⊕ Fin k, h (word i * gen a) =
        ∑ a : Fin k ⊕ Fin k, ((if a ≠ c then h (word i * gen a) else 0) +
          (if a = c then h (word i * gen a) else 0)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp_all
    rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [c, hinit]
  · simp [hi, NB_snoc_succ]

/-! ### The five Blueprint lemmas -/
theorem sum_word_eq_iterate {k : ℕ} (h : FreeGroup (Fin k) → ℝ) (t : ℕ) :
    ∑ i : Fin t → Fin k ⊕ Fin k, h (word i) = (A^[t] h) 1 := by
  induction t generalizing h with
  | zero => simp [word_zero]
  | succ t ih =>
    rw [Function.iterate_succ_apply, ← ih, sum_snoc]
    simp only [word_snoc, A]

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}
/-! ## Part A: combinatorics (stubs) -/
alias sum_word_eq_iterate := Puder.Cog.PartA.sum_word_eq_iterate

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog
theorem S_A_zero {k : ℕ} (h : FreeGroup (Fin k) → ℝ) : S (A h) 0 = S h 1 := by
  rw [S_A, S_eq, sum_snoc]
  simp [NB_of_le_one]

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}
alias S_A_zero := Puder.Cog.PartA.S_A_zero

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog
theorem S_A_one {k : ℕ} (h : FreeGroup (Fin k) → ℝ) : S (A h) 1 = S h 2 + 2 * k * S h 0 := by
  rw [S_A_succ, S_eq h 0]
  simp [NB_of_le_one, word_zero]
  ring_nf
  simp

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}
alias S_A_one := Puder.Cog.PartA.S_A_one

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog
theorem S_A_add_two {k : ℕ} (h : FreeGroup (Fin k) → ℝ) (r : ℕ) :
    S (A h) (r + 2) = S h (r + 3) + (2 * k - 1) * S h (r + 1) := by
  rw [S_A_succ, S_eq h (r + 1), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : NB i
  · simp only [NB_snoc_succ, hi, true_and, if_true]
    exact sum_ne _ _
  · simp [NB_snoc_succ, hi]

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}
alias S_A_add_two := Puder.Cog.PartA.S_A_add_two

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartA
open Puder.Cog

end Puder.Cog.PartA
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}

end Puder.Cog
end

section
open Filter
namespace Puder.Cog.PartB
open Puder.Cog
variable {k : ℕ}
/-! q218 Part B: the potential bound and Puder's extended cogrowth formula (Theorem 4.4). -/
lemma S_zero (h : FreeGroup (Fin k) → ℝ) : S h 0 = h 1 := by
  unfold S
  rw [Finset.filter_true_of_mem (by intro i _ j; exact j.elim0)]
  simp [word, StrongConv.wordFree]

/-- The potential `φ`. -/
noncomputable def phi (q a D : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then q * (1 + D) / (q + 1) else a ^ r + D * (q / a) ^ r

lemma phi_step0 (q a D : ℝ) (ha : 0 < a) (hq : 0 < q) (hD : a ^ 2 - q ^ 2 ≤ D * q * (a ^ 2 - 1)) :
    phi q a D 1 ≤ (a + q / a) * phi q a D 0 := by
  simp only [phi, ↓reduceIte, one_ne_zero, pow_one]
  have key : (a + q / a) * (q * (1 + D) / (q + 1)) - (a + D * (q / a)) =
      (q ^ 2 - a ^ 2 + D * q * (a ^ 2 - 1)) / (a * (q + 1)) := by
    field_simp
    ring
  have : 0 ≤ (q ^ 2 - a ^ 2 + D * q * (a ^ 2 - 1)) / (a * (q + 1)) :=
    div_nonneg (by linarith) (by positivity)
  linarith

lemma phi_step1 (q a D : ℝ) (ha : 0 < a) (hq : 0 < q) :
    phi q a D 2 + (q + 1) * phi q a D 0 = (a + q / a) * phi q a D 1 := by
  simp only [phi, ↓reduceIte, one_ne_zero, OfNat.ofNat_ne_zero, pow_one]
  have hq1 : q + 1 ≠ 0 := by linarith
  rw [mul_div_cancel₀ _ hq1]
  obtain ⟨p, hp⟩ : ∃ p, p = q / a := ⟨_, rfl⟩
  have hq' : q = p * a := by rw [hp]; field_simp
  rw [← hp, hq']
  ring

lemma phi_step2 (q a D : ℝ) (ha : 0 < a) (r : ℕ) :
    phi q a D (r + 3) + q * phi q a D (r + 1) = (a + q / a) * phi q a D (r + 2) := by
  simp only [phi, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, if_false]
  obtain ⟨p, hp⟩ : ∃ p, p = q / a := ⟨_, rfl⟩
  have hq' : q = p * a := by rw [hp]; field_simp
  rw [← hp, hq']
  ring

lemma bound (f : FreeGroup (Fin k) → ℝ) (q a D C : ℝ) (hq : q = 2 * k - 1) (ha : 0 < a)
    (hq0 : 0 < q) (hD : a ^ 2 - q ^ 2 ≤ D * q * (a ^ 2 - 1)) (hC : 0 ≤ C)
    (H : ∀ r, S f r ≤ C * phi q a D r) :
    ∀ t r, S (A^[t] f) r ≤ C * (a + q / a) ^ t * phi q a D r := by
  have hL : 0 < a + q / a := by positivity
  intro t
  induction t with
  | zero => intro r; simpa using H r
  | succ t ih =>
    intro r
    have hCL : 0 ≤ C * (a + q / a) ^ t := by positivity
    rw [Function.iterate_succ_apply']
    rcases r with _ | _ | r
    · rw [S_A_zero]
      calc S (A^[t] f) 1 ≤ C * (a + q / a) ^ t * phi q a D 1 := ih 1
        _ ≤ C * (a + q / a) ^ t * ((a + q / a) * phi q a D 0) :=
          mul_le_mul_of_nonneg_left (phi_step0 q a D ha hq0 hD) hCL
        _ = _ := by ring
    · rw [S_A_one]
      have h2k : (2 * k : ℝ) = q + 1 := by rw [hq]; ring
      calc S (A^[t] f) 2 + 2 * k * S (A^[t] f) 0
          ≤ C * (a + q / a) ^ t * phi q a D 2 + 2 * k * (C * (a + q / a) ^ t * phi q a D 0) := by
            gcongr
            · exact ih 2
            · exact ih 0
        _ = C * (a + q / a) ^ t * (phi q a D 2 + (q + 1) * phi q a D 0) := by rw [h2k]; ring
        _ = _ := by rw [phi_step1 q a D ha hq0]; ring
    · rw [S_A_add_two]
      have hq' : (2 * k - 1 : ℝ) = q := hq.symm
      rw [hq']
      calc S (A^[t] f) (r + 3) + q * S (A^[t] f) (r + 1)
          ≤ C * (a + q / a) ^ t * phi q a D (r + 3) + q * (C * (a + q / a) ^ t * phi q a D (r + 1)) := by
            gcongr
            · exact ih _
            · exact ih _
        _ = C * (a + q / a) ^ t * (phi q a D (r + 3) + q * phi q a D (r + 1)) := by ring
        _ = _ := by rw [phi_step2 q a D ha r]; ring

theorem cogrowth_dev (k : ℕ) (hk : 2 ≤ k) (f : FreeGroup (Fin k) → ℝ)
    (hf : ∀ g, 0 ≤ f g) (α c : ℝ) (hα : 0 ≤ α)
    (hν : ∀ t : ℕ, ∑ i : Fin t → Fin k ⊕ Fin k with
        (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap),
        f (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≤ c * α ^ t) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) ^
          (1 / (t : ℝ))) atTop ≤
        if α ≤ Real.sqrt (2 * k - 1) then 2 * Real.sqrt (2 * k - 1) else (2 * k - 1) / α + α := by
  set q : ℝ := 2 * k - 1 with hq
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hq3 : 3 ≤ q := by rw [hq]; linarith
  have hq0 : 0 < q := by linarith
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  set a := max α (Real.sqrt q) with ha_def
  have ha : 0 < a := lt_of_lt_of_le hsq (le_max_right _ _)
  have hαa : α ≤ a := le_max_left _ _
  have ha2 : q ≤ a ^ 2 := by
    rw [← hsq2]; exact pow_le_pow_left₀ hsq.le (le_max_right _ _) 2
  set D := max 0 ((a ^ 2 - q ^ 2) / (q * (a ^ 2 - 1))) with hD_def
  have hD0 : 0 ≤ D := le_max_left _ _
  have hden : 0 < q * (a ^ 2 - 1) := mul_pos hq0 (by linarith)
  have hD : a ^ 2 - q ^ 2 ≤ D * q * (a ^ 2 - 1) := by
    rw [mul_assoc]
    rcases le_or_gt (a ^ 2 - q ^ 2) 0 with h | h
    · exact h.trans (mul_nonneg hD0 hden.le)
    · have : (a ^ 2 - q ^ 2) / (q * (a ^ 2 - 1)) ≤ D := le_max_right _ _
      rwa [div_le_iff₀ hden] at this
  set C := 2 * max c 0 with hC_def
  have hc0 : 0 ≤ max c 0 := le_max_right _ _
  have hC : 0 ≤ C := by positivity
  have hphi0 : 1 / 2 ≤ phi q a D 0 := by
    simp only [phi, ↓reduceIte]
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have H : ∀ r, S f r ≤ C * phi q a D r := by
    intro r
    have h1 : S f r ≤ c * α ^ r := by
      have := hν r
      unfold S NB word
      convert this using 2
    have h2 : c * α ^ r ≤ max c 0 * a ^ r :=
      (mul_le_mul_of_nonneg_right (le_max_left c 0) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hα hαa r) hc0)
    refine h1.trans (h2.trans ?_)
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [pow_zero, mul_one, hC_def]; nlinarith
    · have : a ^ r ≤ phi q a D r := by
        simp only [phi, if_neg hr.ne']
        have : 0 ≤ D * (q / a) ^ r := by positivity
        linarith
      have hpos : 0 ≤ a ^ r := by positivity
      rw [hC_def]; nlinarith
  have hB := bound f q a D C hq ha hq0 hD hC H
  set L := a + q / a with hL_def
  have hL : 0 < L := by positivity
  set M := C * phi q a D 0 + 1 with hM_def
  have hM : 0 < M := by have := mul_nonneg hC (show 0 ≤ phi q a D 0 by linarith); linarith
  set β : ℕ → ℝ := fun t =>
    ∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j))) with hβ_def
  have hβ0 : ∀ t, 0 ≤ β t := fun t => Finset.sum_nonneg fun i _ => hf _
  have hβ : ∀ t, β t ≤ M * L ^ t := by
    intro t
    have e : β t = (A^[t] f) 1 := sum_word_eq_iterate f t
    rw [e, ← S_zero (A^[t] f)]
    refine (hB t 0).trans ?_
    have : 0 ≤ L ^ t := by positivity
    rw [hM_def]; nlinarith
  set x : ℕ → ℝ := fun t => β t ^ (1 / (t : ℝ)) with hx_def
  set u : ℕ → ℝ := fun t => M ^ (1 / (t : ℝ)) * L with hu_def
  have hxu : ∀ᶠ t in atTop, x t ≤ u t := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    have htne : t ≠ 0 := by omega
    simp only [hx_def, hu_def]
    calc β t ^ (1 / (t : ℝ)) ≤ (M * L ^ t) ^ (1 / (t : ℝ)) :=
          Real.rpow_le_rpow (hβ0 t) (hβ t) (by positivity)
      _ = M ^ (1 / (t : ℝ)) * L := by
          rw [Real.mul_rpow hM.le (by positivity), one_div, Real.pow_rpow_inv_natCast hL.le htne]
  have hu : Tendsto u atTop (nhds L) := by
    have h1 : Tendsto (fun t : ℕ => (1 : ℝ) / t) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun t : ℕ => M ^ (1 / (t : ℝ))) atTop (nhds (M ^ (0 : ℝ))) :=
      ((Real.continuousAt_const_rpow hM.ne').tendsto).comp h1
    rw [Real.rpow_zero] at h2
    have := h2.mul_const L
    rw [one_mul] at this
    exact this
  have hub : IsBoundedUnder (· ≤ ·) atTop u := hu.isBoundedUnder_le
  have hxcob : IsCoboundedUnder (· ≤ ·) atTop x :=
    isCoboundedUnder_le_of_le atTop (fun t => Real.rpow_nonneg (hβ0 t) _)
  have hLeq : L = if α ≤ Real.sqrt (2 * k - 1) then 2 * Real.sqrt (2 * k - 1)
      else (2 * k - 1) / α + α := by
    rw [← hq]
    split_ifs with h
    · have : a = Real.sqrt q := max_eq_right h
      rw [hL_def, this]
      have : q / Real.sqrt q = Real.sqrt q := by
        rw [div_eq_iff hsq.ne', ← sq, hsq2]
      rw [this]; ring
    · have : a = α := max_eq_left (le_of_not_ge h)
      rw [hL_def, this]; ring
  refine ⟨hub.mono_le hxu, ?_⟩
  rw [← hLeq]
  calc limsup x atTop ≤ limsup u atTop := limsup_le_limsup hxu hxcob hub
    _ = L := hu.limsup_eq

end Puder.Cog.PartB
end

section
open Filter
namespace Puder.Cog
variable {k : ℕ}
/-! ## Part B: the potential bound and the theorem (target) -/
alias cogrowth_dev := Puder.Cog.PartB.cogrowth_dev

end Puder.Cog
end

open Filter in
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : FreeGroup (Fin k) → ℝ)
    (hf : ∀ g, 0 ≤ f g) (α c : ℝ) (hα : 0 ≤ α)
    (hν : ∀ t : ℕ, ∑ i : Fin t → Fin k ⊕ Fin k with
        (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap),
        f (StrongConv.wordFree (List.ofFn fun j => some (i j))) ≤ c * α ^ t) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) ^
          (1 / (t : ℝ))) atTop ≤
        if α ≤ Real.sqrt (2 * k - 1) then 2 * Real.sqrt (2 * k - 1) else (2 * k - 1) / α + α :=
  Puder.Cog.cogrowth_dev k hk f hf α c hα hν
