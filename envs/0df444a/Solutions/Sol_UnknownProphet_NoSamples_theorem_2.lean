-- Prove2me | solution 1 for UnknownProphet.NoSamples.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:15:25.25792+00:00
-- url     : https://prove2.me/submissions/b170eb39-70fb-472b-ade0-8c49bf15d798

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model
import Theorems.Thm_UnknownProphet_NoSamples_lemma_1
import Theorems.Thm_UnknownProphet_NoSamples_eq_1
import Theorems.Thm_UnknownProphet_NoSamples_coupling
import Theorems.Thm_UnknownProphet_NoSamples_eq_4

namespace UnknownProphet.NoSamples.Thm2Aux

open Finset UnknownProphet.NoSamples

/-! ### A. Generic facts about stopping rules -/

lemma stopProb_nonneg {k n : ℕ} (R : StoppingRule k n) (s : Fin k → ℝ) (x : Fin n → ℝ)
    (i : Fin n) : 0 ≤ stopProb R s x i := by
  unfold stopProb
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro j _
    linarith [(R.r_mem j s (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt))).2]
  · exact (R.r_mem _ _ _).1

lemma sum_stopProb_le_one {k n : ℕ} (R : StoppingRule k n) (s : Fin k → ℝ)
    (x : Fin n → ℝ) : ∑ i, stopProb R s x i ≤ 1 := by
  classical
  set a : Fin n → ℝ := fun j => 1 - R.r j s (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt))
  have ha0 : ∀ j, 0 ≤ a j := fun j => by
    simp only [a]; linarith [(R.r_mem j s (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt))).2]
  set P : ℕ → ℝ := fun m => ∏ j ∈ univ.filter (fun j : Fin n => j.val < m), a j
  have hIio : ∀ i : Fin n, Finset.Iio i = univ.filter (fun j : Fin n => j.val < i.val) := by
    intro i; ext j
    simp only [Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.lt_def
  have hIic : ∀ i : Fin n, Finset.Iic i = univ.filter (fun j : Fin n => j.val < i.val + 1) := by
    intro i; ext j
    simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.le_def, Nat.lt_succ_iff]
  have hterm : ∀ i : Fin n, stopProb R s x i = P i.val - P (i.val + 1) := by
    intro i
    simp only [P]
    rw [← hIio, ← hIic, ← Finset.Iio_insert, Finset.prod_insert (by simp)]
    unfold stopProb
    simp only [a]
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun m => P m - P (m + 1)), Finset.sum_range_sub']
  have h0 : P 0 = 1 := by simp [P]
  have hn : 0 ≤ P n := Finset.prod_nonneg (fun j _ => ha0 j)
  linarith

lemma pickMaxProb_nonneg {n : ℕ} (R : StoppingRule 0 n) (x : Fin n → ℝ) :
    0 ≤ pickMaxProb R x := by
  unfold pickMaxProb
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact stopProb_nonneg _ _ _ _
  · exact le_refl 0

lemma pickMaxProb_le_one {n : ℕ} (R : StoppingRule 0 n) (x : Fin n → ℝ) :
    pickMaxProb R x ≤ 1 := by
  unfold pickMaxProb
  refine le_trans ?_ (sum_stopProb_le_one R ![] x)
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_refl _
  · exact stopProb_nonneg _ _ _ _

/-! ### B. Finite-distribution helpers -/

lemma sum_piFinset_fin0 (S : Finset ℝ) (f : (Fin 0 → ℝ) → ℝ) :
    ∑ s ∈ Fintype.piFinset (fun _ : Fin 0 => S), f s = f ![] := by
  have : Fintype.piFinset (fun _ : Fin 0 => S) = {![]} := by
    ext y
    simp only [Fintype.mem_piFinset, IsEmpty.forall_iff, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [this, Finset.sum_singleton]

lemma expStop_zero {n : ℕ} (F : FinDist) (R : StoppingRule 0 n) :
    expStop F R = ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      iidWeight F x * ∑ i, stopProb R ![] x i * x i := by
  unfold expStop
  rw [sum_piFinset_fin0 F.supp (fun s => ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      iidWeight F s * iidWeight F x * ∑ i, stopProb R s x i * x i)]
  have : iidWeight F (![] : Fin 0 → ℝ) = 1 := by simp [iidWeight]
  simp [this]

lemma iidWeight_nonneg (F : FinDist) {n : ℕ} (x : Fin n → ℝ)
    (hx : x ∈ Fintype.piFinset (fun _ : Fin n => F.supp)) : 0 ≤ iidWeight F x := by
  rw [Fintype.mem_piFinset] at hx
  exact Finset.prod_nonneg (fun j _ => F.w_nonneg _ (hx j))

lemma sum_iidWeight (F : FinDist) (n : ℕ) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp), iidWeight F x = 1 := by
  unfold iidWeight
  rw [Finset.sum_prod_piFinset F.supp (fun _ y => F.w y), F.w_sum]
  simp

lemma expStop_nonneg {n : ℕ} (F : FinDist) (R : StoppingRule 0 n) : 0 ≤ expStop F R := by
  rw [expStop_zero]
  apply Finset.sum_nonneg
  intro x hx
  apply mul_nonneg (iidWeight_nonneg F x hx)
  apply Finset.sum_nonneg
  intro i _
  rw [Fintype.mem_piFinset] at hx
  exact mul_nonneg (stopProb_nonneg _ _ _ _) (F.supp_nonneg _ (hx i))

/-- Expectation of a product of coordinatewise functions factorises. -/
lemma expect_prod (F : FinDist) {n : ℕ} (g : Fin n → ℝ → ℝ) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp), iidWeight F x * ∏ l, g l (x l) =
      ∏ l, ∑ y ∈ F.supp, F.w y * g l y := by
  rw [← Finset.sum_prod_piFinset F.supp (fun l y => F.w y * g l y)]
  apply Finset.sum_congr rfl
  intro x _
  unfold iidWeight
  rw [← Finset.prod_mul_distrib]

lemma prod_le_prod_subset {n : ℕ} (h : Fin n → ℝ) (h0 : ∀ l, 0 ≤ h l) (h1 : ∀ l, h l ≤ 1)
    (T : Finset (Fin n)) : ∏ l, h l ≤ ∏ l ∈ T, h l := by
  classical
  rw [← Finset.prod_sdiff (Finset.subset_univ T)]
  have hA : ∏ l ∈ univ \ T, h l ≤ 1 := Finset.prod_le_one (fun l _ => h0 l) (fun l _ => h1 l)
  have hB : 0 ≤ ∏ l ∈ T, h l := Finset.prod_nonneg (fun l _ => h0 l)
  nlinarith

/-! ### C. Order invariance of the record rule and the symmetry identity -/

lemma pickMax_hat_congr {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (x y : Fin n → ℝ) (hlt : ∀ a b, x a < x b ↔ y a < y b)
    (hle : ∀ a b, x a ≤ x b ↔ y a ≤ y b) :
    pickMaxProb (hatRule q hq) x = pickMaxProb (hatRule q hq) y := by
  simp only [pickMaxProb, stopProb, hatRule, Function.comp_apply, hlt, hle]

lemma sum_sym {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (Y : Finset (Fin n → ℝ)) (W : (Fin n → ℝ) → ℝ)
    (hY : ∀ x ∈ Y, ∀ σ : Equiv.Perm (Fin n), x ∘ σ ∈ Y)
    (hinj : ∀ x ∈ Y, Function.Injective x)
    (hW : ∀ x ∈ Y, ∀ σ : Equiv.Perm (Fin n), W (x ∘ σ) = W x) :
    ∑ x ∈ Y, W x * pickMaxProb (hatRule q hq) x =
      (∑ x ∈ Y, W x) * recordRuleSuccess q hq := by
  classical
  set g := pickMaxProb (hatRule q hq)
  set vals : Equiv.Perm (Fin n) → (Fin n → ℝ) := fun σ i => ((σ i : ℕ) : ℝ)
  have hfact : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hS : ∑ σ : Equiv.Perm (Fin n), g (vals σ) = n.factorial * recordRuleSuccess q hq := by
    unfold recordRuleSuccess
    rw [← mul_assoc, mul_one_div_cancel hfact, one_mul]
  -- for each σ, reindex Y
  have hre : ∀ σ : Equiv.Perm (Fin n),
      ∑ x ∈ Y, W x * g x = ∑ x ∈ Y, W x * g (x ∘ σ) := by
    intro σ
    symm
    apply Finset.sum_nbij' (fun x => x ∘ σ) (fun x => x ∘ ⇑σ⁻¹)
    · intro x hx; exact hY x hx σ
    · intro x hx; exact hY x hx σ⁻¹
    · intro x _; funext i; simp
    · intro x _; funext i; simp
    · intro x hx; rw [hW x hx σ]
  -- for each x, the inner average
  have hinner : ∀ x ∈ Y, ∑ σ : Equiv.Perm (Fin n), g (x ∘ σ) =
      n.factorial * recordRuleSuccess q hq := by
    intro x hx
    set ρ : Equiv.Perm (Fin n) := (Tuple.sort x)⁻¹
    have hsm : StrictMono (x ∘ Tuple.sort x) :=
      (Tuple.monotone_sort x).strictMono_of_injective
        ((hinj x hx).comp (Tuple.sort x).injective)
    have hxc : ∀ c, x c = (x ∘ Tuple.sort x) (ρ c) := by
      intro c; simp [ρ]
    have hcomp : ∀ σ : Equiv.Perm (Fin n), g (x ∘ σ) = g (vals (ρ * σ)) := by
      intro σ
      apply pickMax_hat_congr
      · intro a b
        simp only [Function.comp_apply, vals, Equiv.Perm.mul_apply]
        rw [hxc (σ a), hxc (σ b), hsm.lt_iff_lt, Nat.cast_lt, Fin.val_fin_lt]
      · intro a b
        simp only [Function.comp_apply, vals, Equiv.Perm.mul_apply]
        rw [hxc (σ a), hxc (σ b), hsm.le_iff_le, Nat.cast_le, Fin.val_fin_le]
    simp_rw [hcomp]
    rw [← hS]
    exact Equiv.sum_comp (Equiv.mulLeft ρ) (fun σ => g (vals σ))
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = n.factorial := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have key : (n.factorial : ℝ) * ∑ x ∈ Y, W x * g x =
      (n.factorial : ℝ) * ((∑ x ∈ Y, W x) * recordRuleSuccess q hq) := by
    calc (n.factorial : ℝ) * ∑ x ∈ Y, W x * g x
        = ∑ σ : Equiv.Perm (Fin n), ∑ x ∈ Y, W x * g x := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ x ∈ Y, W x * g (x ∘ σ) :=
          Finset.sum_congr rfl (fun σ _ => hre σ)
      _ = ∑ x ∈ Y, W x * ∑ σ : Equiv.Perm (Fin n), g (x ∘ σ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
      _ = ∑ x ∈ Y, W x * (n.factorial * recordRuleSuccess q hq) :=
          Finset.sum_congr rfl (fun x hx => by rw [hinner x hx])
      _ = (n.factorial : ℝ) * ((∑ x ∈ Y, W x) * recordRuleSuccess q hq) := by
          rw [← Finset.sum_mul]; ring
  exact mul_left_cancel₀ hfact key


/-! ### D. Construction of the hard law on an infinite value set -/

lemma exists_hard (n : ℕ) (hn : 1 ≤ n) (V : Set ℕ) (hV : V.Infinite) :
    ∃ (F : FinDist) (v : Fin (n ^ 3) → ℝ) (u : ℝ), IsHardInstance n F v u ∧ 0 < u ∧
      ∀ y ∈ F.supp, ∃ m ∈ V, y = (m : ℝ) := by
  classical
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set e := hV.natEmbedding V
  set v0 : Fin (n ^ 3) → ℕ := fun j => ((e j.val : V) : ℕ)
  have hv0inj : Function.Injective v0 := by
    intro a b hab
    have h1 : e a.val = e b.val := Subtype.ext hab
    exact Fin.ext (e.injective h1)
  have hv0V : ∀ j, v0 j ∈ V := fun j => (e j.val).2
  set M : ℕ := ∑ j, v0 j
  obtain ⟨u0, hu0V, hu0⟩ := hV.exists_gt (n ^ 3 * M)
  have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  have hvM : ∀ j, v0 j ≤ M := fun j =>
    Finset.single_le_sum (f := v0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hvle : ∀ j, n ^ 3 * v0 j < u0 := fun j =>
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (hvM j)) hu0
  have hvne : ∀ j, v0 j ≠ u0 := by
    intro j hj
    have := hvle j
    rw [hj] at this
    nlinarith
  set c : ℝ := 1 / (n : ℝ) ^ 3 * (1 - 1 / (n : ℝ) ^ 2)
  have hc0 : 0 ≤ c := by
    have : 1 / (n : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 3 := by positivity
    simp only [c]; nlinarith
  set wf : ℝ → ℝ := fun y => if y = (u0 : ℝ) then 1 / (n : ℝ) ^ 2 else c
  set S : Finset ℝ := insert (u0 : ℝ) (univ.image (fun j => (v0 j : ℝ)))
  have hvR_inj : Function.Injective (fun j => (v0 j : ℝ)) := fun a b hab =>
    hv0inj (by simpa using hab)
  have hu_notin : (u0 : ℝ) ∉ univ.image (fun j => (v0 j : ℝ)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j hj
    exact hvne j (by exact_mod_cast hj)
  have hsum : ∑ y ∈ S, wf y = 1 := by
    rw [Finset.sum_insert hu_notin, Finset.sum_image (fun a _ b _ hab => hvR_inj hab)]
    have h1 : ∀ j : Fin (n ^ 3), wf (v0 j : ℝ) = c := by
      intro j; simp only [wf]; rw [if_neg]; intro h; exact hvne j (by exact_mod_cast h)
    simp only [h1]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [wf, if_pos rfl, c]
    have : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  refine ⟨⟨S, wf, ?_, ?_, hsum⟩, fun j => (v0 j : ℝ), (u0 : ℝ), ⟨hvR_inj, ?_, ?_, ?_, rfl, ?_, ?_⟩, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]; positivity
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h; positivity
  · intro y _
    simp only [wf]; split_ifs
    · positivity
    · exact hc0
  · intro j; positivity
  · intro j h; exact hvne j (by simpa using h)
  · intro j
    have := hvle j
    have : ((n ^ 3 * v0 j : ℕ) : ℝ) ≤ (u0 : ℝ) := by exact_mod_cast this.le
    push_cast at this
    exact this
  · intro j
    show wf _ = _
    simp only [wf]; rw [if_neg]; intro h; exact hvne j (by exact_mod_cast h)
  · show wf _ = _
    simp only [wf, if_pos rfl]
  · have : (0 : ℕ) < u0 := lt_of_le_of_lt (Nat.zero_le _) hu0
    exact_mod_cast this
  · intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact ⟨u0, hu0V, h⟩
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨v0 j, hv0V j, rfl⟩

/-! ### E. The upper bound on the rule's value for the hard law -/

section HardFacts

variable {n : ℕ} {F : FinDist} {v : Fin (n ^ 3) → ℝ} {u : ℝ}

lemma hard_u_mem (hF : IsHardInstance n F v u) : u ∈ F.supp := by
  rw [hF.2.2.2.2.1]; exact Finset.mem_insert_self _ _

lemma hard_small (hn : 1 ≤ n) (hF : IsHardInstance n F v u) :
    ∀ y ∈ F.supp, y ≠ u → y ≤ u / (n : ℝ) ^ 3 ∧ F.w y = 1 / (n : ℝ) ^ 3 * (1 - 1 / (n : ℝ) ^ 2) := by
  obtain ⟨_, hv0, _, hvle, hsupp, hwv, _⟩ := hF
  intro y hy hyu
  rw [hsupp] at hy
  rcases Finset.mem_insert.mp hy with h | h
  · exact absurd h hyu
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
    refine ⟨?_, hwv j⟩
    have hnR : (0 : ℝ) < (n : ℝ) ^ 3 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    rw [le_div_iff₀ hnR]
    linarith [hvle j]

lemma hard_le_u (hn : 1 ≤ n) (hF : IsHardInstance n F v u) : ∀ y ∈ F.supp, y ≤ u := by
  intro y hy
  by_cases hyu : y = u
  · rw [hyu]
  · have h := (hard_small hn hF y hy hyu).1
    have hu0 : 0 ≤ u := F.supp_nonneg u (hard_u_mem hF)
    have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
    have : u / (n : ℝ) ^ 3 ≤ u := div_le_self hu0 this
    linarith

lemma hard_max_iff (hn : 1 ≤ n) (hF : IsHardInstance n F v u) :
    ∀ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp), ((⨆ i, x i) = u ↔ ∃ j, x j = u) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro x hx
  rw [Fintype.mem_piFinset] at hx
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := x)
    exact ⟨i, hi.trans h⟩
  · rintro ⟨j, hj⟩
    apply le_antisymm
    · exact ciSup_le (fun i => hard_le_u hn hF _ (hx i))
    · rw [← hj]; exact le_ciSup (Finite.bddAbove_range x) j

lemma hard_wu (hF : IsHardInstance n F v u) : F.w u = 1 / (n : ℝ) ^ 2 := hF.2.2.2.2.2.2

end HardFacts

/-- Pointwise payoff bound: only a draw equal to `u` can pay more than `u / n^3`. -/
lemma payoff_le (n : ℕ) (hn : 1 ≤ n) (F : FinDist) (v : Fin (n ^ 3) → ℝ) (u : ℝ)
    (hF : IsHardInstance n F v u) (R : StoppingRule 0 n)
    (x : Fin n → ℝ) (hx : x ∈ Fintype.piFinset (fun _ : Fin n => F.supp)) :
    ∑ i, stopProb R ![] x i * x i ≤
      (if ∃ j, x j = u then pickMaxProb R x else 0) * u + u / (n : ℝ) ^ 3 := by
  classical
  have hx' := (Fintype.mem_piFinset).mp hx
  have hu0 : 0 ≤ u := F.supp_nonneg u (hard_u_mem hF)
  have hun : 0 ≤ u / (n : ℝ) ^ 3 := by positivity
  have hterm : ∀ i, stopProb R ![] x i * x i ≤
      (if x i = u then (if ∀ j, x j ≤ x i then stopProb R ![] x i else 0) else 0) * u +
        stopProb R ![] x i * (u / (n : ℝ) ^ 3) := by
    intro i
    have hsp := stopProb_nonneg R ![] x i
    by_cases hxi : x i = u
    · have hall : ∀ j, x j ≤ x i := fun j => by rw [hxi]; exact hard_le_u hn hF _ (hx' j)
      rw [if_pos hxi, if_pos hall, hxi]
      nlinarith
    · rw [if_neg hxi, zero_mul, zero_add]
      exact mul_le_mul_of_nonneg_left (hard_small hn hF _ (hx' i) hxi).1 hsp
  calc ∑ i, stopProb R ![] x i * x i
      ≤ ∑ i, ((if x i = u then (if ∀ j, x j ≤ x i then stopProb R ![] x i else 0) else 0) * u +
          stopProb R ![] x i * (u / (n : ℝ) ^ 3)) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, (if x i = u then (if ∀ j, x j ≤ x i then stopProb R ![] x i else 0) else 0)) * u
          + (∑ i, stopProb R ![] x i) * (u / (n : ℝ) ^ 3) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    _ ≤ (if ∃ j, x j = u then pickMaxProb R x else 0) * u + 1 * (u / (n : ℝ) ^ 3) := by
        gcongr
        · split_ifs with hex
          · unfold pickMaxProb
            apply Finset.sum_le_sum
            intro i _
            split_ifs
            · exact le_refl _
            · exact le_refl _
            · exact stopProb_nonneg _ _ _ _
            · exact le_refl _
          · push Not at hex
            apply le_of_eq
            apply Finset.sum_eq_zero
            intro i _
            rw [if_neg (hex i)]
        · exact sum_stopProb_le_one R ![] x
    _ = _ := by ring


lemma mind (w : ℝ) (hw : 0 ≤ w) (P : Prop) [Decidable P] :
    0 ≤ w * (if P then (1 : ℝ) else 0) := by
  split_ifs <;> simp [hw]

lemma ite_mind (Q : Prop) [Decidable Q] (w : ℝ) (hw : 0 ≤ w) (P : Prop) [Decidable P] :
    0 ≤ (if Q then w * (if P then (1 : ℝ) else 0) else 0) := by
  split_ifs <;> simp [hw]

/-! ### F. Collision bound: two equal draws together with the top atom are unlikely -/

lemma h_bounds (F : FinDist) {n : ℕ} (g : Fin n → ℝ → ℝ)
    (g0 : ∀ l y, 0 ≤ g l y) (g1 : ∀ l y, g l y ≤ 1) :
    ∀ l, 0 ≤ ∑ y ∈ F.supp, F.w y * g l y ∧ ∑ y ∈ F.supp, F.w y * g l y ≤ 1 := by
  intro l
  constructor
  · exact Finset.sum_nonneg (fun y hy => mul_nonneg (F.w_nonneg y hy) (g0 l y))
  · calc ∑ y ∈ F.supp, F.w y * g l y ≤ ∑ y ∈ F.supp, F.w y :=
          Finset.sum_le_sum (fun y hy => by
            have := F.w_nonneg y hy
            have := g1 l y
            nlinarith [g0 l y])
      _ = 1 := F.w_sum

lemma two_point (F : FinDist) {n : ℕ} (a b : Fin n) (hab : a ≠ b) (y1 y2 : ℝ)
    (hy1 : y1 ∈ F.supp) (hy2 : y2 ∈ F.supp) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      iidWeight F x * (if x a = y1 ∧ x b = y2 then (1 : ℝ) else 0) ≤ F.w y1 * F.w y2 := by
  classical
  set g : Fin n → ℝ → ℝ := fun l y =>
    if l = a then (if y = y1 then 1 else 0) else if l = b then (if y = y2 then 1 else 0) else 1
  have g0 : ∀ l y, 0 ≤ g l y := by intro l y; simp only [g]; split_ifs <;> norm_num
  have g1 : ∀ l y, g l y ≤ 1 := by intro l y; simp only [g]; split_ifs <;> norm_num
  have hpt : ∀ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      iidWeight F x * (if x a = y1 ∧ x b = y2 then (1 : ℝ) else 0) ≤
        iidWeight F x * ∏ l, g l (x l) := by
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (iidWeight_nonneg F x hx)
    split_ifs with hc
    · apply le_of_eq; symm
      apply Finset.prod_eq_one
      intro l _
      simp only [g]
      split_ifs with h1 h2 h3 h4 <;> first | rfl | (subst_vars; simp_all)
    · exact Finset.prod_nonneg (fun l _ => g0 l _)
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [expect_prod]
  have hb := h_bounds F g g0 g1
  refine le_trans (prod_le_prod_subset _ (fun l => (hb l).1) (fun l => (hb l).2) {a, b}) ?_
  rw [Finset.prod_pair hab]
  have ha : ∑ y ∈ F.supp, F.w y * g a y = F.w y1 := by
    simp only [g, ↓reduceIte, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' F.supp y1, if_pos hy1]
  have hbb : ∑ y ∈ F.supp, F.w y * g b y = F.w y2 := by
    simp only [g, if_neg hab.symm, ↓reduceIte, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' F.supp y2, if_pos hy2]
  rw [ha, hbb]

lemma three_point (F : FinDist) {n : ℕ} (a b k : Fin n) (hab : a ≠ b) (hak : a ≠ k)
    (hbk : b ≠ k) (y1 y2 y3 : ℝ)
    (hy1 : y1 ∈ F.supp) (hy2 : y2 ∈ F.supp) (hy3 : y3 ∈ F.supp) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      iidWeight F x * (if x a = y1 ∧ x b = y2 ∧ x k = y3 then (1 : ℝ) else 0) ≤
        F.w y1 * F.w y2 * F.w y3 := by
  classical
  set g : Fin n → ℝ → ℝ := fun l y =>
    if l = a then (if y = y1 then 1 else 0) else if l = b then (if y = y2 then 1 else 0)
      else if l = k then (if y = y3 then 1 else 0) else 1
  have g0 : ∀ l y, 0 ≤ g l y := by intro l y; simp only [g]; split_ifs <;> norm_num
  have g1 : ∀ l y, g l y ≤ 1 := by intro l y; simp only [g]; split_ifs <;> norm_num
  have hpt : ∀ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      iidWeight F x * (if x a = y1 ∧ x b = y2 ∧ x k = y3 then (1 : ℝ) else 0) ≤
        iidWeight F x * ∏ l, g l (x l) := by
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (iidWeight_nonneg F x hx)
    split_ifs with hc
    · apply le_of_eq; symm
      apply Finset.prod_eq_one
      intro l _
      simp only [g]
      split_ifs <;> first | rfl | (subst_vars; simp_all)
    · exact Finset.prod_nonneg (fun l _ => g0 l _)
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [expect_prod]
  have hb := h_bounds F g g0 g1
  refine le_trans (prod_le_prod_subset _ (fun l => (hb l).1) (fun l => (hb l).2) {a, b, k}) ?_
  have hnot : a ∉ ({b, k} : Finset (Fin n)) := by simp [hab, hak]
  rw [Finset.prod_insert hnot, Finset.prod_pair hbk]
  have ha : ∑ y ∈ F.supp, F.w y * g a y = F.w y1 := by
    simp only [g, ↓reduceIte, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' F.supp y1, if_pos hy1]
  have hbb : ∑ y ∈ F.supp, F.w y * g b y = F.w y2 := by
    simp only [g, if_neg hab.symm, ↓reduceIte, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' F.supp y2, if_pos hy2]
  have hkk : ∑ y ∈ F.supp, F.w y * g k y = F.w y3 := by
    simp only [g, if_neg hak.symm, if_neg hbk.symm, ↓reduceIte, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' F.supp y3, if_pos hy3]
  rw [ha, hbb, hkk, mul_assoc]

lemma collision (n : ℕ) (hn : 1 ≤ n) (F : FinDist) (v : Fin (n ^ 3) → ℝ) (u : ℝ)
    (hF : IsHardInstance n F v u) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin n => F.supp),
      (if (∃ j, x j = u) ∧ ¬ Function.Injective x then iidWeight F x else 0) ≤
        2 / (n : ℝ) ^ 2 := by
  classical
  set X := Fintype.piFinset (fun _ : Fin n => F.supp)
  set c : ℝ := 1 / (n : ℝ) ^ 3 * (1 - 1 / (n : ℝ) ^ 2)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hu_mem := hard_u_mem hF
  have hwu := hard_wu hF
  have hc0 : 0 ≤ c := by
    have : 1 / (n : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 3 := by positivity
    simp only [c]; nlinarith
  have hc1 : c ≤ 1 / (n : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
    have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 3 := by positivity
    simp only [c]; nlinarith
  -- E1
  have E1 : ∀ a b : Fin n, a ≠ b → ∑ x ∈ X, iidWeight F x *
      (if x a = u ∧ x b = u then (1 : ℝ) else 0) ≤ F.w u * F.w u :=
    fun a b hab => two_point F a b hab u u hu_mem hu_mem
  -- E2
  have E2 : ∀ a b k : Fin n, a ≠ b → ∑ x ∈ X, iidWeight F x *
      (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0) ≤ c * F.w u := by
    intro a b k hab
    have hcw : 0 ≤ c * F.w u := mul_nonneg hc0 (F.w_nonneg u hu_mem)
    by_cases hka : k = a
    · subst hka
      refine le_trans (le_of_eq ?_) hcw
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]; · ring
      rintro ⟨_, h2, h3⟩; exact h2 h3
    by_cases hkb : k = b
    · subst hkb
      refine le_trans (le_of_eq ?_) hcw
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]; · ring
      rintro ⟨h1, h2, h3⟩; exact h2 (h1.trans h3)
    have hpt : ∀ x ∈ X, iidWeight F x *
        (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0) ≤
          ∑ y0 ∈ F.supp, (if y0 ≠ u then iidWeight F x *
            (if x a = y0 ∧ x b = y0 ∧ x k = u then (1 : ℝ) else 0) else 0) := by
      intro x hx
      have hw0 := iidWeight_nonneg F x hx
      have hnn0 : ∀ y0 ∈ F.supp, (0 : ℝ) ≤ (if y0 ≠ u then iidWeight F x *
            (if x a = y0 ∧ x b = y0 ∧ x k = u then (1 : ℝ) else 0) else 0) := by
        intro y0 _
        exact ite_mind _ _ hw0 _
      by_cases hc : x a = x b ∧ x a ≠ u ∧ x k = u
      · obtain ⟨h1, h2, h3⟩ := hc
        have hxa : x a ∈ F.supp := (Fintype.mem_piFinset.mp hx) a
        have hsingle := Finset.single_le_sum hnn0 hxa
        have e1 : (if x a ≠ u then iidWeight F x *
            (if x a = x a ∧ x b = x a ∧ x k = u then (1 : ℝ) else 0) else 0) = iidWeight F x := by
          rw [if_pos h2, if_pos ⟨rfl, h1.symm, h3⟩, mul_one]
        rw [e1] at hsingle
        rw [if_pos ⟨h1, h2, h3⟩, mul_one]
        exact hsingle
      · rw [if_neg hc, mul_zero]
        exact Finset.sum_nonneg hnn0
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [Finset.sum_comm]
    calc ∑ y0 ∈ F.supp, ∑ x ∈ X, (if y0 ≠ u then iidWeight F x *
            (if x a = y0 ∧ x b = y0 ∧ x k = u then (1 : ℝ) else 0) else 0)
        ≤ ∑ y0 ∈ F.supp, c * F.w y0 * F.w u := by
          apply Finset.sum_le_sum
          intro y0 hy0
          by_cases hy0u : y0 = u
          · simp only [hy0u, ne_eq, not_true_eq_false, if_false, Finset.sum_const_zero]
            have := F.w_nonneg u hu_mem
            positivity
          · simp only [ne_eq, hy0u, not_false_eq_true, if_true]
            refine le_trans (three_point F a b k hab (Ne.symm hka) (Ne.symm hkb) y0 y0 u
              hy0 hy0 hu_mem) ?_
            have hw := (hard_small hn hF y0 hy0 hy0u).2
            rw [hw]
      _ = c * F.w u := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, F.w_sum, mul_one]
  -- pointwise union bound
  have hpt : ∀ x ∈ X, (if (∃ j, x j = u) ∧ ¬ Function.Injective x then iidWeight F x else 0) ≤
      ∑ a, ∑ b, (if a ≠ b then (iidWeight F x * (if x a = u ∧ x b = u then (1 : ℝ) else 0) +
        ∑ k, iidWeight F x * (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0)) else 0) := by
    intro x hx
    have hw0 := iidWeight_nonneg F x hx
    have hnn : ∀ a b, 0 ≤ (if a ≠ b then (iidWeight F x * (if x a = u ∧ x b = u then (1 : ℝ) else 0) +
        ∑ k, iidWeight F x * (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0)) else 0) := by
      intro a b
      by_cases hab : a ≠ b
      · rw [if_pos hab]
        apply add_nonneg (mind _ hw0 _)
        exact Finset.sum_nonneg (fun k _ => mind _ hw0 _)
      · rw [if_neg hab]
    split_ifs with hc
    · obtain ⟨⟨k, hk⟩, hni⟩ := hc
      simp only [Function.Injective, not_forall] at hni
      obtain ⟨a, b, hxab, hab⟩ := hni
      refine le_trans ?_ (Finset.single_le_sum (fun a _ => Finset.sum_nonneg
        (fun b _ => hnn a b)) (Finset.mem_univ a))
      refine le_trans ?_ (Finset.single_le_sum (fun b _ => hnn a b) (Finset.mem_univ b))
      rw [if_pos hab]
      by_cases hxa : x a = u
      · have : x a = u ∧ x b = u := ⟨hxa, hxab ▸ hxa⟩
        rw [if_pos this, mul_one]
        have : 0 ≤ ∑ k, iidWeight F x * (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0) :=
          Finset.sum_nonneg (fun k _ => mind _ hw0 _)
        linarith
      · have h0 : 0 ≤ iidWeight F x * (if x a = u ∧ x b = u then (1 : ℝ) else 0) := by
          split_ifs <;> simp [hw0]
        have h1 : iidWeight F x ≤
            ∑ k, iidWeight F x * (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0) := by
          refine le_trans ?_ (Finset.single_le_sum (f := fun k => iidWeight F x *
            (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0))
            (fun k _ => mind _ hw0 _) (Finset.mem_univ k))
          rw [if_pos ⟨hxab, hxa, hk⟩, mul_one]
        linarith
    · exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hnn a b))
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_comm]
  have hab_bound : ∀ a b : Fin n, ∑ x ∈ X, (if a ≠ b then (iidWeight F x *
      (if x a = u ∧ x b = u then (1 : ℝ) else 0) + ∑ k, iidWeight F x *
        (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0)) else 0) ≤
          F.w u * F.w u + n * (c * F.w u) := by
    intro a b
    have hpos : 0 ≤ F.w u * F.w u + n * (c * F.w u) := by
      have := F.w_nonneg u hu_mem; positivity
    by_cases hab : a = b
    · simp only [hab, ne_eq, not_true_eq_false, if_false, Finset.sum_const_zero]; exact hpos
    · simp only [ne_eq, hab, not_false_eq_true, if_true]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      have h2 : ∑ k : Fin n, ∑ x ∈ X, iidWeight F x *
          (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0) ≤ ∑ k : Fin n, c * F.w u :=
        Finset.sum_le_sum (fun k _ => E2 a b k hab)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      linarith [E1 a b hab]
  calc ∑ a, ∑ x ∈ X, ∑ b, (if a ≠ b then (iidWeight F x *
        (if x a = u ∧ x b = u then (1 : ℝ) else 0) + ∑ k, iidWeight F x *
          (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0)) else 0)
      = ∑ a, ∑ b, ∑ x ∈ X, (if a ≠ b then (iidWeight F x *
        (if x a = u ∧ x b = u then (1 : ℝ) else 0) + ∑ k, iidWeight F x *
          (if x a = x b ∧ x a ≠ u ∧ x k = u then (1 : ℝ) else 0)) else 0) := by
        apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, (F.w u * F.w u + n * (c * F.w u)) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hab_bound a b))
    _ = (n : ℝ) * n * (F.w u * F.w u + n * (c * F.w u)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ 2 / (n : ℝ) ^ 2 := by
        rw [hwu]
        have hn0 : (0 : ℝ) < n := by linarith
        have : (n : ℝ) * n * (n * (c * (1 / (n : ℝ) ^ 2))) ≤ 1 / (n : ℝ) ^ 2 := by
          have : (n : ℝ) * n * (n * (c * (1 / (n : ℝ) ^ 2))) = n ^ 3 * c * (1 / (n : ℝ) ^ 2) := by
            ring
          rw [this]
          have h3 : (n : ℝ) ^ 3 * c ≤ 1 := by
            have : (n : ℝ) ^ 3 * c ≤ (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 3) :=
              mul_le_mul_of_nonneg_left hc1 (by positivity)
            rw [mul_one_div_cancel (by positivity)] at this
            exact this
          have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
          nlinarith
        have : (n : ℝ) * n * (1 / (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2)) = 1 / (n : ℝ) ^ 2 := by
          field_simp
        have e : (n : ℝ) * n * (1 / (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2) + n * (c * (1 / (n : ℝ) ^ 2)))
            = (n : ℝ) * n * (1 / (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2)) +
              (n : ℝ) * n * (n * (c * (1 / (n : ℝ) ^ 2))) := by ring
        rw [e]
        have : 2 / (n : ℝ) ^ 2 = 1 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 := by ring
        linarith


/-! ### G. Display (2)–(3) combined with the coupling and the symmetry identity -/

lemma main_bound (n : ℕ) (hn : 1 ≤ n) (F : FinDist) (v : Fin (n ^ 3) → ℝ) (u : ℝ)
    (hF : IsHardInstance n F v u) (R : StoppingRule 0 n) (ε : ℝ) (hε : 0 < ε)
    (V : Set ℕ) (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (h : ValueObliviousWith ε R V q)
    (hVs : ∀ y ∈ F.supp, ∃ m ∈ V, y = (m : ℝ)) :
    expStop F R ≤ (probMaxEq F n u * (recordRuleSuccess q hq + n * ε) + 2 / (n : ℝ) ^ 2) * u
      + u / (n : ℝ) ^ 3 := by
  classical
  set X := Fintype.piFinset (fun _ : Fin n => F.supp) with hXdef
  set S := recordRuleSuccess q hq
  set Y := X.filter (fun x => (∃ j, x j = u) ∧ Function.Injective x)
  have hu_mem := hard_u_mem hF
  have hu0 : 0 ≤ u := F.supp_nonneg u hu_mem
  have hS0 : 0 ≤ S := by
    simp only [S, recordRuleSuccess]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun σ _ => pickMaxProb_nonneg _ _)
  -- Step 1
  have step1 : expStop F R ≤
      (∑ x ∈ X, iidWeight F x * (if ∃ j, x j = u then pickMaxProb R x else 0)) * u
        + u / (n : ℝ) ^ 3 := by
    rw [expStop_zero]
    calc ∑ x ∈ X, iidWeight F x * ∑ i, stopProb R ![] x i * x i
        ≤ ∑ x ∈ X, iidWeight F x * ((if ∃ j, x j = u then pickMaxProb R x else 0) * u
            + u / (n : ℝ) ^ 3) :=
          Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left
            (payoff_le n hn F v u hF R x hx) (iidWeight_nonneg F x hx))
      _ = (∑ x ∈ X, iidWeight F x * (if ∃ j, x j = u then pickMaxProb R x else 0)) * u
            + (∑ x ∈ X, iidWeight F x) * (u / (n : ℝ) ^ 3) := by
          rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _; ring
      _ = _ := by rw [sum_iidWeight]; ring
  -- Step 2: pointwise split
  have step2 : ∀ x ∈ X, iidWeight F x * (if ∃ j, x j = u then pickMaxProb R x else 0) ≤
      (if (∃ j, x j = u) ∧ Function.Injective x then
          iidWeight F x * pickMaxProb (hatRule q hq) x + (n * ε) * iidWeight F x else 0) +
        (if (∃ j, x j = u) ∧ ¬ Function.Injective x then iidWeight F x else 0) := by
    intro x hx
    have hw0 := iidWeight_nonneg F x hx
    have hx' := Fintype.mem_piFinset.mp hx
    by_cases hex : ∃ j, x j = u
    · rw [if_pos hex]
      by_cases hinj : Function.Injective x
      · rw [if_pos ⟨hex, hinj⟩, if_neg (fun hh => hh.2 hinj), add_zero]
        -- write x as a cast of a natural vector in V
        set s : Fin n → ℕ := fun j => ⌊x j⌋₊
        have hxs : ∀ j, x j = (s j : ℝ) := by
          intro j
          obtain ⟨m, _, hm⟩ := hVs (x j) (hx' j)
          simp only [s, hm, Nat.floor_natCast]
        have hsV : ∀ j, s j ∈ V := by
          intro j
          obtain ⟨m, hmV, hm⟩ := hVs (x j) (hx' j)
          simp only [s, hm, Nat.floor_natCast]; exact hmV
        have hsinj : Function.Injective s := by
          intro a b hab
          apply hinj
          rw [hxs a, hxs b, hab]
        have hxeq : x = fun j => (s j : ℝ) := funext hxs
        have hc := coupling n ε hε R V q hq h s hsV hsinj
        rw [← hxeq] at hc
        nlinarith
      · rw [if_neg (fun hh => hinj hh.2), if_pos ⟨hex, hinj⟩, zero_add]
        have := pickMaxProb_le_one R x
        have := pickMaxProb_nonneg R x
        nlinarith
    · rw [if_neg hex, mul_zero, if_neg (fun hh => hex hh.1), if_neg (fun hh => hex hh.1)]
      simp
  -- Step 3: symmetry
  have hYsym : ∑ x ∈ Y, iidWeight F x * pickMaxProb (hatRule q hq) x =
      (∑ x ∈ Y, iidWeight F x) * S := by
    apply sum_sym q hq Y (iidWeight F)
    · intro x hx σ
      simp only [Y, Finset.mem_filter] at hx ⊢
      obtain ⟨hxX, ⟨j, hj⟩, hinj⟩ := hx
      refine ⟨?_, ⟨σ.symm j, by simp [hj]⟩, hinj.comp σ.injective⟩
      rw [Fintype.mem_piFinset] at hxX ⊢
      intro i; exact hxX (σ i)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2.2
    · intro x _ σ
      unfold iidWeight
      exact Equiv.prod_comp σ (fun j => F.w (x j))
  -- Step 4: P(Y) ≤ P(max = u)
  have hPY : ∑ x ∈ Y, iidWeight F x ≤ probMaxEq F n u := by
    unfold probMaxEq
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hc : (∃ j, x j = u) ∧ Function.Injective x
    · rw [if_pos hc, if_pos ((hard_max_iff hn hF x hx).mpr hc.1)]
    · rw [if_neg hc]
      split_ifs
      · exact iidWeight_nonneg F x hx
      · exact le_refl 0
  have hPY0 : 0 ≤ ∑ x ∈ Y, iidWeight F x :=
    Finset.sum_nonneg (fun x hx => iidWeight_nonneg F x (Finset.mem_filter.mp hx).1)
  -- Step 5: collision
  have hcol := collision n hn F v u hF
  -- combine
  have hsum : ∑ x ∈ X, iidWeight F x * (if ∃ j, x j = u then pickMaxProb R x else 0) ≤
      (∑ x ∈ Y, iidWeight F x) * (S + n * ε) + 2 / (n : ℝ) ^ 2 := by
    refine le_trans (Finset.sum_le_sum step2) ?_
    rw [Finset.sum_add_distrib]
    have e1 : ∑ x ∈ X, (if (∃ j, x j = u) ∧ Function.Injective x then
          iidWeight F x * pickMaxProb (hatRule q hq) x + (n * ε) * iidWeight F x else 0) =
        ∑ x ∈ Y, iidWeight F x * pickMaxProb (hatRule q hq) x +
          (n * ε) * ∑ x ∈ Y, iidWeight F x := by
      rw [← Finset.sum_filter, Finset.sum_add_distrib, Finset.mul_sum]
    rw [e1, hYsym]
    have : (∑ x ∈ Y, iidWeight F x) * S + (n * ε) * ∑ x ∈ Y, iidWeight F x =
        (∑ x ∈ Y, iidWeight F x) * (S + n * ε) := by ring
    linarith
  have hSn : 0 ≤ S + n * ε := by positivity
  have hfin : (∑ x ∈ Y, iidWeight F x) * (S + n * ε) ≤ probMaxEq F n u * (S + n * ε) :=
    mul_le_mul_of_nonneg_right hPY hSn
  have := mul_le_mul_of_nonneg_right (le_trans hsum (by linarith : (∑ x ∈ Y, iidWeight F x) *
    (S + n * ε) + 2 / (n : ℝ) ^ 2 ≤ probMaxEq F n u * (S + n * ε) + 2 / (n : ℝ) ^ 2)) hu0
  linarith

end UnknownProphet.NoSamples.Thm2Aux

open UnknownProphet.NoSamples UnknownProphet.NoSamples.Thm2Aux in
theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ R : StoppingRule 0 n,
      ∃ F : FinDist, 0 < expMax F n ∧
        expStop F R ≤ (Real.exp (-1) + δ) * expMax F n := by
  obtain ⟨n1, hn1⟩ := eq_4 (δ / 2) (by linarith)
  refine ⟨max n1 (⌈24 / δ⌉₊ + 1), fun n hn R => ?_⟩
  have hn1' : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hnc : ⌈24 / δ⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hnc
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnbig : 24 / δ < n := by
    have h1 : 24 / δ ≤ (⌈24 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈24 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnc
    push_cast at h2
    linarith
  have hδn : 24 < δ * n := by
    rw [div_lt_iff₀ hδ] at hnbig; linarith
  by_contra hcon
  push Not at hcon
  -- the rule would have guarantee 1/e + δ
  have hα : 0 < Real.exp (-1) + δ := by positivity
  have hG : HasGuarantee R (Real.exp (-1) + δ) := by
    intro F
    by_cases hF : 0 < expMax F n
    · exact (hcon F hF).le
    · push Not at hF
      have := expStop_nonneg F R
      nlinarith
  set ε : ℝ := 1 / (n : ℝ) ^ 2 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨R', hR', V, hV, q, hq⟩ := lemma_1 ε hε 0 n (Real.exp (-1) + δ) ⟨R, hG⟩
  have hqI : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i => (hq i).1
  obtain ⟨F, v, u, hF, hu, hVs⟩ := exists_hard n hn V hV
  have hmain := main_bound n hn F v u hF R' ε hε V q hqI hq hVs
  obtain ⟨hA, _, hC⟩ := eq_1 n hn F v u hF
  have hS := hn1 n hn1' q hqI
  have hguar := hR' F
  set P := probMaxEq F n u
  set S := recordRuleSuccess q hqI
  have hP1 : 1 / (2 * n) ≤ P := by
    refine le_trans ?_ hC
    rw [div_le_div_iff₀ (by positivity) hnpos]
    have : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have hnε : (n : ℝ) * ε = 1 / n := by rw [hεdef]; field_simp
  -- chain
  have h1 : (Real.exp (-1) + δ) * (P * u) ≤ (P * (S + 1 / n) + 2 / (n : ℝ) ^ 2) * u
      + u / (n : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hA hα.le
    rw [hnε] at hmain
    linarith
  -- divide by u
  have h2 : (Real.exp (-1) + δ) * P ≤ P * (S + 1 / n) + 2 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 3 := by
    have e : (P * (S + 1 / n) + 2 / (n : ℝ) ^ 2) * u + u / (n : ℝ) ^ 3 =
        (P * (S + 1 / n) + 2 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 3) * u := by ring
    rw [e, ← mul_assoc] at h1
    exact le_of_mul_le_mul_right h1 hu
  have h3 : 1 / (n : ℝ) ^ 3 ≤ 1 / (n : ℝ) ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hP0 : 0 ≤ P := le_trans (by positivity) hP1
  -- P (δ/2 - 1/n) ≤ 3/n²
  have h4 : P * (δ / 2 - 1 / n) ≤ 3 / (n : ℝ) ^ 2 := by
    have hPS : P * S ≤ P * (Real.exp (-1) + δ / 2) := mul_le_mul_of_nonneg_left hS hP0
    have e1 : P * (S + 1 / n) = P * S + P * (1 / n) := by ring
    have e2 : (Real.exp (-1) + δ) * P = P * Real.exp (-1) + P * δ := by ring
    have e3 : P * (Real.exp (-1) + δ / 2) = P * Real.exp (-1) + P * δ / 2 := by ring
    have e4 : P * (δ / 2 - 1 / n) = P * δ / 2 - P * (1 / n) := by ring
    rw [e4]; rw [e1, e2] at h2; rw [e3] at hPS
    have e5 : 3 / (n : ℝ) ^ 2 = 2 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 := by ring
    rw [e5]
    linarith
  have h5 : 1 / (n : ℝ) ≤ δ / 4 := by
    rw [div_le_iff₀ hnpos]; nlinarith
  have h6 : P * (δ / 4) ≤ 3 / (n : ℝ) ^ 2 := by
    have : P * (δ / 4) ≤ P * (δ / 2 - 1 / n) := mul_le_mul_of_nonneg_left (by linarith) hP0
    linarith
  have h7 : 1 / (2 * n) * (δ / 4) ≤ 3 / (n : ℝ) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right hP1 (by positivity)) h6
  have h8 : δ * n ≤ 24 := by
    have e1 : 1 / (2 * (n : ℝ)) * (δ / 4) = δ * n / (8 * (n : ℝ) ^ 2) := by
      field_simp; ring
    have e2 : 3 / (n : ℝ) ^ 2 = 24 / (8 * (n : ℝ) ^ 2) := by
      field_simp; ring
    rw [e1, e2] at h7
    exact (div_le_div_iff_of_pos_right (by positivity)).mp h7
  linarith
