-- Prove2me | solution 1 for RevenueOrdered.Nesting.marginalValue_le_topRevenue
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:14:24.278994+00:00
-- url     : https://prove2.me/submissions/fdb4b311-2bec-400e-a77a-6127c9a02768

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_LStar
import Definitions.Def_RevenueOrdered_Nesting_DynamicProgram

set_option autoImplicit false
open RevenueOrdered.Nesting
open RevenueOrdered.Ratio (roSet noPurchase level numVals)

theorem nes_jIdx_succ {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) (hq : 1 ≤ q) (ℓ : ℕ) :
    jIdx P r (t + 1) q ℓ =
      shiftedRevenue P r (-marginalValue P r t q) ℓ + jVal P r t q := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have e1 : jIdx P r (t + 1) (q' + 1) ℓ =
      ∑ x ∈ roSet r ℓ, P x (roSet r ℓ) * (r x + jVal P r t q') +
        noPurchase P (roSet r ℓ) * jVal P r t (q' + 1) := rfl
  have e2 : marginalValue P r t (q' + 1) = jVal P r t (q' + 1) - jVal P r t q' := by
    simp [marginalValue]
  rw [e1, e2]
  unfold shiftedRevenue noPurchase
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mul_neg, Finset.sum_neg_distrib]
  ring

theorem nes_sup'_add {C : Type*} [Fintype C] [Nonempty C] (r : C → ℝ) (f : ℕ → ℝ) (c : ℝ) :
    (levels r).sup' (levels_nonempty r) (fun ℓ => f ℓ + c) =
      (levels r).sup' (levels_nonempty r) f + c := by
  exact (Finset.sup'_add (levels r) f c (levels_nonempty r)).symm

theorem nes_jVal_succ {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) (hq : 1 ≤ q) :
    jVal P r (t + 1) q =
      (levels r).sup' (levels_nonempty r) (shiftedRevenue P r (-marginalValue P r t q)) +
        jVal P r t q := by
  unfold jVal
  have : jIdx P r (t + 1) q = fun ℓ => shiftedRevenue P r (-marginalValue P r t q) ℓ + jVal P r t q := by
    funext ℓ; exact nes_jIdx_succ P r t q hq ℓ
  rw [this]
  exact nes_sup'_add r _ _


theorem nes_argmax_shift {C : Type*} [Fintype C] [Nonempty C] (r : C → ℝ) (f : ℕ → ℝ) (c : ℝ) :
    argmaxLevels r (fun ℓ => f ℓ + c) = argmaxLevels r f := by
  unfold argmaxLevels
  simp only [nes_sup'_add]
  ext ℓ
  simp only [Finset.mem_filter]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

theorem nes_level_mono {C : Type*} [Fintype C] (r : C → ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ numVals r) : level r a ≤ level r b := by
  unfold level
  rw [dif_pos ⟨ha, by omega⟩, dif_pos ⟨by omega, hb⟩]
  exact (RevenueOrdered.Ratio.sortedVals r).monotone (Fin.mk_le_mk.mpr (by omega))

theorem nes_roSet_anti {C : Type*} [Fintype C] (r : C → ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ numVals r) : roSet r b ⊆ roSet r a := by
  intro x hx
  simp only [roSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact le_trans (nes_level_mono r ha hab hb) hx

theorem nes_shifted_eq {C : Type*} [Fintype C] (P : C → Finset C → ℝ) (r : C → ℝ) (δ : ℝ) (ℓ : ℕ) :
    shiftedRevenue P r δ ℓ =
      ∑ x ∈ roSet r ℓ, P x (roSet r ℓ) * r x + δ * ∑ x ∈ roSet r ℓ, P x (roSet r ℓ) := by
  unfold shiftedRevenue
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => by ring)


theorem nes_le_top {C : Type*} [Fintype C] [Nonempty C] (r : C → ℝ) (x : C) :
    r x ≤ topRevenue r := by
  have hmem : r x ∈ Set.range (RevenueOrdered.Ratio.sortedVals r) := by
    have e : Set.range (RevenueOrdered.Ratio.sortedVals r) =
        ↑(RevenueOrdered.Ratio.revVals r) := by
      unfold RevenueOrdered.Ratio.sortedVals
      exact Finset.range_orderEmbOfFin _ _
    rw [e]
    simp [RevenueOrdered.Ratio.revVals]
  obtain ⟨j, hj⟩ := hmem
  have hk : 1 ≤ numVals r ∧ numVals r ≤ numVals r := ⟨numVals_pos r, le_rfl⟩
  have htop : topRevenue r = RevenueOrdered.Ratio.sortedVals r ⟨numVals r - 1, by
      have := numVals_pos r; omega⟩ := by
    unfold topRevenue RevenueOrdered.Ratio.level
    rw [dif_pos hk]
  rw [htop, ← hj]
  apply (RevenueOrdered.Ratio.sortedVals r).monotone
  rw [Fin.le_def]
  have := j.isLt
  show j.val ≤ numVals r - 1
  omega

theorem nes_jVal_zero_q {C : Type*} [Fintype C] [Nonempty C] (P : C → Finset C → ℝ) (r : C → ℝ)
    (t : ℕ) : jVal P r t 0 = 0 := by
  unfold jVal
  cases t <;> simp [jIdx]

theorem nes_jVal_zero_t {C : Type*} [Fintype C] [Nonempty C] (P : C → Finset C → ℝ) (r : C → ℝ)
    (q : ℕ) : jVal P r 0 q = 0 := by
  unfold jVal
  simp [jIdx]

theorem nes_jIdx_unfold {C : Type*} [Fintype C] [Nonempty C] (P : C → Finset C → ℝ) (r : C → ℝ)
    (t q ℓ : ℕ) : jIdx P r (t + 1) (q + 1) ℓ =
      ∑ x ∈ roSet r ℓ, P x (roSet r ℓ) * (r x + jVal P r t q) +
        noPurchase P (roSet r ℓ) * jVal P r t (q + 1) := rfl

theorem nes_top_pos {C : Type*} [Fintype C] [Nonempty C] (r : C → ℝ) (hr : ∀ x, 0 < r x) :
    0 < topRevenue r := by
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  exact lt_of_lt_of_le (hr x) (nes_le_top r x)

theorem nes_marg_le {C : Type*} [Fintype C] [Nonempty C] {P : C → Finset C → ℝ} {r : C → ℝ}
    (hP : IsChoiceSystem P) (hr : ∀ x, 0 < r x) :
    ∀ t q : ℕ, 1 ≤ q → marginalValue P r t q ≤ topRevenue r := by
  intro t
  induction t with
  | zero =>
    intro q hq
    unfold marginalValue
    rw [nes_jVal_zero_t, nes_jVal_zero_t]
    simpa using (nes_top_pos r hr).le
  | succ t ih =>
    intro q hq
    obtain ⟨ℓ, hℓ, heq⟩ := Finset.exists_mem_eq_sup' (levels_nonempty r) (jIdx P r (t + 1) q)
    have hJ : jVal P r (t + 1) q = jIdx P r (t + 1) q ℓ := heq
    set S := roSet r ℓ with hS
    set top := topRevenue r with htop
    have ha : ∀ x, 0 ≤ P x S := fun x => hP.nonneg x S
    have hp0 : 0 ≤ noPurchase P S := hP.noPurchase_nonneg S
    have hrx : ∀ x, r x ≤ top := fun x => nes_le_top r x
    have hnp : noPurchase P S = 1 - ∑ x ∈ S, P x S := rfl
    have hfin : (∑ x ∈ S, P x S) * top + noPurchase P S * top = top := by rw [hnp]; ring
    have hun : ∀ q : ℕ, jIdx P r (t + 1) (q + 1) ℓ =
        ∑ x ∈ S, P x S * (r x + jVal P r t q) + noPurchase P S * jVal P r t (q + 1) :=
      fun q => nes_jIdx_unfold P r t q ℓ
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    unfold marginalValue
    rw [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos q' with h0 | h0
    · subst h0
      rw [nes_jVal_zero_q, hJ, hun, nes_jVal_zero_q]
      have ih1 : jVal P r t 1 ≤ top := by
        have := ih 1 le_rfl
        unfold marginalValue at this
        rw [nes_jVal_zero_q] at this
        simpa using this
      have h1 : ∑ x ∈ S, P x S * (r x + 0) ≤ (∑ x ∈ S, P x S) * top := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun x _ => by
          have := mul_le_mul_of_nonneg_left (hrx x) (ha x)
          linarith)
      have h2 : noPurchase P S * jVal P r t 1 ≤ noPurchase P S * top :=
        mul_le_mul_of_nonneg_left ih1 hp0
      linarith
    · obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
      have h2 : jIdx P r (t + 1) (q'' + 1) ℓ ≤ jVal P r (t + 1) (q'' + 1) :=
        Finset.le_sup' _ hℓ
      have ih1 : jVal P r t (q'' + 1) - jVal P r t q'' ≤ top := by
        have := ih (q'' + 1) (by omega)
        unfold marginalValue at this
        rwa [Nat.add_sub_cancel] at this
      have ih2 : jVal P r t (q'' + 1 + 1) - jVal P r t (q'' + 1) ≤ top := by
        have := ih (q'' + 1 + 1) (by omega)
        unfold marginalValue at this
        rwa [Nat.add_sub_cancel] at this
      rw [hJ]
      have hdiff : ∑ x ∈ S, P x S * (r x + jVal P r t (q'' + 1)) -
          ∑ x ∈ S, P x S * (r x + jVal P r t q'') =
          ∑ x ∈ S, P x S * (jVal P r t (q'' + 1) - jVal P r t q'') := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      have hb1 : ∑ x ∈ S, P x S * (jVal P r t (q'' + 1) - jVal P r t q'') ≤ (∑ x ∈ S, P x S) * top := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left ih1 (ha x) |>.trans_eq (by ring))
      have hb2 : noPurchase P S * (jVal P r t (q'' + 1 + 1) - jVal P r t (q'' + 1)) ≤
          noPurchase P S * top := mul_le_mul_of_nonneg_left ih2 hp0
      rw [hun] at h2 ⊢
      linarith

theorem solution {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : IsChoiceSystem P) (hr : ∀ x, 0 < r x)
    (t q : ℕ) (hq : 1 ≤ q) :
    marginalValue P r t q ≤ topRevenue r :=
  nes_marg_le hP hr t q hq
