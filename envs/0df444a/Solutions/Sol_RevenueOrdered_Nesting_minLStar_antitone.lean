-- Prove2me | solution 1 for RevenueOrdered.Nesting.minLStar_antitone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:14:17.460439+00:00
-- url     : https://prove2.me/submissions/431dbcf4-772c-42d7-9b76-7c18c23dee8e

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

theorem solution {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : RevenueOrdered.Nesting.IsRegular P) (hr : ∀ x, 0 < r x)
    {δ₁ δ₂ : ℝ} (hδ₁ : δ₁ + topRevenue r ≥ 0) (hδ : δ₁ ≤ δ₂) :
    minLStar P r δ₂ ≤ minLStar P r δ₁ := by
  by_contra hcon
  push_neg at hcon
  have h1mem : minLStar P r δ₁ ∈ lStar P r δ₁ := Finset.min'_mem _ _
  have h2mem : minLStar P r δ₂ ∈ lStar P r δ₂ := Finset.min'_mem _ _
  set ℓ₁ := minLStar P r δ₁ with hℓ₁
  set ℓ₂ := minLStar P r δ₂ with hℓ₂
  unfold lStar argmaxLevels at h1mem h2mem
  rw [Finset.mem_filter] at h1mem h2mem
  obtain ⟨hl1, hmax1⟩ := h1mem
  obtain ⟨hl2, hmax2⟩ := h2mem
  have hl1' : 1 ≤ ℓ₁ ∧ ℓ₁ ≤ numVals r := by simpa [levels] using hl1
  have hl2' : 1 ≤ ℓ₂ ∧ ℓ₂ ≤ numVals r := by simpa [levels] using hl2
  -- total purchase probability is monotone
  have hQ : ∑ x ∈ roSet r ℓ₂, P x (roSet r ℓ₂) ≤ ∑ x ∈ roSet r ℓ₁, P x (roSet r ℓ₁) := by
    have := hP.noPurchase_mono _ _ (nes_roSet_anti r hl1'.1 hcon.le hl2'.2)
    unfold noPurchase at this
    linarith
  have hf1 : shiftedRevenue P r δ₁ ℓ₂ ≤ shiftedRevenue P r δ₁ ℓ₁ := by
    rw [hmax1]; exact Finset.le_sup' _ hl2
  have hf2 : shiftedRevenue P r δ₂ ℓ₂ ≤ shiftedRevenue P r δ₂ ℓ₁ := by
    rw [nes_shifted_eq] at hf1 ⊢
    rw [nes_shifted_eq] at hf1 ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hδ) (sub_nonneg.2 hQ)]
  have hmem : ℓ₁ ∈ lStar P r δ₂ := by
    unfold lStar argmaxLevels
    rw [Finset.mem_filter]
    refine ⟨hl1, le_antisymm (Finset.le_sup' _ hl1) ?_⟩
    rw [← hmax2]; exact hf2
  have hfin : ℓ₂ ≤ ℓ₁ := Finset.min'_le _ _ hmem
  omega
