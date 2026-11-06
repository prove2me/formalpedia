-- Prove2me | solution 2 for QEC.Locality.card_daiLiRectangleSideStrip_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:30:10.521198+00:00
-- url     : https://prove2.me/submissions/8138cfeb-fc00-4a0e-b0cd-b28d25dc6c76

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QLAux.floor_close {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : ⌊u⌋₊ = ⌊v⌋₊) : (u - v) ^ 2 < 1 := by
  have h1 := Nat.floor_le hu
  have h2 := Nat.floor_le hv
  have h3 := Nat.lt_floor_add_one u
  have h4 := Nat.lt_floor_add_one v
  rw [h] at h1 h3
  nlinarith

theorem QLAux.card_rect_le (E : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (ha : 1 ≤ upper.1 - lower.1) (hb : 1 ≤ upper.2 - lower.2) :
    ((E.qubitsInRectangle lower upper).card : ℝ) ≤ 6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have s2le : Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  set a := upper.1 - lower.1 with ha_def
  set b := upper.2 - lower.2 with hb_def
  let f : ι → ℕ × ℕ := fun p =>
    (⌊((E.point p).1 - lower.1) * Real.sqrt 2⌋₊, ⌊((E.point p).2 - lower.2) * Real.sqrt 2⌋₊)
  have hmem : ∀ p ∈ E.qubitsInRectangle lower upper,
      ((E.point p).1 - lower.1 ≥ 0 ∧ (E.point p).1 - lower.1 ≤ a) ∧
        ((E.point p).2 - lower.2 ≥ 0 ∧ (E.point p).2 - lower.2 ≤ b) := by
    intro p hp
    have hp' : E.point p ∈ rectangle lower upper := (Finset.mem_filter.1 hp).2
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp'
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hmaps : ∀ p ∈ E.qubitsInRectangle lower upper,
      f p ∈ (Finset.range (⌊a * Real.sqrt 2⌋₊ + 1)) ×ˢ (Finset.range (⌊b * Real.sqrt 2⌋₊ + 1)) := by
    intro p hp
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hmem p hp
    simp only [Finset.mem_product, Finset.mem_range, f]
    constructor
    · have : ⌊((E.point p).1 - lower.1) * Real.sqrt 2⌋₊ ≤ ⌊a * Real.sqrt 2⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right h2 s2pos.le)
      omega
    · have : ⌊((E.point p).2 - lower.2) * Real.sqrt 2⌋₊ ≤ ⌊b * Real.sqrt 2⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right h4 s2pos.le)
      omega
  have hinj : Set.InjOn f (E.qubitsInRectangle lower upper : Set ι) := by
    intro p hp q hq hpq
    by_contra hne
    have hd := E.unitSeparated hne
    obtain ⟨⟨hp1, hp2⟩, ⟨hp3, hp4⟩⟩ := hmem p hp
    obtain ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩ := hmem q hq
    have e1 : ⌊((E.point p).1 - lower.1) * Real.sqrt 2⌋₊ = ⌊((E.point q).1 - lower.1) * Real.sqrt 2⌋₊ :=
      congrArg Prod.fst hpq
    have e2 : ⌊((E.point p).2 - lower.2) * Real.sqrt 2⌋₊ = ⌊((E.point q).2 - lower.2) * Real.sqrt 2⌋₊ :=
      congrArg Prod.snd hpq
    have c1 := QLAux.floor_close (mul_nonneg hp1 s2pos.le) (mul_nonneg hq1 s2pos.le) e1
    have c2 := QLAux.floor_close (mul_nonneg hp3 s2pos.le) (mul_nonneg hq3 s2pos.le) e2
    have k1 : (((E.point p).1 - lower.1) * Real.sqrt 2 - ((E.point q).1 - lower.1) * Real.sqrt 2) ^ 2 =
        ((E.point p).1 - (E.point q).1) ^ 2 * 2 := by
      have : (((E.point p).1 - lower.1) * Real.sqrt 2 - ((E.point q).1 - lower.1) * Real.sqrt 2) =
          ((E.point p).1 - (E.point q).1) * Real.sqrt 2 := by ring
      rw [this, mul_pow, s2]
    have k2 : (((E.point p).2 - lower.2) * Real.sqrt 2 - ((E.point q).2 - lower.2) * Real.sqrt 2) ^ 2 =
        ((E.point p).2 - (E.point q).2) ^ 2 * 2 := by
      have : (((E.point p).2 - lower.2) * Real.sqrt 2 - ((E.point q).2 - lower.2) * Real.sqrt 2) =
          ((E.point p).2 - (E.point q).2) * Real.sqrt 2 := by ring
      rw [this, mul_pow, s2]
    rw [k1] at c1
    rw [k2] at c2
    have hd' : 1 ≤ Real.sqrt (((E.point p).1 - (E.point q).1) ^ 2 + ((E.point p).2 - (E.point q).2) ^ 2) := hd
    have hd'' := (Real.le_sqrt' (by norm_num)).1 hd'
    nlinarith
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at hcard
  have hA : ((⌊a * Real.sqrt 2⌋₊ + 1 : ℕ) : ℝ) ≤ (Real.sqrt 2 + 1) * a := by
    have := Nat.floor_le (show 0 ≤ a * Real.sqrt 2 by positivity)
    push_cast
    nlinarith
  have hB : ((⌊b * Real.sqrt 2⌋₊ + 1 : ℕ) : ℝ) ≤ (Real.sqrt 2 + 1) * b := by
    have := Nat.floor_le (show 0 ≤ b * Real.sqrt 2 by positivity)
    push_cast
    nlinarith
  have hcard' : (((E.qubitsInRectangle lower upper).card : ℕ) : ℝ) ≤
      ((⌊a * Real.sqrt 2⌋₊ + 1 : ℕ) : ℝ) * ((⌊b * Real.sqrt 2⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hab : 0 ≤ a * b := by nlinarith
  calc (((E.qubitsInRectangle lower upper).card : ℕ) : ℝ)
      ≤ ((⌊a * Real.sqrt 2⌋₊ + 1 : ℕ) : ℝ) * ((⌊b * Real.sqrt 2⌋₊ + 1 : ℕ) : ℝ) := hcard'
    _ ≤ ((Real.sqrt 2 + 1) * a) * ((Real.sqrt 2 + 1) * b) :=
        mul_le_mul hA hB (by positivity) (by nlinarith)
    _ = (3 + 2 * Real.sqrt 2) * (a * b) := by nlinarith [s2]
    _ ≤ 6 * (a * b) := by nlinarith

theorem solution
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (lower upper : ℝ × ℝ)
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.2 - lower.2 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 0).card : ℝ) ≤
      12 * ell * (upper.2 - lower.2 - 4 * ell) := by
  have h : daiLiRectangleSideStripQubits embedding ell lower upper 0 =
      embedding.qubitsInRectangle (lower.1 - ell, lower.2 + 2 * ell)
        (lower.1 + ell, upper.2 - 2 * ell) := rfl
  rw [h]
  have := QLAux.card_rect_le embedding (lower.1 - ell, lower.2 + 2 * ell)
    (lower.1 + ell, upper.2 - 2 * ell) (by simp only; linarith) (by simp only; linarith)
  refine this.trans (le_of_eq ?_)
  simp only
  ring
