-- Prove2me | solution 1 for RefMNLPricing.PromoInsensitive.observation_p24
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:09:03.930797+00:00
-- url     : https://prove2.me/submissions/6699723f-f39a-4636-b2a7-63dc8df29aa4

import Mathlib
import Definitions.Def_RefMNLPricing_PromoInsensitive_Model
set_option autoImplicit false

open RefMNLPricing.Myopic

lemma rmp_rev_eq {n : ℕ} (a b cp cm : Fin n → ℝ) (p r : Fin n → ℝ) :
    revenue a b cp cm p r = (∑ i, p i * Real.exp (util a b cp cm p r i)) /
      (1 + ∑ k, Real.exp (util a b cp cm p r k)) := by
  unfold revenue share
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_div_assoc]

lemma rmp_den_pos {n : ℕ} (a b cp cm : Fin n → ℝ) (p r : Fin n → ℝ) :
    0 < 1 + ∑ k, Real.exp (util a b cp cm p r k) := by positivity

lemma rmp_ge_iff {n : ℕ} (a b cp cm : Fin n → ℝ) (p r : Fin n → ℝ) (P : ℝ) :
    P ≤ revenue a b cp cm p r ↔
      0 ≤ ∑ i, (p i - P) * Real.exp (util a b cp cm p r i) - P := by
  rw [rmp_rev_eq, le_div_iff₀ (rmp_den_pos a b cp cm p r)]
  have : ∑ i, (p i - P) * Real.exp (util a b cp cm p r i) =
      ∑ i, p i * Real.exp (util a b cp cm p r i) - P * ∑ i, Real.exp (util a b cp cm p r i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  constructor <;> intro h <;> nlinarith

lemma rmp_rev_nonneg {n : ℕ} (a b cp cm : Fin n → ℝ) (p r : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ revenue a b cp cm p r := by
  rw [rmp_rev_eq]
  exact div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (Real.exp_pos _).le)
    (rmp_den_pos a b cp cm p r).le

lemma rmp_rev_le {n : ℕ} (a b cp cm : Fin n → ℝ) (p r : Fin n → ℝ) (pH : ℝ) (hpH : 0 ≤ pH)
    (hp : ∀ i, p i ≤ pH) : revenue a b cp cm p r ≤ pH := by
  rw [rmp_rev_eq, div_le_iff₀ (rmp_den_pos a b cp cm p r)]
  have : ∑ i, p i * Real.exp (util a b cp cm p r i) ≤ ∑ i, pH * Real.exp (util a b cp cm p r i) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hp i) (Real.exp_pos _).le
  rw [← Finset.mul_sum] at this
  nlinarith

lemma rmp_cont {n : ℕ} (a b cp cm : Fin n → ℝ) :
    Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => revenue a b cp cm z.1 z.2) := by
  have hu : ∀ i, Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => util a b cp cm z.1 z.2 i) := by
    intro i
    unfold util
    fun_prop
  have hs : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ∑ i, z.1 i * Real.exp (util a b cp cm z.1 z.2 i)) :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul
      (Real.continuous_exp.comp (hu i))
  have hd : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => 1 + ∑ k, Real.exp (util a b cp cm z.1 z.2 k)) :=
    continuous_const.add (continuous_finsetSum _ fun i _ => Real.continuous_exp.comp (hu i))
  have : (fun z : (Fin n → ℝ) × (Fin n → ℝ) => revenue a b cp cm z.1 z.2) =
      fun z => (∑ i, z.1 i * Real.exp (util a b cp cm z.1 z.2 i)) /
        (1 + ∑ k, Real.exp (util a b cp cm z.1 z.2 k)) := by
    funext z; exact rmp_rev_eq a b cp cm z.1 z.2
  rw [this]
  exact hs.div hd fun z => (rmp_den_pos a b cp cm z.1 z.2).ne'

lemma rmp_key {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH) (hgain : ∀ i, cp i = 0) :
    ∃ x : Fin n → ℝ, InBox pH x ∧
      ∀ p r, InBox pH p → InBox pH r → revenue a b cp cm p r ≤ revenue a b cp cm x x := by
  have hK : IsCompact ((Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) pH) ×ˢ
      (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) pH)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hne : ((Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) pH) ×ˢ
      (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) pH)).Nonempty :=
    ⟨(fun _ => 0, fun _ => 0), fun i _ => ⟨le_rfl, hpH.le⟩, fun i _ => ⟨le_rfl, hpH.le⟩⟩
  obtain ⟨⟨p, r⟩, hmem, hmax⟩ := hK.exists_isMaxOn hne (rmp_cont a b cp cm).continuousOn
  have hpbox : InBox pH p := fun i => hmem.1 i (Set.mem_univ i)
  have hrbox : InBox pH r := fun i => hmem.2 i (Set.mem_univ i)
  have hmax' : ∀ p0 r0, InBox pH p0 → InBox pH r0 →
      revenue a b cp cm p0 r0 ≤ revenue a b cp cm p r := by
    intro p0 r0 hp0 hr0
    exact hmax (show (p0, r0) ∈ _ from ⟨fun i _ => hp0 i, fun i _ => hr0 i⟩)
  set P := revenue a b cp cm p r with hP
  have hPH : P ≤ pH := rmp_rev_le a b cp cm p r pH hpH.le (fun i => (hpbox i).2)
  have hΦ0 : 0 ≤ ∑ i, (p i - P) * Real.exp (util a b cp cm p r i) - P :=
    (rmp_ge_iff a b cp cm p r P).1 le_rfl
  set x : Fin n → ℝ := fun i => max (p i) P with hx
  have hxbox : InBox pH x := fun i =>
    ⟨le_trans (hpbox i).1 (le_max_left _ _), max_le (hpbox i).2 hPH⟩
  have step1 : ∑ i, (p i - P) * Real.exp (util a b cp cm p r i) ≤
      ∑ i, (x i - P) * Real.exp (util a b cp cm x r i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : p i < P
    · have : x i = P := max_eq_right h.le
      rw [this, sub_self, zero_mul]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    · have : x i = p i := max_eq_left (not_lt.mp h)
      simp only [util, this]
      exact le_rfl
  have step2 : ∑ i, (x i - P) * Real.exp (util a b cp cm x r i) ≤
      ∑ i, (x i - P) * Real.exp (util a b cp cm x x i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (by simp only [hx]; linarith [le_max_right (p i) P])
    apply Real.exp_le_exp.mpr
    simp only [util, hgain i, zero_mul, sub_self, max_self, mul_zero, add_zero]
    have := mul_nonneg (hcm i) (le_max_right (x i - r i) 0)
    linarith
  have hge : P ≤ revenue a b cp cm x x := by
    rw [rmp_ge_iff]
    linarith
  exact ⟨x, hxbox, fun p0 r0 hp0 hr0 => (hmax' p0 r0 hp0 hr0).trans hge⟩

theorem solution {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : RefMNLPricing.PromoInsensitive.CeilingOK a b cp cm pH)
    (hgain : ∀ i, cp i = 0) :
    ∃ x : Fin n → ℝ, RefMNLPricing.Myopic.InBox pH x ∧
      (∀ p, RefMNLPricing.Myopic.InBox pH p → RefMNLPricing.Myopic.revenue a b cp cm p x ≤ RefMNLPricing.Myopic.revenue a b cp cm x x) ∧
      (∀ p r, RefMNLPricing.Myopic.InBox pH p → RefMNLPricing.Myopic.InBox pH r → RefMNLPricing.Myopic.revenue a b cp cm p r ≤ RefMNLPricing.Myopic.revenue a b cp cm x x) := by
  obtain ⟨x, hx, hmax⟩ := rmp_key a b cp cm pH hcm hpH hgain
  exact ⟨x, hx, fun p hp => hmax p x hp hx, hmax⟩
