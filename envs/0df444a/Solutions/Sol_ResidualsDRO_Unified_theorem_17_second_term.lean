-- Prove2me | solution 1 for ResidualsDRO.Unified.theorem_17_second_term
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:31:48.603917+00:00
-- url     : https://prove2.me/submissions/195bcd3b-3042-4074-8d9b-df6f02fb3e1b

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

/-- Deterministic Cauchy–Schwarz bound: for a nonempty set `𝔓` of probability vectors whose
squared deviations from uniform are all `≤ S`,
`|sup_p ∑ pᵢ cᵢ - (1/n) ∑ cᵢ| ≤ √(S · ∑ cᵢ²)`. -/
lemma rdro17_sup_dev {n : ℕ} (hn : 1 ≤ n) (𝔓 : Set (Fin n → ℝ))
    (h𝔓 : ∀ p ∈ 𝔓, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) (hne : 𝔓.Nonempty)
    (S : ℝ) (hS : ∀ p ∈ 𝔓, ∑ i, (p i - (n : ℝ)⁻¹) ^ 2 ≤ S) (cv : Fin n → ℝ) :
    |(⨆ p : 𝔓, ∑ i, (p : Fin n → ℝ) i * cv i) - (n : ℝ)⁻¹ * ∑ i, cv i| ≤
      Real.sqrt (S * ∑ i, cv i ^ 2) := by
  set B := Real.sqrt (S * ∑ i, cv i ^ 2)
  have hp : ∀ p ∈ 𝔓, |∑ i, p i * cv i - (n : ℝ)⁻¹ * ∑ i, cv i| ≤ B := by
    intro p hp
    have heq : ∑ i, p i * cv i - (n : ℝ)⁻¹ * ∑ i, cv i = ∑ i, (p i - (n : ℝ)⁻¹) * cv i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1; ext i; ring
    rw [heq]
    apply Real.abs_le_sqrt
    calc (∑ i, (p i - (n : ℝ)⁻¹) * cv i) ^ 2
        ≤ (∑ i, (p i - (n : ℝ)⁻¹) ^ 2) * ∑ i, cv i ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ S * ∑ i, cv i ^ 2 :=
          mul_le_mul_of_nonneg_right (hS p hp) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hbdd : BddAbove (Set.range fun p : 𝔓 => ∑ i, (p : Fin n → ℝ) i * cv i) := by
    refine ⟨(n : ℝ)⁻¹ * ∑ i, cv i + B, ?_⟩
    rintro _ ⟨p, rfl⟩
    have := hp p p.2
    linarith [le_abs_self (∑ i, (p : Fin n → ℝ) i * cv i - (n : ℝ)⁻¹ * ∑ i, cv i)]
  haveI : Nonempty 𝔓 := hne.to_subtype
  rw [abs_le]
  constructor
  · obtain ⟨p0, hp0⟩ := hne
    have h1 := le_ciSup hbdd ⟨p0, hp0⟩
    have h2 := hp p0 hp0
    simp only at h1
    linarith [neg_abs_le (∑ i, p0 i * cv i - (n : ℝ)⁻¹ * ∑ i, cv i)]
  · have : (⨆ p : 𝔓, ∑ i, (p : Fin n → ℝ) i * cv i) ≤ (n : ℝ)⁻¹ * ∑ i, cv i + B := by
      refine ciSup_le fun p => ?_
      have := hp p p.2
      linarith [le_abs_self (∑ i, (p : Fin n → ℝ) i * cv i - (n : ℝ)⁻¹ * ∑ i, cv i)]
    linarith

end ResidualsDRO.Unified

open ResidualsDRO.Unified

theorem solution
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx))
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) (h𝒵 : IsCompact 𝒵) (h𝒵ne : 𝒵.Nonempty)
    (h𝒴ne : D.𝒴.Nonempty) (h𝒴closed : IsClosed D.𝒴) (h𝒴convex : Convex ℝ D.𝒴)
    (hproj : IsProjection D.𝒴 D.proj)
    (hrange : ∀ (i : ℕ) (ω : Ω), D.fstar x + D.eps i ω ∈ D.𝒴)
    (hint : ∀ z ∈ 𝒵, Integrable (fun e => c z (D.fstar x + e)) Pε)
    (𝔓 : (n : ℕ) → Set (Fin n → ℝ))
    (h𝔓 : ∀ n, ∀ p ∈ 𝔓 n, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (h𝔓ne : ∀ n, 1 ≤ n → (𝔓 n).Nonempty)
    (r Cζ : ℝ)
    (h12 : Assumption12 𝔓 Cζ (1 + r))
    (h13 : Assumption13 P c D x Pε 𝒵)
    :
    IsBigOp P (fun n ω => ⨆ z ∈ 𝒵,
        ENNReal.ofReal |gstarS c D x 𝔓 n ω z - gstarN c D x n ω z|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) := by
  obtain ⟨hρ, hCζ, N12, hN12⟩ := h12
  obtain ⟨_, ⟨K0, hK0⟩, hlln⟩ := h13
  set K := max K0 0 with hK
  set M : ℝ := Real.sqrt (Cζ * (K + 1)) + 1 with hMdef
  have hM : 0 < M := by positivity
  intro δ hδ
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp ((hlln 1 one_pos).eventually (gt_mem_nhds hδ'))
  refine ⟨M, hM, max (max N0 N12) 1, fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn12 : N12 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  refine le_trans (measure_mono ?_) (hN0 n hn0).le
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  refine absurd hω (not_lt.mpr (iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal ?_))
  -- bound on the empirical second moment at `z`
  set Q := (n : ℝ)⁻¹ * ∑ i : Fin n, (c z (D.fstar x + D.eps i ω)) ^ 2 with hQ
  have hQle : Q ≤ K + 1 := by
    have h1 : ENNReal.ofReal |Q - ∫ e, (c z (D.fstar x + e)) ^ 2 ∂Pε| ≤ ENNReal.ofReal 1 :=
      le_trans (le_iSup₂ (f := fun z (_ : z ∈ 𝒵) => ENNReal.ofReal
        |(n : ℝ)⁻¹ * ∑ i : Fin n, (c z (D.fstar x + D.eps i ω)) ^ 2 -
          ∫ e, (c z (D.fstar x + e)) ^ 2 ∂Pε|) z hz) hcon
    rw [ENNReal.ofReal_le_ofReal_iff zero_le_one] at h1
    have h2 : ∫ e, (c z (D.fstar x + e)) ^ 2 ∂Pε ≤ K := (hK0 ⟨z, hz, rfl⟩).trans (le_max_left _ _)
    linarith [le_abs_self (Q - ∫ e, (c z (D.fstar x + e)) ^ 2 ∂Pε)]
  have hQnn : 0 ≤ Q := by positivity
  -- squared deviations bounded by the supremum of Assumption 12
  have hsupeq := hN12 n hn12 hn1
  have hbddS : BddAbove (Set.range fun p : 𝔓 n => ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2) := by
    refine ⟨n, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hp := h𝔓 n p p.2
    have hpi : ∀ i, (p : Fin n → ℝ) i ≤ 1 := fun i => by
      rw [← hp.2]
      exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
    have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn1)
    have hinv0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
    calc ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hp.1 i; have := hpi i
          nlinarith
      _ = n := by simp
  have hS : ∀ p ∈ 𝔓 n, ∑ i, (p i - (n : ℝ)⁻¹) ^ 2 ≤ Cζ * (n : ℝ) ^ (-(1 + r)) := by
    intro p hp
    rw [← hsupeq]
    exact le_ciSup hbddS (⟨p, hp⟩ : 𝔓 n)
  have hdev := rdro17_sup_dev hn1 (𝔓 n) (h𝔓 n) (h𝔓ne n hn1) _ hS
    (fun i => c z (D.fstar x + D.eps i ω))
  -- rewrite the bound
  have hrw : Cζ * (n : ℝ) ^ (-(1 + r)) * ∑ i : Fin n, (c z (D.fstar x + D.eps i ω)) ^ 2 =
      Cζ * Q * (n : ℝ) ^ (-r) := by
    rw [hQ, show -(1 + r) = -r + -1 by ring, Real.rpow_add hnpos, Real.rpow_neg_one]
    ring
  have hsq : Real.sqrt ((n : ℝ) ^ (-r)) = (n : ℝ) ^ (-(r / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]; congr 1; ring
  have hw : 0 ≤ (n : ℝ) ^ (-(r / 2)) := Real.rpow_nonneg hnpos.le _
  unfold gstarS gstarN
  refine hdev.trans ?_
  rw [hrw, Real.sqrt_mul (by positivity), hsq]
  refine mul_le_mul_of_nonneg_right ?_ hw
  rw [hMdef]
  have : Real.sqrt (Cζ * Q) ≤ Real.sqrt (Cζ * (K + 1)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hQle hCζ.le)
  linarith
