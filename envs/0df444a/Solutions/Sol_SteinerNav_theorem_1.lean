-- Prove2me | solution 1 for SteinerNav.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:52:27.599737+00:00
-- url     : https://prove2.me/submissions/fe176fc3-ee6a-4999-889b-33de9a96a5ea

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_aspectRatio
import Definitions.Def_SteinerNav_GreedyRun
import Theorems.Thm_SteinerNav_theorem_3
import Theorems.Thm_SteinerNav_descent_terminates
import Theorems.Thm_SteinerNav_lemma_6_5
import Theorems.Thm_SteinerNav_lemma_6_7

open SteinerNav

namespace AuxThm1

lemma aspectRatio_ge_one {d : ℕ} (P : Finset (Pt d)) (hn : 2 ≤ P.card) :
    1 ≤ aspectRatio P := by
  have h1 : 1 < P.card := by omega
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := Finset.one_lt_card.mp h1
  let offDiag : Finset (Pt d × Pt d) := (P ×ˢ P).filter fun e => e.1 ≠ e.2
  let Dset : Finset ℝ := offDiag.image fun e => dist e.1 e.2
  have hmem₀ : (x₀, y₀) ∈ offDiag := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx₀, hy₀⟩, hxy₀⟩
  have hne : Dset.Nonempty := ⟨dist x₀ y₀, Finset.mem_image.mpr ⟨(x₀, y₀), hmem₀, rfl⟩⟩
  have hset : {r : ℝ | ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ r = dist x y} = (Dset : Set ℝ) := by
    ext r
    simp only [Set.mem_setOf, Finset.mem_coe, Dset, offDiag, Finset.mem_image,
      Finset.mem_filter, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, hx, y, hy, hne', rfl⟩
      exact ⟨x, y, ⟨⟨hx, hy⟩, hne'⟩, rfl⟩
    · rintro ⟨x, y, ⟨⟨hx, hy⟩, hne'⟩, rfl⟩
      exact ⟨x, hx, y, hy, hne', rfl⟩
  have hmin_eq : minDist P = Dset.min' hne := by
    rw [minDist, hset]
    exact IsLeast.csInf_eq (Finset.isLeast_min' Dset hne)
  have hmax_eq : maxDist P = Dset.max' hne := by
    rw [maxDist, hset]
    exact IsGreatest.csSup_eq (Finset.isGreatest_max' Dset hne)
  have hmin_mem : Dset.min' hne ∈ Dset := Finset.min'_mem Dset hne
  obtain ⟨⟨x₁, y₁⟩, hxy₁, hdist₁⟩ := Finset.mem_image.mp hmin_mem
  have hxy₁_ne : x₁ ≠ y₁ := (Finset.mem_filter.mp hxy₁).2
  have hmin_pos : 0 < minDist P := by
    rw [hmin_eq, ← hdist₁]
    exact dist_pos.mpr hxy₁_ne
  have hle : minDist P ≤ maxDist P := by
    rw [hmin_eq, hmax_eq]
    exact Finset.min'_le Dset _ (Finset.max'_mem Dset hne)
  rw [aspectRatio, one_le_div hmin_pos]
  exact hle

lemma greedyRun_mem {d : ℕ} {V : Finset (Pt d)} {E : Finset (Pt d × Pt d)}
    (hE : ∀ x y, (x, y) ∈ E → x ∈ V ∧ y ∈ V) {q x₀ : Pt d} (hx₀ : x₀ ∈ V)
    {k : ℕ} {x : Pt d} (hrun : GreedyRun E q x₀ k x) : x ∈ V := by
  induction hrun with
  | start => exact hx₀
  | step _ hstep => exact (hE _ _ hstep.1).2

end AuxThm1

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ P : Finset (Pt d), 2 ≤ P.card →
    let n : ℝ := (P.card : ℝ)
    let α : ℝ := 1 + 1 / (d : ℝ)
    let Δ : ℝ := aspectRatio P
    ∃ (R : Finset (Pt d)) (E : Finset (Pt d × Pt d)),
      IsSteinerNavigable α P R E ∧
      (E.card : ℝ) ≤ C * n ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n * (1 + Real.log Δ)) ∧
      (∀ x, (x, x) ∉ E) ∧
      NoSteinerToSteiner R P E ∧
      (∀ t ∈ P,
        (∀ x₀ ∈ P, ∀ k x, GreedyRun E t x₀ k x → k ≤ ⌊Real.logb α Δ⌋₊ + 2) ∧
        (∀ x₀ ∈ R, ∀ k x, GreedyRun E t x₀ k x → k ≤ ⌊Real.logb α Δ⌋₊ + 3) ∧
        (∀ x₀ ∈ P ∪ R, ∀ k x, GreedyRun E t x₀ k x → GreedyLocalMin E t x → x = t) ∧
        (∀ x₀ ∈ P ∪ R, ∃ k x, GreedyRun E t x₀ k x ∧ GreedyLocalMin E t x)) ∧
      (∀ q : Pt d, ∀ x₀ ∈ P ∪ R,
        (∃ k x, GreedyRun E q x₀ k x ∧ GreedyLocalMin E q x) ∧
        ∀ k x, GreedyRun E q x₀ k x → GreedyLocalMin E q x →
          (∃ y, GreedyReturns E P q x y) ∧
          ∀ y, GreedyReturns E P q x y →
            y ∈ P ∧ ∀ p ∈ P, dist y q ≤ (α + 1) / (α - 1) * dist p q) := by
  obtain ⟨C₁, C₂, _, hC₂, h3⟩ := SteinerNav.theorem_3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let M : ℝ := 1 + 1 / Real.log 2
  have hM : 0 < M := by positivity
  refine ⟨C₂ * Real.sqrt M, by positivity, ?_⟩
  intro d hd P hn
  dsimp only
  obtain ⟨R, E, hG, hN, hnoloop, _, _, hEcard⟩ := h3 d hd P hn
  have hα : 1 < 1 + 1 / (d : ℝ) := by
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    linarith [one_div_pos.mpr hd_pos]
  refine ⟨R, E, hG, ?_, hnoloop, hN, ?_, ?_⟩
  · have hΔ1 : 1 ≤ aspectRatio P := AuxThm1.aspectRatio_ge_one P hn
    have hlogΔ : 0 ≤ Real.log (aspectRatio P) := Real.log_nonneg hΔ1
    have hn_ge2 : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hn
    have hlogn : 0 ≤ Real.log (P.card : ℝ) := Real.log_nonneg (by linarith)
    have hlogb_nonneg : 0 ≤ Real.logb 2 (aspectRatio P) := by
      rw [Real.logb]
      exact div_nonneg hlogΔ (le_of_lt hlog2)
    have hfloor : (⌊Real.logb 2 (aspectRatio P)⌋₊ : ℝ) ≤ Real.log (aspectRatio P) / Real.log 2 := by
      calc (⌊Real.logb 2 (aspectRatio P)⌋₊ : ℝ) ≤ Real.logb 2 (aspectRatio P) :=
            Nat.floor_le hlogb_nonneg
        _ = Real.log (aspectRatio P) / Real.log 2 := rfl
    have hL_le : (annulusCount P : ℝ) ≤ M * (1 + Real.log (aspectRatio P)) := by
      rw [annulusCount, Nat.cast_add, Nat.cast_one]
      have h1 : 1 + Real.log (aspectRatio P) / Real.log 2 ≤
          (1 + 1 / Real.log 2) * (1 + Real.log (aspectRatio P)) := by
        have hpos1 : 0 ≤ 1 / Real.log 2 := by positivity
        have hprod_nonneg : 0 ≤ (1 / Real.log 2) * Real.log (aspectRatio P) :=
          mul_nonneg hpos1 hlogΔ
        have heq : Real.log (aspectRatio P) / Real.log 2 =
            (1 / Real.log 2) * Real.log (aspectRatio P) := by ring
        linarith
      linarith
    have hprod_le : (annulusCount P : ℝ) * Real.log (P.card : ℝ) ≤
        M * (Real.log (P.card : ℝ) * (1 + Real.log (aspectRatio P))) := by
      calc (annulusCount P : ℝ) * Real.log (P.card : ℝ)
          ≤ (M * (1 + Real.log (aspectRatio P))) * Real.log (P.card : ℝ) :=
            mul_le_mul_of_nonneg_right hL_le hlogn
        _ = M * (Real.log (P.card : ℝ) * (1 + Real.log (aspectRatio P))) := by ring
    have hsqrt_le : Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ)) ≤
        Real.sqrt M * Real.sqrt (Real.log (P.card : ℝ) * (1 + Real.log (aspectRatio P))) := by
      calc Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ))
          ≤ Real.sqrt (M * (Real.log (P.card : ℝ) * (1 + Real.log (aspectRatio P)))) :=
            Real.sqrt_le_sqrt hprod_le
        _ = Real.sqrt M * Real.sqrt (Real.log (P.card : ℝ) * (1 + Real.log (aspectRatio P))) :=
            Real.sqrt_mul (le_of_lt hM) _
    have hn32 : 0 ≤ ((P.card : ℝ)) ^ (3 / 2 : ℝ) := by positivity
    calc (E.card : ℝ)
        ≤ C₂ * min ((P.card : ℝ) ^ 2)
            ((P.card : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ))) := hEcard
      _ ≤ C₂ * ((P.card : ℝ) ^ (3 / 2 : ℝ) *
            Real.sqrt ((annulusCount P : ℝ) * Real.log (P.card : ℝ))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hC₂)
      _ ≤ C₂ * ((P.card : ℝ) ^ (3 / 2 : ℝ) *
            (Real.sqrt M * Real.sqrt (Real.log (P.card : ℝ) * (1 + Real.log (aspectRatio P))))) := by
          gcongr
      _ = C₂ * Real.sqrt M * (P.card : ℝ) ^ (3 / 2 : ℝ) *
            Real.sqrt (Real.log (P.card : ℝ) * (1 + Real.log (aspectRatio P))) := by ring
  · intro t ht
    exact SteinerNav.lemma_6_7 (1 + 1 / (d : ℝ)) hα P R E hn hG hN t ht
  · intro q x₀ hx₀
    refine ⟨(SteinerNav.descent_terminates (P ∪ R) E hG.2.1 q x₀ hx₀).2, ?_⟩
    intro k x hrun hloc
    have hx : x ∈ P ∪ R := AuxThm1.greedyRun_mem hG.2.1 hx₀ hrun
    have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨tstar, htstar, hnear⟩ := P.exists_min_image (fun p => dist q p) hPne
    have h65 := (SteinerNav.lemma_6_5 (1 + 1 / (d : ℝ)) hα P R E hn hG q tstar htstar hnear).2 hN x hx hloc
    refine ⟨h65.1, ?_⟩
    intro y hy
    obtain ⟨hyP, hydist⟩ := h65.2 y hy
    refine ⟨hyP, ?_⟩
    intro p hp
    have hqp : dist q tstar ≤ dist p q := by
      rw [dist_comm p q]
      exact hnear p hp
    have hCα : 0 ≤ ((1 + 1 / (d : ℝ)) + 1) / ((1 + 1 / (d : ℝ)) - 1) := by
      apply div_nonneg <;> linarith
    exact le_trans hydist (mul_le_mul_of_nonneg_left hqp hCα)
