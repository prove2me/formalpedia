-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.topsGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:46:54.457076+00:00
-- url     : https://prove2.me/submissions/13f5f163-1005-4722-9823-37aafbc7605a

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_select
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitSum
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_SharesOfCounts
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitTerms
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_NotGoodLe
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_topsGroup
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_not_good_le
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_orbit_sum
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_orbit_terms
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_select
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_shares_of_counts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical
private theorem tg_num (x eps Co δ N o n0 : ℝ) (he : 0 < eps) (hx : 1 ≤ x) (hbig : 64 * Co ^ 4 ≤ x ^ eps)
    (hδe : δ = x ^ (-(eps / 8))) (hN : x ^ (2 + 8 * eps) / 2 ≤ N) (ho1 : 1 ≤ o) (ho : o ≤ Co) (hn : o * n0 = N) :
    4 * o * Real.sqrt (2 * δ * N) ≤ x⁻¹ * (δ * n0) := by
  have hx0 : 0 < x := by linarith
  have hδ : 0 < δ := by rw [hδe]; positivity
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have ho0 : 0 < o := by linarith
  have hn0 : n0 = N / o := by rw [← hn]; field_simp
  have h1 : x ^ 2 * x ^ eps ≤ δ * x ^ (2 + 8 * eps) := by
    rw [hδe, ← Real.rpow_add hx0, ← Real.rpow_two, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h2 : o ^ 4 ≤ Co ^ 4 := pow_le_pow_left₀ ho0.le ho 4
  have h3 : 32 * o ^ 4 * x ^ 2 ≤ δ * N := by
    have a1 := mul_le_mul_of_nonneg_left hN hδ.le
    have a2 : x ^ 2 * (64 * o ^ 4) ≤ x ^ 2 * x ^ eps :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have h4 : Real.sqrt (2 * δ * N) ≤ δ * N / (4 * o ^ 2 * x) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ δ * N)
    calc 2 * δ * N * (4 * o ^ 2 * x) ^ 2 = δ * N * (32 * o ^ 4 * x ^ 2) := by ring
      _ ≤ δ * N * (δ * N) := this
      _ = _ := by ring
  calc 4 * o * Real.sqrt (2 * δ * N) ≤ 4 * o * (δ * N / (4 * o ^ 2 * x)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by rw [hn0]; field_simp
private theorem tg_class_sum (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A)
    (u v : ℝ) (γ : A) :
    ∑ a ∈ univ.filter (fun a : A => a - γ ∈ A0), (if a ∈ A0 then u else v) =
      (if γ ∈ A0 then u else v) * Nat.card A0 := by
  have hc : (univ.filter (fun a : A => a - γ ∈ A0)).card = Nat.card A0 := by
    have e : {a : A // a - γ ∈ A0} ≃ A0 :=
      { toFun := fun a => ⟨a.1 - γ, a.2⟩
        invFun := fun b => ⟨b.1 + γ, by simp⟩
        left_inv := fun a => by ext; simp
        right_inv := fun b => by ext; simp }
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_congr rfl (g := fun _ => if γ ∈ A0 then u else v), Finset.sum_const, nsmul_eq_mul, hc, mul_comm]
  intro a ha
  rw [Finset.mem_filter] at ha
  have hiff : a ∈ A0 ↔ γ ∈ A0 := by
    constructor
    · intro h
      have := A0.sub_mem h ha.2
      simpa using this
    · intro h
      have := A0.add_mem ha.2 h
      simpa using this
  simp only [hiff]
end

set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀,
      ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A) (L₂ : ℕ),
      x ^ hE eps / 2 ≤ (Fintype.card A : ℝ) → (Fintype.card A : ℝ) ≤ Co * x ^ hE eps → (A0.index : ℝ) ≤ Co → (L₂ : ℝ) ≤ Lb →
      ∀ bs : A → A → A, (∀ h t, ∃ i : ℕ, bs h t + i • h = t) →
      ∀ (PP : Finset ℕ) (hp : ℕ → A) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) →
      ∃ TT : Finset A, dE eps x * Fintype.card A / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * dE eps x * Fintype.card A ∧
        (∀ γ : A, |((TT.filter fun t => t - γ ∈ A0).card : ℝ) -
          (if γ ∈ A0 then 4 else 3) / (3 * (A0.index : ℝ) + 1) * (TT.card : ℝ)| ≤ x ^ (-1 + eps) * (TT.card : ℝ)) ∧
        ∑ p ∈ PP, ω p * (({t : A | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p))
            (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (KE eps) (rE eps)
            (dE eps x) (hE eps) x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * x ^ (-2 : ℝ)) * dE eps x * Fintype.card A * ∑ p ∈ PP, ω p := by
  intro eps Co Lb he
  obtain ⟨Cb, x₀, hCb, hnum⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_terms eps Co Lb he
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop he).eventually_ge_atTop (64 * Co ^ 4))
  refine ⟨Cb, max x₀ (max x₁ 1), hCb, ?_⟩
  intro x hx A _ _ _ A0 L₂ hlo hhi hidx hL bs hbs PP hp ω hω hPP
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hδ : 0 < dE eps x := Real.rpow_pos_of_pos hx0 _
  have hδ1 : dE eps x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hN0 : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hβ : 0 ≤ Cb * x ^ (-2 : ℝ) := by positivity
  have hp1 : ∀ a : A, 3 / 4 * dE eps x ≤ (if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) ∧
      (if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) ≤ dE eps x := by
    intro a
    split_ifs <;> constructor <;> linarith
  have hD : 0 < Real.sqrt (2 * dE eps x * Fintype.card A) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨T, hT1, hT2⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.select A (A ⧸ A0) ℕ (fun a => (a : A ⧸ A0))
    (fun a => if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) (dE eps x) (Cb * x ^ (-2 : ℝ))
    (Real.sqrt (2 * dE eps x * Fintype.card A)) PP ω
    (fun p t T => ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter
      (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (KE eps) (rE eps)
      (dE eps x) (hE eps) x)
    (fun a => ⟨le_trans (by positivity) (hp1 a).1, (hp1 a).2⟩) hδ.le hδ1 hβ hω hD
    (le_of_eq (Real.sq_sqrt (by positivity)).symm) (by
      intro p hpp t
      have hn : ((addOrderOf (hp p) : ℕ) : ℝ) ≤ Co * x ^ hE eps :=
        le_trans (Nat.cast_le.mpr addOrderOf_le_card_univ) hhi
      obtain ⟨h1, h2⟩ := hnum x hxx0 (addOrderOf (hp p)) L₂ (hPP p hpp) hn hL
      obtain ⟨i₀, _, _, hsum⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_sum A
        (fun a => if a ∈ A0 then dE eps x else 3 / 4 * dE eps x) (bs (hp p) t) (hp p) t (hbs _ _)
        (fun T => ¬ GoodOrbitIntervalTileCondition (addOrderOf (hp p)) T L₂ (KE eps) (rE eps)
          (Formalism.MainNotions.G.goodU (dE eps x)) (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x)
          (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x)
          (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x))
      have hu : 1 ≤ Formalism.MainNotions.G.goodU (dE eps x) := Nat.ceil_pos.mpr (by positivity)
      have h3 := UpperTheory.BernoulliSumsFrobeniusOrbits.not_good_le
        (fun i => if bs (hp p) t + i • hp p ∈ A0 then dE eps x else 3 / 4 * dE eps x) (dE eps x)
        (addOrderOf (hp p)) L₂ (KE eps) (rE eps)
        (Formalism.MainNotions.G.goodU (dE eps x)) (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x)
        (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x)
        (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x) i₀ (fun i => hp1 _) hδ.le hδ1 hu h1
      refine le_trans (le_of_eq hsum) ?_
      rw [mul_comm (Cb * x ^ (-2 : ℝ))]
      exact le_trans (mul_le_mul_of_nonneg_left (h3.trans h2)
        (le_trans (by positivity) (hp1 t).1)) (mul_le_mul_of_nonneg_right (hp1 t).2 hβ))
  have hidx1 : (1 : ℝ) ≤ A0.index := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 AddSubgroup.index_ne_zero_of_finite
  have hmul : (A0.index : ℝ) * Nat.card A0 = Fintype.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast A0.index_mul_card
  have hnumD := tg_num x eps Co (dE eps x) (Fintype.card A) A0.index (Nat.card A0) he hx1
    (hx₁ x hxx1) rfl hlo hidx1 hidx hmul
  obtain ⟨hS1, hS2, hS3⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.shares_of_counts A A0 T (dE eps x) x⁻¹
    (Real.sqrt (2 * dE eps x * Fintype.card A)) hδ (inv_le_one_of_one_le₀ hx1) hD.le hnumD (by
      intro γ
      have hc : ∀ a : A, ((a : A ⧸ A0) = (γ : A ⧸ A0)) ↔ a - γ ∈ A0 := fun a =>
        QuotientAddGroup.eq_iff_sub_mem
      have := hT1 (γ : A ⧸ A0)
      simp only [hc] at this
      rw [← tg_class_sum A A0 (dE eps x) (3 / 4 * dE eps x) γ]
      convert this)
  refine ⟨T, hS1, hS2, fun γ => le_trans (hS3 γ) ?_, hT2⟩
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
end UpperTheory.BernoulliSumsFrobeniusOrbits
