-- Prove2me | solution 1 for ProxGapTight.amp_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:23:09.08458+00:00
-- url     : https://prove2.me/submissions/e1eb7122-f607-4d3f-b927-c852c9b155f0

import Mathlib
import Definitions.Def_ProxGapTight_Phi
import Definitions.Def_ProxGapTight_amp
import Theorems.Thm_ProxGapTight_amp_coordinate_prob

section
set_option autoImplicit false

namespace ProxGapTight.Dev.AmpCoord

open Classical

end ProxGapTight.Dev.AmpCoord

namespace ProxGapTight

end ProxGapTight
end

section
set_option autoImplicit false

namespace ProxGapTight.Dev.AmpChernoff

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Hoeffding for the uniform law on `Fin N → A` and the count of coordinates satisfying `g`. -/
lemma hoeffding_count {A : Type} [Fintype A] [Nonempty A] (g : A → Prop) [DecidablePred g]
    (N : ℕ) (hN : 1 ≤ N) (ξ : ℝ) (hξ : 0 < ξ) :
    (Nat.card {ω : Fin N → A //
        ξ < |(Fintype.card {j : Fin N // g (ω j)} : ℝ) / (N : ℝ) -
          (Fintype.card {a : A // g a} : ℝ) / (Fintype.card A : ℝ)|} : ℝ) /
      (Nat.card (Fin N → A) : ℝ) ≤ 2 * Real.exp (-2 * ξ ^ 2 * (N : ℝ)) := by
  letI : MeasurableSpace A := ⊤
  haveI : MeasurableSingletonClass A := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let μ₀ : Measure A := (PMF.uniformOfFintype A).toMeasure
  haveI : IsProbabilityMeasure μ₀ := PMF.toMeasure.isProbabilityMeasure _
  let P : Measure (Fin N → A) := Measure.pi (fun _ => μ₀)
  haveI : IsProbabilityMeasure P := inferInstance
  have hsing : ∀ a : A, μ₀ {a} = (Fintype.card A : ℝ≥0∞)⁻¹ := by
    intro a
    simp [μ₀, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  -- counting formula
  have hcount : ∀ S : Set (Fin N → A), P.real S =
      (Nat.card S : ℝ) / (Nat.card (Fin N → A) : ℝ) := by
    intro S
    classical
    have h1 : ∀ ω : Fin N → A, P {ω} = ((Fintype.card A : ℝ≥0∞)⁻¹) ^ N := by
      intro ω
      have : ({ω} : Set (Fin N → A)) = Set.univ.pi (fun i => {ω i}) := (Set.univ_pi_singleton ω).symm
      rw [this]
      simp only [P]
      rw [Measure.pi_pi]
      simp [hsing]
    have h2 : P S = (S.toFinset.card : ℝ≥0∞) * ((Fintype.card A : ℝ≥0∞)⁻¹) ^ N := by
      rw [← Set.Finite.coe_toFinset S.toFinite, ← MeasureTheory.sum_measure_singleton]
      simp only [h1, Finset.sum_const, nsmul_eq_mul]
      simp
    have hA : (Fintype.card A : ℝ≥0∞) ≠ 0 := by simp
    have hA' : (Fintype.card A : ℝ≥0∞) ≠ ⊤ := by simp
    rw [Measure.real, h2, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp [Nat.card_eq_fintype_card, Fintype.card_pi, Set.toFinset_card]
    simp [div_eq_mul_inv]
  let ind : A → ℝ := fun a => if g a then 1 else 0
  let X : Fin N → (Fin N → A) → ℝ := fun j ω => ind (ω j)
  have hind_meas : Measurable ind := measurable_from_top
  have hX_meas : ∀ j, Measurable (X j) := fun j => hind_meas.comp (measurable_pi_apply j)
  have hindep : iIndepFun X P :=
    iIndepFun_pi (μ := fun _ : Fin N => μ₀) (X := fun _ => ind) (fun _ => hind_meas.aemeasurable)
  set m : ℝ := (Fintype.card {a : A // g a} : ℝ) / (Fintype.card A : ℝ) with hm
  have hmean : ∀ j, P[X j] = m := by
    intro j
    have h1 : P[X j] = ∫ a, ind a ∂μ₀ := by
      have := (measurePreserving_eval (fun _ : Fin N => μ₀) j)
      rw [← this.map_eq, integral_map this.measurable.aemeasurable hind_meas.aestronglyMeasurable]
    have hint : Integrable ind μ₀ := Integrable.of_finite
    rw [h1, integral_fintype _]
    have hr : ∀ a : A, μ₀.real {a} = (Fintype.card A : ℝ)⁻¹ := by
      intro a
      simp [Measure.real, hsing]
    simp only [hr, smul_eq_mul, ind]
    rw [← Finset.mul_sum, hm]
    simp [Finset.sum_boole, Fintype.card_subtype, div_eq_inv_mul]
    exact hint
  have hsub : ∀ j, HasSubgaussianMGF (fun ω => X j ω - m) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro j
    have := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := X j) (a := 0) (b := 1)
      (hX_meas j).aemeasurable (ae_of_all _ (fun ω => by
        by_cases h : g (ω j) <;> simp [X, ind, h]))
    rwa [hmean j] at this
  have hindepY : iIndepFun (fun j ω => X j ω - m) P :=
    hindep.comp (fun _ x => x - m) (fun _ => by fun_prop)
  have hindepY' : iIndepFun (fun j ω => -(X j ω - m)) P :=
    hindep.comp (fun _ x => -(x - m)) (fun _ => by fun_prop)
  have hc : ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
    ext; simp; norm_num
  have hbound : ∀ ε : ℝ, 0 ≤ ε → ∀ (Y : Fin N → (Fin N → A) → ℝ) (hY : iIndepFun Y P)
      (hs : ∀ j, HasSubgaussianMGF (Y j) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) P),
      P.real {ω | ε ≤ ∑ j, Y j ω} ≤ Real.exp (-2 * ε ^ 2 / N) := by
    intro ε hε Y hY hs
    have := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (μ := P) hY (s := Finset.univ)
      (c := fun _ => (‖(1:ℝ) - 0‖₊ / 2) ^ 2) (fun j _ => hs j) hε
    convert this using 2
    rw [hc]
    simp
    field_simp
    ring
  have hsum : ∀ ω : Fin N → A, ∑ j, X j ω = (Fintype.card {j : Fin N // g (ω j)} : ℝ) := by
    intro ω
    simp [X, ind, Finset.sum_boole, Fintype.card_subtype]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hε : 0 ≤ ξ * N := by positivity
  set bad : Set (Fin N → A) := {ω | ξ < |(Fintype.card {j : Fin N // g (ω j)} : ℝ) / (N : ℝ) - m|}
    with hbad
  have hsub' : bad ⊆ {ω | ξ * N ≤ ∑ j, (X j ω - m)} ∪ {ω | ξ * N ≤ ∑ j, -(X j ω - m)} := by
    intro ω hω
    simp only [hbad, Set.mem_setOf_eq] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
    have h2 : ξ * N < |(Fintype.card {j : Fin N // g (ω j)} : ℝ) - N * m| := by
      have : (Fintype.card {j : Fin N // g (ω j)} : ℝ) - N * m =
          ((Fintype.card {j : Fin N // g (ω j)} : ℝ) / N - m) * N := by field_simp
      rw [this, abs_mul, abs_of_pos hNpos]
      exact mul_lt_mul_of_pos_right hω hNpos
    rcases lt_abs.1 h2 with h | h
    · left; linarith
    · right; linarith
  have hfin : (Nat.card {ω : Fin N → A //
        ξ < |(Fintype.card {j : Fin N // g (ω j)} : ℝ) / (N : ℝ) - m|} : ℝ) /
      (Nat.card (Fin N → A) : ℝ) = P.real bad := by
    rw [hcount]
    rfl
  rw [hfin]
  calc P.real bad ≤ P.real ({ω | ξ * N ≤ ∑ j, (X j ω - m)} ∪ {ω | ξ * N ≤ ∑ j, -(X j ω - m)}) :=
        measureReal_mono hsub'
    _ ≤ P.real {ω | ξ * N ≤ ∑ j, (X j ω - m)} + P.real {ω | ξ * N ≤ ∑ j, -(X j ω - m)} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-2 * (ξ * N) ^ 2 / N) + Real.exp (-2 * (ξ * N) ^ 2 / N) :=
        add_le_add (hbound _ hε _ hindepY hsub) (hbound _ hε _ hindepY' (fun j => (hsub j).neg))
    _ = 2 * Real.exp (-2 * ξ ^ 2 * N) := by
        have : -2 * (ξ * N) ^ 2 / N = -2 * ξ ^ 2 * N := by field_simp
        rw [this]; ring

end ProxGapTight.Dev.AmpChernoff

namespace ProxGapTight

theorem chk_amp_chernoff (F E : Type) [Field F] [Fintype F] [DecidableEq F] [AddCommGroup E]
    [Module F E] [Fintype E] [DecidableEq E] (n t N : ℕ) (hn : 0 < n) (ht : 1 ≤ t) (hN : 1 ≤ N)
    (ξ : ℝ) (hξ : 0 < ξ) (v : Fin n → E) :
    (Nat.card {ω : Fin N → AmpSample F E n t //
        ξ < |(hammingNorm (amp ω v) : ℝ) / (N : ℝ) -
          (1 - 1 / (Fintype.card F : ℝ)) * Phi t ((hammingNorm v : ℝ) / (n : ℝ))|} : ℝ) /
        (Nat.card (Fin N → AmpSample F E n t) : ℝ) ≤
      2 * Real.exp (-2 * ξ ^ 2 * (N : ℝ)) := by
  classical
  haveI : Fintype (AmpSample F E n t) := Fintype.ofFinite _
  haveI : Nonempty (AmpSample F E n t) := ⟨(fun _ => ⟨0, hn⟩, 0)⟩
  have key := Dev.AmpChernoff.hoeffding_count (A := AmpSample F E n t)
    (fun a => a.2 (fun k => v (a.1 k)) ≠ 0) N hN ξ hξ
  have hm := amp_coordinate_prob F E n t hn ht v
  rw [← hm]
  have e1 : ∀ ω : Fin N → AmpSample F E n t,
      hammingNorm (amp ω v) = Fintype.card {j : Fin N // (ω j).2 (fun k => v ((ω j).1 k)) ≠ 0} := by
    intro ω
    rw [Fintype.card_subtype]
    rfl
  simp only [e1]
  rw [Nat.card_eq_fintype_card (α := {a : AmpSample F E n t // _}),
    Nat.card_eq_fintype_card (α := AmpSample F E n t)]
  exact key

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_amp_chernoff := @ProxGapTight.chk_amp_chernoff
