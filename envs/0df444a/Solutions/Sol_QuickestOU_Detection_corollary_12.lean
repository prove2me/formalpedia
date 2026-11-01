-- Prove2me | solution 1 for QuickestOU.Detection.corollary_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:44:33.89766+00:00
-- url     : https://prove2.me/submissions/a41f0066-b7d7-4d23-9b8c-0e0e2be72b3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuickestOU_Detection_Disorder
import Theorems.Thm_QuickestOU_Detection_theorem_11
import Theorems.Thm_QuickestOU_Detection_measure_change
import Theorems.Thm_QuickestOU_Detection_crossing_measure_change

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuickestOU.Detection in
theorem solution (P : Params) (hS : P.Standing) (x p0 : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : p0 ≤ 1) (M : DisorderModel P p0 x)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω')
    (B' : ℝ≥0 → Ω' → ℝ) (hB' : Driver μ' B') :
    let b := bnd P B' μ' hB'.meas
    BoundaryClass P b ∧ SolvesIE P B' μ' b ∧
    (∀ a : ℝ → ℝ, BoundaryClass P a → SolvesIE P B' μ' a → a = b) ∧
    iePos P B' μ' b (p0 / (1 - p0)) x ≠ ⊤ ∧
    (Vpi M).toReal = (1 - p0) *
      (1 + P.c * Vrep P B' μ' b (p0 / (1 - p0)) x) ∧
    (p0 < 1 →
      IsStoppingTime (natX M) (tauStar M b) ∧
      risk M (tauStar M b) = Vpi M) := by
  intro b
  obtain ⟨hBC, hIE, huniq, hrep, hopt⟩ := theorem_11 P hS μ' B' hB'
  have hphi : 0 ≤ p0 / (1 - p0) := div_nonneg hp0 (sub_nonneg.2 hp1)
  obtain ⟨hfin, hVrep⟩ := hrep (p0 / (1 - p0)) x hphi
  -- Vhat ≤ 0 via the immediate stop
  have hVle : Vhat P B' μ' hB'.meas (p0 / (1 - p0)) x ≤ 0 := by
    have h0 : payoff P B' μ' (p0 / (1 - p0)) x (fun _ => (0 : WithTop ℝ≥0)) = 0 := by
      have hE : ∀ ω : Ω', beforeStop (fun _ : Ω' => (0 : WithTop ℝ≥0)) ω = ∅ := by
        intro ω; ext t
        simp only [beforeStop, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ h
        exact absurd h (not_lt_bot (a := ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0)))
      simp [payoff, payoffPos, payoffNeg, hE]
    unfold Vhat
    exact sInf_le ⟨fun _ => 0, isStoppingTime_const _ 0, h0.symm⟩
  refine ⟨hBC, hIE, huniq, hfin, ?_, ?_⟩
  · rcases lt_or_eq_of_le hp1 with hlt | heq
    · rw [measure_change P hS x p0 hp0 hlt M μ' B' hB', hVrep]
    · subst heq
      have hlaw := M.θ_law
      simp only [sub_self, ENNReal.ofReal_zero, zero_smul, add_zero, ENNReal.ofReal_one,
        one_smul] at hlaw
      have hae : ∀ᵐ ω ∂M.μ, M.θ ω = 0 := by
        have : M.μ {ω | M.θ ω ≠ 0} = 0 := by
          have h1 : {ω | M.θ ω ≠ 0} = M.θ ⁻¹' ({0}ᶜ : Set ℝ) := rfl
          rw [h1, ← Measure.map_apply M.θ_meas (measurableSet_singleton 0).compl, hlaw]
          simp
        exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun ω h => by simpa using h
      have hr : risk M (fun _ => (0 : WithTop ℝ≥0)) = 0 := by
        have hfa : M.μ (falseAlarm M (fun _ => (0 : WithTop ℝ≥0))) = 0 := by
          apply measure_mono_null (t := {ω | M.θ ω ≠ 0})
          · intro ω hω
            obtain ⟨t, ht, hlt⟩ := hω
            have : t = 0 := by
              have h2 : ((t : ℝ≥0) : WithTop ℝ≥0) = 0 := ht.symm
              exact WithTop.coe_eq_zero.1 h2
            subst this
            simp only [Set.mem_ofPred_eq]
            simp at hlt
            exact ne_of_gt hlt
          · have h1 : {ω | M.θ ω ≠ 0} = M.θ ⁻¹' ({0}ᶜ : Set ℝ) := rfl
            rw [h1, ← Measure.map_apply M.θ_meas (measurableSet_singleton 0).compl, hlaw]
            simp
        have hdd : ∫⁻ ω, detectionDelay M (fun _ => (0 : WithTop ℝ≥0)) ω ∂M.μ = 0 := by
          rw [lintegral_eq_zero_iff' ?_]
          · filter_upwards [hae] with ω hω
            simp [detectionDelay, hω]
          · exact (aemeasurable_const (b := (0 : ℝ≥0∞))).congr (by
              filter_upwards [hae] with ω hω
              simp [detectionDelay, hω])
        simp [risk, hfa, hdd]
      have hV0 : Vpi M = 0 := by
        rw [← nonpos_iff_eq_zero, ← hr]
        exact sInf_le ⟨fun _ => 0, isStoppingTime_const _ 0, rfl⟩
      simp [hV0]
  · intro hlt
    obtain ⟨hst, hrisk⟩ := crossing_measure_change P hS x p0 hp0 hlt M μ' B' hB' b hBC
    obtain ⟨_, hpay⟩ := hopt (p0 / (1 - p0)) x hphi
    rw [hpay] at hrisk
    set V := Vhat P B' μ' hB'.meas (p0 / (1 - p0)) x with hVdef
    have hVtop : V ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top hVle
    have hpos : (0 : ℝ) < 1 - p0 := sub_pos.2 hlt
    have hVbot : V ≠ ⊥ := by
      intro hb
      rw [hb] at hrisk
      have hc : (P.c : EReal) * ⊥ = ⊥ := EReal.coe_mul_bot_of_pos hS.2.1
      rw [hc, EReal.add_bot, EReal.coe_mul_bot_of_pos hpos] at hrisk
      exact EReal.coe_ennreal_ne_bot _ hrisk
    have hVeq : V = ((V.toReal : ℝ) : EReal) := (EReal.coe_toReal hVtop hVbot).symm
    rw [hVeq] at hrisk
    have hR : (risk M (tauStar M b) : EReal) =
        (((1 - p0) * (1 + P.c * V.toReal) : ℝ) : EReal) := by
      rw [hrisk, EReal.coe_mul, EReal.coe_add, EReal.coe_mul, EReal.coe_one]
    have hrtop : risk M (tauStar M b) ≠ ⊤ := by
      intro h; rw [h, EReal.coe_ennreal_top] at hR; exact EReal.coe_ne_top _ hR.symm
    have hrr : (risk M (tauStar M b)).toReal = (1 - p0) * (1 + P.c * V.toReal) := by
      have := EReal.coe_ennreal_toReal hrtop
      rw [← this] at hR
      exact_mod_cast hR
    have hVpi_le : Vpi M ≤ risk M (tauStar M b) := sInf_le ⟨tauStar M b, hst, rfl⟩
    have hVpitop : Vpi M ≠ ⊤ := ne_top_of_le_ne_top hrtop hVpi_le
    have hmc := measure_change P hS x p0 hp0 hlt M μ' B' hB'
    refine ⟨hst, ?_⟩
    rw [← ENNReal.toReal_eq_toReal_iff' hrtop hVpitop, hrr, hmc]
    rfl
