-- Prove2me | solution 1 for SolomonRWRE.Recurrence.theorem_0_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:59:43.398975+00:00
-- url     : https://prove2.me/submissions/6e57e668-80e7-47d2-b425-85a14f56027b

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


namespace SolomonRWRE.Recurrence

/-- quenched cylinder weight -/
noncomputable def cylW (n : ℕ) (x : ℕ → ℤ) (a : ℤ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((if x 0 = 0 then 1 else 0) * ∏ k ∈ Finset.range n, step a (x k) (x (k + 1)))

def cyl (n : ℕ) (x : ℕ → ℤ) : Set (ℕ → ℤ) := {w | ∀ k ≤ n, w k = x k}

lemma measurable_step (x y : ℤ) : Measurable fun a : ℤ → ℝ => step a x y := by
  unfold step
  split_ifs
  · exact measurable_pi_apply x
  · exact measurable_const.sub (measurable_pi_apply x)
  · exact measurable_const

lemma measurable_cylW (n : ℕ) (x : ℕ → ℤ) : Measurable (cylW n x) := by
  unfold cylW
  refine Measurable.ennreal_ofReal ?_
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_prod _ fun k _ => measurable_step _ _

lemma measurableSet_cyl (n : ℕ) (x : ℕ → ℤ) : MeasurableSet (cyl n x) := by
  have : cyl n x = ⋂ k, ⋂ (_ : k ≤ n), (fun w : ℕ → ℤ => w k) ⁻¹' {x k} := by
    ext w; simp [cyl]
  rw [this]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurable_pi_apply k (measurableSet_singleton _)

def extP (p : Σ n : ℕ, Fin (n + 1) → ℤ) : ℕ → ℤ :=
  fun k => if h : k < p.1 + 1 then p.2 ⟨k, h⟩ else 0

lemma cyl_extP (n : ℕ) (x : ℕ → ℤ) :
    cyl n (extP ⟨n, fun i => x i⟩) = cyl n x := by
  ext w
  simp only [cyl, Set.mem_setOf_eq, extP]
  constructor
  · intro h k hk; have := h k hk; rwa [dif_pos (Nat.lt_succ_of_le hk)] at this
  · intro h k hk; rw [dif_pos (Nat.lt_succ_of_le hk)]; exact h k hk

lemma cylW_extP (n : ℕ) (x : ℕ → ℤ) (a : ℤ → ℝ) :
    cylW n (extP ⟨n, fun i => x i⟩) a = cylW n x a := by
  unfold cylW
  have h0 : extP ⟨n, fun i => x i⟩ 0 = x 0 := by simp [extP]
  have h1 : ∏ k ∈ Finset.range n, step a (extP ⟨n, fun i => x i⟩ k)
      (extP ⟨n, fun i => x i⟩ (k + 1)) = ∏ k ∈ Finset.range n, step a (x k) (x (k + 1)) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    simp only [extP, dif_pos (by omega : k < n + 1), dif_pos (by omega : k + 1 < n + 1)]
  rw [h0, h1]

theorem theorem_0_1_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (S : Set (ℕ → ℤ)) (hS : MeasurableSet S)
    (h : ∀ᵐ a ∂(P.map (env α)), ∀ ν : Measure (ℕ → ℤ), IsProbabilityMeasure ν →
      IsChainInEnv ν a 0 (fun n w => w n) → ν S = 1) :
    P {ω | (fun n => X n ω) ∈ S} = 1 := by
  have hZ : Measurable (env α) := measurable_pi_iff.mpr fun n => hRW.meas_α n
  have hY : Measurable (fun ω n => X n ω) := measurable_pi_iff.mpr fun n => hRW.meas_X n
  haveI : IsProbabilityMeasure (P.map (env α)) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  -- key identity
  have key : ∀ (n : ℕ) (x : ℕ → ℤ), ∀ᵐ a ∂(P.map (env α)),
      condDistrib (fun ω n => X n ω) (env α) P a (cyl n x) = cylW n x a := by
    intro n x
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (Kernel.measurable_coe _ (measurableSet_cyl n x)) (measurable_cylW n x) ?_
    intro t ht _
    rw [setLIntegral_map ht (Kernel.measurable_coe _ (measurableSet_cyl n x)) hZ,
      setLIntegral_map ht (measurable_cylW n x) hZ,
      setLIntegral_preimage_condDistrib hZ hY.aemeasurable (measurableSet_cyl n x) ht]
    exact hRW.law n x t ht
  have key2 : ∀ᵐ a ∂(P.map (env α)), ∀ p : Σ n : ℕ, Fin (n+1) → ℤ,
      condDistrib (fun ω n => X n ω) (env α) P a (cyl p.1 (extP p)) = cylW p.1 (extP p) a :=
    ae_all_iff.mpr fun p => key p.1 (extP p)
  have hmem : ∀ᵐ a ∂(P.map (env α)), ∀ j, a j ∈ Set.Icc (0:ℝ) 1 := by
    have hms : MeasurableSet {a : ℤ → ℝ | ∀ j, a j ∈ Set.Icc (0:ℝ) 1} := by
      have : {a : ℤ → ℝ | ∀ j, a j ∈ Set.Icc (0:ℝ) 1} =
          ⋂ j, (fun a : ℤ → ℝ => a j) ⁻¹' Set.Icc 0 1 := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun j => measurable_pi_apply j measurableSet_Icc
    rw [ae_map_iff hZ.aemeasurable hms]
    exact Filter.Eventually.of_forall fun ω j => hRW.mem j ω
  have hfin : ∀ᵐ a ∂(P.map (env α)), condDistrib (fun ω n => X n ω) (env α) P a S = 1 := by
    filter_upwards [h, key2, hmem] with a ha hk hm
    refine ha _ inferInstance ⟨hm, fun n => measurable_pi_apply n, ?_⟩
    intro n x
    have := hk ⟨n, fun i => x i⟩
    rw [cyl_extP, cylW_extP] at this
    exact this
  have h1 : P {ω | (fun n => X n ω) ∈ S} =
      ∫⁻ a, condDistrib (fun ω n => X n ω) (env α) P a S ∂(P.map (env α)) := by
    have := setLIntegral_preimage_condDistrib (μ := P) hZ hY.aemeasurable hS MeasurableSet.univ
    rw [Set.preimage_univ, Set.univ_inter, Measure.restrict_univ] at this
    rw [lintegral_map (Kernel.measurable_coe _ hS) hZ, this]
    rfl
  rw [h1, lintegral_congr_ae hfin, lintegral_one, measure_univ]

end SolomonRWRE.Recurrence

open SolomonRWRE.Recurrence


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (S : Set (ℕ → ℤ)) (hS : MeasurableSet S)
    (h : ∀ᵐ a ∂(P.map (env α)), ∀ ν : Measure (ℕ → ℤ), IsProbabilityMeasure ν →
      IsChainInEnv ν a 0 (fun n w => w n) → ν S = 1) :
    P {ω | (fun n => X n ω) ∈ S} = 1 := by
  exact theorem_0_1_core P α X hRW S hS h
