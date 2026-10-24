-- Prove2me | solution 1 for OfflinePolicyLearning.Regret.eq18_regret_le_sup_diff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:27:18.109903+00:00
-- url     : https://prove2.me/submissions/4a683b2d-bf16-45da-8d2b-89442de01913

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open OfflinePolicyLearning.Regret

theorem solution {X : Type*} [MeasurableSpace X] {d K n : ℕ}
    (M : Model X d) (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B)
    (C : CrossFit X d K) (Pol : Set (X → Fin d)) (D : Fin n → Draw X d)
    (πh : X → Fin d) (hmem : πh ∈ Pol) (hmax : ∀ π ∈ Pol, C.Qhat D π ≤ C.Qhat D πh) :
    M.regret Pol πh ≤ ⨆ π₁ : Pol, ⨆ π₂ : Pol, |C.Δhat D π₁.1 π₂.1 - M.Δ π₁.1 π₂.1| := by
  -- a.e. bound on the outcome vector under the joint law
  have hmeasS : MeasurableSet {ω : Draw X d | ∀ a, |ω.2.1 a| ≤ B} := by
    have : {ω : Draw X d | ∀ a, |ω.2.1 a| ≤ B} = ⋂ a, {ω : Draw X d | |ω.2.1 a| ≤ B} := by
      ext ω; simp
    rw [this]
    refine MeasurableSet.iInter fun a => measurableSet_le ?_ measurable_const
    exact ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)).abs
  have hlaw : ∀ᵐ ω ∂M.law, ∀ a, |ω.2.1 a| ≤ B := by
    unfold Model.law
    refine Measure.ae_compProd_of_ae_ae hmeasS (Filter.Eventually.of_forall fun x => ?_)
    rw [Kernel.prod_apply]
    exact (Measure.quasiMeasurePreserving_fst).ae (hB x)
  have hprob : IsProbabilityMeasure M.law := by unfold Model.law; infer_instance
  have hQ : ∀ π : X → Fin d, |M.Q π| ≤ B := by
    intro π
    have := norm_integral_le_of_norm_le_const (μ := M.law) (C := B)
      (f := fun ω : Draw X d => ω.2.1 (π ω.1)) (hlaw.mono fun ω h => by simpa using h (π ω.1))
    simpa [Model.Q, probReal_univ] using this
  -- bound on the cross-fitted estimates (finitely many sample points)
  set G : ℝ := (1 / n : ℝ) * ∑ i, ∑ j, |C.GammaHat D i j| with hG
  have hQh : ∀ π : X → Fin d, |C.Qhat D π| ≤ G := by
    intro π
    unfold CrossFit.Qhat
    rw [hG, abs_mul, abs_of_nonneg (by positivity)]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact Finset.single_le_sum (f := fun j => |C.GammaHat D i j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ _)
  have hterm : ∀ π₁ π₂ : X → Fin d, |C.Δhat D π₁ π₂ - M.Δ π₁ π₂| ≤ 2 * G + 2 * B := by
    intro π₁ π₂
    have h1 := hQh π₁; have h2 := hQh π₂; have h3 := hQ π₁; have h4 := hQ π₂
    unfold CrossFit.Δhat Model.Δ
    rw [abs_le] at *
    constructor <;> linarith
  have : Nonempty Pol := ⟨⟨πh, hmem⟩⟩
  have hinner : ∀ π₁ : Pol, BddAbove (Set.range fun π₂ : Pol => |C.Δhat D π₁.1 π₂.1 - M.Δ π₁.1 π₂.1|) :=
    fun π₁ => ⟨2 * G + 2 * B, by rintro _ ⟨π₂, rfl⟩; exact hterm _ _⟩
  have houter : BddAbove (Set.range fun π₁ : Pol =>
      ⨆ π₂ : Pol, |C.Δhat D π₁.1 π₂.1 - M.Δ π₁.1 π₂.1|) :=
    ⟨2 * G + 2 * B, by rintro _ ⟨π₁, rfl⟩; exact ciSup_le fun π₂ => hterm _ _⟩
  unfold Model.regret
  have key : ∀ π' : Pol, M.Q π'.1 ≤
      (⨆ π₁ : Pol, ⨆ π₂ : Pol, |C.Δhat D π₁.1 π₂.1 - M.Δ π₁.1 π₂.1|) + M.Q πh := by
    intro π'
    have h1 : |C.Δhat D π'.1 πh - M.Δ π'.1 πh| ≤
        ⨆ π₂ : Pol, |C.Δhat D π'.1 π₂.1 - M.Δ π'.1 π₂.1| :=
      le_ciSup (f := fun π₂ : Pol => |C.Δhat D π'.1 π₂.1 - M.Δ π'.1 π₂.1|) (hinner π') ⟨πh, hmem⟩
    have h2 := le_ciSup houter π'
    have h3 := hmax π'.1 π'.2
    have h4 : M.Δ π'.1 πh - C.Δhat D π'.1 πh ≤ |C.Δhat D π'.1 πh - M.Δ π'.1 πh| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have h5 : C.Δhat D π'.1 πh ≤ 0 := by unfold CrossFit.Δhat; linarith
    have h6 : M.Δ π'.1 πh = M.Q π'.1 - M.Q πh := rfl
    linarith
  have := ciSup_le key
  linarith
