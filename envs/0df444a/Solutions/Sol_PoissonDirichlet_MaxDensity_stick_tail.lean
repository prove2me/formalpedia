-- Prove2me | solution 1 for PoissonDirichlet.MaxDensity.stick_tail
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:04:42.891985+00:00
-- url     : https://prove2.me/submissions/307554f4-1a18-4f83-80ac-9c37c15639f3

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology


namespace PoissonDirichlet.MaxDensity

lemma st_measurable_stick : Measurable (PoissonDirichlet.Ratio.stick : (ℕ → ℝ) → ℕ → ℝ) := by
  refine measurable_pi_lambda _ (fun k => ?_)
  unfold PoissonDirichlet.Ratio.stick
  exact (Finset.measurable_prod _ (fun i _ => measurable_const.sub (measurable_pi_apply i))).mul
    (measurable_pi_apply k)

lemma st_stick_succ (y : ℕ → ℝ) (k : ℕ) :
    PoissonDirichlet.Ratio.stick y (k + 1) =
      (1 - y 0) * PoissonDirichlet.Ratio.stick (fun i => y (i + 1)) k := by
  unfold PoissonDirichlet.Ratio.stick
  rw [Finset.prod_range_succ', mul_comm]
  ring

lemma st_beta_singleton (a b x : ℝ) : betaMeasure a b {x} = 0 := by
  unfold betaMeasure
  exact withDensity_absolutelyContinuous _ _ (by simp)

theorem stick_tail_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P) :
    (∃ μ : Measure (ℕ → ℝ), PoissonDirichlet.Ratio.IsStickLaw α (α + θ) μ ∧
        ∀ s : Set (ℕ → ℝ), MeasurableSet s →
          P ((fun ω k => PoissonDirichlet.Ratio.stick (fun i => Ytil i ω) (k + 1) / (1 - Ytil 0 ω)) ⁻¹' s) =
            μ (PoissonDirichlet.Ratio.stick ⁻¹' s)) ∧
      IndepFun (fun ω k => PoissonDirichlet.Ratio.stick (fun i => Ytil i ω) (k + 1) / (1 - Ytil 0 ω))
        (Ytil 0) P := by
  -- the shifted sequence
  set Z : Ω → ℕ → ℝ := fun ω k => Ytil (k + 1) ω with hZ
  have hZm : Measurable Z := measurable_pi_lambda _ (fun k => hYm (k + 1))
  set F : Ω → ℕ → ℝ := fun ω k =>
    PoissonDirichlet.Ratio.stick (fun i => Ytil i ω) (k + 1) / (1 - Ytil 0 ω) with hF
  set G : Ω → ℕ → ℝ := fun ω => PoissonDirichlet.Ratio.stick (Z ω) with hG
  have hGm : Measurable G := st_measurable_stick.comp hZm
  -- Y 0 ≠ 1 a.s.
  have hY0 : ∀ᵐ ω ∂P, Ytil 0 ω ≠ 1 := by
    have h1 : P {ω | Ytil 0 ω = 1} = 0 := by
      have : {ω | Ytil 0 ω = 1} = Ytil 0 ⁻¹' {1} := by ext; simp
      rw [this, ← Measure.map_apply (hYm 0) (measurableSet_singleton 1), (hYlaw 0).map_eq,
        st_beta_singleton]
    rw [ae_iff]
    simpa using h1
  have hFG : F =ᵐ[P] G := by
    filter_upwards [hY0] with ω hω
    funext k
    simp only [hF, hG, hZ]
    rw [st_stick_succ]
    have : (1 : ℝ) - Ytil 0 ω ≠ 0 := sub_ne_zero.2 (Ne.symm hω)
    field_simp
  -- law of Z
  have hZind : iIndepFun (fun k => Ytil (k + 1)) P :=
    hYind.precomp (g := fun k : ℕ => k + 1) (fun a b h => by simpa using h)
  have hZlaw : P.map Z = Measure.infinitePi
      (fun k : ℕ => betaMeasure (1 - α) ((α + θ) + ((k : ℝ) + 1) * α)) := by
    have := hZind.map_fun_eq_infinitePi_map (fun k => hYm (k + 1))
    show P.map (fun ω k => Ytil (k + 1) ω) = _
    rw [this]
    congr 1
    funext k
    rw [(hYlaw (k + 1)).map_eq]
    have e : θ + (((k + 1 : ℕ) : ℝ) + 1) * α = (α + θ) + ((k : ℝ) + 1) * α := by push_cast; ring
    rw [e]
  refine ⟨⟨Measure.infinitePi
      (fun k : ℕ => betaMeasure (1 - α) ((α + θ) + ((k : ℝ) + 1) * α)), ?_, ?_⟩, ?_⟩
  · -- IsStickLaw
    have hprob : ∀ k : ℕ, IsProbabilityMeasure
        (betaMeasure (1 - α) ((α + θ) + ((k : ℝ) + 1) * α)) := by
      intro k
      have h := Measure.isProbabilityMeasure_map (μ := P) (f := Ytil (k + 1)) (hYm (k + 1)).aemeasurable
      rw [(hYlaw (k + 1)).map_eq] at h
      have e : θ + (((k + 1 : ℕ) : ℝ) + 1) * α = (α + θ) + ((k : ℝ) + 1) * α := by push_cast; ring
      rw [e] at h
      exact h
    refine ⟨inferInstance, ?_, ?_⟩
    · exact iIndepFun_infinitePi (X := fun (k : ℕ) (x : ℝ) => x) (fun k => measurable_id)
    · intro k
      exact ⟨(measurable_pi_apply k).aemeasurable, Measure.infinitePi_map_eval _ k⟩
  · intro s hs
    have e1 : P (F ⁻¹' s) = P (G ⁻¹' s) := by
      apply measure_congr
      filter_upwards [hFG] with ω hω
      show (ω ∈ F ⁻¹' s) = (ω ∈ G ⁻¹' s)
      rw [Set.mem_preimage, Set.mem_preimage, hω]
    rw [e1, ← hZlaw, Measure.map_apply hZm (st_measurable_stick hs)]
    rfl
  · -- independence
    have hind : IndepFun Z (Ytil 0) P := by
      rw [IndepFun_iff_Indep]
      have hmeas : ∀ k, MeasurableSpace.comap (Ytil k) inferInstance ≤ ‹MeasurableSpace Ω› :=
        fun k => (hYm k).comap_le
      have hS := indep_iSup_of_disjoint hmeas hYind.iIndep
        (S := {k : ℕ | k ≠ 0}) (T := {0}) (by
          rw [Set.disjoint_left]; intro k hk hk'; simp at hk hk'; exact hk hk')
      refine indep_of_indep_of_le hS ?_ ?_
      · -- measurability of Z w.r.t. the sup σ-algebra
        have : Measurable[⨆ i ∈ {k : ℕ | k ≠ 0}, MeasurableSpace.comap (Ytil i) inferInstance] Z := by
          refine @measurable_pi_lambda Ω ℕ (fun _ => ℝ) (⨆ i ∈ {k : ℕ | k ≠ 0}, MeasurableSpace.comap (Ytil i) inferInstance) _ Z (fun k => ?_)
          have hk : k + 1 ∈ {k : ℕ | k ≠ 0} := by simp
          refine measurable_iff_comap_le.mpr ?_
          exact le_iSup₂ (f := fun i (_ : i ∈ {k : ℕ | k ≠ 0}) =>
            MeasurableSpace.comap (Ytil i) inferInstance) (k + 1) hk
        exact this.comap_le
      · exact le_iSup₂ (f := fun i (_ : i ∈ ({0} : Set ℕ)) =>
          MeasurableSpace.comap (Ytil i) inferInstance) 0 rfl
    have hind' : IndepFun G (Ytil 0) P := hind.comp st_measurable_stick measurable_id
    exact hind'.congr hFG.symm (ae_eq_refl _)

end PoissonDirichlet.MaxDensity

open PoissonDirichlet.MaxDensity


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P) :
    (∃ μ : Measure (ℕ → ℝ), PoissonDirichlet.Ratio.IsStickLaw α (α + θ) μ ∧
        ∀ s : Set (ℕ → ℝ), MeasurableSet s →
          P ((fun ω k => PoissonDirichlet.Ratio.stick (fun i => Ytil i ω) (k + 1) / (1 - Ytil 0 ω)) ⁻¹' s) =
            μ (PoissonDirichlet.Ratio.stick ⁻¹' s)) ∧
      IndepFun (fun ω k => PoissonDirichlet.Ratio.stick (fun i => Ytil i ω) (k + 1) / (1 - Ytil 0 ω))
        (Ytil 0) P := by
  exact stick_tail_core P α θ hα hα1 hθ Ytil hYm hYind hYlaw
