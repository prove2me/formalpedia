-- Prove2me | solution 1 for PI.AprimeInfG.pi_chart_dens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:42.628901+00:00
-- url     : https://prove2.me/submissions/638af78f-088d-44ca-887b-839af6e3f90e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiDens
import Theorems.Thm_PI_AprimeInfG_withDensity_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Set
open scoped ENNReal
namespace PI.AprimeInfG
theorem _root_.solution {V : Type} [Fintype V] {X E : V → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, MeasurableSpace (E v)] (μ : ∀ v, Measure (X v)) [∀ v, SigmaFinite (μ v)]
    (lam : ∀ v, Measure (E v)) [∀ v, SigmaFinite (lam v)]
    (Φ : ∀ v, E v → X v) (hΦm : ∀ v, Measurable (Φ v)) (U : ∀ v, Set (E v)) (hU : ∀ v, MeasurableSet (U v))
    (hinj : ∀ v, InjOn (Φ v) (U v))
    (D : ∀ v, E v → ℝ) (hD : ∀ v, Measurable (D v))
    (h : ∀ v, ∀ A ⊆ U v, MeasurableSet A → μ v (Φ v '' A) = ∫⁻ z in A, ENNReal.ofReal (D v z) ∂lam v)
    (A : Set (∀ v, E v)) (hAU : A ⊆ univ.pi U) (hA : MeasurableSet A)
    (hAi : MeasurableSet ((fun z v => Φ v (z v)) '' A)) :
    Measure.pi μ ((fun z v => Φ v (z v)) '' A) =
      ∫⁻ z in A, ∏ v, ENNReal.ofReal (D v (z v)) ∂Measure.pi lam := by
  classical
  set Ψ : (∀ v, E v) → (∀ v, X v) := fun z v => Φ v (z v) with hΨ
  have hΨm : Measurable Ψ := measurable_pi_lambda _ fun v => (hΦm v).comp (measurable_pi_apply v)
  let S : ∀ v, Set (X v) := fun v => Φ v '' U v
  let ν : ∀ v, Measure (E v) := fun v => (lam v).withDensity fun x => ENNReal.ofReal (D v x)
  haveI : ∀ v, SigmaFinite (ν v) := fun v => SigmaFinite.withDensity_ofReal (D v)
  have hκ : ∀ v, ((ν v).restrict (U v)).map (Φ v) = (μ v).restrict (S v) := by
    intro v
    ext C hC
    rw [Measure.map_apply (hΦm v) hC, Measure.restrict_apply (hΦm v hC), Measure.restrict_apply hC]
    have hsub : Φ v ⁻¹' C ∩ U v ⊆ U v := Set.inter_subset_right
    have hme : MeasurableSet (Φ v ⁻¹' C ∩ U v) := (hΦm v hC).inter (hU v)
    rw [show ν v (Φ v ⁻¹' C ∩ U v) = ∫⁻ z in Φ v ⁻¹' C ∩ U v, ENNReal.ofReal (D v z) ∂lam v from
      withDensity_apply _ hme, ← h v _ hsub hme]
    congr 1
    ext x
    constructor
    · rintro ⟨z, ⟨hzC, hzU⟩, rfl⟩
      exact ⟨hzC, z, hzU, rfl⟩
    · rintro ⟨hxC, z, hzU, rfl⟩
      exact ⟨z, ⟨hxC, hzU⟩, rfl⟩
  have hrestr : (Measure.pi μ).restrict (univ.pi S) = Measure.pi fun v => (μ v).restrict (S v) := by
    refine (Measure.pi_eq fun B hB => ?_).symm
    rw [Measure.restrict_apply (MeasurableSet.univ_pi hB), ← Set.pi_inter_distrib, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Measure.restrict_apply (hB v)]
  have hrestr2 : (Measure.pi ν).restrict (univ.pi U) = Measure.pi fun v => (ν v).restrict (U v) := by
    refine (Measure.pi_eq fun B hB => ?_).symm
    rw [Measure.restrict_apply (MeasurableSet.univ_pi hB), ← Set.pi_inter_distrib, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Measure.restrict_apply (hB v)]
  have hmap : (Measure.pi fun v => (ν v).restrict (U v)).map Ψ =
      Measure.pi fun v => (μ v).restrict (S v) := by
    refine (Measure.pi_eq fun B hB => ?_).symm
    rw [Measure.map_apply hΨm (MeasurableSet.univ_pi hB)]
    have hpre : Ψ ⁻¹' univ.pi B = univ.pi fun v => Φ v ⁻¹' B v := by
      ext z
      simp [hΨ]
    rw [hpre, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← hκ v, Measure.map_apply (hΦm v) (hB v)]
  have hΦA : Ψ '' A ⊆ univ.pi S := by
    rintro _ ⟨z, hz, rfl⟩ v -
    exact ⟨z v, hAU hz v (mem_univ v), rfl⟩
  calc Measure.pi μ (Ψ '' A) = (Measure.pi μ).restrict (univ.pi S) (Ψ '' A) := by
        rw [Measure.restrict_apply hAi, Set.inter_eq_left.2 hΦA]
    _ = (Measure.pi fun v => (ν v).restrict (U v)).map Ψ (Ψ '' A) := by rw [hrestr, hmap]
    _ = (Measure.pi fun v => (ν v).restrict (U v)) (Ψ ⁻¹' (Ψ '' A)) := Measure.map_apply hΨm hAi
    _ = (Measure.pi ν).restrict (univ.pi U) (Ψ ⁻¹' (Ψ '' A)) := by rw [hrestr2]
    _ = Measure.pi ν A := by
        rw [Measure.restrict_apply (hΨm hAi)]
        congr 1
        ext z
        constructor
        · rintro ⟨⟨z', hz', hzz⟩, hzU⟩
          have hzz' : z' = z := by
            funext v
            exact hinj v (hAU hz' v (mem_univ v)) (hzU v (mem_univ v)) (congrFun hzz v)
          rw [← hzz']
          exact hz'
        · intro hz
          exact ⟨⟨z, hz, rfl⟩, hAU hz⟩
    _ = ∫⁻ z in A, ∏ v, ENNReal.ofReal (D v (z v)) ∂Measure.pi lam := by
        rw [← withDensity_apply _ hA, withDensity_pi lam D hD]
end PI.AprimeInfG
