-- Prove2me | solution 1 for ThompsonTutorial.Regret.ts_regret_pessimism_width_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:25:30.746736+00:00
-- url     : https://prove2.me/submissions/3a42beb7-4cd4-4e17-8f41-6b73330dd064

import Mathlib
import Definitions.Def_ThompsonTutorial_Regret_meanReward
import Definitions.Def_ThompsonTutorial_Regret_IsBayesModel
import Definitions.Def_ThompsonTutorial_Regret_history
import Definitions.Def_ThompsonTutorial_Regret_IsThompsonRun

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace TSPWAux

/-- Two random elements `a`, `b` with the same conditional law given a sub-σ-algebra `m`
(tested on `m`-sets) give the same expectation of any `m ⊗ 𝓑(X)`-measurable `U(ω, ·)`. -/
theorem integral_eq_of_cond_law {Ω X : Type*} {m m0 : MeasurableSpace Ω} [mX : MeasurableSpace X]
    (hm : m ≤ m0) (P : @Measure Ω m0) [IsProbabilityMeasure P] (a b : Ω → X)
    (ha : Measurable[m0] a) (hb : Measurable[m0] b)
    (hab : ∀ A : Set X, MeasurableSet A → ∀ B : Set Ω, MeasurableSet[m] B →
      P (B ∩ a ⁻¹' A) = P (B ∩ b ⁻¹' A))
    (U : Ω → X → ℝ) (hU : Measurable[m.prod mX] (Function.uncurry U)) :
    ∫ ω, U ω (a ω) ∂P = ∫ ω, U ω (b ω) ∂P := by
  let mP : MeasurableSpace (Ω × X) := m.prod mX
  have hid : @Measurable Ω Ω m0 m id := fun s hs => hm s hs
  have hφa : @Measurable Ω (Ω × X) m0 mP (fun ω => (ω, a ω)) := hid.prodMk ha
  have hφb : @Measurable Ω (Ω × X) m0 mP (fun ω => (ω, b ω)) := hid.prodMk hb
  have hmap : P.map (fun ω => (ω, a ω)) = P.map (fun ω => (ω, b ω)) := by
    have : IsFiniteMeasure (P.map (fun ω => (ω, a ω))) := Measure.isFiniteMeasure_map _ _
    refine ext_of_generate_finite _ (@generateFrom_prod Ω X m mX).symm
      (@isPiSystem_prod Ω X m mX) ?_ ?_
    · rintro _ ⟨B, hB, A, hA, rfl⟩
      rw [Measure.map_apply hφa ((@MeasurableSet.prod Ω X m mX _ _ hB hA)),
        Measure.map_apply hφb ((@MeasurableSet.prod Ω X m mX _ _ hB hA))]
      have e1 : (fun ω => (ω, a ω)) ⁻¹' (B ×ˢ A) = B ∩ a ⁻¹' A := by ext; simp
      have e2 : (fun ω => (ω, b ω)) ⁻¹' (B ×ˢ A) = B ∩ b ⁻¹' A := by ext; simp
      rw [e1, e2]; exact hab A hA B hB
    · rw [Measure.map_apply hφa MeasurableSet.univ, Measure.map_apply hφb MeasurableSet.univ]
      simp
  have hUs : StronglyMeasurable (Function.uncurry U) := hU.stronglyMeasurable
  have h1 : ∫ ω, U ω (a ω) ∂P = ∫ p, Function.uncurry U p ∂(P.map (fun ω => (ω, a ω))) :=
    (integral_map hφa.aemeasurable hUs.aestronglyMeasurable).symm
  have h2 : ∫ ω, U ω (b ω) ∂P = ∫ p, Function.uncurry U p ∂(P.map (fun ω => (ω, b ω))) :=
    (integral_map hφb.aemeasurable hUs.aestronglyMeasurable).symm
  rw [h1, h2, hmap]

/-- From equality of conditional expectations of indicators to equality of joint probabilities
with `m`-sets. -/
theorem meas_inter_eq_of_condExp {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (hm : m ≤ m0) (P : @Measure Ω m0) [IsProbabilityMeasure P] (S T : Set Ω)
    (hS : MeasurableSet[m0] S) (hT : MeasurableSet[m0] T)
    (h : P[S.indicator (fun _ => (1 : ℝ)) | m] =ᵐ[P] P[T.indicator (fun _ => (1 : ℝ)) | m])
    (B : Set Ω) (hB : MeasurableSet[m] B) : P (B ∩ S) = P (B ∩ T) := by
  have iS : Integrable (S.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hS
  have iT : Integrable (T.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hT
  have e := setIntegral_congr_ae (μ := P) (hm B hB) (h.mono fun x hx _ => hx)
  rw [setIntegral_condExp hm iS hB, setIntegral_condExp hm iT hB,
    setIntegral_indicator hS, setIntegral_indicator hT, setIntegral_const, setIntegral_const] at e
  simp only [smul_eq_mul, mul_one] at e
  have hf1 : P (B ∩ S) ≠ ⊤ := measure_ne_top _ _
  have hf2 : P (B ∩ T) ≠ ⊤ := measure_ne_top _ _
  exact (ENNReal.toReal_eq_toReal_iff' hf1 hf2).1 (by simpa [Measure.real] using e)

end TSPWAux

open MeasureTheory ProbabilityTheory ThompsonTutorial.Regret in
theorem solution {Ω Θ X Y W : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (P : Measure Ω) [IsProbabilityMeasure P] (θ : Ω → Θ) (w : ℕ → Ω → W)
    (g : X → Θ → W → Y) (r : Y → ℝ) (f : Θ → X) (θhat : ℕ → Ω → Θ) (xs : ℕ → Ω → X)
    (hM : IsBayesModel P θ w g r) (hTS : IsThompsonRun P θ w g r f θhat xs)
    (t : ℕ) (ht : 1 ≤ t) (U : Ω → X → ℝ)
    (hU : Measurable[(history g θ w xs t).prod ‹MeasurableSpace X›] (Function.uncurry U))
    (hmustar : Integrable (fun ω => meanReward P w g r (f (θ ω)) (θ ω)) P)
    (hmux : Integrable (fun ω => meanReward P w g r (xs t ω) (θ ω)) P)
    (hUx : Integrable (fun ω => U ω (xs t ω)) P)
    (hUstar : Integrable (fun ω => U ω (f (θ ω))) P) :
    ∫ ω, (meanReward P w g r (f (θ ω)) (θ ω) - meanReward P w g r (xs t ω) (θ ω)) ∂P
        = ∫ ω, (meanReward P w g r (f (θ ω)) (θ ω) - U ω (xs t ω)) ∂P
          + ∫ ω, (U ω (xs t ω) - meanReward P w g r (xs t ω) (θ ω)) ∂P ∧
    ∫ ω, (meanReward P w g r (f (θ ω)) (θ ω) - U ω (xs t ω)) ∂P
          + ∫ ω, (U ω (xs t ω) - meanReward P w g r (xs t ω) (θ ω)) ∂P
        = ∫ ω, (meanReward P w g r (f (θ ω)) (θ ω) - U ω (f (θ ω))) ∂P
          + ∫ ω, (U ω (xs t ω) - meanReward P w g r (xs t ω) (θ ω)) ∂P := by
  obtain ⟨hθ, hw, hg, -, -, -, -⟩ := hM
  obtain ⟨hf, -, hrun, hpost, -⟩ := hTS
  -- the history is a sub-σ-algebra
  have hxs : ∀ s, 1 ≤ s → Measurable (xs s) := fun s hs => by
    rw [(hrun s hs).2]; exact hf.comp (hrun s hs).1
  have hle : history g θ w xs t ≤ ‹MeasurableSpace Ω› := by
    unfold history
    refine iSup₂_le fun s hs => ?_
    have hs1 : 1 ≤ s := (Finset.mem_Ico.1 hs).1
    refine Measurable.comap_le ?_
    exact (hxs s hs1).prodMk (hg.comp ((hxs s hs1).prodMk (hθ.prodMk (hw s))))
  -- the key equality E[U_t(x_t)] = E[U_t(x*)]
  have hkey : ∫ ω, U ω (xs t ω) ∂P = ∫ ω, U ω (f (θ ω)) ∂P := by
    refine TSPWAux.integral_eq_of_cond_law hle P (xs t) (fun ω => f (θ ω)) (hxs t ht)
      (hf.comp hθ) ?_ U hU
    intro A hA B hB
    have hfA : MeasurableSet (f ⁻¹' A) := hf hA
    have e := TSPWAux.meas_inter_eq_of_condExp hle P _ _ ((hrun t ht).1 hfA) (hθ hfA)
      (hpost t ht _ hfA) B hB
    rw [(hrun t ht).2]
    exact e
  have i1 := integral_sub hmustar hmux
  have i2 := integral_sub hmustar hUx
  have i3 := integral_sub hUx hmux
  have i4 := integral_sub hmustar hUstar
  constructor
  · rw [i1, i2, i3]; ring
  · rw [i2, i4, hkey]
