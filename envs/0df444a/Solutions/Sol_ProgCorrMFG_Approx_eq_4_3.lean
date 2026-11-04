-- Prove2me | solution 1 for ProgCorrMFG.Approx.eq_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T12:53:08.059388+00:00
-- url     : https://prove2.me/submissions/9fe4c60d-6b42-4cbe-ac6a-5b56f6bc67f0

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx.Sol43

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

variable {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace X] [MeasurableSpace G]

/-- The state path generated recursively from the initial state, noises, suggestion and flow;
after `k` steps the coordinates `0, …, k` are correct, the others are still `x₀`. -/
noncomputable def pathAux (M : Model T X G) (w : Strat T X G → Prog T X G) (x₀ : X)
    (z : Fin T → I) (φ : Strat T X G) (m : Flow T X) : ℕ → (Fin (T + 1) → X)
  | 0 => fun _ => x₀
  | k + 1 =>
    if h : k < T then
      Function.update (pathAux M w x₀ z φ m k) ⟨k + 1, by omega⟩
        (M.Ψ ⟨k, h⟩ (pathAux M w x₀ z φ m k ⟨k, by omega⟩) (m ⟨k, by omega⟩)
          ((w φ ⟨k, h⟩).1 (pathAux M w x₀ z φ m k) m) (z ⟨k, h⟩))
    else pathAux M w x₀ z φ m k

theorem pathAux_eq (M : Model T X G) (w : Strat T X G → Prog T X G)
    (s : Fin (T + 1) → X) (z : Fin T → I) (φ : Strat T X G) (m : Flow T X)
    (hs : ∀ t : Fin T, s t.succ = M.Ψ t (s t.castSucc) (m t.castSucc)
      ((w φ t).1 s m) (z t)) :
    ∀ k, k ≤ T → ∀ j : Fin (T + 1), j.1 ≤ k → pathAux M w (s 0) z φ m k j = s j := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    obtain rfl : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    rfl
  | succ k ih =>
    intro hk j hj
    have hkT : k < T := by omega
    simp only [pathAux, hkT, dite_true]
    by_cases hjk : j = ⟨k + 1, by omega⟩
    · rw [hjk, Function.update_self]
      have e1 := hs ⟨k, hkT⟩
      have hsucc : (⟨k, hkT⟩ : Fin T).succ = ⟨k + 1, by omega⟩ := rfl
      rw [hsucc] at e1
      rw [e1]
      have hcs : (⟨k, hkT⟩ : Fin T).castSucc = ⟨k, by omega⟩ := rfl
      rw [hcs]
      rw [ih (by omega) ⟨k, by omega⟩ le_rfl]
      congr 1
      apply (w φ ⟨k, hkT⟩).2.1
      intro s' hs'
      refine ⟨ih (by omega) s' ?_, rfl⟩
      have : s'.1 ≤ k := hs'
      exact this
    · rw [Function.update_of_ne hjk]
      apply ih (by omega)
      have : j.1 ≠ k + 1 := fun h => hjk (Fin.ext h)
      omega

variable [DiscreteMeasurableSpace X] [Fintype G] [DiscreteMeasurableSpace G] [DecidableEq X]

theorem measurable_comp_eval (w : Strat T X G → Prog T X G) (t : Fin T) :
    Measurable (fun q : Strat T X G × ((Fin (T + 1) → X) × Flow T X) => (w q.1 t).1 q.2.1 q.2.2) :=
  measurable_from_prod_countable_right (fun φ => (w φ t).2.2)

theorem measurable_pathAux (M : Model T X G) (hΨ : M.PsiMeasurable)
    (w : Strat T X G → Prog T X G) (k : ℕ) :
    Measurable (fun q : X × (Fin T → I) × (Strat T X G × Flow T X) =>
      pathAux M w q.1 q.2.1 q.2.2.1 q.2.2.2 k) := by
  induction k with
  | zero =>
    exact measurable_pi_lambda _ (fun _ => measurable_fst)
  | succ k ih =>
    by_cases hkT : k < T
    · simp only [pathAux, hkT, dite_true]
      apply measurable_pi_lambda
      intro j
      by_cases hj : j = ⟨k + 1, by omega⟩
      · subst hj
        simp only [Function.update_self]
        have h1 : Measurable (fun q : X × (Fin T → I) × (Strat T X G × Flow T X) =>
            ((pathAux M w q.1 q.2.1 q.2.2.1 q.2.2.2 k ⟨k, by omega⟩),
              (q.2.2.2 ⟨k, by omega⟩),
              ((w q.2.2.1 ⟨k, hkT⟩).1 (pathAux M w q.1 q.2.1 q.2.2.1 q.2.2.2 k) q.2.2.2),
              (q.2.1 ⟨k, hkT⟩))) := by
          refine Measurable.prodMk ((measurable_pi_apply _).comp ih) ?_
          refine Measurable.prodMk ((measurable_pi_apply _).comp
            (measurable_snd.comp (measurable_snd.comp measurable_snd))) ?_
          refine Measurable.prodMk ?_ ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd))
          exact (measurable_comp_eval w ⟨k, hkT⟩).comp
            ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
              (ih.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))))
        exact (hΨ ⟨k, hkT⟩).comp h1
      · simp only [Function.update_of_ne hj]
        exact (measurable_pi_apply _).comp ih
    · simp only [pathAux, hkT, dite_false]
      exact ih

end ProgCorrMFG.Approx.Sol43

open MeasureTheory ProbabilityTheory unitInterval Filter Topology ProgCorrMFG.Approx
  ProgCorrMFG.Approx.Sol43

theorem solution {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hcost : M.CostsRegular)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (w : Strat T X G → Prog T X G)
    (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (R₁ : MFGRealization M m₀ ρ w P₁)
    (Ω₂ : Type) [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (R₂ : MFGRealization M m₀ ρ w P₂) :
    R₁.cost = R₂.cost := by
  -- the cost as a function of a path, a suggestion and a flow
  let H : (Fin (T + 1) → X) × (Strat T X G × Flow T X) → ℝ := fun p =>
    (∑ t : Fin T, M.f t (p.1 t.castSucc) (p.2.2 t.castSucc) ((w p.2.1 t).1 p.1 p.2.2)) +
      M.F (p.1 (Fin.last T)) (p.2.2 (Fin.last T))
  have hH : Measurable H := by
    apply Measurable.add
    · apply Finset.measurable_sum
      intro t _
      -- (m, (x, g)) ↦ f t x m g
      have hf : Measurable (fun q : Meas X × (X × G) => M.f t q.2.1 q.1 q.2.2) :=
        measurable_from_prod_countable_left (fun y => hcost.1 t y.1 y.2)
      have hg : Measurable (fun p : (Fin (T + 1) → X) × (Strat T X G × Flow T X) =>
          (w p.2.1 t).1 p.1 p.2.2) :=
        (measurable_comp_eval w t).comp
          ((measurable_fst.comp measurable_snd).prodMk
            (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      exact hf.comp (f := fun p : (Fin (T + 1) → X) × (Strat T X G × Flow T X) =>
          (p.2.2 t.castSucc, (p.1 t.castSucc, (w p.2.1 t).1 p.1 p.2.2)))
        (((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)).prodMk
          (((measurable_pi_apply _).comp measurable_fst).prodMk hg))
    · have hF : Measurable (fun q : Meas X × X => M.F q.2 q.1) :=
        measurable_from_prod_countable_left (fun y => hcost.2.1 y)
      exact hF.comp (f := fun p : (Fin (T + 1) → X) × (Strat T X G × Flow T X) =>
          (p.2.2 (Fin.last T), p.1 (Fin.last T))) (by fun_prop)
  let K : X × (Fin T → I) × (Strat T X G × Flow T X) → ℝ := fun q =>
    H (pathAux M w q.1 q.2.1 q.2.2.1 q.2.2.2 T, q.2.2)
  have hK : Measurable K :=
    hH.comp ((measurable_pathAux M hΨ w T).prodMk (measurable_snd.comp measurable_snd))
  have key : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (R : MFGRealization M m₀ ρ w P),
      R.cost = ∫ q, K q ∂(m₀.prod ((Measure.pi fun _ : Fin T => (volume : Measure I)).prod ρ)) := by
    intro Ω _ P _ R
    have hV : Measurable (fun ω => (R.state ω 0, R.noise ω, (R.sugg ω, R.flow ω))) :=
      ((measurable_pi_apply 0).comp R.measurable_state).prodMk
        (R.measurable_noise.prodMk (R.measurable_sugg.prodMk R.measurable_flow))
    rw [← R.law, integral_map hV.aemeasurable hK.aestronglyMeasurable]
    unfold MFGRealization.cost
    apply integral_congr_ae
    filter_upwards [R.dynamics] with ω hω
    have hp : pathAux M w (R.state ω 0) (R.noise ω) (R.sugg ω) (R.flow ω) T = R.state ω := by
      funext j
      exact pathAux_eq M w (R.state ω) (R.noise ω) (R.sugg ω) (R.flow ω) hω T le_rfl j
        (by omega)
    simp only [K, H, hp]
  rw [key P₁ R₁, key P₂ R₂]
