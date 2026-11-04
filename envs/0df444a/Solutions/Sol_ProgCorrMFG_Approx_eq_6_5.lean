-- Prove2me | solution 1 for ProgCorrMFG.Approx.eq_6_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T13:14:15.866176+00:00
-- url     : https://prove2.me/submissions/d9424a97-62aa-4b29-ab75-73ba776a27d6

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx.Sol65

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem distTV_le_one {X : Type} [Fintype X] (μ μ' : Meas X) : distTV μ μ' ≤ 1 := by
  show (1 / 2 : ℝ) * ∑ x, |μ.1 x - μ'.1 x| ≤ 1
  have h1 : ∑ x, μ.1 x = 1 := μ.2.2
  have h2 : ∑ x, μ'.1 x = 1 := μ'.2.2
  have hle : ∑ x, |μ.1 x - μ'.1 x| ≤ ∑ x, (μ.1 x + μ'.1 x) := by
    apply Finset.sum_le_sum
    intro x _
    have a : 0 ≤ μ.1 x := μ.2.1 x
    have b : 0 ≤ μ'.1 x := μ'.2.1 x
    rw [abs_le]; constructor <;> linarith
  rw [Finset.sum_add_distrib, h1, h2] at hle
  linarith

theorem distTV_nonneg {X : Type} [Fintype X] (μ μ' : Meas X) : 0 ≤ distTV μ μ' := by
  unfold distTV
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem A3_bound {T : ℕ} {X G : Type} [Fintype X] [Nonempty X] [Fintype G] [MeasurableSpace X]
    [MeasurableSpace G] (M : Model T X G) (hA3 : M.A3) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ t x m g, |M.f t x m g| ≤ B) ∧ ∀ x m, |M.F x m| ≤ B := by
  classical
  obtain ⟨L, hf, hF⟩ := hA3
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  let c : Meas X := ⟨Pi.single x₀ 1, single_mem_stdSimplex ℝ x₀⟩
  let K : ℝ := (∑ q : Fin T × X × G, |M.f q.1 q.2.1 c q.2.2|) + ∑ x, |M.F x c|
  have hK1 : ∀ t x g, |M.f t x c g| ≤ K := by
    intro t x g
    have := Finset.single_le_sum (f := fun q : Fin T × X × G => |M.f q.1 q.2.1 c q.2.2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (t, x, g))
    have h2 : 0 ≤ ∑ x, |M.F x c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    simp only [K]; linarith
  have hK2 : ∀ x, |M.F x c| ≤ K := by
    intro x
    have := Finset.single_le_sum (f := fun x => |M.F x c|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x)
    have h2 : 0 ≤ ∑ q : Fin T × X × G, |M.f q.1 q.2.1 c q.2.2| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    simp only [K]; linarith
  have hLd : ∀ m, L * distTV m c ≤ |L| := by
    intro m
    have h0 := distTV_nonneg m c
    have h1 := distTV_le_one m c
    calc L * distTV m c ≤ |L| * distTV m c :=
          mul_le_mul_of_nonneg_right (le_abs_self L) h0
      _ ≤ |L| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg L)
      _ = |L| := mul_one _
  refine ⟨K + |L|, ?_, ?_, ?_⟩
  · have := hK2 x₀
    have := abs_nonneg (M.F x₀ c)
    have := abs_nonneg L
    linarith
  · intro t x m g
    have h1 := hf t x g m c
    have h2 := abs_sub_abs_le_abs_sub (M.f t x m g) (M.f t x c g)
    have := hK1 t x g
    have := hLd m
    linarith
  · intro x m
    have h1 := hF x m c
    have h2 := abs_sub_abs_le_abs_sub (M.F x m) (M.F x c)
    have := hK2 x
    have := hLd m
    linarith


theorem continuous_of_lip {X : Type} [Fintype X] (h : Meas X → ℝ) (L : ℝ)
    (hL : ∀ m m', |h m - h m'| ≤ L * distTV m m') : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro m
  have hd : Continuous (fun m' : Meas X => distTV m' m) := by
    show Continuous (fun m' : Meas X => (1 / 2 : ℝ) * ∑ x, |m'.1 x - m.1 x|)
    exact continuous_const.mul (continuous_finsetSum _ fun x _ =>
      (((continuous_apply x).comp continuous_subtype_val).sub continuous_const).abs)
  have h0 : distTV m m = 0 := by simp [distTV]
  have hlim : Tendsto (fun m' => |L| * distTV m' m) (𝓝 m) (𝓝 0) := by
    have := (hd.tendsto m).const_mul |L|
    rwa [h0, mul_zero] at this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m' => ?_) hlim
  rw [Real.norm_eq_abs]
  calc |h m' - h m| ≤ L * distTV m' m := hL m' m
    _ ≤ |L| * distTV m' m := mul_le_mul_of_nonneg_right (le_abs_self L) (distTV_nonneg _ _)

section Gen

variable {T : ℕ} {Θ Y : Type}

/-- After `k` steps, coordinates `0, …, k` hold the solution, the others still hold `x₀ θ`. -/
noncomputable def genPath (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ) :
    ℕ → Fin (T + 1) → Y
  | 0 => fun _ => x₀ θ
  | k + 1 =>
    if h : k < T then
      Function.update (genPath x₀ step θ k) ⟨k + 1, by omega⟩ (step ⟨k, h⟩ θ (genPath x₀ step θ k))
    else genPath x₀ step θ k

theorem genPath_succ_of_ne (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ)
    (k : ℕ) (j : Fin (T + 1)) (hj : j.1 ≠ k + 1) :
    genPath x₀ step θ (k + 1) j = genPath x₀ step θ k j := by
  simp only [genPath]
  split_ifs with h
  · rw [Function.update_of_ne]
    exact fun h' => hj (by rw [h'])
  · rfl

theorem genPath_stable (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ)
    (j : Fin (T + 1)) : ∀ d, genPath x₀ step θ (j.1 + d) j = genPath x₀ step θ j.1 j := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, genPath_succ_of_ne _ _ _ _ _ (by omega), ih]

theorem genPath_le (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ)
    (j : Fin (T + 1)) (k : ℕ) (hk : j.1 ≤ k) :
    genPath x₀ step θ k j = genPath x₀ step θ j.1 j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact genPath_stable x₀ step θ j d

/-- The solution of the recursion. -/
noncomputable def gen (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ) :
    Fin (T + 1) → Y := genPath x₀ step θ T

def NonAntStep (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) : Prop :=
  ∀ t θ p p', (∀ s : Fin (T + 1), s ≤ t.castSucc → p s = p' s) → step t θ p = step t θ p'

theorem gen_zero (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y) (θ : Θ) :
    gen x₀ step θ 0 = x₀ θ := by
  unfold gen
  rw [genPath_le x₀ step θ 0 T (by simp)]
  rfl

theorem gen_succ (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y)
    (hstep : NonAntStep step) (θ : Θ) (t : Fin T) :
    gen x₀ step θ t.succ = step t θ (gen x₀ step θ) := by
  unfold gen
  rw [genPath_le x₀ step θ t.succ T (by simp)]
  have : (t.succ : Fin (T + 1)).1 = t.1 + 1 := rfl
  rw [this]
  simp only [genPath, t.2, dite_true]
  have e : (⟨t.1 + 1, by omega⟩ : Fin (T + 1)) = t.succ := rfl
  rw [e, Function.update_self]
  apply hstep
  intro s hs
  have hs' : s.1 ≤ t.1 := hs
  rw [genPath_le x₀ step θ s t.1 hs', genPath_le x₀ step θ s T (by omega)]

theorem gen_unique (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y)
    (hstep : NonAntStep step) (θ : Θ) (s : Fin (T + 1) → Y) (h0 : s 0 = x₀ θ)
    (hs : ∀ t : Fin T, s t.succ = step t θ s) : s = gen x₀ step θ := by
  have key : ∀ n, ∀ j : Fin (T + 1), j.1 ≤ n → s j = gen x₀ step θ j := by
    intro n
    induction n with
    | zero =>
      intro j hj
      obtain rfl : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      rw [h0, gen_zero]
    | succ n ih =>
      intro j hj
      rcases Nat.lt_or_ge j.1 (n + 1) with h | h
      · exact ih j (by omega)
      · have hjT : n < T := by have := j.2; omega
        have ej : j = (⟨n, hjT⟩ : Fin T).succ := Fin.ext (by simp; omega)
        rw [ej, hs, gen_succ x₀ step hstep]
        apply hstep
        intro s' hs'
        exact ih s' hs'
  funext j
  exact key j.1 j le_rfl

variable [MeasurableSpace Θ] [MeasurableSpace Y]

theorem measurable_gen (x₀ : Θ → Y) (step : Fin T → Θ → (Fin (T + 1) → Y) → Y)
    (hx₀ : Measurable x₀)
    (hstep : ∀ t, Measurable (fun q : Θ × (Fin (T + 1) → Y) => step t q.1 q.2)) :
    Measurable (gen x₀ step) := by
  have : ∀ k, Measurable (fun θ => genPath x₀ step θ k) := by
    intro k
    induction k with
    | zero => exact measurable_pi_lambda _ (fun _ => hx₀)
    | succ k ih =>
      by_cases hk : k < T
      · simp only [genPath, hk, dite_true]
        apply measurable_pi_lambda
        intro j
        by_cases hj : j = ⟨k + 1, by omega⟩
        · rw [hj]
          simp only [Function.update_self]
          exact (hstep ⟨k, hk⟩).comp (measurable_id.prodMk ih)
        · simp only [Function.update_of_ne hj]
          exact (measurable_pi_apply _).comp ih
      · simp only [genPath, hk, dite_false]
        exact ih
  exact this T

end Gen

section Main

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


theorem exists_MFGReal (M : Model T X G) (hΨ : M.PsiMeasurable)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      Nonempty (MFGRealization M m₀ ρ iotaMFG P) := by
  let step : Fin T → X × (Fin T → I) × (Strat T X G × Flow T X) → (Fin (T + 1) → X) → X :=
    fun t θ p => M.Ψ t (p t.castSucc) (θ.2.2.2 t.castSucc) (θ.2.2.1 t (p t.castSucc)) (θ.2.1 t)
  have hna : NonAntStep step := by
    intro t θ p p' h
    simp only [step, h t.castSucc le_rfl]
  have hmeas : ∀ t, Measurable (fun q : (X × (Fin T → I) × (Strat T X G × Flow T X)) ×
      (Fin (T + 1) → X) => step t q.1 q.2) := by
    intro t
    have h3 : Measurable (fun r : Strat T X G × (Fin (T + 1) → X) => r.1 t (r.2 t.castSucc)) :=
      measurable_of_countable _
    have h3' : Measurable (fun q : (X × (Fin T → I) × (Strat T X G × Flow T X)) ×
        (Fin (T + 1) → X) => q.1.2.2.1 t (q.2 t.castSucc)) :=
      h3.comp (f := fun q : (X × (Fin T → I) × (Strat T X G × Flow T X)) ×
        (Fin (T + 1) → X) => (q.1.2.2.1, q.2)) (by fun_prop)
    exact (hΨ t).comp (f := fun q : (X × (Fin T → I) × (Strat T X G × Flow T X)) ×
        (Fin (T + 1) → X) => (q.2 t.castSucc, q.1.2.2.2 t.castSucc,
          q.1.2.2.1 t (q.2 t.castSucc), q.1.2.1 t))
      (Measurable.prodMk (by fun_prop) (Measurable.prodMk (by fun_prop)
        (Measurable.prodMk h3' (by fun_prop))))
  refine ⟨X × (Fin T → I) × (Strat T X G × Flow T X), inferInstance,
    m₀.prod ((Measure.pi fun _ : Fin T => (volume : Measure I)).prod ρ), inferInstance,
    ⟨{ state := gen Prod.fst step
       sugg := fun ω => ω.2.2.1
       flow := fun ω => ω.2.2.2
       noise := fun ω => ω.2.1
       measurable_state := measurable_gen _ _ measurable_fst hmeas
       measurable_sugg := by fun_prop
       measurable_flow := by fun_prop
       measurable_noise := by fun_prop
       law := ?_
       dynamics := ?_ }⟩⟩
  · have : (fun ω : X × (Fin T → I) × (Strat T X G × Flow T X) =>
        (gen Prod.fst step ω 0, ω.2.1, (ω.2.2.1, ω.2.2.2))) = id := by
      funext ω
      rw [gen_zero]
      rfl
    rw [this, Measure.map_id]
  · exact Filter.Eventually.of_forall fun ω t => gen_succ _ _ hna ω t



end Main

end ProgCorrMFG.Approx.Sol65

open MeasureTheory ProbabilityTheory unitInterval Filter Topology ProgCorrMFG.Approx
  ProgCorrMFG.Approx.Sol65

theorem solution {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (M : Model T X G) (hΨ : M.PsiMeasurable) (hA3 : M.A3)
    (m₀ : Measure X) [IsProbabilityMeasure m₀]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (hρ₁ : ρ = ((ρ.map Prod.snd) ⊗ₘ ρ₁).map Prod.swap)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : MFGRealization M m₀ ρ iotaMFG P)
    (c : Flow T X → ℝ)
    (hc : ∀ᵐ m ∂(ρ.map Prod.snd), ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (R' : MFGRealization M m₀ ((ρ₁ m).prod (Measure.dirac m)) iotaMFG P'),
      R'.cost = c m) :
    R.cost = ∫ m, c m ∂(ρ.map Prod.snd) := by
  classical
  haveI : IsProbabilityMeasure (ρ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂, ρ.map Prod.snd = ρ₂ := ⟨_, rfl⟩
  haveI : IsProbabilityMeasure ρ₂ := hρ₂ ▸ inferInstance
  rw [hρ₂] at hρ₁ hc ⊢
  obtain ⟨B, hB0, hfB, hFB⟩ := A3_bound M hA3
  obtain ⟨L, hfL, hFL⟩ := hA3
  have hfm : ∀ t x g, Measurable (fun m : Meas X => M.f t x m g) := fun t x g =>
    (continuous_of_lip _ L (fun m m' => hfL t x g m m')).measurable
  have hFm : ∀ x, Measurable (fun m : Meas X => M.F x m) := fun x =>
    (continuous_of_lip _ L (fun m m' => hFL x m m')).measurable
  -- the cost as a function of a path, a suggestion and a flow
  let H : (Fin (T + 1) → X) × (Strat T X G × Flow T X) → ℝ := fun p =>
    (∑ t : Fin T, M.f t (p.1 t.castSucc) (p.2.2 t.castSucc) ((iotaMFG p.2.1 t).1 p.1 p.2.2)) +
      M.F (p.1 (Fin.last T)) (p.2.2 (Fin.last T))
  have hH : Measurable H := by
    apply Measurable.add
    · apply Finset.measurable_sum
      intro t _
      have hf : Measurable (fun q : Meas X × (X × G) => M.f t q.2.1 q.1 q.2.2) :=
        measurable_from_prod_countable_left (fun y => hfm t y.1 y.2)
      have hg : Measurable (fun p : (Fin (T + 1) → X) × (Strat T X G × Flow T X) =>
          (iotaMFG p.2.1 t).1 p.1 p.2.2) :=
        (measurable_comp_eval iotaMFG t).comp
          ((measurable_fst.comp measurable_snd).prodMk
            (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      exact hf.comp (f := fun p : (Fin (T + 1) → X) × (Strat T X G × Flow T X) =>
          (p.2.2 t.castSucc, (p.1 t.castSucc, (iotaMFG p.2.1 t).1 p.1 p.2.2)))
        (((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)).prodMk
          (((measurable_pi_apply _).comp measurable_fst).prodMk hg))
    · have hF : Measurable (fun q : Meas X × X => M.F q.2 q.1) :=
        measurable_from_prod_countable_left (fun y => hFm y)
      exact hF.comp (f := fun p : (Fin (T + 1) → X) × (Strat T X G × Flow T X) =>
          (p.2.2 (Fin.last T), p.1 (Fin.last T))) (by fun_prop)
  have hHb : ∀ p, |H p| ≤ (T + 1) * B := by
    intro p
    refine (abs_add_le _ _).trans ?_
    have h1 : |∑ t : Fin T, M.f t (p.1 t.castSucc) (p.2.2 t.castSucc)
        ((iotaMFG p.2.1 t).1 p.1 p.2.2)| ≤ T * B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun t _ => hfB _ _ _ _).trans ?_
      simp
    have h2 := hFB (p.1 (Fin.last T)) (p.2.2 (Fin.last T))
    linarith
  let K : X × (Fin T → I) × (Strat T X G × Flow T X) → ℝ := fun q =>
    H (pathAux M iotaMFG q.1 q.2.1 q.2.2.1 q.2.2.2 T, q.2.2)
  have hK : Measurable K :=
    hH.comp ((measurable_pathAux M hΨ iotaMFG T).prodMk (measurable_snd.comp measurable_snd))
  have hKb : ∀ q, |K q| ≤ (T + 1) * B := fun q => hHb _
  have key : ∀ (ρ' : Measure (Strat T X G × Flow T X)) {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (R : MFGRealization M m₀ ρ' iotaMFG P),
      R.cost = ∫ q, K q ∂(m₀.prod ((Measure.pi fun _ : Fin T => (volume : Measure I)).prod ρ')) := by
    intro ρ' Ω _ P _ R
    have hV : Measurable (fun ω => (R.state ω 0, R.noise ω, (R.sugg ω, R.flow ω))) :=
      ((measurable_pi_apply 0).comp R.measurable_state).prodMk
        (R.measurable_noise.prodMk (R.measurable_sugg.prodMk R.measurable_flow))
    rw [← R.law, integral_map hV.aemeasurable hK.aestronglyMeasurable]
    unfold MFGRealization.cost
    apply integral_congr_ae
    filter_upwards [R.dynamics] with ω hω
    have hp : pathAux M iotaMFG (R.state ω 0) (R.noise ω) (R.sugg ω) (R.flow ω) T = R.state ω := by
      funext j
      exact pathAux_eq M iotaMFG (R.state ω) (R.noise ω) (R.sugg ω) (R.flow ω) hω T le_rfl j
        (by omega)
    simp only [K, H, hp]
  -- reassociate
  set νT : Measure (Fin T → I) := Measure.pi fun _ : Fin T => (volume : Measure I) with hνT
  let μ₁ : Measure (X × (Fin T → I)) := m₀.prod νT
  let K' : (X × (Fin T → I)) × (Strat T X G × Flow T X) → ℝ := fun q => K (q.1.1, q.1.2, q.2)
  have hK' : Measurable K' := hK.comp (measurable_fst.comp measurable_fst |>.prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hK'b : ∀ q, |K' q| ≤ (T + 1) * B := fun q => hKb _
  have hIK : ∀ (ρ' : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ'],
      ∫ q, K q ∂(m₀.prod (νT.prod ρ')) = ∫ y, ∫ q, K' (y, q) ∂ρ' ∂μ₁ := by
    intro ρ' _
    rw [← Measure.prodAssoc_prod, integral_map_equiv]
    exact integral_prod K' (Integrable.of_bound hK'.aestronglyMeasurable ((T + 1) * B)
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hK'b q))
  -- the conditional cost
  let h : (X × (Fin T → I)) → Flow T X → ℝ := fun y m =>
    ∑ φ : Strat T X G, (ρ₁ m).real {φ} * K' (y, (φ, m))
  have hh : Measurable (Function.uncurry h) := by
    apply Finset.measurable_sum
    intro φ _
    exact ((Kernel.measurable_coe ρ₁ (measurableSet_singleton φ)).ennreal_toReal.comp
      measurable_snd).mul (hK'.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  have hint_fin : ∀ (y : X × (Fin T → I)) (m : Flow T X),
      ∫ φ, K' (y, (φ, m)) ∂(ρ₁ m) = h y m := by
    intro y m
    rw [integral_fintype]
    · rfl
    · exact Integrable.of_finite
  have hhb : ∀ y m, |h y m| ≤ (Fintype.card (Strat T X G) : ℝ) * ((T + 1) * B) := by
    intro y m
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ φ ∈ (Finset.univ : Finset (Strat T X G)),
        |(ρ₁ m).real {φ} * K' (y, (φ, m))| ≤ (T + 1) * B := by
      intro φ _
      rw [abs_mul]
      have h1 : |(ρ₁ m).real {φ}| ≤ 1 := by
        rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
      calc |(ρ₁ m).real {φ}| * |K' (y, (φ, m))| ≤ 1 * ((T + 1) * B) :=
            mul_le_mul h1 (hK'b _) (abs_nonneg _) zero_le_one
        _ = (T + 1) * B := one_mul _
    refine (Finset.sum_le_sum this).trans ?_
    simp
  -- Claim 1: the inner integral against ρ₁(·|m) ⊗ δ_m
  have claim1 : ∀ y m, ∫ q, K' (y, q) ∂((ρ₁ m).prod (Measure.dirac m)) = h y m := by
    intro y m
    rw [integral_prod]
    · simp_rw [integral_dirac]
      exact hint_fin y m
    · exact Integrable.of_bound
        (hK'.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ((T + 1) * B)
        (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hK'b _)
  -- Claim 2: the inner integral against ρ
  have claim2 : ∀ y, ∫ q, K' (y, q) ∂ρ = ∫ m, h y m ∂ρ₂ := by
    intro y
    have hmeas : Measurable (fun q : Strat T X G × Flow T X => K' (y, q)) :=
      hK'.comp (measurable_const.prodMk measurable_id)
    conv_lhs => rw [hρ₁]
    rw [integral_map measurable_swap.aemeasurable hmeas.aestronglyMeasurable,
      Measure.integral_compProd]
    · simp only [Prod.swap_prod_mk]
      congr 1
      funext m
      exact hint_fin y m
    · exact Integrable.of_bound (hmeas.comp measurable_swap).aestronglyMeasurable ((T + 1) * B)
        (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hK'b _)
  have hhint : Integrable (Function.uncurry h) (μ₁.prod ρ₂) :=
    Integrable.of_bound hh.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hhb q.1 q.2)
  rw [key ρ P R, hIK ρ]
  simp_rw [claim2]
  rw [integral_integral_swap hhint]
  apply integral_congr_ae
  filter_upwards [hc] with m hm
  obtain ⟨Ω', _, P', _, ⟨R'⟩⟩ := exists_MFGReal M hΨ m₀ ((ρ₁ m).prod (Measure.dirac m))
  rw [← hm Ω' P' R', key _ P' R', hIK]
  simp_rw [claim1]
