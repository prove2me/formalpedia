-- Prove2me | solution 1 for ThompsonTutorial.InfoRatio.bayes_regret_le_sqrt_infoRatio_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T04:40:38.14984+00:00
-- url     : https://prove2.me/submissions/d86811e5-9295-4b84-a320-0be522d634dc

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_history
import Definitions.Def_ThompsonTutorial_InfoRatio_IsAlgorithmRun
import Definitions.Def_ThompsonTutorial_InfoRatio_meanReward
import Definitions.Def_ThompsonTutorial_InfoRatio_bayesRegret
import Definitions.Def_ThompsonTutorial_InfoRatio_infoRatio
import Definitions.Def_ThompsonTutorial_InfoRatio_maxInfoRatio
import Definitions.Def_ThompsonTutorial_InfoRatio_entropy
open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false

namespace TSIRAux

open InformationTheory

variable {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C]

/-- `(ν_V ⊗ κ_W) × P_U` rearranged equals `(P_V × P_U) ⊗ (κ_W ∘ fst)`. -/
lemma map_rearrange_prod (μV : Measure B) [IsProbabilityMeasure μV] (μU : Measure A)
    [IsProbabilityMeasure μU] (κ : Kernel B C) [IsMarkovKernel κ] :
    ((μV ⊗ₘ κ).prod μU).map (fun p : (B × C) × A => ((p.1.1, p.2), p.1.2)) =
      (μV.prod μU) ⊗ₘ (Kernel.prodMkRight A κ) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (by fun_prop)]
  rw [Measure.lintegral_compProd hf]
  rw [lintegral_prod _ (by fun_prop)]
  rw [Measure.lintegral_compProd (by fun_prop)]
  rw [lintegral_prod _ ?_]
  · refine lintegral_congr fun b => ?_
    simp only [Kernel.prodMkRight_apply]
    rw [lintegral_lintegral_swap (by fun_prop)]
  · exact (Measurable.lintegral_kernel_prod_right' (κ := κ.prodMkRight A) hf).aemeasurable

/-- diagonal: `P_{(U,U)} ⊗ (κ_{V|U} ∘ fst)` pushed by `((u1,u2),v) ↦ (v,u2)` is `P_{(V,U)}`. -/
lemma map_diag_compProd (P : Measure Ω) [IsProbabilityMeasure P]
    [StandardBorelSpace B] [Nonempty B]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V) :
    ((P.map (fun ω => (U ω, U ω))) ⊗ₘ (Kernel.prodMkRight A (condDistrib V U P))).map
      (fun p : (A × A) × B => (p.2, p.1.2)) = P.map (fun ω => (V ω, U ω)) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (by fun_prop), Measure.lintegral_compProd (by fun_prop),
    lintegral_map ?_ (by fun_prop), lintegral_map hf (by fun_prop)]
  · simp only [Kernel.prodMkRight_apply]
    have h1 : (P.map U) ⊗ₘ condDistrib V U P = P.map (fun ω => (U ω, V ω)) :=
      compProd_map_condDistrib hV.aemeasurable
    have h2 : ∫⁻ ω, ∫⁻ v, f (v, U ω) ∂(condDistrib V U P (U ω)) ∂P
        = ∫⁻ p, f (p.2, p.1) ∂(P.map (fun ω => (U ω, V ω))) := by
      rw [← h1, Measure.lintegral_compProd (by fun_prop), lintegral_map ?_ hU]
      exact (Measurable.lintegral_kernel_prod_right' (κ := condDistrib V U P)
        (f := fun p : A × B => f (p.2, p.1)) (by fun_prop))
    rw [h2, lintegral_map (by fun_prop) (by fun_prop)]
  · exact (Measurable.lintegral_kernel_prod_right' (κ := Kernel.prodMkRight A (condDistrib V U P))
        (f := fun p : (A × A) × B => f (p.2, p.1.2)) (by fun_prop))

/-- product side of the diagonal step. -/
lemma map_diag_prod (P : Measure Ω) [IsProbabilityMeasure P]
    [StandardBorelSpace B] [Nonempty B]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V) :
    (((P.map U).prod (P.map U)) ⊗ₘ (Kernel.prodMkRight A (condDistrib V U P))).map
      (fun p : (A × A) × B => (p.2, p.1.2)) = (P.map V).prod (P.map U) := by
  haveI := Measure.isProbabilityMeasure_map (μ := P) hU.aemeasurable
  have hmV : P.map V = (P.map (fun ω => (U ω, V ω))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hU.prodMk hV)]; rfl
  have h1 : (P.map U) ⊗ₘ condDistrib V U P = P.map (fun ω => (U ω, V ω)) :=
      compProd_map_condDistrib hV.aemeasurable
  rw [← map_rearrange_prod (P.map U) (P.map U) (condDistrib V U P), h1,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have h3 := (Measure.map_prod_map (P.map (fun ω => (U ω, V ω))) (P.map U) measurable_snd
    measurable_id).symm
  rw [Measure.map_id, ← hmV] at h3
  exact h3

lemma kernel_prod_eq_compProd (κ : Kernel A B) [IsSFiniteKernel κ] (η : Kernel A C)
    [IsSFiniteKernel η] : κ ×ₖ η = κ ⊗ₖ (Kernel.prodMkRight B η) := by
  ext a s hs
  rw [Kernel.prod_apply, Measure.prod_apply hs, Kernel.compProd_apply hs]
  rfl

/-- `I(V;U) ≤ H(U)` in the KL formulation. -/
lemma mi_le_entropy (P : Measure Ω) [IsProbabilityMeasure P]
    [StandardBorelSpace B] [Nonempty B]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V) :
    klDiv (P.map (fun ω => (V ω, U ω))) ((P.map V).prod (P.map U)) ≤
      klDiv (P.map (fun ω => (U ω, U ω))) ((P.map U).prod (P.map U)) := by
  have := Measure.isProbabilityMeasure_map (μ := P) hU.aemeasurable
  rw [← map_diag_compProd P U V hU hV, ← map_diag_prod P U V hU hV]
  calc _ ≤ klDiv ((P.map (fun ω => (U ω, U ω))) ⊗ₘ (Kernel.prodMkRight A (condDistrib V U P)))
        (((P.map U).prod (P.map U)) ⊗ₘ (Kernel.prodMkRight A (condDistrib V U P))) :=
          klDiv_map_le _ _ (by fun_prop)
    _ = _ := klDiv_compProd_left _ _ _

/-- Chain step: `I(V;U) + I(U;W|V) ≤ I((V,W);U)`. -/
lemma chain_step (P : Measure Ω) [IsProbabilityMeasure P]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace C] [Nonempty C]
    (U : Ω → A) (V : Ω → B) (W : Ω → C) (hU : Measurable U) (hV : Measurable V)
    (hW : Measurable W) :
    klDiv (P.map (fun ω => (V ω, U ω))) ((P.map V).prod (P.map U)) +
      klDiv (P.map (fun ω => (V ω, (U ω, W ω))))
        ((P.map V) ⊗ₘ (condDistrib U V P ×ₖ condDistrib W V P)) ≤
      klDiv (P.map (fun ω => ((V ω, W ω), U ω))) ((P.map (fun ω => (V ω, W ω))).prod (P.map U)) := by
  have := Measure.isProbabilityMeasure_map (μ := P) hU.aemeasurable
  have := Measure.isProbabilityMeasure_map (μ := P) hV.aemeasurable
  have hQ : (P.map (fun ω => (V ω, U ω))) ⊗ₘ condDistrib W (fun ω => (V ω, U ω)) P =
      P.map (fun ω => ((V ω, U ω), W ω)) := compProd_map_condDistrib hW.aemeasurable
  have hμ : (P.map V) ⊗ₘ condDistrib U V P = P.map (fun ω => (V ω, U ω)) :=
    compProd_map_condDistrib hU.aemeasurable
  have hVW : (P.map V) ⊗ₘ condDistrib W V P = P.map (fun ω => (V ω, W ω)) :=
    compProd_map_condDistrib hW.aemeasurable
  have hν : (P.map V).prod (P.map U) = (P.map V) ⊗ₘ Kernel.const B (P.map U) :=
    Measure.compProd_const.symm
  have hchain := klDiv_compProd_eq_add (P.map (fun ω => (V ω, U ω))) ((P.map V).prod (P.map U))
    (condDistrib W (fun ω => (V ω, U ω)) P) (Kernel.prodMkRight A (condDistrib W V P))
  -- (b) the conditional term
  have e1 : P.map (fun ω => (V ω, (U ω, W ω))) =
      ((P.map (fun ω => (V ω, U ω))) ⊗ₘ condDistrib W (fun ω => (V ω, U ω)) P).map
        MeasurableEquiv.prodAssoc := by
    rw [hQ, Measure.map_map (by fun_prop) (by fun_prop)]; rfl
  have e2 : (P.map V) ⊗ₘ (condDistrib U V P ×ₖ condDistrib W V P) =
      ((P.map (fun ω => (V ω, U ω))) ⊗ₘ Kernel.prodMkRight A (condDistrib W V P)).map
        MeasurableEquiv.prodAssoc := by
    rw [← hμ, Measure.compProd_assoc', kernel_prod_eq_compProd]
  have hb : klDiv (P.map (fun ω => (V ω, (U ω, W ω))))
        ((P.map V) ⊗ₘ (condDistrib U V P ×ₖ condDistrib W V P)) ≤
      klDiv ((P.map (fun ω => (V ω, U ω))) ⊗ₘ condDistrib W (fun ω => (V ω, U ω)) P)
        ((P.map (fun ω => (V ω, U ω))) ⊗ₘ Kernel.prodMkRight A (condDistrib W V P)) := by
    rw [e1, e2]; exact klDiv_map_le _ _ MeasurableEquiv.prodAssoc.measurable
  -- (c) the total term
  have g1 : (P.map (fun ω => ((V ω, W ω), U ω))).map
      (fun p : (B × C) × A => ((p.1.1, p.2), p.1.2)) =
      (P.map (fun ω => (V ω, U ω))) ⊗ₘ condDistrib W (fun ω => (V ω, U ω)) P := by
    rw [hQ, Measure.map_map (by fun_prop) (by fun_prop)]; rfl
  have g2 : ((P.map (fun ω => (V ω, W ω))).prod (P.map U)).map
      (fun p : (B × C) × A => ((p.1.1, p.2), p.1.2)) =
      ((P.map V).prod (P.map U)) ⊗ₘ Kernel.prodMkRight A (condDistrib W V P) := by
    rw [← hVW]; exact map_rearrange_prod _ _ _
  have hc : klDiv ((P.map (fun ω => (V ω, U ω))) ⊗ₘ condDistrib W (fun ω => (V ω, U ω)) P)
        (((P.map V).prod (P.map U)) ⊗ₘ Kernel.prodMkRight A (condDistrib W V P)) ≤
      klDiv (P.map (fun ω => ((V ω, W ω), U ω)))
        ((P.map (fun ω => (V ω, W ω))).prod (P.map U)) := by
    rw [← g1, ← g2]; exact klDiv_map_le _ _ (by fun_prop)
  calc _ ≤ klDiv (P.map (fun ω => (V ω, U ω))) ((P.map V).prod (P.map U)) +
        klDiv ((P.map (fun ω => (V ω, U ω))) ⊗ₘ condDistrib W (fun ω => (V ω, U ω)) P)
        ((P.map (fun ω => (V ω, U ω))) ⊗ₘ Kernel.prodMkRight A (condDistrib W V P)) := by
          gcongr
    _ = _ := hchain.symm
    _ ≤ _ := hc


open ThompsonTutorial.InfoRatio

lemma history_meas {Ω' B' : Type*} [MeasurableSpace Ω'] [MeasurableSpace B']
    (Z : ℕ → Ω' → B') (n : ℕ) (hZ : ∀ s, Measurable (Z (s + 1))) :
    Measurable (history Z n) := by
  unfold history
  exact measurable_pi_lambda _ (fun i => hZ i)

lemma run_meas {Ω' X Y Θ W Ξ : Type*} [MeasurableSpace Ω'] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Θ] [MeasurableSpace W] [MeasurableSpace Ξ]
    (g : X → Θ → W → Y) (θ : Ω' → Θ) (w : ℕ → Ω' → W) (ξ : Ω' → Ξ)
    (π : (t : ℕ) → (Fin t → X × Y) → Ξ → X) (x : ℕ → Ω' → X) (y : ℕ → Ω' → Y)
    (hg : Measurable (fun p : X × Θ × W => g p.1 p.2.1 p.2.2))
    (hπ : ∀ t, Measurable (fun p : (Fin t → X × Y) × Ξ => π t p.1 p.2))
    (hθ : Measurable θ) (hw : ∀ t, Measurable (w t)) (hξ : Measurable ξ)
    (hrun : IsAlgorithmRun g θ w ξ π x y) :
    ∀ s, Measurable (x (s + 1)) ∧ Measurable (y (s + 1)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    have hH : Measurable (history (fun s ω => (x s ω, y s ω)) s) := by
      unfold history
      refine measurable_pi_lambda _ (fun i => ?_)
      have := ih i i.2
      exact this.1.prodMk this.2
    have hx : Measurable (x (s + 1)) := by
      have : x (s + 1) = fun ω => π s (history (fun s ω => (x s ω, y s ω)) s ω) (ξ ω) :=
        funext fun ω => (hrun s ω).1
      rw [this]
      exact (hπ s).comp (hH.prodMk hξ)
    refine ⟨hx, ?_⟩
    have : y (s + 1) = fun ω => g (x (s + 1) ω) (θ ω) (w (s + 1) ω) :=
      funext fun ω => (hrun s ω).2
    rw [this]
    exact hg.comp (hx.prodMk (hθ.prodMk (hw _)))

lemma sum_cmi_le {Ω' X Y : Type*} [MeasurableSpace Ω']
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (P : Measure Ω') [IsProbabilityMeasure P] (U : Ω' → X) (Z : ℕ → Ω' → X × Y)
    (hU : Measurable U) (hZ : ∀ s, Measurable (Z (s + 1))) (n : ℕ) :
    ∑ t ∈ Finset.Icc 1 n, condMutualInfo P U (Z t) (history Z (t - 1)) ≤
      klDiv (P.map (fun ω => (history Z n ω, U ω))) ((P.map (history Z n)).prod (P.map U)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have hsplit : Measurable (fun h : Fin (n + 1) → X × Y => (Fin.init h, h (Fin.last n))) :=
      (measurable_pi_lambda _ (fun i => measurable_pi_apply _)).prodMk (measurable_pi_apply _)
    have hHn := history_meas Z n hZ
    have hHn1 := history_meas Z (n + 1) hZ
    have hfun : (fun h : Fin (n + 1) → X × Y => (Fin.init h, h (Fin.last n))) ∘ history Z (n + 1)
        = fun ω => (history Z n ω, Z (n + 1) ω) := by
      funext ω
      refine Prod.ext ?_ ?_
      · funext i; simp [Fin.init, history]
      · simp [history]
    have e1 : (P.map (fun ω => (history Z (n + 1) ω, U ω))).map (Prod.map
        (fun h : Fin (n + 1) → X × Y => (Fin.init h, h (Fin.last n))) id) =
        P.map (fun ω => ((history Z n ω, Z (n + 1) ω), U ω)) := by
      rw [Measure.map_map (hsplit.prodMap measurable_id) (hHn1.prodMk hU)]
      congr 1
    have e2 : ((P.map (history Z (n + 1))).prod (P.map U)).map (Prod.map
        (fun h : Fin (n + 1) → X × Y => (Fin.init h, h (Fin.last n))) id) =
        (P.map (fun ω => (history Z n ω, Z (n + 1) ω))).prod (P.map U) := by
      rw [← Measure.map_prod_map _ _ hsplit measurable_id, Measure.map_id,
        Measure.map_map hsplit hHn1, hfun]
    calc _ ≤ klDiv (P.map (fun ω => (history Z n ω, U ω))) ((P.map (history Z n)).prod (P.map U))
          + condMutualInfo P U (Z (n + 1)) (history Z n) := by gcongr
      _ ≤ klDiv (P.map (fun ω => ((history Z n ω, Z (n + 1) ω), U ω)))
          ((P.map (fun ω => (history Z n ω, Z (n + 1) ω))).prod (P.map U)) :=
          chain_step P U (history Z n) (Z (n + 1)) hU hHn (hZ n)
      _ ≤ _ := by
        rw [← e1, ← e2]
        exact klDiv_map_le _ _ (hsplit.prodMap measurable_id)

end TSIRAux

open MeasureTheory ProbabilityTheory ThompsonTutorial.InfoRatio in
theorem solution
    {Ω X Y Θ W Ξ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Θ] [MeasurableSpace W] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : X → Θ → W → Y) (r : Y → ℝ) (θ : Ω → Θ) (w : ℕ → Ω → W) (ξ : Ω → Ξ)
    (π : (t : ℕ) → (Fin t → X × Y) → Ξ → X) (x : ℕ → Ω → X) (y : ℕ → Ω → Y)
    (xstar : Ω → X) (T : ℕ)
    (hg : Measurable (fun p : X × Θ × W => g p.1 p.2.1 p.2.2))
    (hr : Measurable r)
    (hπ : ∀ t, Measurable (fun p : (Fin t → X × Y) × Ξ => π t p.1 p.2))
    (hθ : Measurable θ) (hw : ∀ t, Measurable (w t)) (hξ : Measurable ξ)
    (hw_indep : iIndepFun (fun t : ℕ => w (t + 1)) P)
    (hw_ident : ∀ t : ℕ, IdentDistrib (w (t + 1)) (w 1) P P)
    (hθw : IndepFun θ (fun ω (t : ℕ) => w (t + 1) ω) P)
    (hξθw : IndepFun ξ (fun ω => (θ ω, fun t : ℕ => w (t + 1) ω)) P)
    (hrun : IsAlgorithmRun g θ w ξ π x y)
    (hxstar_meas : Measurable xstar)
    (hxstar : ∀ (ω : Ω) (a : X),
      meanReward g r (P.map (w 1)) a (θ ω) ≤ meanReward g r (P.map (w 1)) (xstar ω) (θ ω))
    (hint : ∀ t ∈ Finset.Icc 1 T, Integrable (fun ω =>
      meanReward g r (P.map (w 1)) (xstar ω) (θ ω) - meanReward g r (P.map (w 1)) (x t ω) (θ ω)) P)
    (hΓ : maxInfoRatio P (meanReward g r (P.map (w 1))) θ xstar x y T ≠ ⊤)
    (hH : entropy P xstar ≠ ⊤) :
    bayesRegret P (meanReward g r (P.map (w 1))) θ xstar x T ≤
      Real.sqrt ((maxInfoRatio P (meanReward g r (P.map (w 1))) θ xstar x y T).toReal *
        (entropy P xstar).toReal * T) := by
  classical
  set μ := meanReward g r (P.map (w 1)) with hμ
  set Z : ℕ → Ω → X × Y := fun s ω => (x s ω, y s ω) with hZdef
  have hxy := TSIRAux.run_meas g θ w ξ π x y hg hπ hθ hw hξ hrun
  have hZ : ∀ s, Measurable (Z (s + 1)) := fun s => (hxy s).1.prodMk (hxy s).2
  set I : ℕ → ℝ≥0∞ := fun t => condMutualInfo P xstar (fun ω => (x t ω, y t ω))
      (history (fun s ω => (x s ω, y s ω)) (t - 1)) with hIdef
  set G := maxInfoRatio P μ θ xstar x y T with hG
  set H := entropy P xstar with hHdef
  set D : ℕ → ℝ := fun t => ∫ ω, (μ (xstar ω) (θ ω) - μ (x t ω) (θ ω)) ∂P with hD
  have hsum : ∑ t ∈ Finset.Icc 1 T, I t ≤ H :=
    (TSIRAux.sum_cmi_le P xstar Z hxstar_meas hZ T).trans
      (TSIRAux.mi_le_entropy P xstar (history Z T) hxstar_meas (TSIRAux.history_meas Z T hZ))
  have hHlt : H < ⊤ := lt_top_iff_ne_top.2 hH
  have hIfin : ∀ t ∈ Finset.Icc 1 T, I t ≠ ⊤ := by
    intro t ht
    exact ne_top_of_le_ne_top hH
      ((Finset.single_le_sum (f := I) (fun i _ => zero_le) ht).trans hsum)
  have hDnn : ∀ t, 0 ≤ D t := fun t =>
    integral_nonneg (fun ω => sub_nonneg.2 (hxstar ω (x t ω)))
  have hDsq : ∀ t ∈ Finset.Icc 1 T, (D t) ^ 2 ≤ G.toReal * (I t).toReal := by
    intro t ht
    have hle : infoRatio P μ θ xstar x y t ≤ G := Finset.le_sup (f := fun t =>
      infoRatio P μ θ xstar x y t) ht
    have hIR : infoRatio P μ θ xstar x y t = ENNReal.ofReal ((D t) ^ 2) / I t := rfl
    by_cases h0 : I t = 0
    · have hz : ENNReal.ofReal ((D t) ^ 2) = 0 := by
        by_contra hne
        have htop : infoRatio P μ θ xstar x y t = ⊤ := by
          rw [hIR, h0]; exact ENNReal.div_zero hne
        exact hΓ (top_le_iff.1 (htop ▸ hle))
      have : (D t) ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 hz
      rw [h0, ENNReal.toReal_zero, mul_zero]; exact this
    · have hmul : ENNReal.ofReal ((D t) ^ 2) = infoRatio P μ θ xstar x y t * I t := by
        rw [hIR, ENNReal.div_mul_cancel h0 (hIfin t ht)]
      have h2 : ENNReal.ofReal ((D t) ^ 2) ≤ G * I t := by
        rw [hmul]; exact mul_le_mul_left hle _
      have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hΓ (hIfin t ht)) h2
      rwa [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul] at h3
  have hreg : bayesRegret P μ θ xstar x T = ∑ t ∈ Finset.Icc 1 T, D t := by
    unfold bayesRegret
    exact integral_finsetSum _ hint
  have hItoReal : ∑ t ∈ Finset.Icc 1 T, (I t).toReal ≤ H.toReal := by
    rw [← ENNReal.toReal_sum hIfin]
    exact ENNReal.toReal_mono hH hsum
  have hGnn : 0 ≤ G.toReal := ENNReal.toReal_nonneg
  have hsq : (∑ t ∈ Finset.Icc 1 T, D t) ^ 2 ≤ G.toReal * H.toReal * T := by
    calc (∑ t ∈ Finset.Icc 1 T, D t) ^ 2
        ≤ (Finset.Icc 1 T).card * ∑ t ∈ Finset.Icc 1 T, (D t) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (Finset.Icc 1 T).card * ∑ t ∈ Finset.Icc 1 T, G.toReal * (I t).toReal := by
          gcongr with t ht
          exact hDsq t ht
      _ = T * (G.toReal * ∑ t ∈ Finset.Icc 1 T, (I t).toReal) := by
          rw [← Finset.mul_sum]; simp
      _ ≤ T * (G.toReal * H.toReal) := by gcongr
      _ = G.toReal * H.toReal * T := by ring
  rw [hreg]
  have hnn : 0 ≤ ∑ t ∈ Finset.Icc 1 T, D t := Finset.sum_nonneg fun t _ => hDnn t
  calc ∑ t ∈ Finset.Icc 1 T, D t = Real.sqrt ((∑ t ∈ Finset.Icc 1 T, D t) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq
