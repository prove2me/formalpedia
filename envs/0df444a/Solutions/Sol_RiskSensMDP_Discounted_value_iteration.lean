-- Prove2me | solution 1 for RiskSensMDP.Discounted.value_iteration
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:23:32.125941+00:00
-- url     : https://prove2.me/submissions/295ace55-aa53-4e2b-9f9a-e4678599e5c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskSensMDP_Discounted_Model
import Theorems.Thm_RiskSensMDP_Discounted_operator_preserves_class
import Theorems.Thm_RiskSensMDP_Discounted_cost_iteration

open MeasureTheory ProbabilityTheory Filter
open RiskSensMDP.Discounted

namespace RSMDP2VIAux

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma dHC_nonneg (M : Model E A) (hB : HasBounds M) (l : List (E × A))
    (hl : ∀ p ∈ l, p ∈ M.P.D) : 0 ≤ discountedHistoryCost M l := by
  induction l with
  | nil => simp [discountedHistoryCost]
  | cons p ps ih =>
    simp only [discountedHistoryCost]
    have h1 := (hB.2.2.2.1 p (hl p (by simp))).1
    have h2 := ih (fun q hq => hl q (by simp [hq]))
    have h3 : 0 ≤ M.β * discountedHistoryCost M ps := mul_nonneg hB.2.2.2.2.1.le h2
    linarith [hB.2.1]

lemma dHC_append (M : Model E A) (l : List (E × A)) (p : E × A) :
    discountedHistoryCost M (l ++ [p]) =
      discountedHistoryCost M l + M.β ^ l.length * M.c p := by
  induction l with
  | nil => simp [discountedHistoryCost]
  | cons q l ih =>
    simp only [List.cons_append, discountedHistoryCost, ih, List.length_cons, pow_succ]
    ring

noncomputable def cOpt (M : Model E A) : Option (E × A) → ℝ
  | none => 0
  | some p => M.c p

lemma cOpt_meas (M : Model E A) (hc : Measurable M.c) : Measurable (cOpt M) := by
  intro S hS
  have h1 : MeasurableSet ({none} : Set (Option (E × A))) :=
    MeasurableSpace.measurableSet_generateFrom (Or.inl rfl)
  have h2 : MeasurableSet (Option.some '' (M.c ⁻¹' S) : Set (Option (E × A))) :=
    MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨_, hc hS, rfl⟩)
  by_cases h0 : (0:ℝ) ∈ S
  · have : cOpt M ⁻¹' S = {none} ∪ Option.some '' (M.c ⁻¹' S) := by
      ext o; cases o <;> simp [cOpt, h0]
    rw [this]; exact h1.union h2
  · have : cOpt M ⁻¹' S = Option.some '' (M.c ⁻¹' S) := by
      ext o; cases o <;> simp [cOpt, h0]
    rw [this]; exact h2

lemma dHC_eq_sum (M : Model E A) (l : List (E × A)) :
    discountedHistoryCost M l =
      ∑ i ∈ Finset.range l.length, M.β ^ i * cOpt M (l[i]?) := by
  induction l with
  | nil => simp [discountedHistoryCost]
  | cons p l ih =>
    rw [List.length_cons, Finset.sum_range_succ', discountedHistoryCost, ih,
      Finset.mul_sum]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, pow_zero, one_mul,
      cOpt, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

lemma get_meas (n : ℕ) : Measurable (fun l : List (E × A) => l[n]?) :=
  (measurable_pi_apply n).comp (fun s hs => ⟨s, hs, rfl⟩)

lemma dHC_meas (M : Model E A) (hc : Measurable M.c) (n : ℕ) :
    Measurable (fun h : {h : History E A // ValidHistory M.P n h} =>
      discountedHistoryCost M h.1.1) := by
  have : (fun h : {h : History E A // ValidHistory M.P n h} =>
      discountedHistoryCost M h.1.1) =
      fun h => ∑ i ∈ Finset.range n, M.β ^ i * cOpt M (h.1.1[i]?) := by
    funext h; rw [dHC_eq_sum, h.2.1]
  rw [this]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
    ((cOpt_meas M hc).comp ((get_meas i).comp (measurable_fst.comp measurable_subtype_coe))))

lemma valid_append (P : ControlledMDP E A) (k : ℕ) (h : History E A)
    (hv : ValidHistory P k h) (a : A) (ha : (h.2, a) ∈ P.D) (x' : E) :
    ValidHistory P (k + 1) (h.1 ++ [(h.2, a)], x') := by
  refine ⟨by simp [hv.1], ?_⟩
  intro q hq
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hv.2 q hq
  · exact ha

lemma expectedFrom_bound (M : Model E A) (hB : HasBounds M) (σ : Policy M.P) (T B : ℝ)
    (hUB : ∀ t ∈ Set.Icc (0:ℝ) T, |M.U t| ≤ B) :
    ∀ (n k : ℕ) (h : History E A) (y z : ℝ), ValidHistory M.P k h → 0 ≤ y → 0 < z → z ≤ 1 →
      y + z * n * M.upperCost ≤ T → |expectedFrom M σ.g k h n y z| ≤ B := by
  intro n
  induction n with
  | zero =>
    intro k h y z hv hy hz hz1 hT
    simp only [expectedFrom]
    exact hUB y ⟨hy, by simpa using hT⟩
  | succ n ih =>
    intro k h y z hv hy hz hz1 hT
    rw [expectedFrom]
    have hD := σ.admissible_g k h hv
    have hc := hB.2.2.2.1 _ hD
    have hlow := hB.2.1
    have hup : 0 < M.upperCost := lt_trans hB.2.1 hB.2.2.1
    have hβ0 := hB.2.2.2.2.1
    have hβ1 := hB.2.2.2.2.2
    have := M.P.markov_Q
    have hbd := norm_integral_le_of_norm_le_const (μ := M.P.Q (h.2, σ.g k h)) (C := B)
      (f := fun x' => expectedFrom M σ.g (k + 1) (h.1 ++ [(h.2, σ.g k h)], x') n
        (y + z * M.c (h.2, σ.g k h)) (z * M.β))
      (Filter.Eventually.of_forall fun x' => ?_)
    · simpa [Real.norm_eq_abs, probReal_univ] using hbd
    rw [Real.norm_eq_abs]
    refine ih (k + 1) _ _ _ (valid_append M.P k h hv _ hD x') ?_ (mul_pos hz hβ0) ?_ ?_
    · have : 0 ≤ z * M.c (h.2, σ.g k h) := mul_nonneg hz.le (by linarith [hc.1])
      linarith
    · nlinarith
    · have e1 : z * M.c (h.2, σ.g k h) ≤ z * M.upperCost :=
        mul_le_mul_of_nonneg_left hc.2 hz.le
      have e2 : z * M.β * (n : ℝ) * M.upperCost ≤ z * (n : ℝ) * M.upperCost := by
        have h0 : 0 ≤ z * (n : ℝ) * M.upperCost := by positivity
        nlinarith
      push_cast at hT
      nlinarith


lemma some_meas : Measurable (Option.some : E × A → Option (E × A)) := by
  apply measurable_generateFrom
  rintro t (rfl | ⟨u, hu, rfl⟩)
  · have : (Option.some ⁻¹' ({none} : Set (Option (E × A)))) = ∅ := by
      ext p; simp
    rw [this]; exact MeasurableSet.empty
  · rwa [Set.preimage_image_eq _ (Option.some_injective _)]

lemma append_meas {α : Type*} [MeasurableSpace α] (k : ℕ) (l : α → List (E × A))
    (hl : Measurable l) (hlen : ∀ a, (l a).length = k) (q : α → E × A) (hq : Measurable q) :
    Measurable (fun a => l a ++ [q a]) := by
  have hfun : Measurable (fun a => fun i : ℕ => (l a ++ [q a])[i]?) := by
    rw [measurable_pi_iff]
    intro i
    rcases lt_trichotomy i k with h | rfl | h
    · have : (fun a => (l a ++ [q a])[i]?) = fun a => (l a)[i]? := by
        funext a; rw [List.getElem?_append_left (by rw [hlen]; exact h)]
      rw [this]; exact (get_meas i).comp hl
    · have : (fun a => (l a ++ [q a])[i]?) = fun a => some (q a) := by
        funext a; rw [List.getElem?_append_right (by rw [hlen])]; simp [hlen]
      rw [this]; exact some_meas.comp hq
    · have : (fun a => (l a ++ [q a])[i]?) = fun _ => none := by
        funext a; rw [List.getElem?_append_right (by rw [hlen]; omega)]
        simp only [hlen]
        rw [List.getElem?_eq_none]; simp; omega
      rw [this]; exact measurable_const
  intro s ⟨t, ht, hst⟩
  rw [← hst]
  exact hfun ht

/-- Domain of the path-expectation recursion at stage `k`. -/
abbrev Dom (P : ControlledMDP E A) (k : ℕ) :=
  {p : History E A × ℝ × ℝ // ValidHistory P k p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}

lemma expectedFrom_meas [TopologicalSpace E] [BorelSpace E] (M : Model E A) (hB : HasBounds M)
    (hU : ContinuousOn M.U (Set.Ici 0)) (τ : Policy M.P) :
    ∀ (n k : ℕ), Measurable (fun p : Dom M.P k =>
      expectedFrom M τ.g k p.1.1 n p.1.2.1 p.1.2.2) := by
  intro n
  induction n with
  | zero =>
    intro k
    simp only [expectedFrom]
    have h1 : Measurable ((Set.Ici (0:ℝ)).restrict M.U) :=
      (hU.restrict).measurable
    have h2 : Measurable (fun p : Dom M.P k => (⟨p.1.2.1, p.2.2.1⟩ : Set.Ici (0:ℝ))) :=
      (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)).subtype_mk
    exact h1.comp h2
  | succ n ih =>
    intro k
    have := M.P.markov_Q
    have hh : Measurable (fun p : Dom M.P k => (⟨p.1.1, p.2.1⟩ : {h // ValidHistory M.P k h})) :=
      (measurable_fst.comp measurable_subtype_coe).subtype_mk
    set φ : Dom M.P k → E × A := fun p => (p.1.1.2, τ.g k p.1.1) with hφdef
    have hφ : Measurable φ :=
      (measurable_snd.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
        ((τ.measurable_g k).comp hh)
    have hcφ : ∀ p : Dom M.P k, 0 ≤ M.c (φ p) := fun p =>
      le_trans hB.2.1.le (hB.2.2.2.1 _ (τ.admissible_g k p.1.1 p.2.1)).1
    let ψ : Dom M.P k × E → Dom M.P (k + 1) := fun q =>
      ⟨((q.1.1.1.1 ++ [φ q.1], q.2), (q.1.1.2.1 + q.1.1.2.2 * M.c (φ q.1), q.1.1.2.2 * M.β)),
        valid_append M.P k q.1.1.1 q.1.2.1 _ (τ.admissible_g k q.1.1.1 q.1.2.1) q.2,
        add_nonneg q.1.2.2.1 (mul_nonneg q.1.2.2.2.le (hcφ q.1)),
        mul_pos q.1.2.2.2 hB.2.2.2.2.1⟩
    have hψ : Measurable ψ := by
      apply Measurable.subtype_mk
      have hp1 : Measurable (fun q : Dom M.P k × E => q.1.1.1.1) :=
        measurable_fst.comp (measurable_fst.comp (measurable_subtype_coe.comp measurable_fst))
      have hyy : Measurable (fun q : Dom M.P k × E => q.1.1.2.1) :=
        measurable_fst.comp (measurable_snd.comp (measurable_subtype_coe.comp measurable_fst))
      have hzz : Measurable (fun q : Dom M.P k × E => q.1.1.2.2) :=
        measurable_snd.comp (measurable_snd.comp (measurable_subtype_coe.comp measurable_fst))
      have hφ' : Measurable (fun q : Dom M.P k × E => φ q.1) := hφ.comp measurable_fst
      refine Measurable.prodMk (Measurable.prodMk ?_ measurable_snd)
        (Measurable.prodMk (hyy.add (hzz.mul (hB.1.comp hφ'))) (hzz.mul measurable_const))
      exact append_meas k _ hp1 (fun q => q.1.2.1.1) _ hφ'
    have hG := ((ih (k + 1)).comp hψ).stronglyMeasurable
    have hI := (StronglyMeasurable.integral_kernel_prod_right' (κ := M.P.Q.comap φ hφ) hG).measurable
    have heq : (fun p : Dom M.P k => expectedFrom M τ.g k p.1.1 (n + 1) p.1.2.1 p.1.2.2) =
        fun p => ∫ x', (fun p : Dom M.P (k + 1) =>
          expectedFrom M τ.g (k + 1) p.1.1 n p.1.2.1 p.1.2.2) (ψ (p, x'))
            ∂((M.P.Q.comap φ hφ) p) := by
      funext p
      rw [expectedFrom]
      rfl
    rw [heq]
    exact hI

/-- The Bellman iterates `TⁿU`. -/
noncomputable def Wv (M : Model E A) : ℕ → ExtendedState E → ℝ
  | 0 => terminal M
  | n + 1 => minimumOperator M (Wv M n)

section Top
variable [TopologicalSpace E] [BorelSpace E]

lemma slice_meas (M : Model E A) (v : ExtendedState E → ℝ) (hv : InClass M v)
    (y z : ℝ) (hyz : (y, z) ∈ yzDomain) : Measurable (fun x' : E => v (x', (y, z))) := by
  have hl := hv.1.comp (g := fun x' : E => ((x', (y, z)) : ExtendedState E))
    (t := Set.univ) (by fun_prop) (fun x' _ => hyz)
  exact (lowerSemicontinuousOn_univ_iff.mp hl).measurable

lemma slice_integrable (M : Model E A) (v : ExtendedState E → ℝ) (hv : InClass M v)
    (y z : ℝ) (hyz : (y, z) ∈ yzDomain) (C : ℝ) (hC : ∀ x', v (x', (y, z)) ≤ C)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    Integrable (fun x' : E => v (x', (y, z))) μ := by
  refine Integrable.of_bound (slice_meas M v hv y z hyz).aestronglyMeasurable
    (max |M.U y| |C|) (Filter.Eventually.of_forall fun x' => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have h1 := hv.2.2.2 (x', (y, z)) hyz
  constructor
  · have := neg_abs_le (M.U y)
    have := le_max_left |M.U y| |C|
    simp only at h1
    linarith
  · have := le_abs_self C
    have := le_max_right |M.U y| |C|
    linarith [hC x']

end Top

lemma step_point (M : Model E A) (hB : HasBounds M) (s : ExtendedState E)
    (hs : s ∈ extendedDomain E) (a : A) (ha : (s.1, a) ∈ M.P.D) :
    (s.2.1 + s.2.2 * M.c (s.1, a), s.2.2 * M.β) ∈ yzDomain := by
  have hc := hB.2.2.2.1 _ ha
  refine ⟨add_nonneg hs.1 (mul_nonneg hs.2.1.le (by linarith [hc.1, hB.2.1])),
    mul_pos hs.2.1 hB.2.2.2.2.1, ?_⟩
  have := hs.2.2; have := hB.2.2.2.2.2; have := hB.2.2.2.2.1
  have := hs.2.1
  nlinarith

lemma U_mono (M : Model E A) (hCC : StrictMonoOn M.U (Set.Ici 0)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : M.U a ≤ M.U b :=
  hCC.monotoneOn ha (le_trans ha hab) hab

section Top2
variable [TopologicalSpace E] [TopologicalSpace A] [BorelSpace E]

/-- Properties of the Bellman iterates. -/
lemma Wv_props (M : Model E A) (hB : HasBounds M) (hCC : HasCC M)
    (hOP : ∀ v, InClass M v → ContinuationIntegrable M v →
      InClass M (minimumOperator M v) ∧ ∃ f : DecisionRule M, IsMinimizer M v f) :
    ∀ n : ℕ, InClass M (Wv M n) ∧ ContinuationIntegrable M (Wv M n) ∧
      ∀ s ∈ extendedDomain E, M.U s.2.1 ≤ Wv M n s ∧
        Wv M n s ≤ M.U (s.2.1 + s.2.2 * n * M.upperCost) := by
  have hup : 0 < M.upperCost := lt_trans hB.2.1 hB.2.2.1
  have hmono := hCC.2.1
  have hQ := M.P.markov_Q
  -- integrability from bounds
  have hint : ∀ (v : ExtendedState E → ℝ) (n : ℕ), InClass M v →
      (∀ s ∈ extendedDomain E, v s ≤ M.U (s.2.1 + s.2.2 * n * M.upperCost)) →
      ContinuationIntegrable M v := by
    intro v n hv hbd s hs a ha
    have hp := step_point M hB s hs a ha
    exact slice_integrable M v hv _ _ hp
      (M.U ((s.2.1 + s.2.2 * M.c (s.1, a)) + (s.2.2 * M.β) * n * M.upperCost))
      (fun x' => hbd (x', _) hp) _
  intro n
  induction n with
  | zero =>
    have hIC : InClass M (Wv M 0) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply ContinuousOn.lowerSemicontinuousOn
        exact hCC.1.comp (by fun_prop) (fun s hs => (hs.1 : (0:ℝ) ≤ s.2.1))
      · intro x
        exact hCC.1.comp (by fun_prop) (fun yz hyz => (hyz.1 : (0:ℝ) ≤ yz.1))
      · intro x a ha b hb hab
        exact hmono.monotoneOn ha.1 hb.1 hab.1
      · intro s _; exact le_rfl
    refine ⟨hIC, hint _ 0 hIC (fun s _ => by simp [Wv, terminal]), fun s _ => ?_⟩
    simp [Wv, terminal]
  | succ n ih =>
    obtain ⟨hIC, hCI, hbd⟩ := ih
    have hIC' : InClass M (Wv M (n + 1)) := (hOP _ hIC hCI).1
    have hbd' : ∀ s ∈ extendedDomain E, M.U s.2.1 ≤ Wv M (n + 1) s ∧
        Wv M (n + 1) s ≤ M.U (s.2.1 + s.2.2 * ((n + 1 : ℕ) : ℝ) * M.upperCost) := by
      intro s hs
      -- bounds on each one-step value
      have hone : ∀ a : M.P.actions s.1, M.U s.2.1 ≤ oneStep M (Wv M n) s a.1 ∧
          oneStep M (Wv M n) s a.1 ≤ M.U (s.2.1 + s.2.2 * ((n + 1 : ℕ) : ℝ) * M.upperCost) := by
        intro a
        have ha : (s.1, a.1) ∈ M.P.D := a.2
        have hp := step_point M hB s hs a.1 ha
        have hc := hB.2.2.2.1 _ ha
        have hI := hCI s hs a.1 ha
        have : IsProbabilityMeasure (M.P.Q (s.1, a.1)) := inferInstance
        constructor
        · have h1 : ∫ _x', M.U (s.2.1 + s.2.2 * M.c (s.1, a.1)) ∂(M.P.Q (s.1, a.1)) ≤
              oneStep M (Wv M n) s a.1 :=
            integral_mono (integrable_const _) hI (fun x' => (hbd (x', _) hp).1)
          simp only [integral_const, probReal_univ, one_smul] at h1
          refine le_trans (U_mono M hmono hs.1 ?_) h1
          have := mul_nonneg hs.2.1.le (le_trans hB.2.1.le hc.1)
          linarith
        · have h1 : oneStep M (Wv M n) s a.1 ≤
              ∫ _x', M.U (s.2.1 + s.2.2 * M.c (s.1, a.1) + s.2.2 * M.β * n * M.upperCost)
                ∂(M.P.Q (s.1, a.1)) :=
            integral_mono hI (integrable_const _) (fun x' => (hbd (x', _) hp).2)
          simp only [integral_const, probReal_univ, one_smul] at h1
          refine le_trans h1 (U_mono M hmono ?_ ?_)
          · have := mul_nonneg hs.2.1.le (le_trans hB.2.1.le hc.1)
            have : 0 ≤ s.2.2 * M.β * n * M.upperCost := by
              have := hs.2.1; have := hB.2.2.2.2.1; positivity
            have := hs.1
            linarith
          · have e1 : s.2.2 * M.c (s.1, a.1) ≤ s.2.2 * M.upperCost :=
              mul_le_mul_of_nonneg_left hc.2 hs.2.1.le
            have e2 : s.2.2 * M.β * (n : ℝ) * M.upperCost ≤ s.2.2 * (n : ℝ) * M.upperCost := by
              have h0 : 0 ≤ s.2.2 * (n : ℝ) * M.upperCost := by
                have := hs.2.1; positivity
              have := hB.2.2.2.2.2
              nlinarith
            push_cast
            nlinarith
      have hne : Nonempty (M.P.actions s.1) := (M.P.nonempty_D s.1).to_subtype
      obtain ⟨a0⟩ := hne
      have hbdd : BddBelow (Set.range fun a : M.P.actions s.1 => oneStep M (Wv M n) s a.1) :=
        ⟨M.U s.2.1, by rintro _ ⟨a, rfl⟩; exact (hone a).1⟩
      constructor
      · show M.U s.2.1 ≤ ⨅ a : M.P.actions s.1, oneStep M (Wv M n) s a.1
        have : Nonempty (M.P.actions s.1) := ⟨a0⟩
        exact le_ciInf (fun a => (hone a).1)
      · show (⨅ a : M.P.actions s.1, oneStep M (Wv M n) s a.1) ≤ _
        exact le_trans (ciInf_le hbdd a0) (hone a0).2
    exact ⟨hIC', hint _ (n + 1) hIC' (fun s hs => (hbd' s hs).2), hbd'⟩

lemma oneStep_lower (M : Model E A) (hB : HasBounds M) (hCC : HasCC M)
    (hP : ∀ n : ℕ, InClass M (Wv M n) ∧ ContinuationIntegrable M (Wv M n) ∧
      ∀ s ∈ extendedDomain E, M.U s.2.1 ≤ Wv M n s ∧
        Wv M n s ≤ M.U (s.2.1 + s.2.2 * n * M.upperCost))
    (n : ℕ) (s : ExtendedState E) (hs : s ∈ extendedDomain E) (a : A) (ha : (s.1, a) ∈ M.P.D) :
    M.U s.2.1 ≤ oneStep M (Wv M n) s a := by
  have hQ := M.P.markov_Q
  have hp := step_point M hB s hs a ha
  have hc := hB.2.2.2.1 _ ha
  have h1 : ∫ _x', M.U (s.2.1 + s.2.2 * M.c (s.1, a)) ∂(M.P.Q (s.1, a)) ≤
      oneStep M (Wv M n) s a :=
    integral_mono (integrable_const _) ((hP n).2.1 s hs a ha) (fun x' => ((hP n).2.2 (x', _) hp).1)
  simp only [integral_const, probReal_univ, one_smul] at h1
  refine le_trans (U_mono M hCC.2.1 hs.1 ?_) h1
  have := mul_nonneg hs.2.1.le (le_trans hB.2.1.le hc.1)
  linarith

lemma lower_bound (M : Model E A) (hB : HasBounds M) (hCC : HasCC M)
    (hP : ∀ n : ℕ, InClass M (Wv M n) ∧ ContinuationIntegrable M (Wv M n) ∧
      ∀ s ∈ extendedDomain E, M.U s.2.1 ≤ Wv M n s ∧
        Wv M n s ≤ M.U (s.2.1 + s.2.2 * n * M.upperCost))
    (τ : Policy M.P) :
    ∀ (n k : ℕ) (h : History E A) (y z : ℝ), ValidHistory M.P k h → 0 ≤ y → 0 < z → z ≤ 1 →
      Wv M n (h.2, (y, z)) ≤ expectedFrom M τ.g k h n y z := by
  have hQ := M.P.markov_Q
  intro n
  induction n with
  | zero =>
    intro k h y z _ _ _ _
    simp [Wv, terminal, expectedFrom]
  | succ n ih =>
    intro k h y z hv hy hz hz1
    rw [expectedFrom]
    have ha := τ.admissible_g k h hv
    have hs : ((h.2, (y, z)) : ExtendedState E) ∈ extendedDomain E := ⟨hy, hz, hz1⟩
    have hp := step_point M hB _ hs _ ha
    simp only at hp
    set a := τ.g k h with ha_def
    set y' := y + z * M.c (h.2, a) with hy'
    set z' := z * M.β with hz'
    -- integrability of the continuation
    have hFm : Measurable (fun x' : E =>
        expectedFrom M τ.g (k + 1) (h.1 ++ [(h.2, a)], x') n y' z') := by
      have hmk : Measurable (fun x' : E => (⟨((h.1 ++ [(h.2, a)], x'), (y', z')),
          valid_append M.P k h hv a ha x', hp.1, hp.2.1⟩ : Dom M.P (k + 1))) :=
        ((measurable_const.prodMk measurable_id).prodMk measurable_const).subtype_mk
      exact (expectedFrom_meas M hB hCC.1 τ n (k + 1)).comp hmk
    obtain ⟨B, hBd⟩ := (isCompact_Icc (a := (0:ℝ))
      (b := y' + z' * n * M.upperCost)).exists_bound_of_continuousOn
      (hCC.1.mono Set.Icc_subset_Ici_self)
    have hFi : Integrable (fun x' : E =>
        expectedFrom M τ.g (k + 1) (h.1 ++ [(h.2, a)], x') n y' z') (M.P.Q (h.2, a)) := by
      refine Integrable.of_bound hFm.aestronglyMeasurable B
        (Filter.Eventually.of_forall fun x' => ?_)
      rw [Real.norm_eq_abs]
      exact expectedFrom_bound M hB τ _ B (fun t ht => by simpa [Real.norm_eq_abs] using hBd t ht)
        n (k + 1) _ y' z' (valid_append M.P k h hv a ha x') hp.1 hp.2.1 hp.2.2 le_rfl
    have hmono : oneStep M (Wv M n) (h.2, (y, z)) a ≤
        ∫ x', expectedFrom M τ.g (k + 1) (h.1 ++ [(h.2, a)], x') n y' z' ∂(M.P.Q (h.2, a)) :=
      integral_mono ((hP n).2.1 _ hs a ha) hFi
        (fun x' => ih (k + 1) _ y' z' (valid_append M.P k h hv a ha x') hp.1 hp.2.1 hp.2.2)
    refine le_trans ?_ hmono
    show (⨅ b : M.P.actions h.2, oneStep M (Wv M n) (h.2, (y, z)) b.1) ≤ _
    refine ciInf_le ⟨M.U y, ?_⟩ (⟨a, ha⟩ : M.P.actions h.2)
    rintro _ ⟨b, rfl⟩
    exact oneStep_lower M hB hCC hP n _ hs b.1 b.2

lemma PI_eq (M : Model E A) (hB : HasBounds M) (fm : ℕ → DecisionRule M)
    (hfm : ∀ m, IsMinimizer M (Wv M m) (fm m)) :
    ∀ (m : ℕ) (π : MarkovPolicy M), (∀ j < m, π j = fm (m - 1 - j)) →
      ∀ s ∈ extendedDomain E, policyIteration M π m s = Wv M m s := by
  intro m
  induction m with
  | zero => intro _ _ _ _; rfl
  | succ m ih =>
    intro π hπ s hs
    have h0 : π 0 = fm m := by rw [hπ 0 (by omega)]; congr 1
    have hsh : ∀ j < m, (fun k => π (k + 1)) j = fm (m - 1 - j) := by
      intro j hj
      show π (j + 1) = _
      rw [hπ (j + 1) (by omega)]; congr 1; omega
    show decisionOperator M (π 0) (policyIteration M (fun k => π (k + 1)) m) s =
      minimumOperator M (Wv M m) s
    rw [← hfm m s hs, h0]
    simp only [decisionOperator, oneStep]
    refine integral_congr_ae (ae_of_all _ fun x' => ?_)
    exact ih _ hsh _ (step_point M hB s hs _ ((fm m).admissible_f s hs))
end Top2

/-- The embedding of an extended-state Markov policy started at `(y,z)` as a history policy. -/
noncomputable def embPolicy (M : Model E A) (hB : HasBounds M) (π : MarkovPolicy M) (y z : ℝ)
    (hy : 0 ≤ y) (hz : 0 < z) (hz1 : z ≤ 1) : Policy M.P where
  g := historyRule M π y z
  measurable_g k := (π k).measurable_f.comp
    ((measurable_snd.comp measurable_subtype_coe).prodMk
      ((measurable_const.add (measurable_const.mul (dHC_meas M hB.1 k))).prodMk measurable_const))
  admissible_g k h hv := (π k).admissible_f
    (h.2, (y + z * discountedHistoryCost M h.1, z * M.β ^ k))
    ⟨add_nonneg hy (mul_nonneg hz.le (dHC_nonneg M hB h.1 hv.2)),
      mul_pos hz (pow_pos hB.2.2.2.2.1 k),
      mul_le_one₀ hz1 (pow_nonneg hB.2.2.2.2.1.le k) (pow_le_one₀ hB.2.2.2.2.1.le hB.2.2.2.2.2.le)⟩

lemma InClass_congr [TopologicalSpace E] (M : Model E A) (v w : ExtendedState E → ℝ)
    (heq : ∀ s ∈ extendedDomain E, v s = w s) (hv : InClass M v) : InClass M w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs c hc
    rw [← heq s hs] at hc
    filter_upwards [hv.1 s hs c hc, self_mem_nhdsWithin] with s' h1 h2
    rwa [← heq s' h2]
  · intro x
    exact (hv.2.1 x).congr (fun yz hyz => (heq (x, yz) hyz).symm)
  · intro x a ha b hb hab
    show w (x, a) ≤ w (x, b)
    rw [← heq (x, a) ha, ← heq (x, b) hb]
    exact hv.2.2.1 x ha hb hab
  · intro s hs
    rw [← heq s hs]; exact hv.2.2.2 s hs

lemma minOp_congr (M : Model E A) (hB : HasBounds M) (v w : ExtendedState E → ℝ)
    (heq : ∀ s ∈ extendedDomain E, v s = w s) (s : ExtendedState E) (hs : s ∈ extendedDomain E) :
    minimumOperator M v s = minimumOperator M w s := by
  simp only [minimumOperator, oneStep]
  refine iInf_congr (fun a => integral_congr_ae (ae_of_all _ fun x' => ?_))
  exact heq _ (step_point M hB s hs a.1 a.2)

end RSMDP2VIAux

open RSMDP2VIAux in
theorem solution {E A : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [StandardBorelSpace A]
    (M : Model E A) (hBounds : HasBounds M) (hCC : HasCC M)
    (N : ℕ) :
    (∀ s ∈ extendedDomain E,
      value M 0 s.1 s.2.1 s.2.2 = M.U s.2.1) ∧
    (∀ n ≤ N, InClass M (fun s => value M n s.1 s.2.1 s.2.2)) ∧
    (∀ n ∈ Finset.Icc 1 N, ∀ s ∈ extendedDomain E,
      value M n s.1 s.2.1 s.2.2 =
        minimumOperator M (fun t => value M (n - 1) t.1 t.2.1 t.2.2) s) := by
  have hOP : ∀ v, InClass M v → ContinuationIntegrable M v →
      InClass M (minimumOperator M v) ∧ ∃ f : DecisionRule M, IsMinimizer M v f :=
    fun v hv hi => operator_preserves_class M hBounds hCC v hv hi
  have hP := Wv_props M hBounds hCC hOP
  choose fm hfm using fun m => (hOP _ (hP m).1 (hP m).2.1).2
  have hVW : ∀ n, ∀ s ∈ extendedDomain E, value M n s.1 s.2.1 s.2.2 = Wv M n s := by
    intro n s hs
    let π : MarkovPolicy M := fun j => fm (n - 1 - j)
    let σ := embPolicy M hBounds π s.2.1 s.2.2 hs.1 hs.2.1 hs.2.2
    have hlow : ∀ τ : Policy M.P, Wv M n s ≤ policyValue M τ n s.1 s.2.1 s.2.2 :=
      fun τ => lower_bound M hBounds hCC hP τ n 0 ([], s.1) s.2.1 s.2.2 ⟨rfl, by simp⟩
        hs.1 hs.2.1 hs.2.2
    have hσ : policyValue M σ n s.1 s.2.1 s.2.2 = Wv M n s := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [policyValue, expectedFrom, Wv, terminal]
      · have := cost_iteration M hBounds hCC n π n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩) s hs
        rw [show policyValue M σ n s.1 s.2.1 s.2.2 = markovValue M π n s.1 s.2.1 s.2.2 from rfl,
          this]
        exact PI_eq M hBounds fm hfm n π (fun j _ => rfl) s hs
    apply le_antisymm
    · rw [← hσ]
      exact ciInf_le ⟨Wv M n s, by rintro _ ⟨τ, rfl⟩; exact hlow τ⟩ σ
    · have : Nonempty (Policy M.P) := ⟨σ⟩
      exact le_ciInf hlow
  refine ⟨fun s hs => by rw [hVW 0 s hs]; rfl,
    fun n _ => InClass_congr M _ _ (fun s hs => (hVW n s hs).symm) (hP n).1, ?_⟩
  intro n hn s hs
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := (Finset.mem_Icc.mp hn).1; omega⟩
  rw [hVW (m + 1) s hs, Nat.add_sub_cancel]
  exact minOp_congr M hBounds _ _ (fun t ht => (hVW m t ht).symm) s hs
