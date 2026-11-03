-- Prove2me | solution 1 for StochasticRewardMatching.Decomposable.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:27:54.347815+00:00
-- url     : https://prove2.me/submissions/3e27a257-b7e1-470b-b8e9-323d12b15574

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Dual

open scoped BigOperators
open MeasureTheory StochasticRewardMatching.Decomposable

noncomputable section

private lemma measurableSet_prop {α : Type*} [MeasurableSpace α] (P : Prop) :
    MeasurableSet {x : α | P} := by
  by_cases h : P
  · convert MeasurableSet.univ; ext x; simp [h]
  · convert MeasurableSet.empty; ext x; simp [h]

private def HasDiscreteMeasurableFibers {n : ℕ} {α : Type*} (R : Seeds n → α) : Prop :=
  (Set.range R).Finite ∧ ∀ a : α, MeasurableSet {Y | R Y = a}

private lemma HasDiscreteMeasurableFibers.const {n : ℕ} {α : Type*} (c : α) :
    HasDiscreteMeasurableFibers (fun _ : Seeds n => c) := by
  refine ⟨(Set.finite_singleton c).subset ?_, fun a => measurableSet_prop (c = a)⟩
  rintro _ ⟨_, rfl⟩
  exact Set.mem_singleton c

private lemma HasDiscreteMeasurableFibers.of_finite {n : ℕ} {α : Type*} [Finite α]
    (R : Seeds n → α) (h : ∀ a : α, MeasurableSet {Y | R Y = a}) :
    HasDiscreteMeasurableFibers R :=
  ⟨Set.toFinite _, h⟩

private lemma HasDiscreteMeasurableFibers.bind {n : ℕ} {α β γ : Type*} [DecidableEq γ]
    {A : Seeds n → α} {B : α → Seeds n → β} (step : α → β → γ)
    (hA : HasDiscreteMeasurableFibers A) (hB : ∀ a, HasDiscreteMeasurableFibers (B a)) :
    HasDiscreteMeasurableFibers (fun Y => step (A Y) (B (A Y) Y)) := by
  classical
  refine ⟨?_, ?_⟩
  · refine (hA.1.biUnion fun a _ => (hB a).1.image (step a)).subset ?_
    rintro _ ⟨Y, rfl⟩
    exact Set.mem_biUnion ⟨Y, rfl⟩ ⟨B (A Y) Y, ⟨Y, rfl⟩, rfl⟩
  · intro c
    have h_eq : {Y | step (A Y) (B (A Y) Y) = c} =
        ⋃ a ∈ hA.1.toFinset, ⋃ b ∈ (hB a).1.toFinset,
          if step a b = c then {Y | A Y = a} ∩ {Y | B a Y = b} else ∅ := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.Finite.mem_toFinset,
        Set.mem_range]
      constructor
      · intro hc
        refine ⟨A Y, ⟨Y, rfl⟩, B (A Y) Y, ⟨Y, rfl⟩, ?_⟩
        rw [if_pos hc]
        exact ⟨rfl, rfl⟩
      · rintro ⟨a, _, b, _, hmem⟩
        split_ifs at hmem with hc
        · rcases hmem with ⟨rfl, rfl⟩
          exact hc
        · exact False.elim hmem
    rw [h_eq]
    refine Finset.measurableSet_biUnion _ fun a _ => ?_
    refine Finset.measurableSet_biUnion _ fun b _ => ?_
    split_ifs
    · exact (hA.2 a).inter ((hB a).2 b)
    · exact MeasurableSet.empty

private lemma continuous_g : Continuous g := by
  unfold g
  exact Real.continuous_exp.comp (continuous_id.sub continuous_const)

private lemma continuous_score {n m : ℕ} (D : Instance n m) (t : Fin m) (i : Fin n) :
    Continuous (fun Y : Seeds n => score D Y t i) := by
  unfold score
  exact continuous_const.mul (continuous_const.sub (continuous_g.comp (continuous_apply i)))

private lemma measurable_score {n m : ℕ} (D : Instance n m) (t : Fin m) (i : Fin n) :
    Measurable (fun Y : Seeds n => score D Y t i) :=
  (continuous_score D t i).measurable

private lemma measurableSet_bestOf_eq {n m : ℕ} (D : Instance n m) (t : Fin m) :
    ∀ (l : List (Fin n)) (x : Option (Fin n)),
      MeasurableSet {Y : Seeds n | bestOf (score D Y t) l = x}
  | [], x => measurableSet_prop (none = x)
  | a :: rest, x => by
    have ih := measurableSet_bestOf_eq D t rest
    have h_eq : {Y : Seeds n | bestOf (score D Y t) (a :: rest) = x} =
        ({Y | bestOf (score D Y t) rest = none} ∩ {Y | some a = x}) ∪
        ⋃ b : Fin n,
          {Y | bestOf (score D Y t) rest = some b} ∩
          (({Y | score D Y t b ≤ score D Y t a} ∩ {Y | some a = x}) ∪
           ({Y | score D Y t a < score D Y t b} ∩ {Y | some b = x})) := by
      ext Y
      simp only [bestOf, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
      cases hrest : bestOf (score D Y t) rest with
      | none =>
        constructor
        · intro hx
          left
          exact ⟨rfl, hx⟩
        · rintro (⟨_, hx⟩ | ⟨b, hb, _⟩)
          · exact hx
          · cases hb
      | some b =>
        dsimp only
        constructor
        · intro hx
          right
          refine ⟨b, rfl, ?_⟩
          split_ifs at hx with hle
          · left; exact ⟨hle, hx⟩
          · right; exact ⟨lt_of_not_ge hle, hx⟩
        · rintro (⟨h1, _⟩ | ⟨b', hb', ⟨hle, hx⟩ | ⟨hlt, hx⟩⟩)
          · cases h1
          · injection hb' with hb'
            subst hb'
            rw [if_pos hle, hx]
          · injection hb' with hb'
            subst hb'
            rw [if_neg (not_le_of_gt hlt), hx]
    rw [h_eq]
    refine MeasurableSet.union ((ih none).inter (measurableSet_prop _))
      (MeasurableSet.iUnion fun b => ?_)
    refine (ih (some b)).inter (MeasurableSet.union ?_ ?_)
    · exact (measurableSet_le (measurable_score D t b) (measurable_score D t a)).inter
        (measurableSet_prop _)
    · exact (measurableSet_lt (measurable_score D t a) (measurable_score D t b)).inter
        (measurableSet_prop _)

private lemma hasDiscreteMeasurableFibers_algorithmChoice {n m : ℕ} (D : Instance n m)
    (S : Finset (Fin n)) (t : Fin m) :
    HasDiscreteMeasurableFibers (fun Y => algorithmChoice D Y S t) :=
  HasDiscreteMeasurableFibers.of_finite _ (measurableSet_bestOf_eq D t _)

private lemma hasDiscreteMeasurableFibers_algorithmRun {n m : ℕ} (D : Instance n m)
    (ω : Outcome D) (initial : Finset (Fin n)) :
    ∀ k : ℕ, HasDiscreteMeasurableFibers (fun Y => algorithmRun D Y ω initial k)
  | 0 => HasDiscreteMeasurableFibers.const (initial, [])
  | k + 1 => by
    have ih := hasDiscreteMeasurableFibers_algorithmRun D ω initial k
    by_cases hk : k < m
    · have h_eq : (fun Y => algorithmRun D Y ω initial (k + 1)) =
          (fun Y =>
            let prev := algorithmRun D Y ω initial k
            let c := algorithmChoice D Y prev.1 ⟨k, hk⟩
            let a : Action n m := (⟨k, hk⟩, c)
            let b := actionBit D ω a
            (if b then afterSuccess prev.1 a else prev.1, prev.2 ++ [(a, b)])) := by
        funext Y
        simp [algorithmRun, hk]
      rw [h_eq]
      exact HasDiscreteMeasurableFibers.bind
        (fun prev c =>
          let a : Action n m := (⟨k, hk⟩, c)
          let b := actionBit D ω a
          (if b then afterSuccess prev.1 a else prev.1, prev.2 ++ [(a, b)]))
        ih (fun prev => hasDiscreteMeasurableFibers_algorithmChoice D prev.1 ⟨k, hk⟩)
    · have h_eq : (fun Y => algorithmRun D Y ω initial (k + 1)) =
          (fun Y => algorithmRun D Y ω initial k) := by
        funext Y
        simp [algorithmRun, hk]
      rw [h_eq]
      exact ih

private lemma hasDiscreteMeasurableFibers_algorithmHistory {n m : ℕ} (D : Instance n m)
    (ω : Outcome D) :
    HasDiscreteMeasurableFibers (fun Y => algorithmHistory D Y ω) := by
  unfold algorithmHistory
  simpa using HasDiscreteMeasurableFibers.bind (fun p _ => p.2)
    (hasDiscreteMeasurableFibers_algorithmRun D ω Finset.univ m)
    (fun _ => HasDiscreteMeasurableFibers.const ())

private instance isProbabilityMeasure_restrict_Icc :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

private instance isProbabilityMeasure_seedLaw (n : ℕ) :
    IsProbabilityMeasure (seedLaw n) := by
  unfold seedLaw
  infer_instance

private lemma ae_seedLaw_mem_Icc (n : ℕ) :
    ∀ᵐ Y ∂seedLaw n, ∀ j : Fin n, Y j ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro j
  have h_mem : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), x ∈ Set.Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  exact (measurePreserving_eval
    (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) j).quasiMeasurePreserving.ae h_mem

private lemma integrable_of_continuous_seedLaw {n : ℕ} {f : Seeds n → ℝ}
    (hf : Continuous f) : Integrable f (seedLaw n) := by
  let K : Set (Seeds n) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine (integrable_const C).mono' hf.measurable.aestronglyMeasurable ?_
  filter_upwards [ae_seedLaw_mem_Icc n] with Y hY
  exact hC Y (fun j _ => hY j)

private lemma HasDiscreteMeasurableFibers.integrable_comp {n : ℕ} {α : Type*} [DecidableEq α]
    {R : Seeds n → α} (hR : HasDiscreteMeasurableFibers R)
    (G : α → Seeds n → ℝ) (hG : ∀ a, Continuous (G a)) :
    Integrable (fun Y => G (R Y) Y) (seedLaw n) := by
  classical
  have h_eq : (fun Y => G (R Y) Y) =
      fun Y => ∑ a ∈ hR.1.toFinset, Set.indicator {Y' | R Y' = a} (G a) Y := by
    funext Y
    have hmem : R Y ∈ hR.1.toFinset := hR.1.mem_toFinset.mpr ⟨Y, rfl⟩
    rw [Finset.sum_eq_single (R Y)]
    · simp [Set.indicator_of_mem]
    · intro a _ ha
      unfold Set.indicator
      rw [if_neg (by simp [Ne.symm ha])]
    · intro hnot
      exact False.elim (hnot hmem)
  rw [h_eq]
  refine integrable_finsetSum _ fun a _ => ?_
  exact (integrable_of_continuous_seedLaw (hG a)).indicator (hR.2 a)

private lemma continuous_list_map_sum {α β : Type*} [TopologicalSpace α]
    {term : β → α → ℝ} (hterm : ∀ z, Continuous (term z)) :
    ∀ l : List β, Continuous (fun x => (l.map (fun z => term z x)).sum)
  | [] => by simp [continuous_const]
  | z :: rest => by
    simp only [List.map_cons, List.sum_cons]
    exact (hterm z).add (continuous_list_map_sum hterm rest)

private lemma integrable_lambdaPath {n m : ℕ} (D : Instance n m) (ω : Outcome D) (t : Fin m) :
    Integrable (fun Y => lambdaPath D ω Y t) (seedLaw n) := by
  unfold lambdaPath
  refine (hasDiscreteMeasurableFibers_algorithmHistory D ω).integrable_comp
    (fun h Y => (h.map fun z =>
      if z.1.1 = t ∧ z.2 = true then
        match z.1.2 with | none => 0 | some i => D.reward i * (1 - g (Y i))
      else 0).sum)
    (fun h => ?_)
  refine continuous_list_map_sum (fun z => ?_) h
  split_ifs
  · cases z.1.2 with
    | none => exact continuous_const
    | some i =>
      exact continuous_const.mul (continuous_const.sub (continuous_g.comp (continuous_apply i)))
  · exact continuous_const

private lemma integrable_thetaPath {n m : ℕ} (D : Instance n m) (ω : Outcome D) (i : Fin n) :
    Integrable (fun Y => thetaPath D ω Y i) (seedLaw n) := by
  unfold thetaPath
  refine (hasDiscreteMeasurableFibers_algorithmHistory D ω).integrable_comp
    (fun h Y => (h.map fun z =>
      if z.1.2 = some i ∧ z.2 = true then D.reward i * g (Y i) else 0).sum)
    (fun h => ?_)
  refine continuous_list_map_sum (fun z => ?_) h
  split_ifs
  · exact continuous_const.mul (continuous_g.comp (continuous_apply i))
  · exact continuous_const

private lemma oneSeedAverage_eq_integral_restrict {n : ℕ} (i₀ : Fin n) (Y : Seeds n)
    (F : Seeds n → ℝ) :
    oneSeedAverage i₀ Y F =
      ∫ y, F (Function.update Y i₀ y) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  unfold oneSeedAverage
  rw [intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private abbrev IsCoord {n : ℕ} (i₀ : Fin n) (j : Fin n) : Prop := j = i₀

private def seedSplitEquiv {n : ℕ} (i₀ : Fin n) :
    ℝ × ({j : Fin n // ¬ IsCoord i₀ j} → ℝ) ≃ᵐ Seeds n :=
  ((MeasurableEquiv.piUnique (fun _ : {j : Fin n // IsCoord i₀ j} => ℝ)).symm.prodCongr
    (MeasurableEquiv.refl ({j : Fin n // ¬ IsCoord i₀ j} → ℝ))).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (IsCoord i₀)).symm

private lemma seedSplitEquiv_apply {n : ℕ} (i₀ : Fin n) (y : ℝ)
    (Y_ne : {j : Fin n // ¬ IsCoord i₀ j} → ℝ) (k : Fin n) :
    seedSplitEquiv i₀ (y, Y_ne) k = if hk : k = i₀ then y else Y_ne ⟨k, hk⟩ := by
  unfold seedSplitEquiv IsCoord
  simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piUnique, Equiv.piUnique]
  split_ifs <;> rfl

private lemma seedSplitEquiv_update {n : ℕ} (i₀ : Fin n) (y : ℝ)
    (Y_ne : {j : Fin n // ¬ IsCoord i₀ j} → ℝ) :
    Function.update (seedSplitEquiv i₀ (0, Y_ne)) i₀ y = seedSplitEquiv i₀ (y, Y_ne) := by
  ext k
  by_cases hk : k = i₀
  · subst hk
    simp [seedSplitEquiv_apply]
  · simp [hk, seedSplitEquiv_apply]

private lemma measurePreserving_seedSplitEquiv {n : ℕ} (i₀ : Fin n) :
    MeasurePreserving (seedSplitEquiv i₀)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
        (Measure.pi fun _ : {j : Fin n // ¬ IsCoord i₀ j} => volume.restrict (Set.Icc (0 : ℝ) 1)))
      (seedLaw n) := by
  unfold seedSplitEquiv seedLaw
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have mp1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ) (IsCoord i₀)
  have mp_uniq : MeasurePreserving
      (MeasurableEquiv.piUnique (fun _ : {j : Fin n // IsCoord i₀ j} => ℝ))
      (@Measure.pi (Subtype (IsCoord i₀)) (fun _ => ℝ) (Subtype.fintype (IsCoord i₀)) _ (fun _ => μ))
      μ := by
    convert measurePreserving_piUnique (fun _ : {j : Fin n // IsCoord i₀ j} => μ)
  have mp2 : MeasurePreserving
      ((MeasurableEquiv.piUnique (fun _ : {j : Fin n // IsCoord i₀ j} => ℝ)).symm.prodCongr
        (MeasurableEquiv.refl ({j : Fin n // ¬ IsCoord i₀ j} → ℝ)))
      (μ.prod (Measure.pi fun _ : {j : Fin n // ¬ IsCoord i₀ j} => μ))
      ((@Measure.pi (Subtype (IsCoord i₀)) (fun _ => ℝ) (Subtype.fintype (IsCoord i₀)) _ (fun _ => μ)).prod
        (Measure.pi fun _ : {j : Fin n // ¬ IsCoord i₀ j} => μ)) :=
    mp_uniq.symm.prod (MeasurePreserving.id _)
  exact mp1.symm.comp mp2

private lemma seedAverage_eq_integral_oneSeedAverage {n : ℕ} (i₀ : Fin n)
    {F : Seeds n → ℝ} (hF : Integrable F (seedLaw n)) :
    ∫ Z, F Z ∂seedLaw n =
      ∫ Y_ne, oneSeedAverage i₀ (seedSplitEquiv i₀ (0, Y_ne)) F
        ∂(Measure.pi fun _ : {j : Fin n // ¬ IsCoord i₀ j} => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let μ_ne : Measure ({j : Fin n // ¬ IsCoord i₀ j} → ℝ) := Measure.pi (fun _ => μ)
  have hψ := measurePreserving_seedSplitEquiv i₀
  have hFψ_int : Integrable (F ∘ seedSplitEquiv i₀) (μ.prod μ_ne) :=
    (hψ.integrable_comp_emb (seedSplitEquiv i₀).measurableEmbedding).mpr hF
  rw [← hψ.integral_comp (seedSplitEquiv i₀).measurableEmbedding F]
  change ∫ p, (F ∘ seedSplitEquiv i₀) p ∂(μ.prod μ_ne) = _
  rw [MeasureTheory.integral_prod_symm (F ∘ seedSplitEquiv i₀) hFψ_int]
  refine integral_congr_ae (ae_of_all _ fun Y_ne => ?_)
  dsimp only
  rw [oneSeedAverage_eq_integral_restrict]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only [Function.comp_apply]
  rw [seedSplitEquiv_update]

theorem solution {n m : ℕ} (D : Instance n m) (e : Edge D)
    (hconditional : ∀ (ω : Outcome D) (Y : Seeds n),
      (∀ j, j ≠ e.val.1 → Y j ∈ Set.Icc (0 : ℝ) 1) →
      (1 - Real.exp (-1)) * D.probability e.val * D.reward e.val.1 ≤
        oneSeedAverage e.val.1 Y (fun Z => resample D e ω
          (fun w => lambdaPath D w Z e.val.2 + thetaPath D w Z e.val.1 * indicator w e))) :
    ∀ ω : Outcome D,
      (1 - Real.exp (-1)) * D.probability e.val * D.reward e.val.1 ≤
        resample D e ω (fun w => lambda D w e.val.2 + theta D w e.val.1 * indicator w e) := by
  intro ω
  let i₀ := e.val.1
  let t₀ := e.val.2
  let p := D.probability e.val
  let c := (1 - Real.exp (-1)) * p * D.reward i₀
  let ω₀ := Function.update ω e false
  let ω₁ := Function.update ω e true
  let F : Seeds n → ℝ := fun Z => resample D e ω
    (fun w => lambdaPath D w Z t₀ + thetaPath D w Z i₀ * indicator w e)
  have h_int_l0 : Integrable (fun Z => lambdaPath D ω₀ Z t₀) (seedLaw n) :=
    integrable_lambdaPath D ω₀ t₀
  have h_int_t0 : Integrable (fun Z => thetaPath D ω₀ Z i₀ * indicator ω₀ e) (seedLaw n) :=
    (integrable_thetaPath D ω₀ i₀).mul_const _
  have h_int_l1 : Integrable (fun Z => lambdaPath D ω₁ Z t₀) (seedLaw n) :=
    integrable_lambdaPath D ω₁ t₀
  have h_int_t1 : Integrable (fun Z => thetaPath D ω₁ Z i₀ * indicator ω₁ e) (seedLaw n) :=
    (integrable_thetaPath D ω₁ i₀).mul_const _
  have h_int_0 : Integrable
      (fun Z => (1 - p) * (lambdaPath D ω₀ Z t₀ + thetaPath D ω₀ Z i₀ * indicator ω₀ e))
      (seedLaw n) :=
    (h_int_l0.add h_int_t0).const_mul (1 - p)
  have h_int_1 : Integrable
      (fun Z => p * (lambdaPath D ω₁ Z t₀ + thetaPath D ω₁ Z i₀ * indicator ω₁ e))
      (seedLaw n) :=
    (h_int_l1.add h_int_t1).const_mul p
  have hF_int : Integrable F (seedLaw n) := h_int_0.add h_int_1
  have hrhs : resample D e ω (fun w => lambda D w t₀ + theta D w i₀ * indicator w e) =
      ∫ Z, F Z ∂seedLaw n := by
    unfold resample lambda theta seedAverage
    dsimp only [F, resample]
    have h0 : ∫ Z, ((1 - p) * (lambdaPath D ω₀ Z t₀ + thetaPath D ω₀ Z i₀ * indicator ω₀ e) +
        p * (lambdaPath D ω₁ Z t₀ + thetaPath D ω₁ Z i₀ * indicator ω₁ e)) ∂seedLaw n =
        (1 - p) * ((∫ Z, lambdaPath D ω₀ Z t₀ ∂seedLaw n) +
          (∫ Z, thetaPath D ω₀ Z i₀ ∂seedLaw n) * indicator ω₀ e) +
        p * ((∫ Z, lambdaPath D ω₁ Z t₀ ∂seedLaw n) +
          (∫ Z, thetaPath D ω₁ Z i₀ ∂seedLaw n) * indicator ω₁ e) := by
      rw [integral_add h_int_0 h_int_1, integral_const_mul, integral_const_mul,
        integral_add h_int_l0 h_int_t0, integral_add h_int_l1 h_int_t1,
        integral_mul_const, integral_mul_const]
    exact h0.symm
  rw [hrhs, seedAverage_eq_integral_oneSeedAverage i₀ hF_int]
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let μ_ne : Measure ({j : Fin n // ¬ IsCoord i₀ j} → ℝ) := Measure.pi (fun _ => μ)
  have h_ae_ne : ∀ᵐ Y_ne ∂μ_ne, ∀ j : {j : Fin n // ¬ IsCoord i₀ j}, Y_ne j ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro j
    have h_mem : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
    exact (measurePreserving_eval (fun _ : {j : Fin n // ¬ IsCoord i₀ j} => μ) j).quasiMeasurePreserving.ae h_mem
  have h_ae_bound : ∀ᵐ Y_ne ∂μ_ne,
      c ≤ oneSeedAverage i₀ (seedSplitEquiv i₀ (0, Y_ne)) F := by
    filter_upwards [h_ae_ne] with Y_ne hY_ne
    refine hconditional ω (seedSplitEquiv i₀ (0, Y_ne)) ?_
    intro j hj
    rw [seedSplitEquiv_apply, dif_neg hj]
    exact hY_ne ⟨j, hj⟩
  have h_int_rhs : Integrable
      (fun Y_ne => oneSeedAverage i₀ (seedSplitEquiv i₀ (0, Y_ne)) F) μ_ne := by
    have hψ := measurePreserving_seedSplitEquiv i₀
    have hFψ_int : Integrable (F ∘ seedSplitEquiv i₀) (μ.prod μ_ne) :=
      (hψ.integrable_comp_emb (seedSplitEquiv i₀).measurableEmbedding).mpr hF_int
    have h_eq_fn : (fun Y_ne => oneSeedAverage i₀ (seedSplitEquiv i₀ (0, Y_ne)) F) =
        (fun Y_ne => ∫ y, (F ∘ seedSplitEquiv i₀) (y, Y_ne) ∂μ) := by
      funext Y_ne
      rw [oneSeedAverage_eq_integral_restrict]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp only [Function.comp_apply]
      rw [seedSplitEquiv_update]
    rw [h_eq_fn]
    exact hFψ_int.integral_prod_right
  have hle := integral_mono_ae (integrable_const c) h_int_rhs h_ae_bound
  simpa [c, i₀, p] using hle

end
