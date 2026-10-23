-- Prove2me | solution 1 for RiskFunctionals.ValueOfInfo.optimality_submartingale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:42:52.663492+00:00
-- url     : https://prove2.me/submissions/aaf6a2f7-0356-4f4d-9421-872fa49723d5

import Mathlib
import Definitions.Def_RiskFunctionals_ValueOfInfo_Compounding
import Definitions.Def_RiskFunctionals_ValueOfInfo_IsTreeProcess
import Definitions.Def_RiskFunctionals_ValueOfInfo_DecisionProblems

open MeasureTheory ProbabilityTheory RiskFunctionals.ValueOfInfo

theorem g81v_nest {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {N : Fin (T + 1) → Type*}
    [∀ t, MeasurableSpace (N t)] [∀ t, MeasurableSingletonClass (N t)]
    (ν : (t : Fin (T + 1)) → Ω → N t) (htree : IsTreeProcess ν) {i j : Fin (T + 1)}
    (hij : i ≤ j) (v : N i) (w : N j) :
    ν j ⁻¹' {w} ⊆ ν i ⁻¹' {v} ∨ Disjoint (ν j ⁻¹' {w}) (ν i ⁻¹' {v}) := by
  have hle : MeasurableSpace.comap (ν i) inferInstance ≤ MeasurableSpace.comap (ν j) inferInstance := by
    rw [htree j]; exact le_iSup₂_of_le i hij le_rfl
  obtain ⟨S, -, hS⟩ := hle _ ⟨{v}, measurableSet_singleton v, rfl⟩
  by_cases hw : w ∈ S
  · left; intro ω hω
    rw [← hS]; simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢; rw [hω]; exact hw
  · right; rw [← hS]
    rw [Set.disjoint_left]; intro ω hω h2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω h2; rw [hω] at h2; exact hw h2

/-- Encoding a finite type into `ℝ` with a measurable left inverse. -/
theorem g81v_encode (α : Type*) [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Nonempty α] : ∃ (e : α → ℝ) (d : ℝ → α), Measurable e ∧ Measurable d ∧ ∀ a, d (e a) = a := by
  classical
  obtain ⟨n, ⟨f⟩⟩ := Finite.exists_equiv_fin α
  let e : α → ℝ := fun a => ((f a : ℕ) : ℝ)
  have he : Function.Injective e := by
    intro a b h; apply f.injective; apply Fin.ext; simp only [e] at h; exact_mod_cast h
  let a0 : α := Classical.arbitrary α
  let d : ℝ → α := fun y => if h : ∃ a, e a = y then h.choose else a0
  have hd : ∀ a, d (e a) = a := by
    intro a
    have h : ∃ b, e b = e a := ⟨a, rfl⟩
    simp only [d, dif_pos h]
    exact he h.choose_spec
  refine ⟨e, d, measurable_of_finite e, ?_, hd⟩
  apply measurable_to_countable'
  intro a
  have hfin : (Set.range e).Finite := Set.finite_range e
  have : d ⁻¹' {a} = {e a} ∪ {y | y ∉ Set.range e ∧ a = a0} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_range]
    constructor
    · intro h
      by_cases hy : ∃ b, e b = y
      · obtain ⟨b, rfl⟩ := hy
        left; rw [hd] at h; rw [h]
      · right; refine ⟨hy, ?_⟩; simp only [d, dif_neg hy] at h; exact h.symm
    · rintro (rfl | ⟨hy, rfl⟩)
      · exact hd a
      · simp only [d, dif_neg hy]
  rw [this]
  refine (measurableSet_singleton _).union ?_
  by_cases ha : a = a0
  · simp only [ha, and_true]; exact hfin.measurableSet.compl
  · simp [ha]

theorem g81v_mix {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]
    (V : Ω → α) (hV : Measurable V) (A : Set Ω) (hA : MeasurableSet A) (hPA : P A ≠ 0)
    (hnest : ∀ w, V ⁻¹' {w} ⊆ A ∨ Disjoint (V ⁻¹' {w}) A)
    (Y : Ω → ℝ) (hY : Measurable Y) (𝒜 : Measure ℝ → ℝ) (𝒟 : Set (Measure ℝ))
    (hD : ∀ w, P (V ⁻¹' {w}) ≠ 0 → (P[|V ⁻¹' {w}]).map Y ∈ 𝒟) :
    ∃ (G : Measure ℝ) (K : Kernel ℝ ℝ), IsProbabilityMeasure G ∧ IsMarkovKernel K ∧
      (∀ᵐ y ∂G, K y ∈ 𝒟) ∧ K ∘ₘ G = (P[|A]).map Y ∧ Integrable (fun y => 𝒜 (K y)) G ∧
      ∫ y, 𝒜 (K y) ∂G = ∑ w, (P[|A]).real (V ⁻¹' {w}) * 𝒜 ((P[|V ⁻¹' {w}]).map Y) := by
  classical
  obtain ⟨e, d, he, hd, hde⟩ := g81v_encode α
  have : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hPA
  let κ : α → Measure ℝ := fun w => if P (V ⁻¹' {w}) ≠ 0 then (P[|V ⁻¹' {w}]).map Y else Measure.dirac 0
  have hκ : ∀ w, IsProbabilityMeasure (κ w) := by
    intro w
    by_cases h : P (V ⁻¹' {w}) ≠ 0
    · simp only [κ, if_pos h]
      have := cond_isProbabilityMeasure (μ := P) h
      exact Measure.isProbabilityMeasure_map hY.aemeasurable
    · simp only [κ, if_neg h]; infer_instance
  let κ' : Kernel α ℝ := Kernel.ofFunOfCountable κ
  have : IsMarkovKernel κ' := ⟨fun w => hκ w⟩
  let K : Kernel ℝ ℝ := κ'.comap d hd
  have hK : ∀ w, K (e w) = κ w := fun w => by
    simp only [K, κ', Kernel.comap_apply, hde]; rfl
  let G : Measure ℝ := (P[|A]).map (e ∘ V)
  have heV : Measurable (e ∘ V) := he.comp hV
  have hKmeas : Measurable (fun y => 𝒜 (K y)) := by
    have : (fun y => 𝒜 (K y)) = (fun w => 𝒜 (κ w)) ∘ d := by
      ext y; simp only [K, κ', Kernel.comap_apply, Function.comp_apply]; rfl
    rw [this]; exact (measurable_of_finite _).comp hd
  -- weights vanish on null atoms
  have hnull : ∀ w, P (V ⁻¹' {w}) = 0 → (P[|A]) (V ⁻¹' {w}) = 0 :=
    fun w h => cond_absolutelyContinuous h
  refine ⟨G, K, Measure.isProbabilityMeasure_map heV.aemeasurable, inferInstance, ?_, ?_, ?_, ?_⟩
  · -- a.e. membership
    rw [ae_iff]
    apply measure_mono_null (t := (e ∘ V) ⁻¹' {y | ∃ w, P (V ⁻¹' {w}) ≠ 0 ∧ e w = y}ᶜ |> fun s => e '' {w | P (V ⁻¹' {w}) = 0} ∪ (Set.range e)ᶜ)
    · intro y hy
      simp only [Set.mem_ofPred_eq] at hy
      by_cases hr : y ∈ Set.range e
      · obtain ⟨w, rfl⟩ := hr
        left; refine ⟨w, ?_, rfl⟩
        by_contra h0
        have h0' : P (V ⁻¹' {w}) ≠ 0 := h0
        apply hy; rw [hK]; simp only [κ]; rw [if_pos h0']; exact hD w h0'
      · right; exact hr
    · rw [Measure.map_apply heV]
      · apply measure_mono_null (t := ⋃ w ∈ {w | P (V ⁻¹' {w}) = 0}, V ⁻¹' {w})
        · intro ω hω
          simp only [Set.mem_preimage, Function.comp_apply, Set.mem_union, Set.mem_image,
            Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists] at hω
          rcases hω with ⟨w, hw, hew⟩ | hω
          · have : w = V ω := by
              have := congrArg d hew; rwa [hde, hde] at this
            simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
            exact ⟨w, hw, this.symm⟩
          · exact absurd rfl (hω (V ω))
        · rw [measure_biUnion_null_iff (Set.toFinite _).countable]
          intro w hw; exact hnull w hw
      · exact ((Set.toFinite _).image e).measurableSet.union (Set.finite_range e).measurableSet.compl
  · -- the mixture identity
    ext B hB
    rw [Measure.bind_apply hB K.measurable.aemeasurable, lintegral_map (Kernel.measurable_coe K hB) heV,
      Measure.map_apply hY hB]
    simp only [Function.comp_apply, hK]
    rw [← lintegral_map (f := fun w => κ w B) (measurable_of_finite _) hV, lintegral_fintype]
    -- partition of `Y ⁻¹' B`
    have hpart : (P[|A]) (Y ⁻¹' B) = ∑ w, (P[|A]) (V ⁻¹' {w} ∩ Y ⁻¹' B) := by
      have := sum_measure_preimage_singleton (μ := (P[|A]).restrict (Y ⁻¹' B)) Finset.univ
        (f := V) (fun w _ => hV (measurableSet_singleton w))
      simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at this
      rw [← this]
      congr 1; ext w
      rw [Measure.restrict_apply (hV (measurableSet_singleton w))]
    rw [hpart]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Measure.map_apply hV (measurableSet_singleton w)]
    by_cases h0 : P (V ⁻¹' {w}) = 0
    · rw [hnull w h0, mul_zero]
      exact (measure_mono_null Set.inter_subset_left (hnull w h0)).symm
    · simp only [κ, if_pos h0]
      rw [Measure.map_apply hY hB, cond_apply (hV (measurableSet_singleton w)),
        cond_apply hA, cond_apply hA]
      rcases hnest w with hs | hdis
      · rw [Set.inter_eq_right.2 hs, ← Set.inter_assoc, Set.inter_eq_right.2 hs]
        have hfin : P (V ⁻¹' {w}) ≠ ⊤ := measure_ne_top _ _
        calc (P (V ⁻¹' {w}))⁻¹ * P (V ⁻¹' {w} ∩ Y ⁻¹' B) * ((P A)⁻¹ * P (V ⁻¹' {w}))
            = (P A)⁻¹ * P (V ⁻¹' {w} ∩ Y ⁻¹' B) * ((P (V ⁻¹' {w}))⁻¹ * P (V ⁻¹' {w})) := by ring
          _ = _ := by rw [ENNReal.inv_mul_cancel h0 hfin, mul_one]
      · have h1 : A ∩ V ⁻¹' {w} = ∅ := Set.disjoint_iff_inter_eq_empty.1 hdis.symm
        have h2 : A ∩ (V ⁻¹' {w} ∩ Y ⁻¹' B) = ∅ := by
          rw [← Set.inter_assoc, h1, Set.empty_inter]
        rw [h1, h2]; simp
  · -- integrability: bounded measurable function
    refine Integrable.of_bound hKmeas.aestronglyMeasurable (∑ w, ‖𝒜 (κ w)‖) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have : 𝒜 (K y) = 𝒜 (κ (d y)) := by simp only [K, κ', Kernel.comap_apply]; rfl
    rw [this]
    exact Finset.single_le_sum (f := fun w => ‖𝒜 (κ w)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  · -- the integral as a finite sum
    rw [integral_map heV.aemeasurable hKmeas.aestronglyMeasurable]
    simp only [Function.comp_apply, hK]
    rw [← integral_map (f := fun w => 𝒜 (κ w)) hV.aemeasurable
      (measurable_of_finite _).aestronglyMeasurable, integral_fintype (Integrable.of_finite)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [smul_eq_mul, Measure.real, Measure.map_apply hV (measurableSet_singleton w), Measure.real]
    by_cases h0 : P (V ⁻¹' {w}) = 0
    · rw [hnull w h0]; simp
    · simp only [κ, if_pos h0]

theorem g81v_int2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] (U : Ω → α) (V : Ω → β)
    (hU : Measurable U) (hV : Measurable V) (g : α → β → ℝ) :
    ∫ ω, g (U ω) (V ω) ∂P = ∑ v, ∑ w, P.real (U ⁻¹' {v} ∩ V ⁻¹' {w}) * g v w := by
  have hUV : Measurable (fun ω => (U ω, V ω)) := hU.prodMk hV
  have h := integral_map (μ := P) hUV.aemeasurable (f := fun p : α × β => g p.1 p.2)
    (measurable_of_finite _).aestronglyMeasurable
  simp only at h
  rw [← h, integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
  rw [smul_eq_mul, Measure.real, Measure.map_apply hUV (measurableSet_singleton _), Measure.real]
  congr 3
  ext ω; simp

theorem g81v_profit_meas {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {N : Fin (T + 1) → Type*}
    [∀ t, MeasurableSpace (N t)] [∀ t, MeasurableSingletonClass (N t)] [∀ t, Finite (N t)]
    (ν : (t : Fin (T + 1)) → Ω → N t) (hν : ∀ t, Measurable (ν t))
    {Ξ : Type*} [MeasurableSpace Ξ] (f : (i : Fin T) → N i.succ → Ξ)
    {𝕏 : Type*} [MeasurableSpace 𝕏] (H : (Fin T → 𝕏) → (Fin T → Ξ) → ℝ)
    (hH : Measurable (Function.uncurry H)) (x : Ω → Fin T → 𝕏) (hx : Measurable x) :
    Measurable (profit ν f H x) := by
  have h2 : Measurable (fun ω => (fun i : Fin T => f i (ν i.succ ω))) :=
    measurable_pi_lambda _ fun i => (measurable_of_finite (f i)).comp (hν i.succ)
  exact hH.comp (hx.prodMk h2)

theorem g81v_cond_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) (hPA : P A ≠ 0) (t : Set Ω) :
    P.real A * (P[|A]).real t = P.real (A ∩ t) := by
  rw [Measure.real, Measure.real, Measure.real, cond_apply hA, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact ENNReal.toReal_ne_zero.2 ⟨hPA, measure_ne_top _ _⟩

section Node

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℕ} {N : Fin (T + 1) → Type*} [∀ t, MeasurableSpace (N t)]
    [∀ t, MeasurableSingletonClass (N t)] [∀ t, Fintype (N t)]
    (ν : (t : Fin (T + 1)) → Ω → N t) (hν : ∀ t, Measurable (ν t)) (htree : IsTreeProcess ν)
    {Ξ : Type*} [MeasurableSpace Ξ] (f : (i : Fin T) → N i.succ → Ξ)
    {𝕏 : Type*} [MeasurableSpace 𝕏] (𝒳 : Set (Fin T → 𝕏))
    (H : (Fin T → 𝕏) → (Fin T → Ξ) → ℝ) (hH : Measurable (Function.uncurry H))
    (𝒜 : Measure ℝ → ℝ) (𝒟 : Set (Measure ℝ))
    (Feas : (Ω → Fin T → 𝕏) → Prop) (hFeas : ∀ x, Feas x → Measurable x)
    (h𝒟 : ∀ t (v : N t) (x : Ω → Fin T → 𝕏), P (ν t ⁻¹' {v}) ≠ 0 → Feas x →
      (∀ ω, x ω ∈ 𝒳) → (P[|ν t ⁻¹' {v}]).map (profit ν f H x) ∈ 𝒟)
    (C : (t : Fin (T + 1)) → N t → ℝ)
    (hC : ∀ t (v : N t), P (ν t ⁻¹' {v}) ≠ 0 →
      IsGreatest {a | ∃ x, Feas x ∧ (∀ ω, x ω ∈ 𝒳) ∧
        a = condAcceptability 𝒜 P ν t v (profit ν f H x)} (C t v))

include hν htree hH hFeas h𝒟 hC in
theorem g81v_node_le (hconv : CompoundConvex 𝒟 𝒜) {i j : Fin (T + 1)} (hij : i ≤ j) (v : N i) :
    P.real (ν i ⁻¹' {v}) * C i v ≤
      ∑ w, P.real (ν i ⁻¹' {v} ∩ ν j ⁻¹' {w}) * C j w := by
  classical
  have hAm : MeasurableSet (ν i ⁻¹' {v}) := hν i (measurableSet_singleton v)
  by_cases hA : P (ν i ⁻¹' {v}) = 0
  · have h0 : P.real (ν i ⁻¹' {v}) = 0 := by simp [Measure.real, hA]
    rw [h0, zero_mul]
    apply le_of_eq; symm
    refine Finset.sum_eq_zero fun w _ => ?_
    have : P (ν i ⁻¹' {v} ∩ ν j ⁻¹' {w}) = 0 := measure_mono_null Set.inter_subset_left hA
    simp [Measure.real, this]
  obtain ⟨⟨x, hxF, hx𝒳, hCx⟩, -⟩ := hC i v hA
  obtain ⟨ω0, -⟩ := nonempty_of_measure_ne_zero hA
  have : Nonempty (N j) := ⟨ν j ω0⟩
  have hY := g81v_profit_meas ν hν f H hH x (hFeas x hxF)
  obtain ⟨G, K, hG, hK, hae, hcomp, hint, hsum⟩ := g81v_mix P (ν j) (hν j) _ hAm hA
    (fun w => g81v_nest ν htree hij v w) _ hY 𝒜 𝒟 (fun w hw => h𝒟 j w x hw hxF hx𝒳)
  have key := hconv G hG K hK hae (by rw [hcomp]; exact h𝒟 i v x hA hxF hx𝒳) hint
  rw [hcomp, hsum] at key
  have hCv : C i v = 𝒜 ((P[|ν i ⁻¹' {v}]).map (profit ν f H x)) := hCx
  have step : ∑ w, (P[|ν i ⁻¹' {v}]).real (ν j ⁻¹' {w}) * 𝒜 ((P[|ν j ⁻¹' {w}]).map (profit ν f H x))
      ≤ ∑ w, (P[|ν i ⁻¹' {v}]).real (ν j ⁻¹' {w}) * C j w := by
    refine Finset.sum_le_sum fun w _ => ?_
    by_cases hw : P (ν j ⁻¹' {w}) = 0
    · have : (P[|ν i ⁻¹' {v}]) (ν j ⁻¹' {w}) = 0 := cond_absolutelyContinuous hw
      simp [Measure.real, this]
    · exact mul_le_mul_of_nonneg_left ((hC j w hw).2 ⟨x, hxF, hx𝒳, rfl⟩) measureReal_nonneg
  calc P.real (ν i ⁻¹' {v}) * C i v
      ≤ P.real (ν i ⁻¹' {v}) * ∑ w, (P[|ν i ⁻¹' {v}]).real (ν j ⁻¹' {w}) * C j w := by
        rw [hCv]; exact mul_le_mul_of_nonneg_left (key.trans step) measureReal_nonneg
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← mul_assoc, g81v_cond_real P hAm hA]

include hν htree hH hFeas h𝒟 hC in
theorem g81v_node_ge (hlin : CompoundLinear 𝒟 𝒜) {i j : Fin (T + 1)} (hij : i ≤ j) (v : N i)
    (hpaste : ∀ xs : N j → Ω → Fin T → 𝕏, (∀ w, Feas (xs w)) → Feas (fun ω => xs (ν j ω) ω)) :
    ∑ w, P.real (ν i ⁻¹' {v} ∩ ν j ⁻¹' {w}) * C j w ≤ P.real (ν i ⁻¹' {v}) * C i v := by
  classical
  have hAm : MeasurableSet (ν i ⁻¹' {v}) := hν i (measurableSet_singleton v)
  by_cases hA : P (ν i ⁻¹' {v}) = 0
  · have h0 : P.real (ν i ⁻¹' {v}) = 0 := by simp [Measure.real, hA]
    rw [h0, zero_mul]
    apply le_of_eq
    refine Finset.sum_eq_zero fun w _ => ?_
    have : P (ν i ⁻¹' {v} ∩ ν j ⁻¹' {w}) = 0 := measure_mono_null Set.inter_subset_left hA
    simp [Measure.real, this]
  obtain ⟨⟨x0, hx0F, hx0𝒳, -⟩, -⟩ := hC i v hA
  obtain ⟨ω0, -⟩ := nonempty_of_measure_ne_zero hA
  have : Nonempty (N j) := ⟨ν j ω0⟩
  let xs : N j → Ω → Fin T → 𝕏 := fun w =>
    if hw : P (ν j ⁻¹' {w}) ≠ 0 then (hC j w hw).1.choose else x0
  have hxsF : ∀ w, Feas (xs w) ∧ (∀ ω, xs w ω ∈ 𝒳) := by
    intro w
    by_cases hw : P (ν j ⁻¹' {w}) ≠ 0
    · simp only [xs, dif_pos hw]
      exact ⟨(hC j w hw).1.choose_spec.1, (hC j w hw).1.choose_spec.2.1⟩
    · simp only [xs, dif_neg hw]; exact ⟨hx0F, hx0𝒳⟩
  have hxsC : ∀ w, P (ν j ⁻¹' {w}) ≠ 0 →
      C j w = 𝒜 ((P[|ν j ⁻¹' {w}]).map (profit ν f H (xs w))) := by
    intro w hw
    have := (hC j w hw).1.choose_spec.2.2
    simp only [xs, dif_pos hw]; exact this
  let xt : Ω → Fin T → 𝕏 := fun ω => xs (ν j ω) ω
  have hxtF : Feas xt := hpaste xs fun w => (hxsF w).1
  have hxt𝒳 : ∀ ω, xt ω ∈ 𝒳 := fun ω => (hxsF _).2 ω
  have hY := g81v_profit_meas ν hν f H hH xt (hFeas xt hxtF)
  obtain ⟨G, K, hG, hK, hae, hcomp, hint, hsum⟩ := g81v_mix P (ν j) (hν j) _ hAm hA
    (fun w => g81v_nest ν htree hij v w) _ hY 𝒜 𝒟 (fun w hw => h𝒟 j w xt hw hxtF hxt𝒳)
  have key := hlin G hG K hK hae (by rw [hcomp]; exact h𝒟 i v xt hA hxtF hxt𝒳) hint
  rw [hcomp, hsum] at key
  have hle : 𝒜 ((P[|ν i ⁻¹' {v}]).map (profit ν f H xt)) ≤ C i v :=
    (hC i v hA).2 ⟨xt, hxtF, hxt𝒳, rfl⟩
  have step : ∑ w, (P[|ν i ⁻¹' {v}]).real (ν j ⁻¹' {w}) * C j w =
      ∑ w, (P[|ν i ⁻¹' {v}]).real (ν j ⁻¹' {w}) * 𝒜 ((P[|ν j ⁻¹' {w}]).map (profit ν f H xt)) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : P (ν j ⁻¹' {w}) = 0
    · have : (P[|ν i ⁻¹' {v}]) (ν j ⁻¹' {w}) = 0 := cond_absolutelyContinuous hw
      simp [Measure.real, this]
    · congr 1
      rw [hxsC w hw]
      congr 1
      apply Measure.map_congr
      filter_upwards [ae_cond_mem (hν j (measurableSet_singleton w))] with ω hω
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
      simp only [profit, xt, hω]
  calc ∑ w, P.real (ν i ⁻¹' {v} ∩ ν j ⁻¹' {w}) * C j w
      = P.real (ν i ⁻¹' {v}) * ∑ w, (P[|ν i ⁻¹' {v}]).real (ν j ⁻¹' {w}) * C j w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← mul_assoc, g81v_cond_real P hAm hA]
    _ ≤ _ := by
        rw [step, ← key]
        exact mul_le_mul_of_nonneg_left hle measureReal_nonneg

end Node

open Classical in
theorem g81v_setint {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] (U : Ω → α) (V : Ω → β)
    (hU : Measurable U) (hV : Measurable V) (S : Set α) (g : α → β → ℝ) :
    ∫ ω in U ⁻¹' S, g (U ω) (V ω) ∂P =
      ∑ v, if v ∈ S then ∑ w, P.real (U ⁻¹' {v} ∩ V ⁻¹' {w}) * g v w else 0 := by
  classical
  have hS : MeasurableSet (U ⁻¹' S) := hU (Set.toFinite S).measurableSet
  rw [← integral_indicator hS]
  have : (U ⁻¹' S).indicator (fun ω => g (U ω) (V ω)) =
      fun ω => (fun v w => if v ∈ S then g v w else 0) (U ω) (V ω) := by
    ext ω; simp [Set.indicator]
  rw [this, g81v_int2 P U V hU hV (fun v w => if v ∈ S then g v w else 0)]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs with hv
  · rfl
  · simp

theorem g81v_part {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] (V : Ω → β)
    (hV : Measurable V) (A : Set Ω) :
    ∑ w, P.real (A ∩ V ⁻¹' {w}) = P.real A := by
  have := sum_measureReal_preimage_singleton (μ := P.restrict A) Finset.univ (f := V)
    (fun w _ => hV (measurableSet_singleton w))
  simp only [Finset.coe_univ, Set.preimage_univ, measureReal_restrict_apply_univ] at this
  rw [← this]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [measureReal_restrict_apply (hV (measurableSet_singleton w)), Set.inter_comm]


/-- Generic (sub)martingale assembly from node inequalities. -/
theorem g81v_assemble {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℕ} {N : Fin (T + 1) → Type*} [∀ t, MeasurableSpace (N t)]
    [∀ t, MeasurableSingletonClass (N t)] [∀ t, Fintype (N t)]
    (ν : (t : Fin (T + 1)) → Ω → N t) (hν : ∀ t, Measurable (ν t))
    (ℱ : Filtration (Fin (T + 1)) ‹MeasurableSpace Ω›)
    (hℱ : ∀ t, ℱ t = MeasurableSpace.comap (ν t) inferInstance)
    (C : (t : Fin (T + 1)) → N t → ℝ)
    (hnode : ∀ i j : Fin (T + 1), i ≤ j → ∀ v : N i,
      P.real (ν i ⁻¹' {v}) * C i v ≤ ∑ w, P.real (ν i ⁻¹' {v} ∩ ν j ⁻¹' {w}) * C j w) :
    Submartingale (fun t ω => C t (ν t ω)) ℱ P := by
  classical
  refine submartingale_of_setIntegral_le ?_ ?_ ?_
  · intro t
    rw [hℱ t]
    exact ((measurable_of_finite (C t)).comp (comap_measurable (ν t))).stronglyMeasurable
  · intro t
    refine Integrable.of_bound ((measurable_of_finite (C t)).comp (hν t)).aestronglyMeasurable
      (∑ v, ‖C t v‖) (Filter.Eventually.of_forall fun ω => ?_)
    exact Finset.single_le_sum (f := fun v => ‖C t v‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  · intro i j hij s hs
    rw [hℱ i] at hs
    obtain ⟨S, -, rfl⟩ := hs
    have e1 := g81v_setint P (ν i) (ν j) (hν i) (hν j) S (fun v _ => C i v)
    have e2 := g81v_setint P (ν i) (ν j) (hν i) (hν j) S (fun _ w => C j w)
    rw [e1, e2]
    refine Finset.sum_le_sum fun v _ => ?_
    split_ifs with hv
    · rw [← Finset.sum_mul, g81v_part P (ν j) (hν j)]
      exact hnode i j hij v
    · exact le_rfl

theorem g81v_comap_le {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {N : Fin (T + 1) → Type*}
    [∀ t, MeasurableSpace (N t)] (ν : (t : Fin (T + 1)) → Ω → N t) (htree : IsTreeProcess ν)
    {i j : Fin (T + 1)} (hij : i ≤ j) :
    MeasurableSpace.comap (ν i) inferInstance ≤ MeasurableSpace.comap (ν j) inferInstance := by
  rw [htree j]; exact le_iSup₂_of_le i hij le_rfl

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℕ} {N : Fin (T + 1) → Type*} [∀ t, MeasurableSpace (N t)]
    [∀ t, MeasurableSingletonClass (N t)] [∀ t, Finite (N t)] [Unique (N 0)]
    (ν : (t : Fin (T + 1)) → Ω → N t) (hν : ∀ t, Measurable (ν t)) (htree : IsTreeProcess ν)
    (ℱ : Filtration (Fin (T + 1)) ‹MeasurableSpace Ω›)
    (hℱ : ∀ t, ℱ t = MeasurableSpace.comap (ν t) inferInstance)
    {Ξ : Type*} [MeasurableSpace Ξ] (f : (i : Fin T) → N i.succ → Ξ)
    {𝕏 : Type*} [MeasurableSpace 𝕏] [MeasurableSingletonClass 𝕏] (𝒳 : Set (Fin T → 𝕏))
    (H : (Fin T → 𝕏) → (Fin T → Ξ) → ℝ) (hH : Measurable (Function.uncurry H))
    (𝒜 : Measure ℝ → ℝ) (𝒟 : Set (Measure ℝ))
    (h𝒟 : ∀ t (v : N t) (x : Ω → Fin T → 𝕏), P (ν t ⁻¹' {v}) ≠ 0 → IsNonanticipative ν x →
      (∀ ω, x ω ∈ 𝒳) → (P[|ν t ⁻¹' {v}]).map (profit ν f H x) ∈ 𝒟)
    (A : (t : Fin (T + 1)) → N t → ℝ)
    (hA : ∀ t (v : N t), P (ν t ⁻¹' {v}) ≠ 0 →
      IsGreatest (optimalityValues 𝒜 P ν f H 𝒳 t v) (A t v))
    (hconv : CompoundConvex 𝒟 𝒜) :
    Submartingale (fun t ω => A t (ν t ω)) ℱ P := by
  classical
  letI : ∀ t, Fintype (N t) := fun t => Fintype.ofFinite _
  have hFeas : ∀ x : Ω → Fin T → 𝕏, IsNonanticipative ν x → Measurable x := fun x hx =>
    measurable_pi_iff.2 fun i => (hx i).mono (hν _).comap_le le_rfl
  exact g81v_assemble P ν hν ℱ hℱ A fun i j hij v =>
    g81v_node_le P ν hν htree f 𝒳 H hH 𝒜 𝒟 (IsNonanticipative ν) hFeas h𝒟 A hA hconv hij v
