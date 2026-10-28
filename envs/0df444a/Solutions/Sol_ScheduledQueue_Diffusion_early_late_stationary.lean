-- Prove2me | solution 1 for ScheduledQueue.Diffusion.early_late_stationary
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:28:20.907403+00:00
-- url     : https://prove2.me/submissions/1200cc5b-039f-42d5-b9c1-dc4fa6fa1d72

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

open Set Filter Topology MeasureTheory ProbabilityTheory

/-- the fractional-part rotation preserves the uniform law on `[0,1]` -/
lemma SQS_fract_pres (q : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    (volume.restrict (Icc (0 : ℝ) 1)) {u | Int.fract (u - q) ∈ A} =
      (volume.restrict (Icc (0 : ℝ) 1)) A := by
  have hS : MeasurableSet {u : ℝ | Int.fract (u - q) ∈ A} :=
    (measurable_id.sub_const q).fract hA
  have hIcc : (volume.restrict (Icc (0 : ℝ) 1)) = volume.restrict (Ioc (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  have hIoo : (volume.restrict (Ioc (0 : ℝ) 1)) = volume.restrict (Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  set ψ : ℝ → UnitAddCircle := fun x => (x : UnitAddCircle) with hψ
  set g : UnitAddCircle → ENNReal := fun z => A.indicator 1 ((AddCircle.equivIco 1 0 z : ℝ))
    with hg
  have hgψ : ∀ x : ℝ, g (ψ x) = A.indicator 1 (Int.fract x) := by
    intro x
    simp only [hg, hψ]
    rw [AddCircle.coe_equivIco_mk_apply]
    simp
  rw [hIcc, ← lintegral_indicator_one hS, ← lintegral_indicator_one hA]
  have e1 : ∫⁻ u, {u : ℝ | Int.fract (u - q) ∈ A}.indicator 1 u ∂(volume.restrict (Ioc (0 : ℝ) 1)) =
      ∫⁻ u in Ioc (0 : ℝ) (0 + 1), (fun z => g (z + ψ (-q))) (ψ u) := by
    simp only [zero_add]
    refine lintegral_congr (fun u => ?_)
    have : ψ u + ψ (-q) = ψ (u - q) := by
      simp only [hψ]; rw [sub_eq_add_neg, AddCircle.coe_add]
    simp only [this, hgψ]
    simp [Set.indicator]
  have e2 : ∫⁻ u in Ioc (0 : ℝ) (0 + 1), (fun z => g (z + ψ (-q))) (ψ u) =
      ∫⁻ u in Ioc (0 : ℝ) (0 + 1), g (ψ u) := by
    rw [UnitAddCircle.lintegral_preimage 0 (fun z => g (z + ψ (-q))),
      UnitAddCircle.lintegral_preimage 0 g]
    exact lintegral_add_right_eq_self g (ψ (-q))
  rw [e1, e2, zero_add, hIoo]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
  rw [hgψ]
  have : Int.fract u = u := Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩
  rw [this]

lemma SQS_encard_meas {α : Type*} [MeasurableSpace α] (A : ℤ → Set α)
    (hA : ∀ j, MeasurableSet (A j)) : Measurable (fun p => {j : ℤ | p ∈ A j}.encard) := by
  set Ψ : α → ENNReal := fun p => ∑' j : ℤ, {j : ℤ | p ∈ A j}.indicator 1 j with hΨ
  have hΨm : Measurable Ψ := by
    refine Measurable.ennreal_tsum (fun j => ?_)
    have : (fun p : α => {j : ℤ | p ∈ A j}.indicator (1 : ℤ → ENNReal) j) = (A j).indicator 1 := by
      funext p; simp [Set.indicator]
    rw [this]
    exact measurable_const.indicator (hA j)
  have hΨeq : ∀ p, Ψ p = (({j : ℤ | p ∈ A j}.encard : ℕ∞) : ENNReal) := by
    intro p
    simp only [hΨ]
    rw [← tsum_subtype]; simp only [Pi.one_apply]; rw [ENNReal.tsum_set_one]
  apply measurable_to_countable'
  intro n
  have : (fun p => {j : ℤ | p ∈ A j}.encard) ⁻¹' {n} = Ψ ⁻¹' {(n : ENNReal)} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, hΨeq, ENat.toENNReal_inj]
  rw [this]
  exact hΨm (measurableSet_singleton _)

/-- the time-shift map on the input `(u, x)` -/
noncomputable def SQS_T (q : ℝ) (p : ℝ × (ℤ → ℝ)) : ℝ × (ℤ → ℝ) :=
  (Int.fract (p.1 - q), fun m => p.2 (m - ⌊p.1 - q⌋))

lemma SQS_T_meas (q : ℝ) : Measurable (SQS_T q) := by
  have h1 : Measurable (fun p : ℝ × (ℤ → ℝ) => Int.fract (p.1 - q)) :=
    (measurable_fst.sub_const q).fract
  have h2 : Measurable (fun p : ℝ × (ℤ → ℝ) => fun m : ℤ => p.2 (m - ⌊p.1 - q⌋)) := by
    refine measurable_pi_lambda _ (fun m => ?_)
    have hF : Measurable (fun r : (ℤ → ℝ) × ℤ => r.1 (m - r.2)) :=
      measurable_from_prod_countable_left (fun K => measurable_pi_apply (m - K))
    have hG : Measurable (fun p : ℝ × (ℤ → ℝ) => (p.2, ⌊p.1 - q⌋)) :=
      measurable_snd.prodMk (measurable_fst.sub_const q).floor
    exact hF.comp hG
  exact h1.prodMk h2

lemma SQS_T_law (q : ℝ) (μ : Measure (ℤ → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ K : ℤ, μ.map (fun (x : ℤ → ℝ) (m : ℤ) => x (m - K)) = μ) :
    ((volume.restrict (Icc (0 : ℝ) 1)).prod μ).map (SQS_T q) =
      (volume.restrict (Icc (0 : ℝ) 1)).prod μ := by
  set lam := volume.restrict (Icc (0 : ℝ) 1) with hlam
  haveI : IsFiniteMeasure lam := by
    rw [hlam]; exact isFiniteMeasure_restrict.mpr (by simp)
  symm
  refine Measure.prod_eq (fun A B hA hB => ?_)
  rw [Measure.map_apply (SQS_T_meas q) (hA.prod hB),
    Measure.prod_apply ((SQS_T_meas q) (hA.prod hB))]
  have hsh : ∀ K : ℤ, Measurable (fun (x : ℤ → ℝ) (m : ℤ) => x (m - K)) :=
    fun K => measurable_pi_lambda _ (fun m => measurable_pi_apply (m - K))
  have hS : MeasurableSet {u : ℝ | Int.fract (u - q) ∈ A} :=
    (measurable_id.sub_const q).fract hA
  have hpt : ∀ u : ℝ, μ (Prod.mk u ⁻¹' (SQS_T q ⁻¹' A ×ˢ B)) =
      {u : ℝ | Int.fract (u - q) ∈ A}.indicator (fun _ => μ B) u := by
    intro u
    by_cases hu : Int.fract (u - q) ∈ A
    · have e : Prod.mk u ⁻¹' (SQS_T q ⁻¹' A ×ˢ B) =
          (fun (x : ℤ → ℝ) (m : ℤ) => x (m - ⌊u - q⌋)) ⁻¹' B := by
        ext x; simp [SQS_T, hu]
      rw [e, ← Measure.map_apply (hsh _) hB, hμ]
      simp [Set.indicator, hu]
    · have e : Prod.mk u ⁻¹' (SQS_T q ⁻¹' A ×ˢ B) = ∅ := by
        ext x; simp [SQS_T, hu]
      rw [e]
      simp [Set.indicator, hu]
  simp_rw [hpt]
  rw [lintegral_indicator_const hS, SQS_fract_pres q A hA, mul_comm]

/-- the early-count process as a function of the input -/
noncomputable def SQS_GE (h : ℝ) (p : ℝ × (ℤ → ℝ)) : ℝ → ℕ∞ := fun s =>
  {m : ℤ | p ∈ {p : ℝ × (ℤ → ℝ) | s < m * h + p.1 * h ∧ m * h + p.1 * h + p.2 m ≤ s}}.encard

/-- the late-count process as a function of the input -/
noncomputable def SQS_GL (h : ℝ) (p : ℝ × (ℤ → ℝ)) : ℝ → ℕ∞ := fun s =>
  {m : ℤ | p ∈ {p : ℝ × (ℤ → ℝ) | m * h + p.1 * h < s ∧ s ≤ m * h + p.1 * h + p.2 m}}.encard

lemma SQS_GE_meas (h : ℝ) : Measurable (SQS_GE h) := by
  refine measurable_pi_lambda _ (fun s => ?_)
  apply SQS_encard_meas
  intro m
  have hf1 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h) := by fun_prop
  have hf2 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h + p.2 m) := by fun_prop
  exact (measurableSet_lt measurable_const hf1).inter (measurableSet_le hf2 measurable_const)

lemma SQS_GL_meas (h : ℝ) : Measurable (SQS_GL h) := by
  refine measurable_pi_lambda _ (fun s => ?_)
  apply SQS_encard_meas
  intro m
  have hf1 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h) := by fun_prop
  have hf2 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h + p.2 m) := by fun_prop
  exact (measurableSet_lt hf1 measurable_const).inter (measurableSet_le measurable_const hf2)

/-- time shift of the input -/
lemma SQS_shift_set (h : ℝ) (hh : 0 < h) (t s u : ℝ) (x : ℤ → ℝ)
    (P : ℝ → ℝ → Prop) :
    {i : ℤ | P (i * h + u * h - t) (i * h + u * h + x i - t)} =
      (fun m : ℤ => m - ⌊u - t / h⌋) '' {m : ℤ | P (m * h + (SQS_T (t / h) (u, x)).1 * h)
        (m * h + (SQS_T (t / h) (u, x)).1 * h + (SQS_T (t / h) (u, x)).2 m)} := by
  have key : ∀ m : ℤ, ((m - ⌊u - t / h⌋ : ℤ) : ℝ) * h + u * h - t =
      m * h + Int.fract (u - t / h) * h := by
    intro m
    have e1 : Int.fract (u - t / h) = (u - t / h) - ⌊u - t / h⌋ := (Int.self_sub_floor _).symm
    rw [e1]; push_cast; field_simp; ring
  ext i
  simp only [mem_setOf_eq, mem_image, SQS_T]
  constructor
  · intro hi
    refine ⟨i + ⌊u - t / h⌋, ?_, by ring⟩
    have e : i + ⌊u - t / h⌋ - ⌊u - t / h⌋ = i := by ring
    have k := key (i + ⌊u - t / h⌋)
    rw [e] at k
    rw [e, ← k]
    have : (i : ℝ) * h + u * h + x i - t = (i : ℝ) * h + u * h - t + x i := by ring
    rw [← this]; exact hi
  · rintro ⟨m, hm, rfl⟩
    have k := key m
    rw [k]
    have : ((m - ⌊u - t / h⌋ : ℤ) : ℝ) * h + u * h + x (m - ⌊u - t / h⌋) - t =
        m * h + Int.fract (u - t / h) * h + x (m - ⌊u - t / h⌋) := by
      rw [show ((m - ⌊u - t / h⌋ : ℤ) : ℝ) * h + u * h + x (m - ⌊u - t / h⌋) - t =
        ((m - ⌊u - t / h⌋ : ℤ) : ℝ) * h + u * h - t + x (m - ⌊u - t / h⌋) by ring, k]
    rw [this]; exact hm

open ScheduledQueue.Diffusion in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ t : ℝ,
      IdentDistrib (fun ω (s : ℝ) => early h ξ U (t + s) ω) (fun ω (s : ℝ) => early h ξ U s ω) P P ∧
      IdentDistrib (fun ω (s : ℝ) => late h ξ U (t + s) ω) (fun ω (s : ℝ) => late h ξ U s ω) P P := by
  intro t
  set pair : Ω → ℝ × (ℤ → ℝ) := fun ω => (U ω, fun j => ξ j ω) with hpair
  have hUm : AEMeasurable U P := hin.uniform.aemeasurable
  have hξm : Measurable (fun ω j => ξ j ω) := measurable_pi_lambda _ hin.measurable
  have hpm : AEMeasurable pair P := hUm.prodMk hξm.aemeasurable
  set μ := P.map (fun ω j => ξ j ω) with hμdef
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hξm.aemeasurable
  have hmap : P.map pair = (volume.restrict (Icc (0 : ℝ) 1)).prod μ := by
    rw [hpair, (indepFun_iff_map_prod_eq_prod_map_map hUm hξm.aemeasurable).mp hin.indep_shift,
      hin.uniform.map_eq]
  have hμ : ∀ K : ℤ, μ.map (fun (x : ℤ → ℝ) (m : ℤ) => x (m - K)) = μ := by
    intro K
    have hsh : Measurable (fun (x : ℤ → ℝ) (m : ℤ) => x (m - K)) :=
      measurable_pi_lambda _ (fun m => measurable_pi_apply (m - K))
    rw [hμdef, Measure.map_map hsh hξm]
    have hinj : Function.Injective (fun j : ℤ => j - K) := sub_left_injective
    have hiind : iIndepFun (fun j => ξ (j - K)) P := hin.indep.precomp hinj
    have e : (fun (x : ℤ → ℝ) (m : ℤ) => x (m - K)) ∘ (fun ω j => ξ j ω) =
        fun ω j => ξ (j - K) ω := rfl
    rw [e, hiind.map_fun_eq_infinitePi_map (fun j => hin.measurable _),
      hin.indep.map_fun_eq_infinitePi_map hin.measurable]
    congr 1
    funext j
    rw [(hin.identDistrib (j - K)).map_eq, (hin.identDistrib j).map_eq]
  have hT : IdentDistrib (SQS_T (t / h) ∘ pair) pair P P := by
    refine ⟨(SQS_T_meas _).comp_aemeasurable hpm, hpm, ?_⟩
    rw [← AEMeasurable.map_map_of_aemeasurable (SQS_T_meas _).aemeasurable hpm, hmap,
      SQS_T_law _ μ hμ]
  constructor
  · have e1 : (fun ω (s : ℝ) => early h ξ U (t + s) ω) = SQS_GE h ∘ SQS_T (t / h) ∘ pair := by
      funext ω s
      simp only [Function.comp_apply, SQS_GE, early, hpair]
      have := SQS_shift_set h hh t s (U ω) (fun j => ξ j ω)
        (fun a b => s < a ∧ b ≤ s)
      have e : {i : ℤ | t + s < (i : ℝ) * h + U ω * h ∧ (i : ℝ) * h + U ω * h + ξ i ω ≤ t + s} =
          {i : ℤ | s < (i : ℝ) * h + U ω * h - t ∧ (i : ℝ) * h + U ω * h + ξ i ω - t ≤ s} := by
        ext i; simp only [mem_setOf_eq]
        constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
      rw [e, this, (sub_left_injective).encard_image]
      rfl
    have e0 : (fun ω (s : ℝ) => early h ξ U s ω) = SQS_GE h ∘ pair := by
      funext ω s; rfl
    rw [e1, e0]
    exact hT.comp (SQS_GE_meas h)
  · have e1 : (fun ω (s : ℝ) => late h ξ U (t + s) ω) = SQS_GL h ∘ SQS_T (t / h) ∘ pair := by
      funext ω s
      simp only [Function.comp_apply, SQS_GL, late, hpair]
      have := SQS_shift_set h hh t s (U ω) (fun j => ξ j ω)
        (fun a b => a < s ∧ s ≤ b)
      have e : {i : ℤ | (i : ℝ) * h + U ω * h < t + s ∧ t + s ≤ (i : ℝ) * h + U ω * h + ξ i ω} =
          {i : ℤ | (i : ℝ) * h + U ω * h - t < s ∧ s ≤ (i : ℝ) * h + U ω * h + ξ i ω - t} := by
        ext i; simp only [mem_setOf_eq]
        constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
      rw [e, this, (sub_left_injective).encard_image]
      rfl
    have e0 : (fun ω (s : ℝ) => late h ξ U s ω) = SQS_GL h ∘ pair := by
      funext ω s; rfl
    rw [e1, e0]
    exact hT.comp (SQS_GL_meas h)
