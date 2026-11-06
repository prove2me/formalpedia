-- Prove2me | solution 1 for UncertainPricing.Superrep.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:54:15.29476+00:00
-- url     : https://prove2.me/submissions/aef85439-2afe-433f-83e8-ad97879bc7a4

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting
import Definitions.Def_UncertainPricing_Superrep_Compact

open MeasureTheory Filter Topology BoundedContinuousFunction
open UncertainPricing.Superrep

namespace L54

instance (T : ℝ) : SecondCountableTopology (Ω T) := by
  have : SecondCountableTopology C(Set.Icc (0:ℝ) T, ℝ) := inferInstance
  exact inferInstanceAs (SecondCountableTopology {ω : C(Set.Icc (0 : ℝ) T, ℝ) //
    ∀ h : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T, ω ⟨0, h⟩ = 0})

theorem dist_le_iff {T : ℝ} (S : Set (Set.Icc (0:ℝ) T)) (hS : Dense S) (z y : Ω T) {q : ℝ}
    (hq : 0 ≤ q) : dist z y ≤ q ↔ ∀ t ∈ S, |z.1 t - y.1 t| ≤ q := by
  change dist z.1 y.1 ≤ q ↔ _
  rw [ContinuousMap.dist_le hq]
  constructor
  · intro h t _; simpa [Real.dist_eq] using h t
  · intro h t
    have hc : IsClosed {t : Set.Icc (0:ℝ) T | |z.1 t - y.1 t| ≤ q} :=
      isClosed_le ((z.1.continuous.sub y.1.continuous).abs) continuous_const
    have : S ⊆ {t | |z.1 t - y.1 t| ≤ q} := fun t ht => h t ht
    have := hc.closure_subset_iff.mpr this (hS t)
    simpa [Real.dist_eq] using this


theorem measurable_closedBall_pre {α : Type*} [MeasurableSpace α] {T : ℝ} (g : α → Ω T)
    (hg : ∀ t, Measurable fun x => (g x).1 t) (y : Ω T) (q : ℝ) :
    MeasurableSet {x | dist (g x) y ≤ q} := by
  by_cases hq : 0 ≤ q
  · obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0:ℝ) T)
    have : {x | dist (g x) y ≤ q} = ⋂ t ∈ S, {x | |(g x).1 t - y.1 t| ≤ q} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact dist_le_iff S hSd (g x) y hq
    rw [this]
    refine MeasurableSet.biInter hSc fun t _ => ?_
    exact measurableSet_le (((hg t).sub measurable_const).abs) measurable_const
  · have : {x | dist (g x) y ≤ q} = ∅ := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (not_le.mp hq) dist_nonneg
    rw [this]; exact MeasurableSet.empty

theorem measurable_ball_pre {α : Type*} [MeasurableSpace α] {T : ℝ} (g : α → Ω T)
    (hg : ∀ t, Measurable fun x => (g x).1 t) (y : Ω T) (r : ℝ) :
    MeasurableSet (g ⁻¹' Metric.ball y r) := by
  have : g ⁻¹' Metric.ball y r = ⋃ n : ℕ, {x | dist (g x) y ≤ r - 1 / ((n:ℝ) + 1)} := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  rw [this]
  exact MeasurableSet.iUnion fun n => measurable_closedBall_pre g hg y _

theorem measurable_of_coords {α : Type*} [MeasurableSpace α] {T : ℝ} (g : α → Ω T)
    (hg : ∀ t, Measurable fun x => (g x).1 t) : Measurable g := by
  refine measurable_of_isOpen fun s hs => ?_
  let S : Set (Set (Ω T)) := {b | ∃ y r, b = Metric.ball y r ∧ b ⊆ s}
  obtain ⟨T', hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable S (by
    rintro b ⟨y, r, rfl, -⟩; exact Metric.isOpen_ball)
  have hsU : s = ⋃₀ S := by
    apply le_antisymm
    · intro x hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x hx
      exact ⟨Metric.ball x ε, ⟨x, ε, rfl, hball⟩, Metric.mem_ball_self hε⟩
    · exact Set.sUnion_subset fun b ⟨_, _, _, hb⟩ => hb
  rw [hsU, ← hTU, Set.preimage_sUnion]
  refine MeasurableSet.biUnion hTc fun b hb => ?_
  obtain ⟨y, r, rfl, -⟩ := hTS hb
  exact measurable_ball_pre g hg y r

theorem measurable_pathOf {T : ℝ} {Q : Measure (Ωt T)} {X : Set.Icc (0 : ℝ) T → Ωt T → ℝ}
    (hX : IsContModif Q X) : Measurable (pathOf hX) :=
  measurable_of_coords _ fun t => hX.meas t


example : CompactSpace EReal := inferInstance
example : T2Space EReal := inferInstance
example : ContinuousNeg EReal := inferInstance

theorem ext_eq_of {T : ℝ} (f : Ω T →ᵇ ℝ) (h : Ωt T → ℝ) (hc : Continuous h)
    (heq : ∀ ω, h (stoneCechUnit ω) = f ω) : ⇑(ext f) = h := by
  refine Continuous.ext_on denseRange_stoneCechUnit (ext f).continuous hc ?_
  rintro _ ⟨ω, rfl⟩
  rw [heq ω]
  change ((stoneCechExtend (continuous_toIcc f) (stoneCechUnit ω) : Set.Icc (-‖f‖) ‖f‖) : ℝ) = _
  rw [stoneCechExtend_stoneCechUnit]
  rfl

/-- The `EReal`-valued Stone–Čech extension of `B_t`. -/
noncomputable def Ee {T : ℝ} (t : Set.Icc (0 : ℝ) T) : Ωt T → EReal :=
  stoneCechExtend (g := fun ω : Ω T => ((B t ω : ℝ) : EReal))
    (continuous_coe_real_ereal.comp (continuous_B t))

theorem continuous_Ee {T : ℝ} (t : Set.Icc (0 : ℝ) T) : Continuous (Ee t) :=
  continuous_stoneCechExtend _

theorem Ee_unit {T : ℝ} (t : Set.Icc (0 : ℝ) T) (ω : Ω T) :
    Ee t (stoneCechUnit ω) = (B t ω : EReal) := by
  unfold Ee; rw [stoneCechExtend_stoneCechUnit]

/-- `y ↦ min (max y 0) n`, as a real number. -/
noncomputable def clampE (n : ℕ) (y : EReal) : ℝ := (min (max y 0) (n : EReal)).toReal

theorem continuous_clampE (n : ℕ) : Continuous (clampE n) := by
  rw [continuous_iff_continuousAt]
  intro y
  have h1 : Continuous fun y : EReal => min (max y 0) (n : EReal) :=
    (continuous_id.max continuous_const).min continuous_const
  have hne1 : min (max y 0) (n : EReal) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.natCast_ne_top n) (min_le_right _ _)
  have hne2 : min (max y 0) (n : EReal) ≠ ⊥ := by
    apply ne_bot_of_le_ne_bot (b := 0) EReal.zero_ne_bot
    exact le_min (le_max_right _ _) (by exact_mod_cast Nat.zero_le n)
  exact (EReal.tendsto_toReal hne1 hne2).comp h1.continuousAt

theorem clampE_coe (n : ℕ) (a : ℝ) : clampE n (a : EReal) = min (max a 0) (n : ℝ) := by
  unfold clampE
  have : min (max (a : EReal) 0) (n : EReal) = ((min (max a 0) (n : ℝ) : ℝ) : EReal) := by
    have hm : Monotone (fun x : ℝ => (x : EReal)) := EReal.coe_strictMono.monotone
    rw [hm.map_min, hm.map_max]; simp
  rw [this, EReal.toReal_coe]

theorem ext_truncPos {T : ℝ} (t : Set.Icc (0 : ℝ) T) (n : ℕ) :
    ⇑(ext (truncPos (Bc t) n)) = fun x => clampE n (Ee t x) := by
  apply ext_eq_of _ _ ((continuous_clampE n).comp (continuous_Ee t))
  intro ω
  show clampE n (Ee t (stoneCechUnit ω)) = _
  rw [Ee_unit, clampE_coe]
  rfl

theorem ext_truncPos_neg {T : ℝ} (t : Set.Icc (0 : ℝ) T) (n : ℕ) :
    ⇑(ext (truncPos (-Bc t) n)) = fun x => clampE n (-Ee t x) := by
  apply ext_eq_of _ _ ((continuous_clampE n).comp (continuous_Ee t).neg)
  intro ω
  show clampE n (-Ee t (stoneCechUnit ω)) = _
  rw [Ee_unit, ← EReal.coe_neg, clampE_coe]
  rfl


theorem PP_top : (⨆ n : ℕ, ENNReal.ofReal (clampE n ⊤)) = ⊤ := by
  have : ∀ n : ℕ, clampE n ⊤ = n := by
    intro n; unfold clampE
    rw [max_eq_left le_top, min_eq_right le_top]; rfl
  simp_rw [this, ENNReal.ofReal_natCast]
  exact ENNReal.iSup_natCast

theorem PP_bot : (⨆ n : ℕ, ENNReal.ofReal (clampE n ⊥)) = 0 := by
  have : ∀ n : ℕ, clampE n ⊥ = 0 := by
    intro n; unfold clampE
    rw [max_eq_right bot_le, min_eq_left (by exact_mod_cast Nat.zero_le n)]; rfl
  simp [this]

theorem PP_coe (a : ℝ) : (⨆ n : ℕ, ENNReal.ofReal (clampE n (a : EReal))) = ENNReal.ofReal a := by
  simp_rw [clampE_coe]
  apply le_antisymm
  · refine iSup_le fun n => ENNReal.ofReal_le_ofReal_iff'.mpr ?_
    rcases le_total a 0 with h | h
    · right; rw [max_eq_right h]; exact min_le_left _ _
    · left; rw [max_eq_left h]; exact min_le_left _ _
  · obtain ⟨n, hn⟩ := exists_nat_ge (max a 0)
    refine le_iSup_of_le n ?_
    rw [min_eq_left hn]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

theorem extNN_Bc {T : ℝ} (t : Set.Icc (0 : ℝ) T) (x : Ωt T) :
    extNN (Bc t) x = ⨆ n : ℕ, ENNReal.ofReal (clampE n (Ee t x)) := by
  unfold extNN; simp_rw [ext_truncPos]

theorem extNN_negBc {T : ℝ} (t : Set.Icc (0 : ℝ) T) (x : Ωt T) :
    extNN (-Bc t) x = ⨆ n : ℕ, ENNReal.ofReal (clampE n (-Ee t x)) := by
  unfold extNN; simp_rw [ext_truncPos_neg]

theorem Btilde_eq {T : ℝ} (t : Set.Icc (0 : ℝ) T) (x : Ωt T) : Btilde t x = Ee t x := by
  unfold Btilde extE
  rw [extNN_Bc, extNN_negBc]
  induction Ee t x using EReal.rec with
  | bot => rw [PP_bot, EReal.neg_bot, PP_top]; simp
  | top => rw [PP_top]; simp
  | coe a =>
    rw [← EReal.coe_neg, PP_coe, PP_coe]
    simp only [ENNReal.ofReal_ne_top, if_false, ENNReal.toReal_ofReal']
    congr 1
    rcases le_total a 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring


theorem ext_unit {T : ℝ} (f : Ω T →ᵇ ℝ) (ω : Ω T) : ext f (stoneCechUnit ω) = f ω := by
  change ((stoneCechExtend (continuous_toIcc f) (stoneCechUnit ω) : Set.Icc (-‖f‖) ‖f‖) : ℝ) = _
  rw [stoneCechExtend_stoneCechUnit]
  rfl

theorem ext_cyl {T : ℝ} (f : Ω T →ᵇ ℝ) {d : ℕ} (ts : Fin d → Set.Icc (0 : ℝ) T)
    (F : (Fin d → ℝ) → ℝ) (hFc : Continuous F) (hf : ∀ ω, f ω = F (fun i => B (ts i) ω))
    (x : Ωt T) (hx : ∀ i, Ee (ts i) x ≠ ⊤ ∧ Ee (ts i) x ≠ ⊥) :
    ext f x = F (fun i => (Ee (ts i) x).toReal) := by
  let U : Set (Ωt T) := {x | ∀ i, Ee (ts i) x ≠ ⊤ ∧ Ee (ts i) x ≠ ⊥}
  have hsub : Set.range (stoneCechUnit : Ω T → Ωt T) ⊆ U := by
    rintro _ ⟨ω, rfl⟩ i
    rw [Ee_unit]; exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have hEq : Set.EqOn (ext f) (fun x => F (fun i => (Ee (ts i) x).toReal))
      (Set.range (stoneCechUnit : Ω T → Ωt T)) := by
    rintro _ ⟨ω, rfl⟩
    simp only [ext_unit, hf ω, Ee_unit, EReal.toReal_coe]
  have hcont : ContinuousOn (fun x => F (fun i => (Ee (ts i) x).toReal)) U := by
    refine hFc.comp_continuousOn (continuousOn_pi.mpr fun i => ?_)
    refine EReal.continuousOn_toReal.comp (continuous_Ee (ts i)).continuousOn ?_
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨(hy i).2, (hy i).1⟩
  have hcl : U ⊆ closure (Set.range (stoneCechUnit : Ω T → Ωt T)) := by
    rw [denseRange_stoneCechUnit.closure_range]; exact Set.subset_univ _
  exact hEq.of_subset_closure (ext f).continuous.continuousOn hcont hsub hcl hx

end L54

theorem solution (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
    (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
    (hHol : IsHolder T μU) (f : Ω T →ᵇ ℝ) (hf : IsCylindrical f) : InGamma Ps μU f := by
  intro Q _ X hX
  obtain ⟨d, ts, F, hFc, -, hfF⟩ := hf
  rw [lawOf, integral_map (L54.measurable_pathOf hX).aemeasurable
    f.continuous.aestronglyMeasurable]
  apply integral_congr_ae
  have hae : ∀ᵐ x ∂Q, ∀ i, (X (ts i) x : EReal) = Btilde (ts i) x :=
    ae_all_iff.mpr fun i => hX.ae_eq (ts i)
  filter_upwards [hae] with x hx
  have hE : ∀ i, L54.Ee (ts i) x = X (ts i) x := fun i => by rw [← L54.Btilde_eq, ← hx i]
  rw [L54.ext_cyl f ts F hFc hfF x (fun i => by
    rw [hE i]; exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩), hfF]
  simp only [hE, EReal.toReal_coe]
  rfl
