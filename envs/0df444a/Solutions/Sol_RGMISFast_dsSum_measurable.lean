-- Prove2me | solution 1 for RGMISFast.dsSum_measurable
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T01:41:48.036733+00:00
-- url     : https://prove2.me/submissions/ede2b91a-0566-42f1-8cac-6f4900bfe67e

import Definitions.Def_RGMISFast_Y
open RGMISFast MeasureTheory
set_option autoImplicit false

lemma mis_true_iff {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (v : V) :
    inMIS G r v = true ↔ ∀ w, G.Adj v w → r w < r v → inMIS G r w = false := by
  rw [inMIS_eq]
  simp only [List.all_eq_true]
  constructor
  · intro h w ha hr
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using h ⟨w,(mem_lowerNbrs G r).mpr ⟨ha,hr⟩⟩ (by simp)
  · intro h w hw
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using h w.val ((mem_lowerNbrs G r).mp w.property).1 ((mem_lowerNbrs G r).mp w.property).2

lemma mis_order_congr {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r s : V → ℝ)
    (hord : ∀ v w, r v < r w ↔ s v < s w) (v : V) : inMIS G r v = inMIS G s v := by
  induction v using (measure (rk r)).wf.induction with
  | h v ih =>
    have he : inMIS G r v = true ↔ inMIS G s v = true := by
      rw [mis_true_iff,mis_true_iff]
      constructor
      · intro h w ha hw
        rw [← ih w (rk_lt r ((hord w v).mpr hw))]
        exact h w ha ((hord w v).mpr hw)
      · intro h w ha hw
        rw [ih w (rk_lt r hw)]
        exact h w ha ((hord w v).mp hw)
    cases hr : inMIS G r v <;> cases hs : inMIS G s v <;> simp_all

lemma mis_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Measurable (fun r : V → ℝ => inMIS G r v) := by
  classical
  let code : (V → ℝ) → (V → V → Prop) := fun r a b => r a < r b
  have hm : Measurable code := by
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    exact measurableSet_setOf.mp (measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b))
  have hf : (fun r : V → ℝ => inMIS G r v).FactorsThrough code := by
    intro r s he
    apply mis_order_congr G r s
    intro a b
    exact iff_of_eq (congrFun (congrFun he a) b)
  obtain ⟨f,he⟩ := (Function.factorsThrough_iff _).mp hf
  rw [he]
  exact (measurable_of_countable f).comp hm

lemma active_vertex_iff {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (t : ℝ) (v : V) :
    t ≤ tau G r v ↔ ∀ w, (w = v ∨ G.Adj v w) → inMIS G r w = true → t ≤ r w := by
  classical
  unfold tau
  rw [Finset.le_min'_iff]
  constructor
  · intro h w hw hm
    exact h (r w) (Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr
      ⟨by simpa using hw,hm⟩,rfl⟩)
  · intro h y hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hw,hm⟩ := Finset.mem_filter.mp hw
    exact h w (by simpa using hw) hm

lemma active_vertex_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (v : V) :
    MeasurableSet {r : V → ℝ | t ≤ tau G r v} := by
  simp only [active_vertex_iff, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro w
  apply MeasurableSet.iInter
  intro hw
  have hm := mis_measurable G w
  have hb : MeasurableSet {r : V → ℝ | inMIS G r w = true} := measurableSet_eq_fun hm measurable_const
  have ht : MeasurableSet {r : V → ℝ | t ≤ r w} := measurableSet_le measurable_const (measurable_pi_apply w)
  convert hb.compl.union ht using 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]

lemma measurable_of_activity {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (f : (V → ℝ) → ℕ)
    (hf : ∀ r s, (∀ v, t ≤ tau G r v ↔ t ≤ tau G s v) → f r = f s) : Measurable f := by
  classical
  let code : (V → ℝ) → (V → Prop) := fun r v => t ≤ tau G r v
  have hm : Measurable code := by
    apply measurable_pi_lambda
    intro v
    exact measurableSet_setOf.mp (active_vertex_measurable G t v)
  have hfac : f.FactorsThrough code := by
    intro r s he
    exact hf r s (fun v => iff_of_eq (congrFun he v))
  obtain ⟨g,he⟩ := (Function.factorsThrough_iff _).mp hfac
  rw [he]
  exact (measurable_of_countable g).comp hm

lemma activeAt_congr {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (r s : V → ℝ)
    (h : ∀ v, t ≤ tau G r v ↔ t ≤ tau G s v) (A : Finset V) :
    ActiveAt G r t A = ActiveAt G s t A := by
  unfold ActiveAt
  simp_rw [h]

lemma Ncount_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => Ncount G A k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  unfold Ncount
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [activeAt_congr G t r s h]

lemma Y_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => Y G u k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  unfold Y
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [activeAt_congr G t r s h]

lemma dsSum_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => dsSum G u k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  have he : {x | t ≤ tau G r x} = {x | t ≤ tau G s x} := Set.ext h
  have hc : countedW G u k t r = countedW G u k t s := by
    unfold countedW
    apply Finset.filter_congr
    intro W hw
    rw [activeAt_congr G t r s h]
  unfold dsSum
  rw [he,hc]

 theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) :
    Measurable (fun r : V → ℝ => dsSum G u k s r) := by
  exact dsSum_measurable_complete G u k s

#print axioms solution
