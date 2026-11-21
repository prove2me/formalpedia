-- Prove2me | solution 1 for ProphetMatchingEFGT.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:21:14.385741+00:00
-- url     : https://prove2.me/submissions/dea7f167-a683-4120-a193-46c062be520c

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_BatchedModel

open MeasureTheory ProbabilityTheory

namespace Aux_ProphetMatchingEFGT_eq_2

open ProphetMatchingEFGT

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem blocks_disj (Bs : List (Finset E)) (hBs : IsOrderedPartition Bs) (i j : Fin Bs.length)
    (hij : i ≠ j) : Disjoint (Bs.get i) (Bs.get j) := by
  have hp := List.pairwise_iff_getElem.mp hBs.2.1
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · have := hp i j i.isLt j.isLt h
    simpa using this
  · have := hp j i j.isLt i.isLt h
    simpa using (this.symm)

theorem block_of (Bs : List (Finset E)) (hBs : IsOrderedPartition Bs) (e : E) :
    ∃ i : Fin Bs.length, e ∈ Bs.get i := by
  obtain ⟨B, hB, he⟩ := hBs.2.2 e
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hB
  exact ⟨i, by rw [hi]; exact he⟩

theorem hybrid_measurable (B : Finset E) :
    Measurable (fun p : (E → ℝ) × (E → ℝ) => hybrid B p.1 p.2) := by
  apply measurable_pi_lambda
  intro e
  unfold hybrid
  by_cases he : e ∈ B
  · simp only [he, if_true]
    exact (measurable_pi_apply e).comp measurable_fst
  · simp only [he, if_false]
    exact (measurable_pi_apply e).comp measurable_snd

theorem G_measurable (opt : (E → ℝ) → Finset E) (hopt : ∀ S : Finset E, MeasurableSet {w | opt w = S})
    (B : Finset E) : Measurable (fun w : E → ℝ => setWeight w (opt w ∩ B)) := by
  have h : (fun w : E → ℝ => setWeight w (opt w ∩ B)) =
      fun w => ∑ S : Finset E, Set.indicator {w | opt w = S} (fun w => setWeight w (S ∩ B)) w := by
    funext w
    rw [Finset.sum_eq_single (opt w)]
    · rw [Set.indicator_of_mem (show w ∈ {x | opt x = opt w} from rfl)]
    · intro S _ hS
      rw [Set.indicator_of_notMem]
      intro h'
      exact hS h'.symm
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  rw [h]
  apply Finset.measurable_sum
  intro S _
  apply Measurable.indicator _ (hopt S)
  unfold setWeight
  apply Finset.measurable_sum
  intro e _
  exact measurable_pi_apply e

theorem map_hybrid (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ] (Bs : List (Finset E))
    (hBs : IsOrderedPartition Bs) (hind : BlocksIndep μ Bs) (t : Fin Bs.length) :
    (μ.prod μ).map (fun p : (E → ℝ) × (E → ℝ) => hybrid (Bs.get t) p.1 p.2) = μ := by
  have hm := hybrid_measurable (Bs.get t)
  haveI : IsProbabilityMeasure ((μ.prod μ).map (fun p : (E → ℝ) × (E → ℝ) => hybrid (Bs.get t) p.1 p.2)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi
  · intro s hs
    obtain ⟨A, hA, rfl⟩ := hs
    have hAm : ∀ e, MeasurableSet (A e) := fun e => hA e (Set.mem_univ e)
    have hpi : MeasurableSet (Set.pi Set.univ A) := MeasurableSet.univ_pi hAm
    rw [Measure.map_apply hm hpi]
    -- the preimage is a product of two sets
    obtain ⟨U, hU⟩ : ∃ U : Set (E → ℝ), U = {w | ∀ e ∈ Bs.get t, w e ∈ A e} := ⟨_, rfl⟩
    obtain ⟨W, hW⟩ : ∃ W : Set (E → ℝ), W = {w | ∀ e, e ∉ Bs.get t → w e ∈ A e} := ⟨_, rfl⟩
    have hpre : (fun p : (E → ℝ) × (E → ℝ) => hybrid (Bs.get t) p.1 p.2) ⁻¹' Set.pi Set.univ A =
        U ×ˢ W := by
      ext p
      rw [hU, hW]
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Set.mem_setOf_eq, hybrid]
      constructor
      · intro h
        constructor
        · intro e he
          have := h e
          rw [if_pos he] at this
          exact this
        · intro e he
          have := h e
          rw [if_neg he] at this
          exact this
      · rintro ⟨h1, h2⟩ e
        by_cases he : e ∈ Bs.get t
        · rw [if_pos he]
          exact h1 e he
        · rw [if_neg he]
          exact h2 e he
    have hsplit : Set.pi Set.univ A = U ∩ W := by
      ext w
      rw [hU, hW]
      simp only [Set.mem_univ_pi, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro h
        exact ⟨fun e _ => h e, fun e _ => h e⟩
      · rintro ⟨h1, h2⟩ e
        by_cases he : e ∈ Bs.get t
        · exact h1 e he
        · exact h2 e he
    rw [hpre, Measure.prod_prod, hsplit]
    -- independence of block t from the other blocks
    have hmeasf : ∀ i : Fin Bs.length,
        Measurable (fun (w : E → ℝ) (e : {e // e ∈ Bs.get i}) => w e) := by
      intro i
      apply measurable_pi_lambda
      intro e
      exact measurable_pi_apply e.1
    have hindep := iIndepFun.indepFun_finset {t} (Finset.univ \ {t})
      (Finset.disjoint_sdiff) hind hmeasf
    obtain ⟨S1, hS1⟩ : ∃ S1 : Set ((i : ({t} : Finset (Fin Bs.length))) → ({e // e ∈ Bs.get i} → ℝ)),
        S1 = {z | ∀ i e, z i e ∈ A e.1} := ⟨_, rfl⟩
    obtain ⟨S2, hS2⟩ : ∃ S2 : Set ((i : (Finset.univ \ {t} : Finset (Fin Bs.length))) →
        ({e // e ∈ Bs.get i} → ℝ)), S2 = {z | ∀ i e, z i e ∈ A e.1} := ⟨_, rfl⟩
    have hS1m : MeasurableSet S1 := by
      rw [hS1]
      have : {z : (i : ({t} : Finset (Fin Bs.length))) → ({e // e ∈ Bs.get i} → ℝ) |
          ∀ i e, z i e ∈ A e.1} = ⋂ i, ⋂ e, {z | z i e ∈ A e.1} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this]
      exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun e =>
        measurableSet_preimage ((measurable_pi_apply e).comp (measurable_pi_apply i)) (hAm e.1)))
    have hS2m : MeasurableSet S2 := by
      rw [hS2]
      have : {z : (i : (Finset.univ \ {t} : Finset (Fin Bs.length))) → ({e // e ∈ Bs.get i} → ℝ) |
          ∀ i e, z i e ∈ A e.1} = ⋂ i, ⋂ e, {z | z i e ∈ A e.1} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this]
      exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun e =>
        measurableSet_preimage ((measurable_pi_apply e).comp (measurable_pi_apply i)) (hAm e.1)))
    have hpre1 : (fun (w : E → ℝ) (i : ({t} : Finset (Fin Bs.length))) (e : {e // e ∈ Bs.get i}) => w e) ⁻¹' S1 = U := by
      ext w
      rw [hS1, hU]
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro h e he
        exact h ⟨t, Finset.mem_singleton_self t⟩ ⟨e, he⟩
      · intro h i e
        obtain ⟨i, hi⟩ := i
        obtain rfl := Finset.mem_singleton.mp hi
        exact h e.1 e.2
    have hpre2 : (fun (w : E → ℝ) (i : (Finset.univ \ {t} : Finset (Fin Bs.length)))
        (e : {e // e ∈ Bs.get i}) => w e) ⁻¹' S2 = W := by
      ext w
      rw [hS2, hW]
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro h e he
        obtain ⟨i, hi⟩ := block_of Bs hBs e
        have hit : i ≠ t := by
          intro h'
          rw [h'] at hi
          exact he hi
        have hmem : i ∈ Finset.univ \ {t} := by
          rw [Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨Finset.mem_univ _, hit⟩
        exact h ⟨i, hmem⟩ ⟨e, hi⟩
      · intro h i e
        have hit : (i : Fin Bs.length) ≠ t := by
          have := i.2
          rw [Finset.mem_sdiff, Finset.mem_singleton] at this
          exact this.2
        apply h e.1
        intro he
        exact Finset.disjoint_left.mp (blocks_disj Bs hBs i t hit) e.2 he
    have := hindep.measure_inter_preimage_eq_mul S1 S2 hS1m hS2m
    rw [hpre1, hpre2] at this
    exact this.symm
  · rw [measure_univ, measure_univ]

theorem eq2_main (M : Set (Finset E)) (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (opt : (E → ℝ) → Finset E) (hopt : IsOPT M opt)
    (Bs : List (Finset E)) (hBs : IsOrderedPartition Bs) (hind : BlocksIndep μ Bs)
    (t : Fin Bs.length) :
    ∫ p : (E → ℝ) × (E → ℝ), setWeight p.1 (Bs.get t ∩ opt (hybrid (Bs.get t) p.1 p.2)) ∂(μ.prod μ)
      = ∫ w, setWeight w (opt w ∩ Bs.get t) ∂μ := by
  have hpt : ∀ p : (E → ℝ) × (E → ℝ),
      setWeight p.1 (Bs.get t ∩ opt (hybrid (Bs.get t) p.1 p.2)) =
        (fun w : E → ℝ => setWeight w (opt w ∩ Bs.get t)) (hybrid (Bs.get t) p.1 p.2) := by
    intro p
    show ∑ e ∈ Bs.get t ∩ opt (hybrid (Bs.get t) p.1 p.2), p.1 e =
      ∑ e ∈ opt (hybrid (Bs.get t) p.1 p.2) ∩ Bs.get t, hybrid (Bs.get t) p.1 p.2 e
    rw [Finset.inter_comm (Bs.get t)]
    apply Finset.sum_congr rfl
    intro e he
    unfold hybrid
    rw [if_pos (Finset.mem_inter.mp he).2]
  simp_rw [hpt]
  rw [← integral_map (hybrid_measurable (Bs.get t)).aemeasurable
    (G_measurable opt hopt.measurableSet_eq (Bs.get t)).aestronglyMeasurable,
    map_hybrid μ Bs hBs hind t]

end Aux_ProphetMatchingEFGT_eq_2

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT Aux_ProphetMatchingEFGT_eq_2 in
theorem solution {E : Type*} [Fintype E] [DecidableEq E] (M : Set (Finset E))
    (hM : IsDownwardClosed M) (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ e, Integrable (fun w => w e) μ) (opt : (E → ℝ) → Finset E) (hopt : IsOPT M opt)
    (Bs : List (Finset E)) (hBs : IsOrderedPartition Bs) (hind : BlocksIndep μ Bs)
    (t : Fin Bs.length) :
    ∫ p : (E → ℝ) × (E → ℝ), setWeight p.1 (Bs.get t ∩ opt (hybrid (Bs.get t) p.1 p.2)) ∂(μ.prod μ)
      = ∫ w, setWeight w (opt w ∩ Bs.get t) ∂μ :=
  eq2_main M μ opt hopt Bs hBs hind t
