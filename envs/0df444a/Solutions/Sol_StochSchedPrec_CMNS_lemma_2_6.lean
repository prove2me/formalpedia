-- Prove2me | solution 1 for StochSchedPrec.CMNS.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:48:47.275198+00:00
-- url     : https://prove2.me/submissions/da71ea84-a3da-4365-9ba5-2612fd2a4801

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

theorem SSP_indep_of_invariant {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (P : V → Ω → ℝ) (hPm : ∀ k, Measurable (P k)) (hP0 : ∀ k ω, 0 ≤ P k ω)
    (hind : iIndepFun P Pr) (j : V) (F : (V → ℝ) → ℝ)
    (hF : AEMeasurable F (Pr.map (fun ω k => P k ω)))
    (hinv : ∀ p : V → ℝ, (∀ k, 0 ≤ p k) → F p = F (Function.update p j 1)) :
    IndepFun (P j) (fun ω => F (fun k => P k ω)) Pr := by
  classical
  set T : Finset V := Finset.univ.erase j with hT
  have hST : Disjoint ({j} : Finset V) T := by simp [hT]
  have h1 := hind.indepFun_finset {j} T hST hPm
  set Y : Ω → (T → ℝ) := fun ω i => P i ω with hYdef
  have hYm : Measurable Y := measurable_pi_lambda _ (fun i => hPm i)
  have hindY : IndepFun (P j) Y Pr := by
    have := h1.comp (measurable_pi_apply (⟨j, Finset.mem_singleton_self j⟩ : ({j} : Finset V)))
      measurable_id
    exact this
  let combine : ℝ × (T → ℝ) → (V → ℝ) := fun z k =>
    if h : k = j then z.1 else z.2 ⟨k, Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩⟩
  have hcomb : Measurable combine := by
    refine measurable_pi_lambda _ (fun k => ?_)
    by_cases h : k = j
    · simp only [combine, h, dite_true]
      exact measurable_fst
    · simp only [combine, h, dite_false]
      exact (measurable_pi_apply _).comp measurable_snd
  set Z : Ω → ℝ × (T → ℝ) := fun ω => (P j ω, Y ω) with hZdef
  have hZm : Measurable Z := (hPm j).prodMk hYm
  have hXZ : (fun ω k => P k ω) = combine ∘ Z := by
    funext ω k
    by_cases h : k = j
    · subst h; simp [combine, Z]
    · simp [combine, Z, Y, h]
  have hmapprod : Pr.map Z = (Pr.map (P j)).prod (Pr.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map (hPm j).aemeasurable hYm.aemeasurable).1 hindY
  have hF' : AEMeasurable (F ∘ combine) (Pr.map Z) := by
    have : Pr.map (fun ω k => P k ω) = (Pr.map Z).map combine := by
      rw [Measure.map_map hcomb hZm, hXZ]
    rw [this] at hF
    exact hF.comp_measurable hcomb
  set H : (T → ℝ) → ℝ := fun y => F (combine (1, y)) with hHdef
  have hGm : MeasurableSet {z : ℝ × (T → ℝ) | 0 ≤ z.1 ∧ ∀ k, 0 ≤ z.2 k} := by
    have : {z : ℝ × (T → ℝ) | 0 ≤ z.1 ∧ ∀ k, 0 ≤ z.2 k}
        = (Set.Ici (0 : ℝ)) ×ˢ (Set.univ.pi fun _ => Set.Ici (0 : ℝ)) := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ici, Set.mem_pi, Set.mem_univ, true_implies, forall_const]
    rw [this]
    exact measurableSet_Ici.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ici)
  have hG : ∀ᵐ z ∂(Pr.map Z), 0 ≤ z.1 ∧ ∀ k, 0 ≤ z.2 k :=
    (ae_map_iff hZm.aemeasurable hGm).2
      (Filter.Eventually.of_forall fun ω => ⟨hP0 j ω, fun k => hP0 k ω⟩)
  have heq : F ∘ combine =ᵐ[Pr.map Z] H ∘ Prod.snd := by
    filter_upwards [hG] with z hz
    have hnn : ∀ k, 0 ≤ combine z k := by
      intro k
      by_cases h : k = j
      · simp only [combine, h, dite_true]; exact hz.1
      · simp only [combine, h, dite_false]; exact hz.2 _
    simp only [Function.comp, H]
    rw [hinv _ hnn]
    congr 1
    funext k
    by_cases h : k = j
    · subst h; simp [combine]
    · simp [combine, h]
  have hH2 : AEMeasurable (H ∘ Prod.snd) ((Pr.map (P j)).prod (Pr.map Y)) := by
    rw [← hmapprod]
    exact hF'.congr heq
  have : IsProbabilityMeasure (Pr.map (P j)) := Measure.isProbabilityMeasure_map (hPm j).aemeasurable
  have : IsProbabilityMeasure (Pr.map Y) := Measure.isProbabilityMeasure_map hYm.aemeasurable
  have hae := Measure.ae_ae_of_ae_prod hH2.ae_eq_mk
  obtain ⟨a, ha⟩ := hae.exists
  have hHρ : AEMeasurable H (Pr.map Y) :=
    ⟨fun y => hH2.mk _ (a, y), hH2.measurable_mk.comp measurable_prodMk_left, ha⟩
  have hfin := hindY.comp₀ (hPm j).aemeasurable hYm.aemeasurable aemeasurable_id hHρ
  have hFY : (fun ω => F (fun k => P k ω)) = H ∘ Y := by
    funext ω
    simp only [Function.comp, H]
    rw [hinv _ (fun k => hP0 k ω)]
    congr 1
    funext k
    by_cases h : k = j
    · subst h; simp [combine]
    · simp [combine, h, Y]
  rw [hFY]
  exact hfin

open StochSchedPrec.CMNS in
theorem SSP_oo_key {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (A : V → V → Prop) (r : V → ℝ) (L : Fin (Fintype.card V) ≃ V)
    (hLE : IsLinearExtension A L) (β : ℝ) (μ : V → ℝ)
    (σ : (V → ℝ) → V → ℝ) (hσ : IsCMNSPolicy m A r L β μ σ) (hσna : IsNonanticipatory σ)
    (j i : V) (hji : L.symm j < L.symm i) (w w' : V → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hw' : ∀ k, 0 ≤ w' k) (hagree : ∀ k, k ≠ i → w' k = w k)
    (h1 : σ w i < σ w j) (h2 : σ w' j ≤ σ w' i) : False := by
  -- nonanticipation before `i` starts
  have hNA : ∀ u u' : V → ℝ, (∀ k, 0 ≤ u k) → (∀ k, 0 ≤ u' k) → (∀ k, k ≠ i → u' k = u k) →
      ∀ t, t < σ u i → ∀ k, (σ u k ≤ t ↔ σ u' k ≤ t) := by
    intro u u' hu hu' hag t ht k
    refine (hσna t u u' hu hu' (fun x hx => ?_) k).1
    have hxi : x ≠ i := by rintro rfl; linarith
    have he := hag x hxi
    exact ⟨fun _ => he, fun h => by rw [he]; exact h⟩
  have hagree' : ∀ k, k ≠ i → w k = w' k := fun k hk => (hagree k hk).symm
  set s := σ w i with hsdef
  have hs' : σ w' i = s := by
    have key : ∀ u u' : V → ℝ, (∀ k, 0 ≤ u k) → (∀ k, 0 ≤ u' k) → (∀ k, k ≠ i → u' k = u k) →
        ¬ σ u i < σ u' i := by
      intro u u' hu hu' hag hlt
      have := (hNA u' u hu' hu (fun k hk => (hag k hk).symm) (σ u i) hlt i).2 le_rfl
      linarith
    rcases lt_trichotomy (σ w' i) s with h | h | h
    · exact absurd h (key w' w hw' hw hagree')
    · exact h
    · exact absurd h (key w w' hw hw' hagree)
  have hE : ∀ k, σ w' k < s → σ w k = σ w' k := by
    intro k hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := (hNA w' w hw' hw hagree' (σ w k) (by rw [hs']; linarith) k).2 le_rfl
      linarith
    · have := (hNA w w' hw hw' hagree (σ w' k) (by linarith) k).2 le_rfl
      linarith
  have hj' : σ w' j = s := by
    rcases lt_or_eq_of_le h2 with h | h
    · rw [hs'] at h
      have := hE j h
      linarith
    · rw [h, hs']
  -- the run in world `w`
  obtain ⟨_, ⟨ord, hmono, hdec⟩, _, _⟩ := hσ w hw
  have hji_ord : ord.symm i ≤ ord.symm j := by
    by_contra h
    push Not at h
    have := hmono j i h
    linarith
  classical
  set Y := Finset.univ.filter fun y => (y = j ∨ Relation.TransGen A y j) ∧ ord.symm i ≤ ord.symm y
  have hjY : j ∈ Y := by simp [Y, hji_ord]
  obtain ⟨x, hxY, hxmin⟩ := Finset.exists_min_image Y (fun y => L.symm y) ⟨j, hjY⟩
  simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and] at hxY
  obtain ⟨hxj, hxord⟩ := hxY
  have hLx : L.symm x ≤ L.symm j := by
    rcases hxj with h | h
    · rw [h]
    · exact (hLE x j h).le
  have hxi : x ≠ i := by rintro rfl; exact absurd hLx (not_le.2 hji)
  have hord : ord.symm i < ord.symm x :=
    lt_of_le_of_ne hxord (fun h => hxi (ord.symm.injective h).symm)
  have hzj : ∀ z, Relation.TransGen A z x → Relation.TransGen A z j := by
    intro z hz
    rcases hxj with h | h
    · rw [← h]; exact hz
    · exact hz.trans h
  have hpreds : ∀ z, Relation.TransGen A z x → ord.symm z < ord.symm i := by
    intro z hz
    by_contra h
    push Not at h
    have hzY : z ∈ Y := by
      simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Or.inr (hzj z hz), h⟩
    have := hxmin z hzY
    have := hLE z x hz
    exact absurd this (not_lt.2 (by assumption))
  have hnotavail : ¬ AvailAtDecision A r w (σ w) ord i x := by
    intro hav
    rcases (hdec i).2.2 with hfirst | ⟨_, hfirst2, _⟩
    · have := hfirst.2 j hji_ord
      exact absurd this (not_le.2 hji)
    · have := hfirst2.2 x ⟨hord.le, hav⟩
      exact absurd (lt_of_le_of_lt hLx hji) (not_lt.2 this)
  -- feasibility facts in world `w'`
  have hfeas' := (hσ w' hw').1
  have hchain : ∀ z y, Relation.TransGen A z y → σ w' z + w' z ≤ σ w' y := by
    intro z y h
    induction h with
    | single hab => exact hfeas'.2.1 _ _ hab
    | @tail b c _ hbc ih =>
      have := hfeas'.2.1 _ _ hbc
      linarith [hw' b]
  have hxav' : r x ≤ s ∧ ∀ z, Relation.TransGen A z x → σ w' z + w' z ≤ s := by
    rcases hxj with h | h
    · subst h
      exact ⟨by rw [← hj']; exact hfeas'.1 x, fun z hz => by rw [← hj']; exact hchain z x hz⟩
    · have hx' := hchain x j h
      rw [hj'] at hx'
      have hxs : σ w' x ≤ s := by linarith [hw' x]
      exact ⟨le_trans (hfeas'.1 x) hxs, fun z hz => le_trans (hchain z x hz) hxs⟩
  apply hnotavail
  refine ⟨hxav'.1, fun z hz => ⟨hpreds z hz, ?_⟩⟩
  have hzi : z ≠ i := by
    rintro rfl
    have := hLE z j (hzj z hz)
    exact absurd hji (not_lt.2 this.le)
  have hz' := hxav'.2 z hz
  rw [hagree z hzi] at hz'
  have hzs : σ w z ≤ s := hmono z i (hpreds z hz)
  rcases lt_or_eq_of_le (hw z) with hpos | hzero
  · have : σ w' z < s := by linarith
    rw [hE z this]
    exact hz'
  · rw [← hzero]; simpa using hzs

open StochSchedPrec.CMNS in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P)
    (L : Fin (Fintype.card V) ≃ V) (hLE : IsLinearExtension A L) (β : ℝ) (hβ : 0 ≤ β)
    (σ : (V → ℝ) → V → ℝ) (hσ : IsCMNSPolicy m A r L β (fun j => ∫ ω, P j ω ∂Pr) σ)
    (hσna : IsNonanticipatory σ)
    (hσm : AEMeasurable σ (Pr.map (fun ω k => P k ω))) (j : V) :
    ∫ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, P i ω ∂Pr
      = ∫ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, (∫ ω', P i ω' ∂Pr) ∂Pr := by
  set μ : V → ℝ := fun j => ∫ ω, P j ω ∂Pr with hμdef
  classical
  set F : V → (V → ℝ) → ℝ := fun i p => if σ p i < σ p j then 1 else 0 with hF
  have hFm : ∀ i, AEMeasurable (F i) (Pr.map (fun ω k => P k ω)) := by
    intro i
    have hg : Measurable (fun S : V → ℝ => if S i < S j then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j))
        measurable_const measurable_const
    exact hg.comp_aemeasurable hσm
  have hinv : ∀ i ∈ after L j, ∀ p : V → ℝ, (∀ k, 0 ≤ p k) →
      F i p = F i (Function.update p i 1) := by
    intro i hi p hp
    have hji : L.symm j < L.symm i := (Finset.mem_filter.mp hi).2
    have hq : ∀ k, 0 ≤ Function.update p i 1 k := by
      intro k
      by_cases h : k = i
      · subst h; simp
      · simp [h, hp k]
    have hag : ∀ k, k ≠ i → Function.update p i 1 k = p k := fun k hk => by simp [hk]
    have hag' : ∀ k, k ≠ i → p k = Function.update p i 1 k := fun k hk => (hag k hk).symm
    have hiff : σ p i < σ p j ↔ σ (Function.update p i 1) i < σ (Function.update p i 1) j := by
      constructor
      · intro h
        by_contra h'
        exact SSP_oo_key m A r L hLE β μ σ hσ hσna j i hji p _ hp hq hag h (not_lt.1 h')
      · intro h
        by_contra h'
        exact SSP_oo_key m A r L hLE β μ σ hσ hσna j i hji _ p hq hp hag' h (not_lt.1 h')
    simp only [hF, hiff]
  have hind : ∀ i ∈ after L j, IndepFun (P i) (fun ω => F i (fun k => P k ω)) Pr := fun i hi =>
    SSP_indep_of_invariant P hP.1 hP.2.1 hP.2.2.2 i (F i) (hFm i) (hinv i hi)
  have hXm : Measurable (fun ω k => P k ω) := measurable_pi_lambda _ (fun k => hP.1 k)
  have hFi : ∀ i, Integrable (fun ω => F i (fun k => P k ω)) Pr := by
    intro i
    refine (integrable_const (1 : ℝ)).mono' ((hFm i).comp_aemeasurable hXm.aemeasurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hF]
    split_ifs <;> simp
  have hL : ∀ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, P i ω
      = ∑ i ∈ after L j, P i ω * F i (fun k => P k ω) := by
    intro ω
    rw [outOfOrder, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hF]
    split_ifs <;> simp
  have hR : ∀ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, μ i
      = ∑ i ∈ after L j, μ i * F i (fun k => P k ω) := by
    intro ω
    rw [outOfOrder, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hF]
    split_ifs <;> simp
  show ∫ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, P i ω ∂Pr
      = ∫ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, μ i ∂Pr
  simp only [hL, hR]
  rw [integral_finsetSum (f := fun i ω => P i ω * F i (fun k => P k ω)) _
      (fun i hi => (hind i hi).integrable_mul (hP.2.2.1 i) (hFi i)),
    integral_finsetSum (f := fun i ω => μ i * F i (fun k => P k ω)) _
      (fun i _ => (hFi i).const_mul (μ i))]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [(hind i hi).integral_fun_mul_eq_mul_integral (hP.2.2.1 i).aestronglyMeasurable
    (hFi i).aestronglyMeasurable, integral_const_mul]
