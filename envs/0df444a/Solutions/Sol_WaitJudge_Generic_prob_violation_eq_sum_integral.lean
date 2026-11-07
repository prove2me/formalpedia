-- Prove2me | solution 1 for WaitJudge.Generic.prob_violation_eq_sum_integral
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:28:14.617192+00:00
-- url     : https://prove2.me/submissions/6ecf7add-8c63-4335-841a-fe6348e3bbbe

import Mathlib
import Definitions.Def_WaitJudge_Generic_Setting

open MeasureTheory WaitJudge.Generic

namespace WJGCore

variable {S Δ : Type*} [Nonempty S] {p : ℕ} (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S)
  (tb : Fin p → S → ℝ)

lemma feasibleOn_comp {m k : ℕ} (ω : Fin m → Δ) (g : Fin k → Fin m) (J : Finset (Fin k)) :
    feasibleOn X Xδ (ω ∘ g) J = feasibleOn X Xδ ω (J.image g) := by
  ext x; simp [feasibleOn]

lemma uniq_all {m : ℕ} (hA1 : Assumption1 f X Xδ tb) (ω : Fin m → Δ) (J : Finset (Fin m)) :
    ∃! x, IsTBSolution f tb (feasibleOn X Xδ ω J) x := by
  have h := hA1 J.card (ω ∘ (J.orderEmbOfFin rfl))
  rw [feasibleOn_comp] at h
  have : (Finset.univ : Finset (Fin J.card)).image (J.orderEmbOfFin rfl) = J := by
    simpa using Finset.image_orderEmbOfFin_univ J rfl
  rwa [this] at h

lemma sol_spec {F : Set S} (h : ∃! x, IsTBSolution f tb F x) :
    IsTBSolution f tb F (sol f tb F) := by
  unfold sol; rw [dif_pos h]; exact h.exists.choose_spec

lemma sol_eq {F : Set S} (h : ∃! x, IsTBSolution f tb F x) {y : S}
    (hy : IsTBSolution f tb F y) : sol f tb F = y :=
  h.unique (sol_spec f tb h) hy

/-- monotonicity: if `J ⊆ J'` and the solution of `J` is feasible for `J'`, it is the solution
of `J'`. -/
lemma sol_mono {m : ℕ} (hA1 : Assumption1 f X Xδ tb) (ω : Fin m → Δ) {J J' : Finset (Fin m)}
    (hJ : J ⊆ J') (hmem : sol f tb (feasibleOn X Xδ ω J) ∈ feasibleOn X Xδ ω J') :
    sol f tb (feasibleOn X Xδ ω J') = sol f tb (feasibleOn X Xδ ω J) := by
  apply sol_eq f tb (uniq_all f X Xδ tb hA1 ω J')
  have hs := sol_spec f tb (uniq_all f X Xδ tb hA1 ω J)
  refine ⟨hmem, fun y hy => hs.2 y ?_⟩
  exact ⟨hy.1, fun i hi => hy.2 i (hJ hi)⟩

lemma feasibleOn_anti {m : ℕ} (ω : Fin m → Δ) {J J' : Finset (Fin m)} (hJ : J ⊆ J') :
    feasibleOn X Xδ ω J' ⊆ feasibleOn X Xδ ω J :=
  fun _ hx => ⟨hx.1, fun i hi => hx.2 i (hJ hi)⟩

lemma sol_mem {m : ℕ} (hA1 : Assumption1 f X Xδ tb) (ω : Fin m → Δ) (J : Finset (Fin m)) :
    sol f tb (feasibleOn X Xδ ω J) ∈ feasibleOn X Xδ ω J :=
  (sol_spec f tb (uniq_all f X Xδ tb hA1 ω J)).1

/-- The key deterministic characterization of the event `supportSet ω = I`. -/
lemma supp_eq_iff {m : ℕ} (hA1 : Assumption1 f X Xδ tb) (ω : Fin m → Δ)
    (hA2 : sol f tb (feasibleOn X Xδ ω (supportSet f X Xδ tb ω)) = xstar f X Xδ tb ω)
    (I : Finset (Fin m)) :
    supportSet f X Xδ tb ω = I ↔
      ((∀ i ∈ I, sol f tb (feasibleOn X Xδ ω (I.erase i)) ≠ sol f tb (feasibleOn X Xδ ω I)) ∧
       (∀ j ∉ I, sol f tb (feasibleOn X Xδ ω I) ∈ Xδ (ω j))) := by
  classical
  have hsupp : ∀ i, i ∈ supportSet f X Xδ tb ω ↔
      sol f tb (feasibleOn X Xδ ω (Finset.univ.erase i)) ≠ xstar f X Xδ tb ω := by
    intro i; unfold supportSet IsSupport; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro rfl
    refine ⟨fun i hi heq => ?_, fun j hj => ?_⟩
    · have h1 : sol f tb (feasibleOn X Xδ ω (Finset.univ.erase i)) =
          sol f tb (feasibleOn X Xδ ω ((supportSet f X Xδ tb ω).erase i)) := by
        apply sol_mono f X Xδ tb hA1 ω (Finset.erase_subset_erase _ (Finset.subset_univ _))
        rw [heq, hA2]
        exact feasibleOn_anti X Xδ ω (Finset.erase_subset _ _) (sol_mem f X Xδ tb hA1 ω _)
      exact (hsupp i).1 hi (by rw [h1, heq, hA2])
    · rw [hA2]
      exact (sol_mem f X Xδ tb hA1 ω Finset.univ).2 j (Finset.mem_univ _)
  · rintro ⟨h1, h2⟩
    have hmemU : sol f tb (feasibleOn X Xδ ω I) ∈ feasibleOn X Xδ ω Finset.univ := by
      refine ⟨(sol_mem f X Xδ tb hA1 ω I).1, fun j _ => ?_⟩
      by_cases hj : j ∈ I
      · exact (sol_mem f X Xδ tb hA1 ω I).2 j hj
      · exact h2 j hj
    have hx : xstar f X Xδ tb ω = sol f tb (feasibleOn X Xδ ω I) :=
      sol_mono f X Xδ tb hA1 ω (Finset.subset_univ _) hmemU
    have hsub : supportSet f X Xδ tb ω ⊆ I := by
      intro j hj
      by_contra hjI
      apply (hsupp j).1 hj
      rw [hx]
      apply sol_mono f X Xδ tb hA1 ω
      · intro a ha; rw [Finset.mem_erase]; exact ⟨fun h => hjI (h ▸ ha), Finset.mem_univ _⟩
      · exact feasibleOn_anti X Xδ ω (Finset.erase_subset _ _) hmemU
    apply Finset.Subset.antisymm hsub
    intro i hi
    by_contra hni
    apply h1 i hi
    have hsub' : supportSet f X Xδ tb ω ⊆ I.erase i := by
      intro a ha; rw [Finset.mem_erase]; exact ⟨fun h => hni (h ▸ ha), hsub ha⟩
    have := sol_mono f X Xδ tb hA1 ω hsub' (by
      rw [hA2, hx]; exact feasibleOn_anti X Xδ ω (Finset.erase_subset _ _)
        (sol_mem f X Xδ tb hA1 ω I))
    rw [this, hA2, hx]

lemma image_erase_emb {m k : ℕ} (I : Finset (Fin m)) (hI : I.card = k) (a : Fin k) :
    (Finset.univ.erase a).image (I.orderEmbOfFin hI) = I.erase (I.orderEmbOfFin hI a) := by
  rw [Finset.image_erase (I.orderEmbOfFin hI).injective, Finset.image_orderEmbOfFin_univ]

lemma xstar_comp {m k : ℕ} (ω : Fin m → Δ) (I : Finset (Fin m)) (hI : I.card = k) :
    xstar f X Xδ tb (fun a => ω (I.orderEmbOfFin hI a)) = sol f tb (feasibleOn X Xδ ω I) := by
  unfold xstar
  rw [show (fun a => ω (I.orderEmbOfFin hI a)) = ω ∘ (I.orderEmbOfFin hI) from rfl,
    feasibleOn_comp, Finset.image_orderEmbOfFin_univ]

lemma sstar_comp {m k : ℕ} (ω : Fin m → Δ) (I : Finset (Fin m)) (hI : I.card = k) :
    sstar f X Xδ tb (fun a => ω (I.orderEmbOfFin hI a)) = k ↔
      ∀ i ∈ I, sol f tb (feasibleOn X Xδ ω (I.erase i)) ≠ sol f tb (feasibleOn X Xδ ω I) := by
  set e := I.orderEmbOfFin hI
  have hsupp : ∀ a, a ∈ supportSet f X Xδ tb (fun a => ω (e a)) ↔
      sol f tb (feasibleOn X Xδ ω (I.erase (e a))) ≠ sol f tb (feasibleOn X Xδ ω I) := by
    intro a; unfold supportSet IsSupport
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [xstar_comp, show (fun a => ω (e a)) = ω ∘ e from rfl, feasibleOn_comp, image_erase_emb]
  unfold sstar
  constructor
  · intro h i hi
    obtain ⟨a, rfl⟩ : ∃ a, e a = i := by
      have : i ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hi
      exact this
    have hall : supportSet f X Xδ tb (fun a => ω (e a)) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [h, Fintype.card_fin])
    exact (hsupp a).1 (hall ▸ Finset.mem_univ a)
  · intro h
    have hall : supportSet f X Xδ tb (fun a => ω (e a)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro a; exact (hsupp a).2 (h _ (Finset.orderEmbOfFin_mem I hI a))
    rw [hall, Finset.card_univ, Fintype.card_fin]

variable [MeasurableSpace S] [MeasurableSpace Δ]

lemma meas_supp_eq {m : ℕ} (hmeas : MeasurabilityPins f X Xδ tb) (I : Finset (Fin m)) :
    MeasurableSet {ω : Fin m → Δ | supportSet f X Xδ tb ω = I} := by
  have : {ω : Fin m → Δ | supportSet f X Xδ tb ω = I} =
      ⋂ i : Fin m, (if i ∈ I then {ω | i ∈ supportSet f X Xδ tb ω}
        else {ω | i ∈ supportSet f X Xδ tb ω}ᶜ) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro h i; split_ifs with hi <;> simp [h, hi]
    · intro h; ext i
      have := h i
      split_ifs at this with hi <;> simp_all
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  split_ifs
  · exact hmeas.2.2 m i
  · exact (hmeas.2.2 m i).compl

lemma meas_sstar_eq {m : ℕ} (hmeas : MeasurabilityPins f X Xδ tb) (k : ℕ) :
    MeasurableSet {ω : Fin m → Δ | sstar f X Xδ tb ω = k} := by
  have : {ω : Fin m → Δ | sstar f X Xδ tb ω = k} =
      ⋃ I ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        {ω | supportSet f X Xδ tb ω = I} := by
    ext ω; simp [sstar]
  rw [this]
  exact Finset.measurableSet_biUnion _ fun I _ => meas_supp_eq f X Xδ tb hmeas I

lemma meas_viol (P : Measure Δ) [IsProbabilityMeasure P] (hmeas : MeasurabilityPins f X Xδ tb) :
    Measurable (fun x : S => ScenarioApproach.Nonconvex.violation P Xδ x) := by
  unfold ScenarioApproach.Nonconvex.violation ScenarioApproach.Nonconvex.violationSet
  have h := measurable_measure_prodMk_left (ν := P) hmeas.1.compl
  exact h.ennreal_toReal

lemma meas_good (P : Measure Δ) [IsProbabilityMeasure P] (hmeas : MeasurabilityPins f X Xδ tb) :
    Measurable (fun x : S => P {δ | x ∈ Xδ δ}) :=
  measurable_measure_prodMk_left (ν := P) hmeas.1

lemma meas_sec (hmeas : MeasurabilityPins f X Xδ tb) (x : S) :
    MeasurableSet {δ : Δ | x ∈ Xδ δ} :=
  measurable_prodMk_left hmeas.1

lemma split_measure (P : Measure Δ) [IsProbabilityMeasure P]
    (hmeas : MeasurabilityPins f X Xδ tb) {m k : ℕ} (I : Finset (Fin m)) (hI : I.card = k)
    (A : Set (Fin k → Δ)) (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin m => P)
      {ω | (fun a => ω (I.orderEmbOfFin hI a)) ∈ A ∧
        ∀ j ∉ I, xstar f X Xδ tb (fun a => ω (I.orderEmbOfFin hI a)) ∈ Xδ (ω j)} =
    ∫⁻ a in A, (P {δ | xstar f X Xδ tb a ∈ Xδ δ}) ^ (m - k)
      ∂(Measure.pi fun _ : Fin k => P) := by
  classical
  have hJ : Iᶜ.card = m - k := by rw [Finset.card_compl, Fintype.card_fin, hI]
  let g : Fin k ⊕ Fin (m - k) ≃ Fin m :=
    (Equiv.sumCongr (I.orderIsoOfFin hI).toEquiv
      ((Iᶜ.orderIsoOfFin hJ).toEquiv.trans
        (Equiv.subtypeEquivRight (fun x => Finset.mem_compl)))).trans
      (Equiv.sumCompl (fun x => x ∈ I))
  have hgl : ∀ a, g (Sum.inl a) = I.orderEmbOfFin hI a := by
    intro a; simp [g, Finset.coe_orderIsoOfFin_apply]
  have hgr : ∀ b, g (Sum.inr b) ∉ I := by
    intro b
    have := (Equiv.subtypeEquivRight (p := fun x => x ∈ Iᶜ) (q := fun x => x ∉ I)
      (fun x => Finset.mem_compl) ((Iᶜ.orderIsoOfFin hJ) b)).2
    simpa [g] using this
  have hgsurj : ∀ j ∉ I, ∃ b, g (Sum.inr b) = j := by
    intro j hj
    obtain ⟨y, hy⟩ := g.surjective j
    rcases y with a | b
    · exact absurd (hy ▸ (hgl a ▸ Finset.orderEmbOfFin_mem I hI a)) hj
    · exact ⟨b, hy⟩
  let Φ : (Fin m → Δ) → (Fin k → Δ) × (Fin (m - k) → Δ) :=
    fun ω => (fun a => ω (g (Sum.inl a)), fun b => ω (g (Sum.inr b)))
  have hΦ : MeasurePreserving Φ (Measure.pi fun _ : Fin m => P)
      ((Measure.pi fun _ : Fin k => P).prod (Measure.pi fun _ : Fin (m - k) => P)) := by
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin m => P) g).symm
    have h2 := measurePreserving_sumPiEquivProdPi
      (X := fun _ : Fin k ⊕ Fin (m - k) => Δ) (fun _ => P)
    have h3 := h2.comp h1
    convert h3 using 1
    funext ω
    apply Prod.ext <;> funext x <;>
      simp [Φ, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi] <;>
      exact (Equiv.piCongrLeft_symm_apply (P := fun _ => Δ) (e := g) ω _).symm
  set T : Set ((Fin k → Δ) × (Fin (m - k) → Δ)) :=
    {q | q.1 ∈ A ∧ ∀ b, xstar f X Xδ tb q.1 ∈ Xδ (q.2 b)} with hTdef
  have hT : MeasurableSet T := by
    have : T = (Prod.fst ⁻¹' A) ∩ ⋂ b : Fin (m - k),
        (fun q : (Fin k → Δ) × (Fin (m - k) → Δ) => (xstar f X Xδ tb q.1, q.2 b)) ⁻¹'
          {q : S × Δ | q.1 ∈ Xδ q.2} := by
      ext q; simp [T]
    rw [this]
    refine (measurable_fst hA).inter (MeasurableSet.iInter fun b => ?_)
    refine Measurable.prodMk ((hmeas.2.1 k).comp measurable_fst)
      ((measurable_pi_apply b).comp measurable_snd) hmeas.1
  have hev : {ω : Fin m → Δ | (fun a => ω (I.orderEmbOfFin hI a)) ∈ A ∧
        ∀ j ∉ I, xstar f X Xδ tb (fun a => ω (I.orderEmbOfFin hI a)) ∈ Xδ (ω j)} =
      Φ ⁻¹' T := by
    have hfun : ∀ ω : Fin m → Δ, (fun a => ω (g (Sum.inl a))) =
        (fun a => ω (I.orderEmbOfFin hI a)) := by
      intro ω; funext a; rw [hgl]
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, T, Φ, hfun]
    refine and_congr_right fun _ => ⟨fun h b => h _ (hgr b), fun h j hj => ?_⟩
    obtain ⟨b, rfl⟩ := hgsurj j hj
    exact h b
  rw [hev, hΦ.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT,
    ← lintegral_indicator hA]
  congr 1
  funext a
  by_cases ha : a ∈ A
  · rw [Set.indicator_of_mem ha]
    have : Prod.mk a ⁻¹' T = Set.univ.pi (fun _ : Fin (m - k) => {δ | xstar f X Xδ tb a ∈ Xδ δ}) := by
      ext b; simp [T, ha]
    rw [this, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [Set.indicator_of_notMem ha]
    have : Prod.mk a ⁻¹' T = ∅ := by
      ext b; simp [T, ha]
    rw [this, measure_empty]

lemma meas_Vx (P : Measure Δ) [IsProbabilityMeasure P] (hmeas : MeasurabilityPins f X Xδ tb)
    (m : ℕ) : Measurable (fun ω : Fin m → Δ =>
      ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω)) :=
  (meas_viol f X Xδ tb P hmeas).comp (hmeas.2.1 m)

lemma core (P : Measure Δ) [IsProbabilityMeasure P]
    (hA1 : Assumption1 f X Xδ tb) (hA2 : Assumption2 f X Xδ tb P)
    (hmeas : MeasurabilityPins f X Xδ tb) (m k : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (Measure.pi fun _ : Fin m => P)
      {ω | sstar f X Xδ tb ω = k ∧
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω) ∈ B} =
    (m.choose k : ENNReal) *
      ∫⁻ a in {a : Fin k → Δ | sstar f X Xδ tb a = k ∧
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb a) ∈ B},
        (P {δ | xstar f X Xδ tb a ∈ Xδ δ}) ^ (m - k) ∂(Measure.pi fun _ : Fin k => P) := by
  classical
  set μ := Measure.pi fun _ : Fin m => P
  set V := fun ω : Fin m → Δ => ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω)
  set A := {a : Fin k → Δ | sstar f X Xδ tb a = k ∧
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb a) ∈ B}
  have hAm : MeasurableSet A :=
    (meas_sstar_eq f X Xδ tb hmeas k).inter (meas_Vx f X Xδ tb P hmeas k hB)
  set E' := fun I : Finset (Fin m) => {ω : Fin m → Δ | supportSet f X Xδ tb ω = I ∧ V ω ∈ B}
  have hunion : {ω : Fin m → Δ | sstar f X Xδ tb ω = k ∧ V ω ∈ B} =
      ⋃ I ∈ (Finset.univ : Finset (Fin m)).powersetCard k, E' I := by
    ext ω; simp [E', sstar]
  rw [hunion, measure_biUnion_finset]
  · have hconst : ∀ I ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        μ (E' I) = ∫⁻ a in A, (P {δ | xstar f X Xδ tb a ∈ Xδ δ}) ^ (m - k)
          ∂(Measure.pi fun _ : Fin k => P) := by
      intro I hI'
      have hI : I.card = k := (Finset.mem_powersetCard.1 hI').2
      rw [← split_measure f X Xδ tb P hmeas I hI A hAm]
      apply measure_congr
      rw [Filter.eventuallyEq_set]
      filter_upwards [hA2 m] with ω hω
      simp only [E', A, V, Set.mem_ofPred_eq]
      rw [supp_eq_iff f X Xδ tb hA1 ω hω I, sstar_comp f X Xδ tb ω I hI,
        xstar_comp f X Xδ tb ω I hI]
      constructor
      · rintro ⟨⟨h1, h2⟩, hB'⟩
        have hx : xstar f X Xδ tb ω = sol f tb (feasibleOn X Xδ ω I) := by
          rw [← hω, (supp_eq_iff f X Xδ tb hA1 ω hω I).2 ⟨h1, h2⟩]
        rw [hx] at hB'
        exact ⟨⟨h1, hB'⟩, h2⟩
      · rintro ⟨⟨h1, hB'⟩, h2⟩
        have hx : xstar f X Xδ tb ω = sol f tb (feasibleOn X Xδ ω I) := by
          rw [← hω, (supp_eq_iff f X Xδ tb hA1 ω hω I).2 ⟨h1, h2⟩]
        rw [hx]
        exact ⟨⟨h1, h2⟩, hB'⟩
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro I _ J _ hIJ
    refine Set.disjoint_left.2 fun ω h1 h2 => hIJ ?_
    exact h1.1.symm.trans h2.1
  · intro I _
    exact (meas_supp_eq f X Xδ tb hmeas I).inter (meas_Vx f X Xδ tb P hmeas m hB)

lemma one_sub_viol (P : Measure Δ) [IsProbabilityMeasure P] (hmeas : MeasurabilityPins f X Xδ tb)
    (x : S) : 1 - ScenarioApproach.Nonconvex.violation P Xδ x = (P {δ | x ∈ Xδ δ}).toReal := by
  unfold ScenarioApproach.Nonconvex.violation ScenarioApproach.Nonconvex.violationSet
  have h : {δ | x ∉ Xδ δ} = {δ | x ∈ Xδ δ}ᶜ := rfl
  rw [h, prob_compl_eq_one_sub (meas_sec f X Xδ tb hmeas x),
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
  simp

lemma real_conv (P : Measure Δ) [IsProbabilityMeasure P]
    (hmeas : MeasurabilityPins f X Xδ tb) (n k : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ a in {a : Fin k → Δ | sstar f X Xδ tb a = k ∧
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb a) ∈ B},
        (P {δ | xstar f X Xδ tb a ∈ Xδ δ}) ^ n ∂(Measure.pi fun _ : Fin k => P)).toReal =
    ∫ v in B, (1 - v) ^ n ∂(Fk f X Xδ tb P k) := by
  set φ := fun ω : Fin k → Δ => ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω)
  have hφ : Measurable φ := meas_Vx f X Xδ tb P hmeas k
  unfold Fk
  rw [setIntegral_map hB (by fun_prop : Continuous fun v : ℝ => (1 - v) ^ n).aestronglyMeasurable
    hφ.aemeasurable, Measure.restrict_restrict (hφ hB)]
  have hset : φ ⁻¹' B ∩ {ω : Fin k → Δ | sstar f X Xδ tb ω = k} =
      {a : Fin k → Δ | sstar f X Xδ tb a = k ∧ φ a ∈ B} := by
    ext a; simp [and_comm]
  rw [hset, integral_eq_lintegral_of_nonneg_ae]
  · congr 1
    refine lintegral_congr fun a => ?_
    simp only [φ]
    rw [one_sub_viol f X Xδ tb P hmeas, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · refine Filter.Eventually.of_forall fun a => ?_
    simp only [Pi.zero_apply, φ]
    rw [one_sub_viol f X Xδ tb P hmeas]
    positivity
  · exact ((by fun_prop : Continuous fun v : ℝ => (1 - v) ^ n).measurable.comp
      hφ).aestronglyMeasurable

lemma core_real (P : Measure Δ) [IsProbabilityMeasure P]
    (hA1 : Assumption1 f X Xδ tb) (hA2 : Assumption2 f X Xδ tb P)
    (hmeas : MeasurabilityPins f X Xδ tb) (m k : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.pi fun _ : Fin m => P)
      {ω | sstar f X Xδ tb ω = k ∧
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω) ∈ B}).toReal =
    (m.choose k : ℝ) * ∫ v in B, (1 - v) ^ (m - k) ∂(Fk f X Xδ tb P k) := by
  rw [core f X Xδ tb P hA1 hA2 hmeas m k B hB, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    real_conv f X Xδ tb P hmeas _ _ B hB]

lemma partition (P : Measure Δ) [IsProbabilityMeasure P]
    (hmeas : MeasurabilityPins f X Xδ tb) (m : ℕ) (g : ℕ → Set ℝ)
    (hg : ∀ k, MeasurableSet (g k)) :
    ((Measure.pi fun _ : Fin m => P)
      {ω | ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω) ∈
        g (sstar f X Xδ tb ω)}).toReal =
    ∑ k ∈ Finset.range (m + 1), ((Measure.pi fun _ : Fin m => P)
      {ω | sstar f X Xδ tb ω = k ∧
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω) ∈ g k}).toReal := by
  have hset : {ω : Fin m → Δ | ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω) ∈
        g (sstar f X Xδ tb ω)} =
      ⋃ k ∈ Finset.range (m + 1), {ω | sstar f X Xδ tb ω = k ∧
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω) ∈ g k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · intro h
      refine ⟨sstar f X Xδ tb ω, ?_, rfl, h⟩
      have := Finset.card_le_univ (supportSet f X Xδ tb ω)
      rw [Fintype.card_fin] at this
      unfold sstar; omega
    · rintro ⟨k, _, rfl, h⟩; exact h
  rw [hset, measure_biUnion_finset, ENNReal.toReal_sum]
  · intro k _; exact measure_ne_top _ _
  · intro k _ l _ hkl
    exact Set.disjoint_left.2 fun ω h1 h2 => hkl (h1.1.symm.trans h2.1)
  · intro k _
    exact (meas_sstar_eq f X Xδ tb hmeas k).inter (meas_Vx f X Xδ tb P hmeas m (hg k))

lemma viol_mem (P : Measure Δ) [IsProbabilityMeasure P] (hmeas : MeasurabilityPins f X Xδ tb)
    (x : S) : ScenarioApproach.Nonconvex.violation P Xδ x ∈ Set.Icc (0 : ℝ) 1 := by
  have h := one_sub_viol f X Xδ tb P hmeas x
  have h0 : 0 ≤ ScenarioApproach.Nonconvex.violation P Xδ x := ENNReal.toReal_nonneg
  have h1 : 0 ≤ (P {δ | x ∈ Xδ δ}).toReal := ENNReal.toReal_nonneg
  exact ⟨h0, by linarith⟩

end WJGCore

open WJGCore in
theorem solution
    {S Δ : Type*} [Nonempty S] [MeasurableSpace S] [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S)
    {p : ℕ} (tb : Fin p → S → ℝ)
    (hA1 : Assumption1 f X Xδ tb)
    (hA2 : Assumption2 f X Xδ tb P)
    (hmeas : MeasurabilityPins f X Xδ tb)
    (N : ℕ) (hN : 0 < N) (ε : ℕ → ℝ)
    (hε : ∀ k ≤ N, 0 ≤ ε k ∧ ε k ≤ 1) :
    ((Measure.pi fun _ : Fin N => P)
      {ω : Fin N → Δ | ε (sstar f X Xδ tb ω) <
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω)}).toReal =
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
      ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(Fk f X Xδ tb P k) := by
  simp_rw [← core_real f X Xδ tb P hA1 hA2 hmeas N _ _ measurableSet_Ioc]
  rw [← partition f X Xδ tb P hmeas N (fun k => Set.Ioc (ε k) 1) (fun _ => measurableSet_Ioc)]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_Ioc]
  exact ⟨fun h => ⟨h, (viol_mem f X Xδ tb P hmeas _).2⟩, fun h => h.1⟩
