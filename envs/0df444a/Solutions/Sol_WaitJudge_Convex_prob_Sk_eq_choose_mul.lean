-- Prove2me | solution 1 for WaitJudge.Convex.prob_Sk_eq_choose_mul
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:37:10.91011+00:00
-- url     : https://prove2.me/submissions/2d8379dd-97e1-46be-90f7-ba7381041bbe

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization WaitJudge.Convex

theorem solution {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hmeas : MeasurabilityPins c X Xδ tb) (ε : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    (Measure.pi fun _ : Fin N => P) {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k} =
      ((N.choose k : ℕ) : ENNReal) * (Measure.pi fun _ : Fin N => P)
        {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k ∧
          ∀ i : Fin N, i.val < k → i ∈ supportSet c X Xδ tb ω} := by
  classical
  set μ := Measure.pi fun _ : Fin N => P with hμ
  -- permutation invariance of the scenario program
  have hfeas : ∀ (σ : Equiv.Perm (Fin N)) (ω : Fin N → Δ),
      feasibleOn X Xδ (fun i => ω (σ i)) Finset.univ = feasibleOn X Xδ ω Finset.univ := by
    intro σ ω; ext x
    simp only [feasibleOn, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_univ, true_implies]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, fun j => by simpa using h (σ.symm j)⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, fun j => h (σ j)⟩
  have hfeas' : ∀ (σ : Equiv.Perm (Fin N)) (ω : Fin N → Δ) (i : Fin N),
      feasibleOn X Xδ (fun i => ω (σ i)) (Finset.univ.erase i) =
        feasibleOn X Xδ ω (Finset.univ.erase (σ i)) := by
    intro σ ω i; ext x
    simp only [feasibleOn, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_erase,
      Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, fun j hj => ?_⟩
      have : σ.symm j ≠ i := fun h' => hj (by rw [← h']; simp)
      simpa using h (σ.symm j) this
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun j hj => h (σ j) (fun h' => hj (σ.injective h'))⟩
  have hx : ∀ (σ : Equiv.Perm (Fin N)) (ω : Fin N → Δ),
      xstar c X Xδ tb (fun i => ω (σ i)) = xstar c X Xδ tb ω := by
    intro σ ω; simp only [xstar, hfeas]
  have hT : ∀ (σ : Equiv.Perm (Fin N)) (ω : Fin N → Δ) (i : Fin N),
      i ∈ supportSet c X Xδ tb (fun i => ω (σ i)) ↔ σ i ∈ supportSet c X Xδ tb ω := by
    intro σ ω i
    simp only [supportSet, IsSupport, Finset.mem_filter, Finset.mem_univ, true_and, hfeas', hfeas]
  -- measurability
  have hviol : Measurable (fun x : E d => violation P Xδ x) := by
    have hs : MeasurableSet {q : E d × Δ | q.1 ∉ Xδ q.2} := hmeas.1.compl
    exact (measurable_measure_prodMk_left (ν := P) hs).ennreal_toReal
  have hV : Measurable (fun ω : Fin N → Δ => violation P Xδ (xstar c X Xδ tb ω)) :=
    hviol.comp (hmeas.2 N)
  have hsupp : ∀ i : Fin N, MeasurableSet {ω : Fin N → Δ | i ∈ supportSet c X Xδ tb ω} := by
    intro i
    obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by have := i.isLt; omega⟩
    subst hm
    have hF : ∀ ω : Fin (m + 1) → Δ, feasibleOn X Xδ ω (Finset.univ.erase i) =
        feasibleOn X Xδ (fun j => ω (i.succAbove j)) Finset.univ := by
      intro ω
      ext x
      simp only [feasibleOn, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_erase,
        Finset.mem_univ, and_true, true_implies]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨hx, fun j => h _ (Fin.succAbove_ne i j)⟩
      · rintro ⟨hx, h⟩; refine ⟨hx, fun j hj => ?_⟩
        obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        exact h j'
    have hm1 : Measurable (fun ω : Fin (m + 1) → Δ =>
        sol c tb (feasibleOn X Xδ ω (Finset.univ.erase i))) := by
      simp_rw [hF]
      exact (hmeas.2 m).comp (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
    have : {ω : Fin (m + 1) → Δ | i ∈ supportSet c X Xδ tb ω} =
        {ω | sol c tb (feasibleOn X Xδ ω (Finset.univ.erase i)) = xstar c X Xδ tb ω}ᶜ := by
      ext ω; simp [supportSet, IsSupport, xstar]
    rw [this]
    exact (measurableSet_eq_fun hm1 (hmeas.2 (m + 1))).compl
  have hTmeas : ∀ I : Finset (Fin N), MeasurableSet {ω : Fin N → Δ | supportSet c X Xδ tb ω = I} := by
    intro I
    have : {ω : Fin N → Δ | supportSet c X Xδ tb ω = I} =
        ⋂ i : Fin N, {ω | i ∈ supportSet c X Xδ tb ω ↔ i ∈ I} := by
      ext ω; simp [Finset.ext_iff]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hi : i ∈ I
    · simpa [hi] using hsupp i
    · have : {ω : Fin N → Δ | i ∈ supportSet c X Xδ tb ω ↔ i ∈ I} =
          {ω : Fin N → Δ | i ∈ supportSet c X Xδ tb ω}ᶜ := by
        ext ω; simp [hi]
      rw [this]; exact (hsupp i).compl
  -- the pieces
  let piece : Finset (Fin N) → Set (Fin N → Δ) := fun I =>
    {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ supportSet c X Xδ tb ω = I}
  have hpiece_meas : ∀ I, MeasurableSet (piece I) := fun I =>
    (measurableSet_lt measurable_const hV).inter (hTmeas I)
  let I₀ : Finset (Fin N) := Finset.univ.filter (fun i => i.val < k)
  have hI₀card : I₀.card = k := by
    have : I₀ = (Finset.range k).attachFin (fun i hi => by simp at hi; omega) := by
      ext i; simp [I₀]
    rw [this, Finset.card_attachFin, Finset.card_range]
  -- (i) S_k is the disjoint union of the pieces
  have hsplit : {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k} =
      ⋃ I ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)), piece I := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, exists_prop, piece,
      sstar, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, h2, h1, rfl⟩
    · rintro ⟨I, hI, h1, rfl⟩; exact ⟨h1, hI⟩
  -- (ii) all pieces have the same probability
  have hsame : ∀ I ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
      μ (piece I) = μ (piece I₀) := by
    intro I hI
    rw [Finset.mem_powersetCard] at hI
    have hcard : Fintype.card {x // x ∈ I₀} = Fintype.card {x // x ∈ I} := by
      simp [hI₀card, hI.2]
    let e : {x // x ∈ I₀} ≃ {x // x ∈ I} := Fintype.equivOfCardEq hcard
    let σ : Equiv.Perm (Fin N) := e.extendSubtype
    have hσ : ∀ x, σ x ∈ I ↔ x ∈ I₀ := by
      intro x
      by_cases hx0 : x ∈ I₀
      · exact ⟨fun _ => hx0, fun _ => Equiv.extendSubtype_mem e x hx0⟩
      · exact ⟨fun h => absurd h (Equiv.extendSubtype_not_mem e x hx0), fun h => absurd h hx0⟩
    have hmp : MeasurePreserving (fun ω : Fin N → Δ => fun i => ω (σ i)) μ μ := by
      have := measurePreserving_piCongrLeft (fun _ : Fin N => P) σ.symm
      convert this using 1
      funext ω i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    have hpre : (fun ω : Fin N → Δ => fun i => ω (σ i)) ⁻¹' piece I₀ = piece I := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, piece, hx]
      apply and_congr_right; intro _
      constructor
      · intro h
        ext j
        have := (hT σ ω (σ.symm j))
        rw [h] at this
        simp only [Equiv.apply_symm_apply] at this
        rw [← this, ← hσ (σ.symm j)]; simp
      · intro h
        ext i
        rw [hT σ ω i, h, hσ]
    rw [← hpre, hmp.measure_preimage (hpiece_meas I₀).nullMeasurableSet]
  -- (iii) A is the piece of the first k indices
  have hA : {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k ∧
      ∀ i : Fin N, i.val < k → i ∈ supportSet c X Xδ tb ω} = piece I₀ := by
    ext ω
    simp only [Set.mem_setOf_eq, piece, sstar]
    apply and_congr_right; intro _
    constructor
    · rintro ⟨h1, h2⟩
      have hsub : I₀ ⊆ supportSet c X Xδ tb ω := by
        intro i hi; exact h2 i (by simpa [I₀] using hi)
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [h1, hI₀card])).symm
    · intro h
      rw [h]
      exact ⟨hI₀card, fun i hi => by simp [I₀, hi]⟩
  rw [hsplit, measure_biUnion_finset, Finset.sum_congr rfl hsame, Finset.sum_const,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, hA, nsmul_eq_mul]
  · intro I _ J _ hIJ
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    exact hIJ (h1.symm.trans h2)
  · intro I _; exact hpiece_meas I
