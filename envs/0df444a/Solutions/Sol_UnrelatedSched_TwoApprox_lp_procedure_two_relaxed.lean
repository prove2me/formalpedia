-- Prove2me | solution 1 for UnrelatedSched.TwoApprox.lp_procedure_two_relaxed
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:11:52.325363+00:00
-- url     : https://prove2.me/submissions/044b0c45-8223-4c7c-ade0-f2f9865eb3b1

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP
import Definitions.Def_UnrelatedSched_TwoApprox_Algorithm

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoApprox

lemma e57_load_le_makespan {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) (i : Fin m) :
    load (realTimes P) σ i ≤ makespan (realTimes P) σ :=
  le_ciSup (f := fun i => load (realTimes P) σ i) (Set.finite_range _).bddAbove i

theorem yes_core {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : ℝ)
    (σ : Fin n → Fin m) (hσ : makespan (realTimes P) σ ≤ d) :
    assignmentMatrix σ ∈ LPPolytope P (fun _ => d) d := by
  classical
  have hload : ∀ i, ∑ j, (P i j : ℝ) * assignmentMatrix σ i j = load (realTimes P) σ i := by
    intro i
    unfold load assignmentMatrix realTimes
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : σ j = i <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases h : σ j = i
    · exfalso
      have h1 : (P i j : ℝ) ≤ load (realTimes P) σ i := by
        unfold load realTimes
        apply Finset.single_le_sum (f := fun j => (P i j : ℝ)) (fun _ _ => by positivity)
        simp [h]
      have := e57_load_le_makespan P σ i
      linarith
    · simp [assignmentMatrix, h]
  · intro j
    simp [assignmentMatrix]
  · intro i
    rw [hload]
    exact (e57_load_le_makespan P σ i).trans hσ
  · intro i j
    unfold assignmentMatrix
    split_ifs <;> norm_num

theorem rounding_core {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (x : Matrix (Fin m) (Fin n) ℝ) (hx : LPFeasible P d t x)
    (σ : Fin n → Fin m) (hσ : SupportedOn x σ)
    (hfrac : ∀ i (j₁ j₂ : Fin n), σ j₁ = i → σ j₂ = i → x i j₁ < 1 → x i j₂ < 1 → j₁ = j₂) :
    ∀ i, load (realTimes P) σ i ≤ d i + t := by
  classical
  intro i
  set J := Finset.univ.filter (fun j => σ j = i) with hJ
  have hl : load (realTimes P) σ i = ∑ j ∈ J, (P i j : ℝ) := rfl
  rw [hl, ← Finset.sum_filter_add_sum_filter_not J (fun j => x i j < 1)]
  have hA : ∑ j ∈ J.filter (fun j => x i j < 1), (P i j : ℝ) ≤ t := by
    have h1 : ∀ j ∈ J.filter (fun j => x i j < 1), (P i j : ℝ) ≤ t := by
      intro j hj
      simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨hσj, _⟩ := hj
      have hpos := hσ j
      rw [hσj] at hpos
      by_contra hc
      push_neg at hc
      have := hx.zero_outside i j hc
      linarith
    have h2 : (J.filter (fun j => x i j < 1)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hfrac i a b ha.1 hb.1 ha.2 hb.2
    calc _ ≤ (J.filter (fun j => x i j < 1)).card • t := Finset.sum_le_card_nsmul _ _ _ h1
      _ ≤ 1 • t := nsmul_le_nsmul_left ht h2
      _ = t := one_nsmul t
  have hB : ∑ j ∈ J.filter (fun j => ¬ x i j < 1), (P i j : ℝ) ≤ d i := by
    have h1 : ∑ j ∈ J.filter (fun j => ¬ x i j < 1), (P i j : ℝ) ≤
        ∑ j ∈ J.filter (fun j => ¬ x i j < 1), (P i j : ℝ) * x i j := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_filter] at hj
      have := hj.2
      push_neg at this
      have hp : (0 : ℝ) ≤ P i j := by positivity
      nlinarith
    refine h1.trans (le_trans ?_ (hx.machine i))
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro j _ _
    exact mul_nonneg (by positivity) (hx.nonneg i j)
  linarith

lemma e57_ker {ι κ : Type*} [DecidableEq ι] (E : Finset ι) (K : Finset κ) (c : κ → ι → ℝ)
    (hlt : K.card < E.card) :
    ∃ y : ι → ℝ, (∃ e ∈ E, y e ≠ 0) ∧ (∀ e, e ∉ E → y e = 0) ∧
      ∀ k ∈ K, ∑ e ∈ E, c k e * y e = 0 := by
  classical
  let f : (↥E → ℝ) →ₗ[ℝ] (↥K → ℝ) :=
    LinearMap.pi (fun k : ↥K => ∑ e : ↥E, (c k e) • LinearMap.proj e)
  have hf : Module.finrank ℝ (↥K → ℝ) < Module.finrank ℝ (↥E → ℝ) := by
    simpa using hlt
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := f) hf
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 hker
  refine ⟨fun e => if h : e ∈ E then z ⟨e, h⟩ else 0, ?_, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    apply hz0
    funext e
    have := hcon e e.2
    simpa using this
  · intro e he; simp [he]
  · intro k hk
    have := congrFun (LinearMap.mem_ker.1 hz) ⟨k, hk⟩
    simp [f] at this
    rw [← Finset.sum_attach E]
    simpa using this

theorem pseudoforest_core {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ)
    (t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ) (hx : IsLPVertex P d t x) :
    IsPseudoforest (supportEdges x) := by
  classical
  intro S T
  by_contra hlt
  push_neg at hlt
  obtain ⟨hxQ, hxext⟩ := (mem_extremePoints.1 hx)
  have hxQ' : LPFeasible P d t x := hxQ
  let E : Finset (Fin m × Fin n) := (supportEdges x).filter fun e => e.1 ∈ S ∧ e.2 ∈ T
  have hEmem : ∀ e, e ∈ E ↔ 0 < x e.1 e.2 ∧ e.1 ∈ S ∧ e.2 ∈ T := by
    intro e; simp [E, supportEdges]
  let K : Finset (Fin n ⊕ Fin m) := T.disjSum S
  have hKcard : K.card < E.card := by
    have hlt' : S.card + T.card < E.card := hlt
    simp only [K, Finset.card_disjSum]; omega
  let c : Fin n ⊕ Fin m → (Fin m × Fin n) → ℝ := fun k e =>
    match k with
    | Sum.inl j => if e.2 = j then 1 else 0
    | Sum.inr i => if e.1 = i then (P i e.2 : ℝ) else 0
  obtain ⟨y, ⟨e0, he0, hy0⟩, hyout, hyK⟩ := e57_ker E K c hKcard
  have hsumE : ∀ g : Fin m × Fin n → ℝ, (∀ e, e ∉ E → g e = 0) →
      ∑ e ∈ E, g e = ∑ e, g e := by
    intro g hg
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he; exact hg e he
  have hcol : ∀ j ∈ T, ∑ i, y (i, j) = 0 := by
    intro j hj
    have := hyK (Sum.inl j) (by simp [K, hj])
    rw [hsumE _ (fun e he => by simp [hyout e he])] at this
    rw [Fintype.sum_prod_type] at this
    simpa [c] using this
  have hrow : ∀ i ∈ S, ∑ j, (P i j : ℝ) * y (i, j) = 0 := by
    intro i hi
    have := hyK (Sum.inr i) (by simp [K, hi])
    rw [hsumE _ (fun e he => by simp [hyout e he])] at this
    rw [Fintype.sum_prod_type] at this
    simpa [c] using this
  have hyE : ∀ i j, y (i, j) ≠ 0 → 0 < x i j ∧ i ∈ S ∧ j ∈ T := by
    intro i j h
    by_contra hc
    exact h (hyout _ (fun hm => hc ((hEmem _).1 hm)))
  have hEne : E.Nonempty := ⟨e0, he0⟩
  obtain ⟨δ, hδ, hδy⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ e ∈ E, δ * |y e| ≤ x e.1 e.2 := by
    refine ⟨E.inf' hEne (fun e => x e.1 e.2 / (|y e| + 1)), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro e he
      exact div_pos ((hEmem e).1 he).1 (by positivity)
    · intro e he
      have h1 := Finset.inf'_le (fun e => x e.1 e.2 / (|y e| + 1)) he
      have hxe : 0 < x e.1 e.2 := ((hEmem e).1 he).1
      calc _ ≤ x e.1 e.2 / (|y e| + 1) * |y e| := by
            exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ x e.1 e.2 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [abs_nonneg (y e)]
  have key : ∀ s : ℝ, |s| ≤ δ →
      LPFeasible P d t (Matrix.of fun i j => x i j + s * y (i, j)) := by
    intro s hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hij
      have h0 := hxQ'.zero_outside i j hij
      have : y (i, j) = 0 := by
        apply hyout
        intro hm
        have := ((hEmem _).1 hm).1
        simp only at this
        linarith
      simp [h0, this]
    · intro j
      have h0 := hxQ'.job j
      simp only [Matrix.of_apply, Finset.sum_add_distrib, ← Finset.mul_sum]
      by_cases hjT : j ∈ T
      · rw [hcol j hjT, h0]; ring
      · have : ∀ i, y (i, j) = 0 := by
          intro i
          apply hyout
          intro hm
          exact hjT ((hEmem _).1 hm).2.2
        simp [this, h0]
    · intro i
      have h0 := hxQ'.machine i
      simp only [Matrix.of_apply, mul_add, Finset.sum_add_distrib]
      have : ∑ j, (P i j : ℝ) * (s * y (i, j)) = 0 := by
        by_cases him : i ∈ S
        · have := hrow i him
          calc ∑ j, (P i j : ℝ) * (s * y (i, j)) = s * ∑ j, (P i j : ℝ) * y (i, j) := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
            _ = 0 := by rw [this]; ring
        · have : ∀ j, y (i, j) = 0 := by
            intro j
            apply hyout
            intro hm
            exact him ((hEmem _).1 hm).2.1
          simp [this]
      rw [this, add_zero]; exact h0
    · intro i j
      by_cases hm : (i, j) ∈ E
      · have h1 := hδy _ hm
        simp only at h1
        have h2 : |s * y (i, j)| ≤ x i j := by
          rw [abs_mul]
          calc |s| * |y (i, j)| ≤ δ * |y (i, j)| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
            _ ≤ _ := h1
        have := neg_abs_le (s * y (i, j))
        simp only [Matrix.of_apply]
        linarith
      · simp [hyout _ hm, hxQ'.nonneg i j]
  have hpos := key δ (by rw [abs_of_pos hδ])
  have hneg := key (-δ) (by rw [abs_neg, abs_of_pos hδ])
  have hseg : x ∈ openSegment ℝ (Matrix.of fun i j => x i j + δ * y (i, j))
      (Matrix.of fun i j => x i j + (-δ) * y (i, j)) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    ring
  have := (hxext _ hpos _ hneg hseg).1
  have h3 := congrFun (congrFun this e0.1) e0.2
  simp only [Matrix.of_apply] at h3
  have : δ * y (e0.1, e0.2) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hδ.ne'
  exact hy0 this

theorem matching_core {m n : ℕ} (hm : 0 < m)
    (E : Finset (Fin m × Fin n)) (hE : IsPseudoforest E)
    (T : Finset (Fin n)) (hdeg : ∀ j ∈ T, 2 ≤ (E.filter fun e => e.2 = j).card) :
    ∃ f : Fin n → Fin m, (∀ j ∈ T, (f j, j) ∈ E) ∧ Set.InjOn f (T : Set (Fin n)) := by
  classical
  let nb : Fin n → Finset (Fin m) := fun j => (E.filter fun e => e.2 = j).image Prod.fst
  have hnb : ∀ j i, i ∈ nb j ↔ (i, j) ∈ E := by
    intro j i
    simp only [nb, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨he, hej⟩, rfl⟩
      rw [← hej]; exact he
    · intro h; exact ⟨(i, j), ⟨h, rfl⟩, rfl⟩
  have hhall : ∀ s : Finset ↥T, s.card ≤ (s.biUnion (fun j => nb j.1)).card := by
    intro s
    set S' : Finset (Fin n) := s.map (Function.Embedding.subtype _) with hS'
    set M' : Finset (Fin m) := s.biUnion (fun j => nb j.1) with hM'
    have hS'c : S'.card = s.card := by simp [hS']
    have hS'T : ∀ j ∈ S', j ∈ T := by
      intro j hj
      obtain ⟨j', _, rfl⟩ := Finset.mem_map.1 hj
      exact j'.2
    let E' := E.filter fun e => e.1 ∈ M' ∧ e.2 ∈ S'
    have hmem : ∀ e, e ∈ E' ↔ e ∈ E ∧ e.1 ∈ M' ∧ e.2 ∈ S' := by intro e; simp [E']
    have h1 : E'.card = ∑ j ∈ S', (E'.filter fun e => e.2 = j).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun e he => ((hmem e).1 he).2.2)
    have h2 : ∀ j ∈ S', 2 ≤ (E'.filter fun e => e.2 = j).card := by
      intro j hj
      refine (hdeg j (hS'T j hj)).trans (Finset.card_le_card ?_)
      intro e he
      simp only [Finset.mem_filter] at he ⊢
      obtain ⟨heE, hej⟩ := he
      refine ⟨(hmem e).2 ⟨heE, ?_, ?_⟩, hej⟩
      · obtain ⟨j', hj's, rfl⟩ := Finset.mem_map.1 hj
        refine Finset.mem_biUnion.2 ⟨j', hj's, ?_⟩
        rw [hnb]
        have h5 : (e.1, e.2) ∈ E := heE
        rw [hej] at h5
        exact h5
      · rw [hej]; exact hj
    have h3 : 2 * S'.card ≤ E'.card := by
      rw [h1]
      calc 2 * S'.card = ∑ j ∈ S', 2 := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum h2
    have h4 : E'.card ≤ M'.card + S'.card := hE M' S'
    omega
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun j : ↥T => nb j.1)).1 hhall
  refine ⟨fun j => if h : j ∈ T then f ⟨j, h⟩ else ⟨0, hm⟩, ?_, ?_⟩
  · intro j hj
    simp only [hj, dif_pos]
    exact (hnb j _).1 (hfmem ⟨j, hj⟩)
  · intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only [ha, hb, dif_pos] at hab
    have := hfinj hab
    simpa using this


theorem theorem1_core {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (x : Matrix (Fin m) (Fin n) ℝ) (hx : IsLPVertex P d t x) :
    ∃ σ : Fin n → Fin m, SupportedOn x σ ∧ IPFeasible P d t σ := by
  classical
  have hxQ : LPFeasible P d t x := (mem_extremePoints.1 hx).1
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    have hn : IsEmpty (Fin n) := ⟨fun j => by have := hxQ.job j; simp at this⟩
    exact ⟨fun j => (hn.false j).elim, fun j => (hn.false j).elim, fun j => (hn.false j).elim, fun i => i.elim0⟩
  have hE := pseudoforest_core P d t x hx
  let F : Finset (Fin n) := Finset.univ.filter (fun j => ∀ i, x i j ≠ 1)
  have hFmem : ∀ j, j ∈ F ↔ ∀ i, x i j ≠ 1 := by intro j; simp [F]
  have hdeg : ∀ j ∈ F, 2 ≤ ((supportEdges x).filter fun e => e.2 = j).card := by
    intro j hj
    have hj1 := (hFmem j).1 hj
    let nb : Finset (Fin m) := Finset.univ.filter (fun i => 0 < x i j)
    have hmemnb : ∀ i, i ∈ nb ↔ 0 < x i j := by intro i; simp [nb]
    have hnb2 : 2 ≤ nb.card := by
      by_contra hc
      push_neg at hc
      have hsum := hxQ.job j
      have hne : nb.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have : ∀ i, x i j = 0 := by
          intro i
          by_contra h0
          have : i ∈ nb := (hmemnb i).2 (lt_of_le_of_ne (hxQ.nonneg i j) (Ne.symm h0))
          rw [hne] at this; simp at this
        simp [this] at hsum
      obtain ⟨i0, hi0⟩ := hne
      have hcard : nb.card = 1 := by
        have := Finset.card_pos.2 ⟨i0, hi0⟩; omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
      have : ∑ i, x i j = x a j := by
        rw [Finset.sum_eq_single a]
        · intro b _ hb
          by_contra h0
          have : b ∈ nb := (hmemnb b).2 (lt_of_le_of_ne (hxQ.nonneg b j) (Ne.symm h0))
          rw [ha] at this; simp at this; exact hb this
        · simp
      exact hj1 a (by rw [← this]; exact hsum)
    refine hnb2.trans ?_
    apply Finset.card_le_card_of_injOn (fun i => (i, j))
    · intro i hi
      simp only [Finset.mem_coe, hmemnb] at hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq, supportEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨hi, trivial⟩
    · intro a _ b _ h; simpa using h
  obtain ⟨f, hfE, hfinj⟩ := matching_core hm (supportEdges x) hE F hdeg
  have hint : ∀ j, j ∉ F → ∃ i, x i j = 1 := by
    intro j hj
    by_contra hc
    push_neg at hc
    exact hj ((hFmem j).2 hc)
  let σ : Fin n → Fin m := fun j => if h : j ∈ F then f j else (hint j h).choose
  have hσF : ∀ j, j ∈ F → σ j = f j := by intro j h; simp [σ, h]
  have hσI : ∀ j, (h : j ∉ F) → x (σ j) j = 1 := by
    intro j h
    simp only [σ, h, dif_neg, not_false_eq_true]
    exact (hint j h).choose_spec
  have hsup : SupportedOn x σ := by
    intro j
    by_cases h : j ∈ F
    · rw [hσF j h]
      have := hfE j h
      simpa [supportEdges] using this
    · rw [hσI j h]; norm_num
  refine ⟨σ, hsup, fun j => ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have := hxQ.zero_outside (σ j) j hc
    have := hsup j
    linarith
  · refine rounding_core P d t ht x hxQ σ hsup ?_
    intro i j1 j2 h1 h2 hl1 hl2
    have hj1 : j1 ∈ F := by
      by_contra h
      have := hσI j1 h
      rw [h1] at this; linarith
    have hj2 : j2 ∈ F := by
      by_contra h
      have := hσI j2 h
      rw [h2] at this; linarith
    rw [hσF j1 hj1] at h1
    rw [hσF j2 hj2] at h2
    exact hfinj (Finset.mem_coe.2 hj1) (Finset.mem_coe.2 hj2) (h1.trans h2.symm)


lemma e57_makespan_eq {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) :
    makespan (realTimes P) σ = ((natMakespan P σ : ℕ) : ℝ) := by
  classical
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · simp [makespan, natMakespan]
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin m))
      Finset.univ_nonempty (fun i => natLoad P σ i)
    have hload : ∀ i, load (realTimes P) σ i = ((natLoad P σ i : ℕ) : ℝ) := by
      intro i
      simp [load, natLoad, realTimes]
    have hN : natMakespan P σ = natLoad P σ i0 := hi0
    apply le_antisymm
    · apply Real.iSup_le _ (by positivity)
      intro i
      rw [hload]
      have : natLoad P σ i ≤ natMakespan P σ :=
        Finset.le_sup (f := fun i => natLoad P σ i) (Finset.mem_univ i)
      exact_mod_cast this
    · rw [hN, ← hload]
      exact e57_load_le_makespan P σ i0

lemma e57_loop {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (D : DecisionProcedure m n) (M : ℕ)
    (hsome : ∀ d σ, D d = some σ → (natMakespan P σ : ℝ) ≤ ρ * (d : ℝ))
    (hnone : ∀ d, D d = none → d < M) :
    ∀ (k l u : ℕ) (best : Fin n → Fin m), u - l ≤ k → l ≤ M →
      (natMakespan P best : ℝ) ≤ ρ * (u : ℝ) →
      (natMakespan P (searchLoop P D l u best) : ℝ) ≤ ρ * (M : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro l u best hk hl hb
    have hnl : ¬ l < u := by omega
    rw [searchLoop, dif_neg hnl]
    refine hb.trans ?_
    have : (u : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : u ≤ M)
    nlinarith
  | succ k ih =>
    intro l u best hk hl hb
    by_cases hlu : l < u
    · rw [searchLoop, dif_pos hlu]
      rcases hDd : D ((u + l) / 2) with _ | σ
      · simp only [hDd]
        have := hnone _ hDd
        exact ih _ _ _ (by omega) (by omega) hb
      · simp only [hDd]
        apply ih _ _ _ (by omega) hl
        have h1 := hsome _ σ hDd
        split_ifs with hc
        · exact h1
        · push_neg at hc
          have : (natMakespan P best : ℝ) ≤ natMakespan P σ := by exact_mod_cast hc
          linarith
    · rw [searchLoop, dif_neg hlu]
      refine hb.trans ?_
      have : (u : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : u ≤ M)
      nlinarith

lemma e57_greedy_le {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) :
    natMakespan P (greedySchedule P hm) ≤ m * natMakespan P σ := by
  classical
  have hg : ∀ j, ∀ i', P (greedySchedule P hm j) j ≤ P i' j := by
    intro j
    have := Finset.min'_mem (Finset.univ.filter (fun i : Fin m => ∀ i', P i j ≤ P i' j)) (by
      obtain ⟨i, -, hi⟩ :=
        Finset.univ.exists_min_image (fun i => P i j) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      exact ⟨i, by simpa using hi⟩)
    exact (Finset.mem_filter.1 this).2
  have h1 : natMakespan P (greedySchedule P hm) ≤ ∑ j, P (greedySchedule P hm j) j := by
    unfold natMakespan
    apply Finset.sup_le
    intro i _
    unfold natLoad
    calc ∑ j ∈ Finset.univ.filter (fun j => greedySchedule P hm j = i), P i j
        = ∑ j ∈ Finset.univ.filter (fun j => greedySchedule P hm j = i),
            P (greedySchedule P hm j) j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [(Finset.mem_filter.1 hj).2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
  have h2 : ∑ j, P (greedySchedule P hm j) j ≤ ∑ j, P (σ j) j :=
    Finset.sum_le_sum (fun j _ => hg j (σ j))
  have h3 : ∑ j, P (σ j) j = ∑ i, natLoad P σ i := by
    unfold natLoad
    rw [← Finset.sum_fiberwise Finset.univ σ (fun j => P (σ j) j)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.1 hj).2]
  have h4 : ∑ i, natLoad P σ i ≤ ∑ _i : Fin m, natMakespan P σ := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.le_sup (f := fun i => natLoad P σ i) (Finset.mem_univ i)
  have h5 : ∑ _i : Fin m, natMakespan P σ = m * natMakespan P σ := by simp
  omega

theorem lemma1_core {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (hP : ∀ i j, 0 < P i j)
    (ρ : ℝ) (D : DecisionProcedure m n) (hD : IsRelaxedDecisionProcedure P ρ D)
    (σopt : Fin n → Fin m) (hopt : IsOptimalSchedule (realTimes P) σopt) :
    makespan (realTimes P) (binarySearch P hm D) ≤ ρ * makespan (realTimes P) σopt := by
  set M := natMakespan P σopt with hM
  have hMeq : makespan (realTimes P) σopt = (M : ℝ) := e57_makespan_eq P σopt
  have hsome : ∀ d σ, D d = some σ → (natMakespan P σ : ℝ) ≤ ρ * (d : ℝ) := by
    intro d σ h
    have := (hD d).1 σ h
    rwa [e57_makespan_eq] at this
  have hnone : ∀ d, D d = none → d < M := by
    intro d hd
    have := (hD d).2 hd σopt
    rw [hMeq] at this
    exact_mod_cast this
  have hDM : ∀ d, M ≤ d → ∃ σ, D d = some σ := by
    intro d hd
    rcases h : D d with _ | σ
    · exact absurd (hnone d h) (by omega)
    · exact ⟨σ, rfl⟩
  have hρ : 0 ≤ ρ := by
    obtain ⟨σ, hσ⟩ := hDM (M + 1) (by omega)
    have h1 := hsome _ σ hσ
    have h2 : (0 : ℝ) ≤ natMakespan P σ := by positivity
    by_contra hneg
    push_neg at hneg
    have : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  set T := natMakespan P (greedySchedule P hm) with hT
  have hTM : T ≤ m * M := e57_greedy_le hm P σopt
  have hinit : (T : ℝ) ≤ ρ * (T : ℝ) := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · rw [h0]; simp
    · have hMpos : 0 < M := by
        rcases Nat.eq_zero_or_pos M with h | h
        · rw [h] at hTM; omega
        · exact h
      obtain ⟨σ, hσ⟩ := hDM M le_rfl
      have h1 := hsome _ σ hσ
      have h2 := hopt σ
      rw [hMeq, e57_makespan_eq] at h2
      have h3 : (M : ℝ) ≤ ρ * M := le_trans h2 h1
      have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
      have hρ1 : 1 ≤ ρ := by
        by_contra hlt
        push_neg at hlt
        nlinarith
      have : (0 : ℝ) ≤ T := by positivity
      nlinarith
  rw [hMeq, e57_makespan_eq]
  unfold binarySearch
  apply e57_loop P ρ hρ D M hsome hnone
  · exact le_refl _
  · rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hm)]
    have h2 : (T : ℚ) ≤ ((m * M : ℕ) : ℚ) := by exact_mod_cast hTM
    push_cast at h2
    linarith
  · exact hinit

theorem lpproc_core {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (D : DecisionProcedure m n) (hD : IsLPRoundingProcedure P V D) :
    IsRelaxedDecisionProcedure P 2 D := by
  intro d
  refine ⟨?_, ?_⟩
  · intro σ hσ
    obtain ⟨x, _, _, hip⟩ := (hD d).2 σ hσ
    apply Real.iSup_le _ (by positivity)
    intro i
    have := hip.2 i
    linarith
  · intro hnone τ
    have hVn : V d = none := ((hD d).1).1 hnone
    have hemp := (hV d).2 hVn
    by_contra hle
    push_neg at hle
    have := yes_core P (d : ℝ) τ hle
    rw [hemp] at this
    exact this

theorem theorem2_core {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (hP : ∀ i j, 0 < P i j)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (σopt : Fin n → Fin m) (hopt : IsOptimalSchedule (realTimes P) σopt) :
    (∃ D : DecisionProcedure m n, IsLPRoundingProcedure P V D) ∧
      ∀ D : DecisionProcedure m n, IsLPRoundingProcedure P V D →
        makespan (realTimes P) (binarySearch P hm D) ≤ 2 * makespan (realTimes P) σopt := by
  refine ⟨?_, fun D hD => lemma1_core hm P hP 2 D (lpproc_core P V hV D hD) σopt hopt⟩
  have key : ∀ d : ℕ, ∃ o : Option (Fin n → Fin m), (o = none ↔ V d = none) ∧
      ∀ σ, o = some σ → ∃ x, V d = some x ∧ SupportedOn x σ ∧
        IPFeasible P (fun _ => (d : ℝ)) d σ := by
    intro d
    rcases hVd : V d with _ | x
    · exact ⟨none, ⟨fun _ => rfl, fun _ => rfl⟩, fun σ hσ => by simp at hσ⟩
    · obtain ⟨σ, hs, hi⟩ := theorem1_core P (fun _ => (d : ℝ)) (d : ℝ) (by positivity) x
        ((hV d).1 x hVd)
      exact ⟨some σ, ⟨by simp, by simp⟩, fun σ' hσ' => by
        obtain rfl : σ = σ' := by simpa using hσ'
        exact ⟨x, rfl, hs, hi⟩⟩
  choose D hD using key
  exact ⟨D, fun d => ⟨(hD d).1, (hD d).2⟩⟩

end UnrelatedSched.TwoApprox

open UnrelatedSched.TwoApprox


theorem solution {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (D : DecisionProcedure m n) (hD : IsLPRoundingProcedure P V D) :
    IsRelaxedDecisionProcedure P 2 D := by
  exact lpproc_core P V hV D hD
