-- Prove2me | solution 1 for UnrelatedSched.FixedMachines.relaxed_procedure
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:39:50.519778+00:00
-- url     : https://prove2.me/submissions/3a476693-c9f1-471e-8b67-c341edaf1b50

import Mathlib
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment
import Definitions.Def_UnrelatedSched_FixedMachines_BinarySearch



namespace UnrelatedSched.FixedMachines

open MatousekLP.Scheduling

lemma e54_ker {ι κ : Type*} [DecidableEq ι] (E : Finset ι) (K : Finset κ) (c : κ → ι → ℝ)
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


lemma e54_hall_count {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (R : Set (Fin n)) (dl : Fin m → ℝ)
    (t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ) (hx : x ∈ Set.extremePoints ℝ (DeadlineLP P R dl t))
    (S : Finset (Fin n)) (hSR : ∀ j ∈ S, j ∈ R)
    (hS2 : ∀ j ∈ S, 2 ≤ (Finset.univ.filter (fun i => 0 < x i j)).card) :
    S.card ≤ (S.biUnion (fun j => Finset.univ.filter (fun i => 0 < x i j))).card := by
  classical
  by_contra hlt
  push_neg at hlt
  set M' := S.biUnion (fun j => Finset.univ.filter (fun i => 0 < x i j)) with hM'
  obtain ⟨hxQ, hxext⟩ := (mem_extremePoints.1 hx)
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hxQ
  let E : Finset (Fin m × Fin n) := (Finset.univ ×ˢ S).filter (fun e => 0 < x e.1 e.2)
  have hEmem : ∀ e, e ∈ E ↔ e.2 ∈ S ∧ 0 < x e.1 e.2 := by
    intro e; simp [E]
  have hEcard : 2 * S.card ≤ E.card := by
    have h1 : E.card = ∑ j ∈ S, (E.filter (fun e => e.2 = j)).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun e he => ((hEmem e).1 he).1)
    have h2 : ∀ j ∈ S, 2 ≤ (E.filter (fun e => e.2 = j)).card := by
      intro j hj
      refine (hS2 j hj).trans ?_
      apply Finset.card_le_card_of_injOn (fun i => (i, j))
      · intro i hi
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨(hEmem _).2 ⟨hj, hi⟩, trivial⟩
      · intro a _ b _ h; simpa using h
    rw [h1]
    calc 2 * S.card = ∑ j ∈ S, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum h2
  let K : Finset (Fin n ⊕ Fin m) := S.disjSum M'
  have hKcard : K.card < E.card := by
    simp only [K, Finset.card_disjSum]; omega
  let c : Fin n ⊕ Fin m → (Fin m × Fin n) → ℝ := fun k e =>
    match k with
    | Sum.inl j => if e.2 = j then 1 else 0
    | Sum.inr i => if e.1 = i then (P i e.2 : ℝ) else 0
  obtain ⟨y, ⟨e0, he0, hy0⟩, hyout, hyK⟩ := e54_ker E K c hKcard
  have hsumE : ∀ g : Fin m × Fin n → ℝ, (∀ e, e ∉ E → g e = 0) →
      ∑ e ∈ E, g e = ∑ e, g e := by
    intro g hg
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he; exact hg e he
  have hcol : ∀ j ∈ S, ∑ i, y (i, j) = 0 := by
    intro j hj
    have := hyK (Sum.inl j) (by simp [K, hj])
    rw [hsumE _ (fun e he => by simp [hyout e he])] at this
    rw [Fintype.sum_prod_type] at this
    simpa [c] using this
  have hrow : ∀ i ∈ M', ∑ j, (P i j : ℝ) * y (i, j) = 0 := by
    intro i hi
    have := hyK (Sum.inr i) (by simp [K, hi])
    rw [hsumE _ (fun e he => by simp [hyout e he])] at this
    rw [Fintype.sum_prod_type] at this
    simpa [c] using this
  -- support facts
  have hyE : ∀ i j, y (i, j) ≠ 0 → j ∈ S ∧ 0 < x i j := by
    intro i j h
    by_contra hc
    exact h (hyout _ (fun hm => hc ((hEmem _).1 hm)))
  have hrowout : ∀ i, i ∉ M' → ∀ j, y (i, j) = 0 := by
    intro i hi j
    by_contra h
    obtain ⟨hjS, hxp⟩ := hyE i j h
    exact hi (Finset.mem_biUnion.2 ⟨j, hjS, by simp [hxp]⟩)
  -- step size
  have hEne : E.Nonempty := ⟨e0, he0⟩
  obtain ⟨δ, hδ, hδy⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ e ∈ E, δ * |y e| ≤ x e.1 e.2 := by
    refine ⟨E.inf' hEne (fun e => x e.1 e.2 / (|y e| + 1)), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro e he
      exact div_pos ((hEmem e).1 he).2 (by positivity)
    · intro e he
      have h1 := Finset.inf'_le (fun e => x e.1 e.2 / (|y e| + 1)) he
      have hxe : 0 < x e.1 e.2 := ((hEmem e).1 he).2
      calc _ ≤ x e.1 e.2 / (|y e| + 1) * |y e| := by
            exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ x e.1 e.2 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [abs_nonneg (y e)]
  have key : ∀ s : ℝ, |s| ≤ δ →
      (Matrix.of fun i j => x i j + s * y (i, j)) ∈ DeadlineLP P R dl t := by
    intro s hs
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
      · simp [hyout _ hm, hx1 i j]
    · intro i j hij
      have h0 := hx2 i j hij
      have : y (i, j) = 0 := by
        apply hyout
        intro hm
        have := ((hEmem _).1 hm).2
        simp only at this
        linarith
      simp [h0, this]
    · intro i j hj
      have h0 := hx3 i j hj
      have : y (i, j) = 0 := by
        apply hyout
        intro hm
        exact hj (hSR _ ((hEmem _).1 hm).1)
      simp [h0, this]
    · intro j hj
      have h0 := hx4 j hj
      simp only [Matrix.of_apply, Finset.sum_add_distrib, ← Finset.mul_sum]
      by_cases hjS : j ∈ S
      · rw [hcol j hjS, h0]; ring
      · have : ∀ i, y (i, j) = 0 := by
          intro i
          apply hyout
          intro hm
          exact hjS ((hEmem _).1 hm).1
        simp [this, h0]
    · intro i
      have h0 := hx5 i
      simp only [Matrix.of_apply, mul_add, Finset.sum_add_distrib]
      have : ∑ j, (P i j : ℝ) * (s * y (i, j)) = 0 := by
        by_cases him : i ∈ M'
        · have := hrow i him
          calc ∑ j, (P i j : ℝ) * (s * y (i, j)) = s * ∑ j, (P i j : ℝ) * y (i, j) := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
            _ = 0 := by rw [this]; ring
        · simp [hrowout i him]
      rw [this, add_zero]; exact h0
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


open Classical in
lemma e54_round {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (R : Set (Fin n)) (dl : Fin m → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (x : Matrix (Fin m) (Fin n) ℝ)
    (hx : x ∈ Set.extremePoints ℝ (DeadlineLP P R dl t)) (τ0 : Fin n → Fin m) :
    ∃ τ : Fin n → Fin m, (∀ j, j ∉ R → τ j = τ0 j) ∧ (∀ j, j ∈ R → 0 < x (τ j) j) ∧
      ∀ i, ∑ j ∈ Finset.univ.filter (fun j => j ∈ R ∧ τ j = i), (P i j : ℝ) ≤ dl i + t := by
  classical
  have hxQ := (mem_extremePoints.1 hx).1
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hxQ
  let nb : Fin n → Finset (Fin m) := fun j => Finset.univ.filter (fun i => 0 < x i j)
  let F : Finset (Fin n) := Finset.univ.filter (fun j => j ∈ R ∧ ∀ i, x i j ≠ 1)
  have hFmem : ∀ j, j ∈ F ↔ j ∈ R ∧ ∀ i, x i j ≠ 1 := by intro j; simp [F]
  have hnb2 : ∀ j ∈ F, 2 ≤ (nb j).card := by
    intro j hj
    obtain ⟨hjR, hj1⟩ := (hFmem j).1 hj
    by_contra hc
    push_neg at hc
    have hsum := hx4 j hjR
    have hne : (nb j).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : ∀ i, x i j = 0 := by
        intro i
        by_contra h0
        have : i ∈ nb j := by
          simp only [nb, Finset.mem_filter, Finset.mem_univ, true_and]
          exact lt_of_le_of_ne (hx1 i j) (Ne.symm h0)
        rw [hne] at this; simp at this
      simp [this] at hsum
    obtain ⟨i0, hi0⟩ := hne
    have hcard : (nb j).card = 1 := by
      have := Finset.card_pos.2 ⟨i0, hi0⟩; omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
    have : ∑ i, x i j = x a j := by
      rw [Finset.sum_eq_single a]
      · intro b _ hb
        by_contra h0
        have : b ∈ nb j := by
          simp only [nb, Finset.mem_filter, Finset.mem_univ, true_and]
          exact lt_of_le_of_ne (hx1 b j) (Ne.symm h0)
        rw [ha] at this; simp at this; exact hb this
      · simp
    exact hj1 a (by rw [← this]; exact hsum)
  have hhall : ∀ s : Finset ↥F, s.card ≤ (s.biUnion (fun j => nb j.1)).card := by
    intro s
    have h := e54_hall_count P R dl t x hx (s.map (Function.Embedding.subtype _))
      (by
        intro j hj
        obtain ⟨j', _, rfl⟩ := Finset.mem_map.1 hj
        exact ((hFmem _).1 j'.2).1)
      (by
        intro j hj
        obtain ⟨j', _, rfl⟩ := Finset.mem_map.1 hj
        exact hnb2 _ j'.2)
    rw [Finset.card_map] at h
    refine h.trans (Finset.card_le_card ?_)
    intro i hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.1 hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.1 hj
    exact Finset.mem_biUnion.2 ⟨j', hj', hij⟩
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun j : ↥F => nb j.1)).1 hhall
  have hint : ∀ j, j ∈ R → j ∉ F → ∃ i, x i j = 1 := by
    intro j hjR hjF
    by_contra hc
    push_neg at hc
    exact hjF ((hFmem j).2 ⟨hjR, hc⟩)
  let τ : Fin n → Fin m := fun j =>
    if h : j ∈ F then f ⟨j, h⟩
    else if h2 : j ∈ R then (hint j h2 h).choose
    else τ0 j
  have hτF : ∀ j (h : j ∈ F), τ j = f ⟨j, h⟩ := by intro j h; simp [τ, h]
  have hτI : ∀ j, j ∈ R → (h : j ∉ F) → x (τ j) j = 1 := by
    intro j h2 h
    simp only [τ, h, h2, dif_neg, dif_pos, not_false_eq_true]
    exact (hint j h2 h).choose_spec
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro j hj
    have : j ∉ F := fun h => hj ((hFmem j).1 h).1
    simp [τ, this, hj]
  · intro j hj
    by_cases h : j ∈ F
    · rw [hτF j h]
      have := hfmem ⟨j, h⟩
      simpa [nb] using this
    · rw [hτI j hj h]; norm_num
  · intro i
    set J := Finset.univ.filter (fun j => j ∈ R ∧ τ j = i) with hJ
    rw [← Finset.sum_filter_add_sum_filter_not J (fun j => j ∈ F)]
    have hA : ∑ j ∈ J.filter (fun j => j ∈ F), (P i j : ℝ) ≤ t := by
      have h1 : ∀ j ∈ J.filter (fun j => j ∈ F), (P i j : ℝ) ≤ t := by
        intro j hj
        simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨⟨_, hτi⟩, hjF⟩ := hj
        rw [hτF j hjF] at hτi
        have hpos : 0 < x i j := by
          have := hfmem ⟨j, hjF⟩
          simpa [nb, hτi] using this
        by_contra hc
        push_neg at hc
        have := hx2 i j hc
        linarith
      have h2 : (J.filter (fun j => j ∈ F)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        obtain ⟨⟨_, ha1⟩, haF⟩ := ha
        obtain ⟨⟨_, hb1⟩, hbF⟩ := hb
        rw [hτF a haF] at ha1
        rw [hτF b hbF] at hb1
        have := hfinj (ha1.trans hb1.symm)
        simpa using this
      calc _ ≤ (J.filter (fun j => j ∈ F)).card • t := Finset.sum_le_card_nsmul _ _ _ h1
        _ ≤ 1 • t := by
            exact nsmul_le_nsmul_left ht h2
        _ = t := one_nsmul t
    have hB : ∑ j ∈ J.filter (fun j => j ∉ F), (P i j : ℝ) ≤ dl i := by
      have h1 : ∑ j ∈ J.filter (fun j => j ∉ F), (P i j : ℝ) =
          ∑ j ∈ J.filter (fun j => j ∉ F), (P i j : ℝ) * x i j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨⟨hjR, hτi⟩, hjF⟩ := hj
        have := hτI j hjR hjF
        rw [hτi] at this
        rw [this]; ring
      rw [h1]
      refine le_trans ?_ (hx5 i)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      exact mul_nonneg (by positivity) (hx1 i j)
    linarith


lemma e54_load_decomp {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (L : Fin n → Option (Fin m))
    (σ : Fin n → Fin m) (hf : ∀ j i, L j = some i → σ j = i) (i : Fin m) :
    load (fun i j => (P i j : ℝ)) σ i = longLoad P L i + shortLoad P L σ i := by
  classical
  unfold load longLoad shortLoad
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun j => σ j = i))
    (fun j => L j = none)]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      cases hL : L j with
      | none => exact absurd hL h2
      | some i' => rw [hf j i' hL] at h1; rw [h1]
    · intro h
      exact ⟨hf j i h, by simp [h]⟩
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto

lemma e54_makespan_le {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) (b : ℝ)
    (hb : 0 ≤ b) (h : ∀ i, load (fun i j => (P i j : ℝ)) σ i ≤ b) :
    makespan (fun i j => (P i j : ℝ)) σ ≤ b :=
  Real.iSup_le h hb

lemma e54_load_le_makespan {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m)
    (i : Fin m) :
    load (fun i j => (P i j : ℝ)) σ i ≤ makespan (fun i j => (P i j : ℝ)) σ :=
  le_ciSup (f := fun i => load (fun i j => (P i j : ℝ)) σ i) (Set.finite_range _).bddAbove i

lemma e54_relaxed {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (ε : ℝ) (hε : 0 < ε)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ))
    (hV : IsVertexSelector P ε V) (D : ℕ → Option (Fin n → Fin m))
    (hD : IsAepsProcedure P ε V D) :
    IsRelaxedDecisionProcedure P (1 + ε) D := by
  classical
  intro d
  have hεd : 0 ≤ ε * (d : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · intro σ hσ
    obtain ⟨L, x, hadm, _, hfol, _, hshort⟩ := (hD d).2 σ hσ
    apply e54_makespan_le P σ _ (by positivity)
    intro i
    rw [e54_load_decomp P L σ hfol i]
    have := hshort i
    nlinarith
  · intro hnone τ
    by_contra hcon
    push_neg at hcon
    have hload : ∀ i, load (fun i j => (P i j : ℝ)) τ i ≤ (d : ℝ) :=
      fun i => (e54_load_le_makespan P τ i).trans hcon
    let L : Fin n → Option (Fin m) :=
      fun j => if ε * (d : ℝ) < (P (τ j) j : ℝ) then some (τ j) else none
    have hLsome : ∀ j i, L j = some i → τ j = i ∧ ε * (d : ℝ) < (P (τ j) j : ℝ) := by
      intro j i h
      simp only [L] at h
      split_ifs at h with hc
      · exact ⟨Option.some_injective _ h, hc⟩
    have hfol : ∀ j i, L j = some i → τ j = i := fun j i h => (hLsome j i h).1
    have hdec := fun i => e54_load_decomp P L τ hfol i
    have hlong : ∀ i, longLoad P L i ≤ (d : ℝ) := by
      intro i
      have := hload i
      rw [hdec i] at this
      have hs : 0 ≤ shortLoad P L τ i := by
        unfold shortLoad
        exact Finset.sum_nonneg (fun j _ => by positivity)
      linarith
    have hadm : IsAdmissible P ε d L := by
      refine ⟨?_, hlong⟩
      intro j i h
      have := hLsome j i h
      rw [← this.1]; exact this.2
    have hnoneL := (hD d).1.1 hnone L hadm
    have hres := (hV d L).2 hnoneL
    have hmem : (fun i j => if L j = none ∧ τ j = i then (1 : ℝ) else 0) ∈ ResidualLP P ε d L := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i j; simp only; split_ifs <;> norm_num
      · intro i j hij
        simp only
        rw [if_neg]
        rintro ⟨hL, hτ⟩
        simp only [L] at hL
        split_ifs at hL with hc
        rw [hτ] at hc
        linarith
      · intro i j hj
        simp only
        rw [if_neg]
        rintro ⟨hL, _⟩
        exact hj hL
      · intro j hj
        have hj' : L j = none := hj
        simp [hj']
      · intro i
        have h1 : ∑ j, (P i j : ℝ) * (if L j = none ∧ τ j = i then (1 : ℝ) else 0) =
            shortLoad P L τ i := by
          unfold shortLoad
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> simp
        rw [h1]
        have := hload i
        rw [hdec i] at this
        show shortLoad P L τ i ≤ (d : ℝ) - longLoad P L i
        linarith
    rw [hres] at hmem
    exact hmem


lemma e54_exists {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (ε : ℝ) (hε : 0 < ε)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ))
    (hV : IsVertexSelector P ε V) :
    ∃ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D := by
  classical
  have key : ∀ d : ℕ, ∃ o : Option (Fin n → Fin m),
      (o = none ↔ ∀ L, IsAdmissible P ε d L → V d L = none) ∧
      (∀ σ, o = some σ →
        ∃ L x, IsAdmissible P ε d L ∧ V d L = some x ∧
          (∀ j i, L j = some i → σ j = i) ∧
          (∀ j, L j = none → 0 < x (σ j) j) ∧
          (∀ i, shortLoad P L σ i ≤ ((d : ℝ) - longLoad P L i) + ε * (d : ℝ))) := by
    intro d
    by_cases h : ∃ L, IsAdmissible P ε d L ∧ V d L ≠ none
    · obtain ⟨L, hadm, hne⟩ := h
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hne
      have hext : x ∈ Set.extremePoints ℝ (ResidualLP P ε d L) := (hV d L).1 x hx
      have hxQ := hext.1
      have hmne : ∀ j, L j = none → Nonempty (Fin m) := by
        intro j hj
        by_contra hn
        rw [not_nonempty_iff] at hn
        have := hxQ.2.2.2.1 j hj
        simp at this
      have hτ0 : ∀ j, ∃ i : Fin m, ∀ i', L j = some i' → i = i' := by
        intro j
        cases hLj : L j with
        | none => obtain ⟨i⟩ := hmne j hLj; exact ⟨i, by simp⟩
        | some i0 => exact ⟨i0, by intro i' h; simpa using h⟩
      choose τ0 hτ0 using hτ0
      have hεd : 0 ≤ ε * (d : ℝ) := by positivity
      obtain ⟨τ, hτout, hτpos, hτload⟩ := e54_round P {j | L j = none}
        (fun i => (d : ℝ) - longLoad P L i) (ε * (d : ℝ)) hεd x hext τ0
      refine ⟨some τ, ?_, ?_⟩
      · constructor
        · intro h; simp at h
        · intro hall; exact absurd (hall L hadm) hne
      · intro σ hσ
        have hστ : τ = σ := Option.some_injective _ hσ
        subst hστ
        refine ⟨L, x, hadm, hx, ?_, ?_, ?_⟩
        · intro j i hj
          have hnn : j ∉ {j | L j = none} := by simp [hj]
          rw [hτout j hnn]
          exact hτ0 j i hj
        · intro j hj
          exact hτpos j hj
        · intro i
          have := hτload i
          unfold shortLoad
          convert this using 3
          exact Iff.rfl
    · refine ⟨none, ?_, ?_⟩
      · constructor
        · intro _ L hL
          by_contra hc
          exact h ⟨L, hL, hc⟩
        · intro _; rfl
      · intro σ hσ; simp at hσ
  choose D hD using key
  exact ⟨D, fun d => ⟨(hD d).1, (hD d).2⟩⟩

theorem relaxed_procedure_core {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ))
    (hV : IsVertexSelector P ε V) :
    (∃ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D) ∧
    ∀ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D →
      IsRelaxedDecisionProcedure P (1 + ε) D :=
  ⟨e54_exists P ε hε V hV, fun D hD => e54_relaxed P ε hε V hV D hD⟩

end UnrelatedSched.FixedMachines

open UnrelatedSched.FixedMachines


theorem solution {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ))
    (hV : IsVertexSelector P ε V) :
    (∃ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D) ∧
    ∀ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D →
      IsRelaxedDecisionProcedure P (1 + ε) D := by
  exact relaxed_procedure_core P hP ε hε V hV
