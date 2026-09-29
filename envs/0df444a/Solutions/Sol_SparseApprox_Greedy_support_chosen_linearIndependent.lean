-- Prove2me | solution 1 for SparseApprox.Greedy.support_chosen_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:22:26.666993+00:00
-- url     : https://prove2.me/submissions/2173eea8-8468-4efd-aff1-e3866364a06a

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- Invariant of the greedy run, relative to the initial columns `f`. -/
def aux_gs_Inv {m n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin m)) (s : State m n) : Prop :=
  (∀ j ∉ s.chosen, s.col j ∈ (Submodule.span ℝ (s.col '' ↑s.chosen))ᗮ) ∧
  s.res ∈ (Submodule.span ℝ (s.col '' ↑s.chosen))ᗮ ∧
  (∃ c : Fin n → ℝ, ∀ j ∉ s.chosen,
      s.col j - c j • f j ∈ Submodule.span ℝ (s.col '' ↑s.chosen)) ∧
  Submodule.span ℝ (f '' ↑s.chosen) = Submodule.span ℝ (s.col '' ↑s.chosen) ∧
  (∀ j ∉ s.chosen, s.col j ≠ 0 → ⟪s.col j, s.col j⟫_ℝ = 1) ∧
  LinearIndepOn ℝ f (↑s.chosen : Set (Fin n))

lemma aux_gs_unit {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) (h : normalizeVec v ≠ 0) :
    ⟪normalizeVec v, normalizeVec v⟫_ℝ = 1 := by
  unfold normalizeVec at *
  have hv : v ≠ 0 := by
    rintro rfl; simp at h
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [real_inner_self_eq_norm_sq, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn, one_pow]

lemma aux_gs_zero_of_mem_both {m : ℕ} {Q : Submodule ℝ (EuclideanSpace ℝ (Fin m))}
    {x : EuclideanSpace ℝ (Fin m)} (h1 : x ∈ Q) (h2 : x ∈ Qᗮ) : x = 0 := by
  have := Submodule.inner_right_of_mem_orthogonal h1 h2
  exact inner_self_eq_zero.mp this

lemma aux_gs_mem_orth_sup {m : ℕ} {Q : Submodule ℝ (EuclideanSpace ℝ (Fin m))}
    {a x : EuclideanSpace ℝ (Fin m)} (h1 : ⟪a, x⟫_ℝ = 0) (h2 : x ∈ Qᗮ) :
    x ∈ (Submodule.span ℝ {a} ⊔ Q)ᗮ := by
  rw [← Submodule.inf_orthogonal]
  exact ⟨Submodule.mem_orthogonal_singleton_iff_inner_right.mpr h1, h2⟩

lemma aux_gs_span_insert {m n : ℕ} (g : Fin n → EuclideanSpace ℝ (Fin m))
    (τ : Finset (Fin n)) (k : Fin n) :
    Submodule.span ℝ (g '' ↑(insert k τ)) =
      Submodule.span ℝ {g k} ⊔ Submodule.span ℝ (g '' ↑τ) := by
  rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert]

lemma aux_gs_step_span {m n : ℕ} (s : State m n) (k : Fin n) :
    Submodule.span ℝ ((greedyStep s k).col '' ↑(greedyStep s k).chosen) =
      Submodule.span ℝ {s.col k} ⊔ Submodule.span ℝ (s.col '' ↑s.chosen) := by
  have : (greedyStep s k).col '' ↑(insert k s.chosen) = s.col '' ↑(insert k s.chosen) := by
    apply Set.image_congr
    intro j hj
    have hj' : j ∈ insert k s.chosen := by simpa using hj
    simp only [greedyStep]
    rw [if_pos hj']
  show Submodule.span ℝ ((greedyStep s k).col '' ↑(insert k s.chosen)) = _
  rw [this, aux_gs_span_insert]

lemma aux_gs_step {m n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin m)) (s : State m n) (k : Fin n)
    (hs : aux_gs_Inv f s) (hk : k ∉ s.chosen) (hne : ⟪s.col k, s.res⟫_ℝ ≠ 0) :
    aux_gs_Inv f (greedyStep s k) := by
  unfold aux_gs_Inv at hs ⊢
  obtain ⟨h1, h2, ⟨c, h3⟩, h4, h6, h7⟩ := hs
  have ha0 : s.col k ≠ 0 := by
    intro h; apply hne; rw [h, inner_zero_left]
  have haa : ⟪s.col k, s.col k⟫_ℝ = 1 := h6 k hk ha0
  have haQ : s.col k ∈ (Submodule.span ℝ (s.col '' ↑s.chosen))ᗮ := h1 k hk
  have hck : c k ≠ 0 := by
    intro h0
    have : s.col k ∈ Submodule.span ℝ (s.col '' ↑s.chosen) := by
      simpa [h0] using h3 k hk
    exact ha0 (aux_gs_zero_of_mem_both this haQ)
  have hQ' := aux_gs_step_span s k
  have hmemQ' : ∀ x ∈ Submodule.span ℝ (s.col '' ↑s.chosen),
      x ∈ Submodule.span ℝ {s.col k} ⊔ Submodule.span ℝ (s.col '' ↑s.chosen) :=
    fun x hx => Submodule.mem_sup_right hx
  have haQ' : s.col k ∈ Submodule.span ℝ {s.col k} ⊔ Submodule.span ℝ (s.col '' ↑s.chosen) :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hchosen : (greedyStep s k).chosen = insert k s.chosen := rfl
  have hcol : ∀ j ∉ insert k s.chosen, (greedyStep s k).col j =
      normalizeVec (s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k) := by
    intro j hj
    simp only [greedyStep]; rw [if_neg hj]
  have hres : (greedyStep s k).res = s.res - ⟪s.col k, s.res⟫_ℝ • s.col k := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hQ', hcol j hj]
    rw [hchosen, Finset.mem_insert, not_or] at hj
    apply aux_gs_mem_orth_sup
    · unfold normalizeVec
      rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, haa]; ring
    · unfold normalizeVec
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (h1 j hj.2) (Submodule.smul_mem _ _ haQ))
  · rw [hQ', hres]
    apply aux_gs_mem_orth_sup
    · rw [inner_sub_right, real_inner_smul_right, haa]; ring
    · exact Submodule.sub_mem _ h2 (Submodule.smul_mem _ _ haQ)
  · refine ⟨fun j => ‖s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k‖⁻¹ * c j, ?_⟩
    intro j hj
    rw [hQ', hcol j hj]
    rw [hchosen, Finset.mem_insert, not_or] at hj
    have heq : normalizeVec (s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k) -
        (‖s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k‖⁻¹ * c j) • f j
        = ‖s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k‖⁻¹ •
            ((s.col j - c j • f j) - ⟪s.col k, s.col j⟫_ℝ • s.col k) := by
      unfold normalizeVec; module
    rw [heq]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (hmemQ' _ (h3 j hj.2)) (Submodule.smul_mem _ _ haQ'))
  · rw [hQ', hchosen, aux_gs_span_insert, h4]
    have hfk : f k = (c k)⁻¹ • s.col k - (c k)⁻¹ • (s.col k - c k • f k) := by
      rw [smul_sub (c k)⁻¹ (s.col k), smul_smul, inv_mul_cancel₀ hck, one_smul, sub_sub_cancel]
    apply le_antisymm
    · apply sup_le _ le_sup_right
      rw [Submodule.span_singleton_le_iff_mem, hfk]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ haQ')
        (Submodule.smul_mem _ _ (hmemQ' _ (h3 k hk)))
    · apply sup_le _ le_sup_right
      rw [Submodule.span_singleton_le_iff_mem]
      have : s.col k = (s.col k - c k • f k) + c k • f k := by abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_right (h3 k hk))
        (Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)))
  · intro j hj hne'
    rw [hcol j hj] at hne' ⊢
    exact aux_gs_unit _ hne'
  · rw [hchosen, Finset.coe_insert, linearIndepOn_insert (by simpa using hk)]
    refine ⟨h7, ?_⟩
    rw [h4]
    intro hfkQ
    have : s.col k ∈ Submodule.span ℝ (s.col '' ↑s.chosen) := by
      have e : s.col k = (s.col k - c k • f k) + c k • f k := by abel
      rw [e]; exact Submodule.add_mem _ (h3 k hk) (Submodule.smul_mem _ _ hfkQ)
    exact ha0 (aux_gs_zero_of_mem_both this haQ)

lemma aux_gs_init {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    aux_gs_Inv (initState A b).col (initState A b) := by
  unfold aux_gs_Inv
  have he : (initState A b).chosen = ∅ := rfl
  simp only [he, Finset.coe_empty, Set.image_empty, Submodule.span_empty,
    Submodule.bot_orthogonal_eq_top, Submodule.mem_top, Submodule.mem_bot]
  refine ⟨fun _ _ => trivial, trivial, ⟨fun _ => 1, fun j _ => by simp⟩, trivial, ?_, ?_⟩
  · intro j _ hj
    exact aux_gs_unit (colE A j) hj
  · first
      | trivial
      | exact linearIndepOn_empty _ _

lemma aux_gs_run {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (ε : ℝ) (k : ℕ → Fin n) (t : ℕ) (hrun : IsGreedyRun A b ε k t) :
    ∀ r ≤ t, aux_gs_Inv (initState A b).col (greedyState A b k r) := by
  intro r
  induction r with
  | zero => intro _; exact aux_gs_init A b
  | succ r ih =>
    intro hr
    have hrt : r < t := by omega
    obtain ⟨_, hk, hne, _⟩ := hrun r hrt
    exact aux_gs_step _ _ _ (ih hrt.le) hk hne

lemma aux_gs_final {m n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin m)) (s : State m n)
    (hs : aux_gs_Inv f s) (δ : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol s.col s.res δ u) :
    Disjoint (nzSet u) s.chosen ∧
      LinearIndependent ℝ (fun i : ↥(nzSet u ∪ s.chosen) => f i) := by
  unfold aux_gs_Inv at hs
  obtain ⟨h1, h2, ⟨c, h3⟩, h4, h6, h7⟩ := hs
  obtain ⟨hfeas, hmin⟩ := hu
  have hcolQ : ∀ i ∈ s.chosen, s.col i ∈ Submodule.span ℝ (s.col '' ↑s.chosen) :=
    fun i hi => Submodule.subset_span ⟨i, hi, rfl⟩
  -- Part 1: disjointness
  have hdisj : Disjoint (nzSet u) s.chosen := by
    rw [Finset.disjoint_left]
    intro j hjS hjτ
    let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => if i ∈ s.chosen then 0 else u i)
    have hv : ∀ i, v i = if i ∈ s.chosen then 0 else u i := fun i => rfl
    have hsplit : (∑ i, u i • s.col i) - s.res =
        ((∑ i, v i • s.col i) - s.res) + ∑ i, (if i ∈ s.chosen then u i else 0) • s.col i := by
      rw [sub_add_eq_add_sub, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hv i]
      split_ifs <;> simp
    have hyQ : ∑ i, (if i ∈ s.chosen then u i else 0) • s.col i ∈
        Submodule.span ℝ (s.col '' ↑s.chosen) := by
      apply Submodule.sum_mem
      intro i _
      split_ifs with hi
      · exact Submodule.smul_mem _ _ (hcolQ i hi)
      · simp
    have hwQ : (∑ i, v i • s.col i) - s.res ∈ (Submodule.span ℝ (s.col '' ↑s.chosen))ᗮ := by
      apply Submodule.sub_mem _ _ h2
      apply Submodule.sum_mem
      intro i _
      rw [hv i]
      split_ifs with hi
      · simp
      · exact Submodule.smul_mem _ _ (h1 i hi)
    have hinner : ⟪(∑ i, v i • s.col i) - s.res,
        ∑ i, (if i ∈ s.chosen then u i else 0) • s.col i⟫_ℝ = 0 := by
      rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal hyQ hwQ
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real hinner
    rw [← hsplit] at hpyth
    have hwle : ‖(∑ i, v i • s.col i) - s.res‖ ≤ ‖(∑ i, u i • s.col i) - s.res‖ := by
      nlinarith [norm_nonneg ((∑ i, v i • s.col i) - s.res),
        norm_nonneg ((∑ i, u i • s.col i) - s.res),
        norm_nonneg (∑ i, (if i ∈ s.chosen then u i else 0) • s.col i)]
    have hle := hmin v (le_trans hwle hfeas)
    have hsub : nzSet v ⊆ (nzSet u).erase j := by
      intro i hi
      simp only [nzSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hv i] at hi
      split_ifs at hi with hiτ
      · exact absurd rfl hi
      · rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · rintro rfl; exact hiτ hjτ
        · simp [nzSet, hi]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hjS] at hc
    unfold nnz at hle
    have hpos : 0 < (nzSet u).card := Finset.card_pos.mpr ⟨j, hjS⟩
    omega
  -- Part 2: the current columns on the support are independent
  have hli : LinearIndepOn ℝ s.col (↑(nzSet u) : Set (Fin n)) := by
    rw [linearIndepOn_finset_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg, j, hjS, hgj⟩ := hcon
    let v : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i => u i - (u j / g j) * (if i ∈ nzSet u then g i else 0))
    have hv : ∀ i, v i = u i - (u j / g j) * (if i ∈ nzSet u then g i else 0) := fun i => rfl
    have hsum : (∑ i, v i • s.col i) = ∑ i, u i • s.col i := by
      have e1 : ∀ i, v i • s.col i = u i • s.col i -
          (u j / g j) • (if i ∈ nzSet u then g i • s.col i else 0) := by
        intro i; rw [hv i]; split_ifs <;> simp [sub_smul, mul_smul]
      simp only [e1, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_ite_mem,
        Finset.univ_inter, hg, smul_zero, sub_zero]
    have hle := hmin v (by rw [hsum]; exact hfeas)
    have hsub : nzSet v ⊆ (nzSet u).erase j := by
      intro i hi
      simp only [nzSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_erase]
      by_cases hiS : i ∈ nzSet u
      · refine ⟨?_, hiS⟩
        rintro rfl
        apply hi
        rw [hv i, if_pos hiS, div_mul_cancel₀ _ hgj, sub_self]
      · exfalso; apply hi
        rw [hv i, if_neg hiS, mul_zero, sub_zero]
        simpa [nzSet] using hiS
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hjS] at hc
    unfold nnz at hle
    have hpos : 0 < (nzSet u).card := Finset.card_pos.mpr ⟨j, hjS⟩
    omega
  -- Part 3: lift to the initial columns
  have hcne : ∀ j ∈ nzSet u, c j ≠ 0 := by
    intro j hj h0
    have hjτ : j ∉ s.chosen := Finset.disjoint_left.mp hdisj hj
    have hmem : s.col j ∈ Submodule.span ℝ (s.col '' ↑s.chosen) := by
      simpa [h0] using h3 j hjτ
    exact hli.ne_zero (by simpa using hj) (aux_gs_zero_of_mem_both hmem (h1 j hjτ))
  refine ⟨hdisj, ?_⟩
  show LinearIndepOn ℝ f ↑(nzSet u ∪ s.chosen)
  rw [linearIndepOn_finset_iff]
  intro g hg i hi
  rw [Finset.sum_union hdisj] at hg
  have hτmem : ∑ i ∈ s.chosen, g i • f i ∈ Submodule.span ℝ (s.col '' ↑s.chosen) := by
    rw [← h4]
    exact Submodule.sum_mem _
      (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩))
  have hSmem : ∑ i ∈ nzSet u, g i • f i ∈ Submodule.span ℝ (s.col '' ↑s.chosen) := by
    have : ∑ i ∈ nzSet u, g i • f i = -(∑ i ∈ s.chosen, g i • f i) :=
      eq_neg_of_add_eq_zero_left hg
    rw [this]; exact Submodule.neg_mem _ hτmem
  have hcolmem : ∑ i ∈ nzSet u, (g i / c i) • s.col i ∈
      Submodule.span ℝ (s.col '' ↑s.chosen) := by
    have : ∑ i ∈ nzSet u, (g i / c i) • s.col i =
        ∑ i ∈ nzSet u, (g i / c i) • (s.col i - c i • f i) + ∑ i ∈ nzSet u, g i • f i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_sub, smul_smul, div_mul_cancel₀ _ (hcne i hi)]; abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.sum_mem _ (fun i hi =>
      Submodule.smul_mem _ _ (h3 i (Finset.disjoint_left.mp hdisj hi)))) hSmem
  have hcolorth : ∑ i ∈ nzSet u, (g i / c i) • s.col i ∈
      (Submodule.span ℝ (s.col '' ↑s.chosen))ᗮ :=
    Submodule.sum_mem _ (fun i hi =>
      Submodule.smul_mem _ _ (h1 i (Finset.disjoint_left.mp hdisj hi)))
  have hzero := aux_gs_zero_of_mem_both hcolmem hcolorth
  have hgS : ∀ i ∈ nzSet u, g i = 0 := by
    intro i hi
    have := (linearIndepOn_finset_iff.mp hli) (fun i => g i / c i) hzero i hi
    simpa [hcne i hi] using this
  rcases Finset.mem_union.mp hi with hiS | hiτ
  · exact hgS i hiS
  · have hS0 : ∑ i ∈ nzSet u, g i • f i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hgS i hi, zero_smul])
    rw [hS0, zero_add] at hg
    exact (linearIndepOn_finset_iff.mp h7) g hg i hiτ

end SparseApprox.Greedy

open SparseApprox.Greedy
open scoped InnerProductSpace

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u) :
    Disjoint (nzSet u) (greedyState A b k r).chosen ∧
      LinearIndependent ℝ
        (fun i : ↥(nzSet u ∪ (greedyState A b k r).chosen) => (initState A b).col i) :=
  aux_gs_final _ _ (aux_gs_run A b ε k t hrun r hr.le) _ u hu
