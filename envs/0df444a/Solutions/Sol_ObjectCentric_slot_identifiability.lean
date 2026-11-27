-- Prove2me | solution 1 for ObjectCentric.slot_identifiability
-- status  : ACCEPTED   (prove)
-- author  : @fangshuming
-- created : 2026-11-27T04:19:40.04483+00:00
-- url     : https://prove2.me/submissions/4b2ad2f2-3b3a-44fb-bc5c-eb74f7577fa4

import Mathlib
import Definitions.Def_ObjectCentric_Basic
import Theorems.Thm_ObjectCentric_jacobian_rank_equality
import Theorems.Thm_ObjectCentric_inferred_slot_depends_on_some_slot
import Theorems.Thm_ObjectCentric_submechanisms_distinct_mechanisms_independent
import Theorems.Thm_ObjectCentric_mechanism_rank_eq_slot_dim

open MeasureTheory
open ObjectCentric
open scoped Topology Matrix

set_option autoImplicit false

/-! # Theorem 1: slot identifiability -/

namespace SlotId

variable {K M N : ℕ}

noncomputable def H (f : Lat K M → Obs N) (ghat : Obs N → Lat K M) : Lat K M → Lat K M :=
  fun z => ghat (f z)

lemma mem_X_of_f {X : Set (Obs N)} {f : Lat K M → Obs N} {g : Obs N → Lat K M}
    (hf : IsDiffeoWithInv f g X) (z : Lat K M) : f z ∈ X := by
  have : f z ∈ Set.range f := ⟨z, rfl⟩
  simpa [hf.2.2.1] using this

lemma fhat_H_eq_f {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (z : Lat K M) : fhat (H f ghat z) = f z := by
  have hxX : f z ∈ X := mem_X_of_f hf z
  have hxR : f z ∈ Set.range fhat := by simpa [hhat.2.2.1] using hxX
  rcases hxR with ⟨y, hy⟩
  calc
    fhat (H f ghat z) = fhat (ghat (f z)) := rfl
    _ = fhat (ghat (fhat y)) := by simpa [hy]
    _ = fhat y := by simpa [hhat.2.2.2 y]
    _ = f z := by simpa [hy]

lemma mechanism_rank (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (z : Lat K M) (k : Fin K) :
    subRank f z (indexSet f z k) = M :=
  mechanism_rank_eq_slot_dim hM X f g hf hfc z k

lemma subRank_empty (f : Lat K M → Obs N) (z : Lat K M) :
    subRank f z (∅ : Set (Fin N)) = 0 := by
  classical
  unfold subRank
  apply le_antisymm
  · have : Fintype.card (∅ : Set (Fin N)) = 0 := by simp
    have h := Matrix.rank_le_card_height
      (A := (jac f z).submatrix (fun n : (∅ : Set (Fin N)) => (n : Fin N)) id)
    simpa [this] using h
  · exact Nat.zero_le _

lemma slotGrad_eq_zero_of_mem_index_ne
    (f : Lat K M → Obs N) (hfc : IsCompositional f)
    (z : Lat K M) (k j : Fin K) (hj : j ≠ k) (n : Fin N)
    (hn : n ∈ indexSet f z k) : slotGrad f z n j = 0 := by
  have hd := hfc z k j (Ne.symm hj)
  have : n ∉ indexSet f z j := Set.disjoint_left.mp hd hn
  by_contra hne
  exact this (by simpa [indexSet] using hne)

lemma subRank_le_M_of_subset_index
    (f : Lat K M → Obs N) (hfc : IsCompositional f)
    (z : Lat K M) (k : Fin K) (S : Set (Fin N)) (hS : S ⊆ indexSet f z k) :
    subRank f z S ≤ M := by
  classical
  let A : Matrix S (Fin K × Fin M) ℝ :=
    (jac f z).submatrix (fun n : S => (n : Fin N)) id
  let Ak : Matrix S (Fin M) ℝ := fun n m => A n (k, m)
  let P : Matrix (Fin M) (Fin K × Fin M) ℝ := fun m c =>
    if c.1 = k ∧ c.2 = m then (1 : ℝ) else 0
  have hfac : A = Ak * P := by
    ext n c
    rw [Matrix.mul_apply]
    -- goal: A n c = ∑ m, Ak n m * P m c
    dsimp [Ak, A, P]
    by_cases h1 : c.1 = k
    · have hsum :
          (∑ m : Fin M,
              jac f z (↑n) (k, m) * (if c.1 = k ∧ c.2 = m then (1 : ℝ) else 0))
            = jac f z (↑n) (k, c.2) := by
        rw [Fintype.sum_eq_single c.2]
        · simp [h1]
        · intro m hm
          simp [h1, show ¬ c.2 = m from fun h => hm h.symm]
      have hL : jac f z (↑n) c = jac f z (↑n) (k, c.2) := by
        rcases c with ⟨c1, c2⟩
        change jac f z (↑n) (c1, c2) = jac f z (↑n) (k, c2)
        simp only at h1
        subst h1
        rfl
      exact hL.trans hsum.symm
    · have hnI : (↑n : Fin N) ∈ indexSet f z k := hS n.property
      have hz := slotGrad_eq_zero_of_mem_index_ne f hfc z k c.1 h1 (↑n) hnI
      have hL : jac f z (↑n) c = 0 := by
        simpa [slotGrad] using congrArg (fun v : Fin M → ℝ => v c.2) hz
      rw [hL]
      exact Eq.symm (Finset.sum_eq_zero (fun m _ => by simp [h1]))
  have hle : A.rank ≤ Ak.rank := by
    simpa [hfac] using Matrix.rank_mul_le_left Ak P
  have hAk : Ak.rank ≤ M := by
    simpa [Fintype.card_fin] using Matrix.rank_le_card_width (A:=Ak)
  simpa [subRank] using le_trans hle hAk


lemma exists_index_intersection
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (j : Fin K) :
    ∃ i : Fin K, (indexSet fhat (H f ghat z) j ∩ indexSet f z i).Nonempty := by
  classical
  by_contra hnone
  push_neg at hnone
  -- hnone : ∀ i, indexSet fhat (H f ghat z) j ∩ indexSet f z i = ∅
  let zhat : Lat K M := H f ghat z
  let S : Set (Fin N) := indexSet fhat zhat j
  have hdisj : ∀ i, indexSet fhat zhat j ∩ indexSet f z i = ∅ := by
    intro i
    simpa [zhat, S] using hnone i
  have hrow0 : ∀ (n : Fin N), n ∈ S → ∀ c : Fin K × Fin M, jac f z n c = 0 := by
    intro n hn c
    have : slotGrad f z n c.1 = 0 := by
      by_contra hne
      have hine : n ∈ indexSet f z c.1 := by simpa [indexSet] using hne
      have hinter : n ∈ indexSet fhat zhat j ∩ indexSet f z c.1 := ⟨hn, hine⟩
      have : n ∈ (∅ : Set (Fin N)) := by simpa [hdisj c.1] using hinter
      exact this.elim
    simpa [slotGrad] using congrArg (fun v : Fin M → ℝ => v c.2) this
  have hrankf : subRank f z S = 0 := by
    have : (jac f z).submatrix (fun n : S => (n : Fin N)) id = 0 := by
      ext n c; exact hrow0 (n : Fin N) n.property c
    simpa [subRank, this]
  have hrankfhat : subRank fhat zhat S = M :=
    mechanism_rank hM (X:=X) fhat ghat hhat hfhatc zhat j
  by_cases hSne : S.Nonempty
  · have hEq := jacobian_rank_equality hM X f g hf fhat ghat hhat z S hSne
    have hM0 : M = 0 := by
      have := hrankfhat.symm.trans (hEq.symm.trans hrankf)
      simpa using this
    have : ¬ 0 < M := by simpa [hM0]
    exact this hM
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    have hz0 : subRank fhat zhat S = 0 := by simpa [hSempty] using subRank_empty fhat zhat
    have hM0 : M = 0 := by
      simpa [hz0] using hrankfhat.symm
    have : ¬ 0 < M := by simpa [hM0]
    exact this hM

/-- The intersection of an inferred index set with a ground-truth index set. -/
def meet (f : Lat K M → Obs N) (fhat : Lat K M → Obs N)
    (z zhat : Lat K M) (i j : Fin K) : Set (Fin N) :=
  indexSet fhat zhat j ∩ indexSet f z i

/-- Pixels of ground-truth slot `i` outside inferred slot `j`. -/
def meetCompl (f : Lat K M → Obs N) (fhat : Lat K M → Obs N)
    (z zhat : Lat K M) (i j : Fin K) : Set (Fin N) :=
  indexSet f z i \ indexSet fhat zhat j

lemma meet_union_compl (f : Lat K M → Obs N) (fhat : Lat K M → Obs N)
    (z zhat : Lat K M) (i j : Fin K) :
    meet f fhat z zhat i j ∪ meetCompl f fhat z zhat i j = indexSet f z i := by
  ext n; constructor
  · intro hn
    cases hn with
    | inl h => exact h.2
    | inr h => exact h.1
  · intro hn
    by_cases hj : n ∈ indexSet fhat zhat j
    · exact Or.inl ⟨hj, hn⟩
    · exact Or.inr ⟨hn, hj⟩

lemma meet_disjoint_compl (f : Lat K M → Obs N) (fhat : Lat K M → Obs N)
    (z zhat : Lat K M) (i j : Fin K) :
    Disjoint (meet f fhat z zhat i j) (meetCompl f fhat z zhat i j) := by
  refine Set.disjoint_left.mpr ?_
  intro n hn hm
  exact hm.2 hn.1

/-- If two distinct ground-truth slots both meet the same inferred slot, both
`meet` sets are nonempty (by assumption) and both `meetCompl` sets are nonempty
(otherwise rank would exceed `M`). -/
lemma meetCompl_nonempty_of_two_meets
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (j : Fin K) (i i' : Fin K) (hii : i ≠ i')
    (hne_i : (meet f fhat z (H f ghat z) i j).Nonempty)
    (hne_i' : (meet f fhat z (H f ghat z) i' j).Nonempty) :
    (meetCompl f fhat z (H f ghat z) i j).Nonempty := by
  classical
  let zhat := H f ghat z
  by_contra hempty
  have hCempty : meetCompl f fhat z zhat i j = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hempty
  -- Then I_i ⊆ Î_j
  have hsub : indexSet f z i ⊆ indexSet fhat zhat j := by
    intro n hn
    have : n ∈ meet f fhat z zhat i j ∪ meetCompl f fhat z zhat i j := by
      simpa [meet_union_compl] using hn
    cases this with
    | inl h => exact h.1
    | inr h =>
      have : n ∈ (∅ : Set (Fin N)) := by simpa [hCempty] using h
      exact this.elim
  -- A := I_i ∪ meet(i',j) ⊆ Î_j
  let A : Set (Fin N) := indexSet f z i ∪ meet f fhat z zhat i' j
  have hAsub : A ⊆ indexSet fhat zhat j := by
    intro n hn
    cases hn with
    | inl h => exact hsub h
    | inr h => exact h.1
  -- rank_fhat(A) ≤ M
  have hleM : subRank fhat zhat A ≤ M :=
    subRank_le_M_of_subset_index fhat hfhatc zhat j A hAsub
  -- rank equality
  have hAne : A.Nonempty := by
    rcases hne_i with ⟨n, hn⟩
    exact ⟨n, Or.inl hn.2⟩
  have hEq : subRank f z A = subRank fhat zhat A :=
    jacobian_rank_equality hM X f g hf fhat ghat hhat z A hAne
  -- I_i and meet(i',j) are independent under f (meet ⊆ I_i', disjoint by compositionality)
  have hmeet_sub : meet f fhat z zhat i' j ⊆ indexSet f z i' := fun _ h => h.2
  have hdis : Disjoint (indexSet f z i) (meet f fhat z zhat i' j) := by
    refine Set.disjoint_left.mpr ?_
    intro n hni hnm
    have : n ∈ indexSet f z i ∩ indexSet f z i' := ⟨hni, hnm.2⟩
    have hd := hfc z i i' hii
    exact (Set.disjoint_left.mp hd) this.1 this.2
  have hmeet_ne : (meet f fhat z zhat i' j).Nonempty := hne_i'
  have hIi_ne : (indexSet f z i).Nonempty := by
    rcases hne_i with ⟨n, hn⟩; exact ⟨n, hn.2⟩
  have hInd :
      SubmechIndependent f z (indexSet f z i) (meet f fhat z zhat i' j) :=
    submechanisms_distinct_mechanisms_independent hM X f g hf hfc
      (indexSet f z i) (meet f fhat z zhat i' j) hIi_ne hmeet_ne z i
      (fun _ h => h)
      (Set.disjoint_iff_inter_eq_empty.mp hdis.symm)
  have hrankIi : subRank f z (indexSet f z i) = M :=
    mechanism_rank hM (X:=X) f g hf hfc z i
  have hsum :
      subRank f z A =
        subRank f z (indexSet f z i) + subRank f z (meet f fhat z zhat i' j) := by
    simpa [A, SubmechIndependent] using hInd
  have hpos : 0 < subRank f z (meet f fhat z zhat i' j) := by
    rcases hmeet_ne with ⟨n0, hn0⟩
    have hsg : slotGrad f z n0 i' ≠ 0 := by simpa [indexSet] using hn0.2
    rcases Function.ne_iff.mp hsg with ⟨m0, hm0⟩
    let B := (jac f z).submatrix (fun n : meet f fhat z zhat i' j => (n : Fin N)) id
    have hentry : B ⟨n0, hn0⟩ (i', m0) ≠ 0 := by
      simpa [B, slotGrad, Matrix.submatrix_apply] using hm0
    -- rank ≥ 1 because a nonzero column exists
    have hcol : B.col (i', m0) ≠ 0 := by
      intro hc
      have : B ⟨n0, hn0⟩ (i', m0) = 0 := by
        simpa [Matrix.col] using congrArg (fun v : _ → ℝ => v ⟨n0, hn0⟩) hc
      exact hentry this
    have : 0 < Module.finrank ℝ (LinearMap.range (B.mulVecLin)) := by
      have hmem : B.col (i', m0) ∈ LinearMap.range B.mulVecLin := by
        refine ⟨Pi.single (i', m0) (1 : ℝ), ?_⟩
        ext r
        simp [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.col, dotProduct,
          Pi.single_apply]
      have hne0 : (⟨B.col (i', m0), hmem⟩ : LinearMap.range B.mulVecLin) ≠ 0 := by
        intro h
        apply hcol
        simpa using congrArg Subtype.val h
      haveI : Nontrivial (LinearMap.range B.mulVecLin) := ⟨⟨_, 0, hne0⟩⟩
      exact Module.finrank_pos_iff.mpr inferInstance
    simpa [subRank, B, Matrix.rank] using this
  have hgt : M < subRank f z A := by
    rw [hsum, hrankIi]
    exact Nat.lt_add_of_pos_right hpos
  have h2 : M < subRank fhat zhat A := by simpa [hEq] using hgt
  exact (not_lt_of_ge hleM) h2

/-- Prop. 2: each inferred index set meets exactly one ground-truth index set. -/
lemma unique_index_intersection
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (j : Fin K) :
    ∃! i : Fin K, (indexSet fhat (H f ghat z) j ∩ indexSet f z i).Nonempty := by
  classical
  let zhat := H f ghat z
  obtain ⟨i0, hi0⟩ :=
    exists_index_intersection hM (X:=X) f g hf hfc ghat fhat hhat hfhatc z j
  refine ⟨i0, hi0, ?_⟩
  intro i1 hi1
  by_contra hne
  -- Two distinct ground-truth slots meet Î_j
  have hC0 :=
    meetCompl_nonempty_of_two_meets hM (X:=X) f g hf hfc ghat fhat hhat hfhatc
      z j i0 i1 (Ne.symm hne) hi0 hi1
  have hC1 :=
    meetCompl_nonempty_of_two_meets hM (X:=X) f g hf hfc ghat fhat hhat hfhatc
      z j i1 i0 hne hi1 hi0
  -- Apply irreducibility at i0 with partition meet / meetCompl
  have hO1 : (meet f fhat z zhat i0 j).Nonempty := by simpa [meet] using hi0
  have hO2 : (meetCompl f fhat z zhat i0 j).Nonempty := hC0
  have hdis := meet_disjoint_compl f fhat z zhat i0 j
  have hunion := meet_union_compl f fhat z zhat i0 j
  have hDep : SubmechDependent f z (meet f fhat z zhat i0 j) (meetCompl f fhat z zhat i0 j) :=
    hfi z i0 (meet f fhat z zhat i0 j) (meetCompl f fhat z zhat i0 j) hO1 hO2 hdis hunion
  -- Translate dependence via jacobian rank equality to fhat
  have hEq1 : subRank f z (meet f fhat z zhat i0 j) =
      subRank fhat zhat (meet f fhat z zhat i0 j) :=
    jacobian_rank_equality hM X f g hf fhat ghat hhat z _ hO1
  have hEq2 : subRank f z (meetCompl f fhat z zhat i0 j) =
      subRank fhat zhat (meetCompl f fhat z zhat i0 j) :=
    jacobian_rank_equality hM X f g hf fhat ghat hhat z _ hO2
  have hEqU : subRank f z (indexSet f z i0) =
      subRank fhat zhat (indexSet f z i0) :=
    jacobian_rank_equality hM X f g hf fhat ghat hhat z _ (by
      rcases hi0 with ⟨n, hn⟩; exact ⟨n, hn.2⟩)
  -- Under fhat: meet ⊆ Î_j and meetCompl ∩ Î_j = ∅ ⇒ independent
  have hmeet_sub : meet f fhat z zhat i0 j ⊆ indexSet fhat zhat j := fun _ h => h.1
  have hcompl_dis : meetCompl f fhat z zhat i0 j ∩ indexSet fhat zhat j = ∅ := by
    ext n; constructor
    · intro hn
      exact (hn.1.2 hn.2).elim
    · intro hn; exact hn.elim
  have hIndHat :
      SubmechIndependent fhat zhat (meet f fhat z zhat i0 j) (meetCompl f fhat z zhat i0 j) :=
    submechanisms_distinct_mechanisms_independent hM X fhat ghat hhat hfhatc
      (meet f fhat z zhat i0 j) (meetCompl f fhat z zhat i0 j) hO1 hO2 zhat j
      hmeet_sub hcompl_dis
  -- rank_fhat(I_i0) = rank(meet)+rank(meetCompl) > M by dependence+eq, contradicting = M
  -- Independence under fhat: rank(I_i0) = rank(meet)+rank(meetCompl)
  have hsumHat :
      subRank fhat zhat (indexSet f z i0) =
        subRank fhat zhat (meet f fhat z zhat i0 j) +
          subRank fhat zhat (meetCompl f fhat z zhat i0 j) := by
    simpa [SubmechIndependent, hunion] using hIndHat
  -- Dependence under f + rank equality ⇒ rank(I_i0) < sum of ranks under fhat
  have hDep' : subRank fhat zhat (indexSet f z i0) <
      subRank fhat zhat (meet f fhat z zhat i0 j) +
        subRank fhat zhat (meetCompl f fhat z zhat i0 j) := by
    have : subRank f z (indexSet f z i0) <
        subRank f z (meet f fhat z zhat i0 j) +
          subRank f z (meetCompl f fhat z zhat i0 j) := by
      simpa [SubmechDependent, hunion] using hDep
    simpa [hEqU, hEq1, hEq2] using this
  -- Contradiction: rank < rank
  have : subRank fhat zhat (indexSet f z i0) < subRank fhat zhat (indexSet f z i0) := by
    simpa [hsumHat] using hDep'
  exact (lt_irrefl _ this).elim


/-- Existence half of Cor. 1. -/
lemma exists_index_intersection_symm
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (i : Fin K) :
    ∃ j : Fin K, (indexSet fhat (H f ghat z) j ∩ indexSet f z i).Nonempty := by
  classical
  let zhat := H f ghat z
  by_contra hnone
  push_neg at hnone
  let S := indexSet f z i
  have hdisj : ∀ j, indexSet fhat zhat j ∩ S = ∅ := by
    intro j; simpa [S] using hnone j
  have hrow0 : ∀ n ∈ S, ∀ c : Fin K × Fin M, jac fhat zhat n c = 0 := by
    intro n hn c
    have : slotGrad fhat zhat n c.1 = 0 := by
      by_contra hne
      have hine : n ∈ indexSet fhat zhat c.1 := by simpa [indexSet] using hne
      have : n ∈ indexSet fhat zhat c.1 ∩ S := ⟨hine, hn⟩
      have : n ∈ (∅ : Set (Fin N)) := by simpa [hdisj c.1] using this
      exact this.elim
    simpa [slotGrad] using congrArg (fun v : Fin M → ℝ => v c.2) this
  have hrankfhat : subRank fhat zhat S = 0 := by
    have : (jac fhat zhat).submatrix (fun n : S => (n : Fin N)) id = 0 := by
      ext n c; exact hrow0 (n : Fin N) n.property c
    simpa [subRank, this]
  have hrankf : subRank f z S = M :=
    mechanism_rank hM (X:=X) f g hf hfc z i
  by_cases hSne : S.Nonempty
  · have hEq := jacobian_rank_equality hM X f g hf fhat ghat hhat z S hSne
    have hM0 : M = 0 := by
      have := hrankf.symm.trans (hEq.trans hrankfhat)
      simpa using this
    exact absurd hM (by simpa [hM0])
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    have : subRank f z S = 0 := by simpa [hSempty] using subRank_empty f z
    have hM0 : M = 0 := by simpa [this] using hrankf.symm
    exact absurd hM (by simpa [hM0])

/-- Cor. 1: each ground-truth index set meets exactly one inferred index set. -/
lemma unique_index_intersection_symm
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (i : Fin K) :
    ∃! j : Fin K, (indexSet fhat (H f ghat z) j ∩ indexSet f z i).Nonempty := by
  classical
  let zhat := H f ghat z
  obtain ⟨j0, hj0⟩ :=
    exists_index_intersection_symm hM (X:=X) f g hf hfc ghat fhat hhat hfhatc z i
  refine ⟨j0, hj0, ?_⟩
  intro j1 hj1
  by_contra hne
  let π : Fin K → Fin K := fun j =>
    Classical.choose
      (unique_index_intersection hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc z j).exists
  have hπ : ∀ j, (indexSet fhat zhat j ∩ indexSet f z (π j)).Nonempty := fun j => by
    simpa [zhat] using Classical.choose_spec
      (unique_index_intersection hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc z j).exists
  have hπ_eq : ∀ j i', (indexSet fhat zhat j ∩ indexSet f z i').Nonempty → π j = i' := by
    intro j i' hi'
    exact Eq.symm <|
      (unique_index_intersection hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc z j).unique
        hi' (by simpa [zhat] using hπ j)
  have hπj0 : π j0 = i := hπ_eq j0 i (by simpa [zhat] using hj0)
  have hπj1 : π j1 = i := hπ_eq j1 i (by simpa [zhat] using hj1)
  have hnotinj : ¬ Function.Injective π := by
    intro hinj
    exact hne (hinj (hπj1.trans hπj0.symm))
  have hnotsurj : ¬ Function.Surjective π :=
    fun hsurj => hnotinj ((Finite.injective_iff_surjective (f := π)).2 hsurj)
  obtain ⟨i', hi'⟩ := not_forall.mp hnotsurj
  push_neg at hi'
  obtain ⟨j', hj'⟩ :=
    exists_index_intersection_symm hM (X:=X) f g hf hfc ghat fhat hhat hfhatc z i'
  have : π j' = i' := hπ_eq j' i' (by simpa [zhat] using hj')
  exact hi' j' this


/-- `H` is `C¹`. -/
lemma contDiff_H {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X) :
    ContDiff ℝ 1 (H f ghat) := by
  exact (hhat.2.1.comp_contDiff hf.1) (fun z => by
    have : f z ∈ Set.range f := ⟨z, rfl⟩
    simpa [hf.2.2.1] using this)

lemma differentiable_H {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X) :
    Differentiable ℝ (H f ghat) :=
  (contDiff_H (X:=X) f g hf ghat fhat hhat).differentiable (by decide)

/-- Inverse of `H`. -/
noncomputable def Ginv (g : Obs N → Lat K M) (fhat : Lat K M → Obs N) : Lat K M → Lat K M :=
  fun zhat => g (fhat zhat)

lemma contDiff_Ginv {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X) :
    ContDiff ℝ 1 (Ginv g fhat) := by
  exact (hf.2.1.comp_contDiff hhat.1) (fun z => by
    have : fhat z ∈ Set.range fhat := ⟨z, rfl⟩
    simpa [hhat.2.2.1] using this)

lemma leftInverse_Ginv_H {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X) :
    Function.LeftInverse (Ginv g fhat) (H f ghat) := by
  intro z
  have : fhat (H f ghat z) = f z := fhat_H_eq_f (X:=X) f g hf ghat fhat hhat z
  simpa [Ginv, this] using hf.2.2.2 z

lemma rightInverse_Ginv_H {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X) :
    Function.RightInverse (Ginv g fhat) (H f ghat) := by
  intro zhat
  have hxX : fhat zhat ∈ X := by
    have : fhat zhat ∈ Set.range fhat := ⟨zhat, rfl⟩
    simpa [hhat.2.2.1] using this
  have hxR : fhat zhat ∈ Set.range f := by simpa [hf.2.2.1] using hxX
  rcases hxR with ⟨z, hz⟩
  have hg : g (fhat zhat) = z := by simpa [hz] using hf.2.2.2 z
  calc
    H f ghat (Ginv g fhat zhat) = ghat (f (g (fhat zhat))) := rfl
    _ = ghat (f z) := by simp [hg]
    _ = ghat (fhat zhat) := by simp [hz]
    _ = zhat := hhat.2.2.2 zhat

lemma fderiv_f_eq_fhat_comp_H {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (z : Lat K M) :
    fderiv ℝ f z =
      (fderiv ℝ fhat (H f ghat z)).comp (fderiv ℝ (H f ghat) z) := by
  have hf_eq : ∀ w, fhat (H f ghat w) = f w := fun w =>
    fhat_H_eq_f (X:=X) f g hf ghat fhat hhat w
  have hH := (differentiable_H (X:=X) f g hf ghat fhat hhat z).hasFDerivAt
  have hF := (hhat.1.differentiable (by decide) (H f ghat z)).hasFDerivAt
  have hcomp := hF.comp z hH
  -- hcomp : HasFDerivAt (fhat ∘ H) ...; rewrite via hf_eq
  have hcomp' : HasFDerivAt f
      ((fderiv ℝ fhat (H f ghat z)).comp (fderiv ℝ (H f ghat) z)) z := by
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with w
    exact (hf_eq w).symm
  exact hcomp'.fderiv

/-- Expand `fderiv H` on a slot basis vector via `slotBlock`. -/
lemma fderiv_H_single (f : Lat K M → Obs N) (ghat : Obs N → Lat K M)
    (z : Lat K M) (i : Fin K) (b : Fin M) :
    fderiv ℝ (H f ghat) z (Pi.single i (Pi.single b 1)) =
      fun j a => slotBlock (H f ghat) z j i a b := rfl

/-- Pointwise chain rule on an inferred-index pixel. -/
lemma jac_eq_slotJac_mul_slotBlock_apply {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (j i : Fin K) (n : Fin N) (hn : n ∈ indexSet fhat (H f ghat z) j)
    (b : Fin M) :
    jac f z n (i, b) =
      ∑ a : Fin M, jac fhat (H f ghat z) n (j, a) * slotBlock (H f ghat) z j i a b := by
  classical
  let zhat := H f ghat z
  have hchain := fderiv_f_eq_fhat_comp_H (X:=X) f g hf ghat fhat hhat z
  have hL : jac f z n (i, b) =
      fderiv ℝ fhat zhat (fderiv ℝ (H f ghat) z (Pi.single i (Pi.single b 1))) n := by
    simpa [jac, zhat] using
      congrArg (fun L : Lat K M →L[ℝ] Obs N => L (Pi.single i (Pi.single b 1)) n) hchain
  let v : Lat K M := fderiv ℝ (H f ghat) z (Pi.single i (Pi.single b 1))
  have hv : v = ∑ j' : Fin K, ∑ a : Fin M,
      (slotBlock (H f ghat) z j' i a b) • Pi.single j' (Pi.single a (1 : ℝ)) := by
    funext j0 a0
    change
      fderiv ℝ (H f ghat) z (Pi.single i (Pi.single b 1)) j0 a0 =
        (∑ j' : Fin K, ∑ a : Fin M,
          (slotBlock (H f ghat) z j' i a b) • Pi.single j' (Pi.single a (1 : ℝ))) j0 a0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Fintype.sum_eq_single j0]
    · simp only [Pi.single_apply, ↓reduceIte]
      rw [Fintype.sum_eq_single a0]
      · simp [Pi.single_apply, slotBlock]
      · intro a hne
        have : a0 ≠ a := Ne.symm hne
        simp [Pi.single_apply, this]
    · intro j' hne
      have : j0 ≠ j' := Ne.symm hne
      simp [Pi.single_apply, this]
  have hmap :
      fderiv ℝ fhat zhat v =
        ∑ j' : Fin K, ∑ a : Fin M,
          slotBlock (H f ghat) z j' i a b •
            fderiv ℝ fhat zhat (Pi.single j' (Pi.single a 1)) := by
    calc
      fderiv ℝ fhat zhat v
          = fderiv ℝ fhat zhat
              (∑ j' : Fin K, ∑ a : Fin M,
                slotBlock (H f ghat) z j' i a b •
                  Pi.single j' (Pi.single a (1 : ℝ))) := by rw [hv]
      _ = ∑ j' : Fin K, fderiv ℝ fhat zhat
              (∑ a : Fin M,
                slotBlock (H f ghat) z j' i a b •
                  Pi.single j' (Pi.single a (1 : ℝ))) := by simp [map_sum]
      _ = ∑ j' : Fin K, ∑ a : Fin M,
              slotBlock (H f ghat) z j' i a b •
                fderiv ℝ fhat zhat (Pi.single j' (Pi.single a 1)) := by
            congr 1; funext j'; simp [map_sum, map_smul]
  have happly := congrArg (fun w : Obs N => w n) hmap
  have hsum :
      fderiv ℝ fhat zhat v n =
        ∑ j' : Fin K, ∑ a : Fin M,
          slotBlock (H f ghat) z j' i a b * jac fhat zhat n (j', a) := by
    simpa [jac, smul_eq_mul, mul_comm] using happly
  have honly :
      (∑ j' : Fin K, ∑ a : Fin M,
          slotBlock (H f ghat) z j' i a b * jac fhat zhat n (j', a))
        = ∑ a : Fin M, slotBlock (H f ghat) z j i a b * jac fhat zhat n (j, a) := by
    have hmem : j ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ j
    refine Finset.sum_eq_single_of_mem j hmem ?_
    intro j' _ hne
    apply Finset.sum_eq_zero
    intro a _
    have hz := slotGrad_eq_zero_of_mem_index_ne fhat hfhatc zhat j j' hne n hn
    have : jac fhat zhat n (j', a) = 0 := by
      simpa [slotGrad] using congrArg (fun vv : Fin M → ℝ => vv a) hz
    simp [this]
  calc
    jac f z n (i, b) = fderiv ℝ fhat zhat v n := hL
    _ = ∑ j' : Fin K, ∑ a : Fin M,
          slotBlock (H f ghat) z j' i a b * jac fhat zhat n (j', a) := hsum
    _ = ∑ a : Fin M, slotBlock (H f ghat) z j i a b * jac fhat zhat n (j, a) := honly
    _ = ∑ a : Fin M, jac fhat zhat n (j, a) * slotBlock (H f ghat) z j i a b := by
          congr 1; funext a; ring

/-- Full-column-rank left factor forces right factor zero. -/
lemma eq_zero_of_left_mul_eq_zero_of_rank
    {ι : Type*} [Fintype ι] (A : Matrix ι (Fin M) ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (hA : A.rank = M) (hAB : A * B = 0) : B = 0 := by
  classical
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have hr : Module.finrank ℝ (LinearMap.range A.mulVecLin) = M := by
      simpa [Matrix.rank] using hA
    have hdom : Module.finrank ℝ (Fin M → ℝ) = M := by simp [Fintype.card_fin]
    have : Module.finrank ℝ ↥(LinearMap.ker A.mulVecLin) = 0 := by
      have := hsum
      simp only [hr, hdom] at this
      omega
    exact Submodule.finrank_eq_zero.mp this
  ext b a
  have hcol : A.mulVec (fun m => B m a) = 0 := by
    ext n
    have hentry := congrArg (fun M : Matrix ι (Fin M) ℝ => M n a) hAB
    -- hentry : (A*B) n a = 0 = ∑ A n j * B j a
    have : ∑ j, A n j * B j a = 0 := by
      simpa [Matrix.mul_apply] using hentry
    simpa [Matrix.mulVec, dotProduct] using this
  have hvec : (fun m => B m a) = 0 := by
    have : (fun m => B m a) ∈ LinearMap.ker A.mulVecLin := by
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hcol
    simpa [hker] using this
  simpa using congrArg (fun v : Fin M → ℝ => v b) hvec

/-- Rank of the `j`-block of `jac fhat` on `Î_j` equals `M`. -/
lemma slotJac_rank
    (hM : 0 < M) {X : Set (Obs N)}
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (zhat : Lat K M) (j : Fin K) :
    let S := indexSet fhat zhat j
    let Ak : Matrix S (Fin M) ℝ := fun n m => jac fhat zhat (n : Fin N) (j, m)
    Ak.rank = M := by
  classical
  intro S Ak
  let A : Matrix S (Fin K × Fin M) ℝ :=
    (jac fhat zhat).submatrix (fun n : S => (n : Fin N)) id
  let P : Matrix (Fin M) (Fin K × Fin M) ℝ := fun m c =>
    if c.1 = j ∧ c.2 = m then (1 : ℝ) else 0
  have hfac : A = Ak * P := by
    ext n c
    rw [Matrix.mul_apply]
    dsimp [Ak, A, P]
    by_cases h1 : c.1 = j
    · have hsum :
          (∑ m : Fin M,
              jac fhat zhat (↑n) (j, m) * (if c.1 = j ∧ c.2 = m then (1 : ℝ) else 0))
            = jac fhat zhat (↑n) (j, c.2) := by
        rw [Fintype.sum_eq_single c.2]
        · simp [h1]
        · intro m hm; simp [h1, show ¬ c.2 = m from fun h => hm h.symm]
      have hL : jac fhat zhat (↑n) c = jac fhat zhat (↑n) (j, c.2) := by
        rcases c with ⟨c1, c2⟩
        change jac fhat zhat (↑n) (c1, c2) = jac fhat zhat (↑n) (j, c2)
        simp only at h1; subst h1; rfl
      exact hL.trans hsum.symm
    · have hnI : (↑n : Fin N) ∈ S := n.property
      have hz := slotGrad_eq_zero_of_mem_index_ne fhat hfhatc zhat j c.1 h1 (↑n) hnI
      have hL : jac fhat zhat (↑n) c = 0 := by
        simpa [slotGrad] using congrArg (fun v : Fin M → ℝ => v c.2) hz
      rw [hL]
      exact Eq.symm (Finset.sum_eq_zero (fun m _ => by simp [h1]))
  have hrankA : A.rank = M := by
    simpa [subRank, A, S] using mechanism_rank hM (X:=X) fhat ghat hhat hfhatc zhat j
  have hle : A.rank ≤ Ak.rank := by simpa [hfac] using Matrix.rank_mul_le_left Ak P
  have hAk : Ak.rank ≤ M := by
    simpa [Fintype.card_fin] using Matrix.rank_le_card_width (A:=Ak)
  exact le_antisymm hAk (by simpa [hrankA] using hle)

/-- Prop. 3: each ground-truth slot affects at most one inferred slot. -/
lemma at_most_one_slotBlock
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (i : Fin K) (j j' : Fin K)
    (hj : slotBlock (H f ghat) z j i ≠ 0)
    (hj' : slotBlock (H f ghat) z j' i ≠ 0) :
    j = j' := by
  classical
  by_contra hne
  let zhat := H f ghat z
  obtain ⟨jMeet, hMeet, hMeetUniq⟩ :=
    unique_index_intersection_symm hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc z i
  obtain ⟨j0, hBne, hdis⟩ :
      ∃ j0 : Fin K, slotBlock (H f ghat) z j0 i ≠ 0 ∧
        indexSet fhat zhat j0 ∩ indexSet f z i = ∅ := by
    by_cases hjm : j = jMeet
    · have : j' ≠ jMeet := by intro h; exact hne (hjm.trans h.symm)
      refine ⟨j', hj', ?_⟩
      by_contra hne'
      have hneS : (indexSet fhat zhat j' ∩ indexSet f z i).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hne'
      exact this (hMeetUniq j' (by simpa [zhat] using hneS))
    · refine ⟨j, hj, ?_⟩
      by_contra hne'
      have hneS : (indexSet fhat zhat j ∩ indexSet f z i).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hne'
      exact hjm (hMeetUniq j (by simpa [zhat] using hneS))
  let S := indexSet fhat zhat j0
  let Ak : Matrix S (Fin M) ℝ := fun n m => jac fhat zhat (n : Fin N) (j0, m)
  let B := slotBlock (H f ghat) z j0 i
  have hmul : Ak * B = 0 := by
    ext n b
    have hL : jac f z (n : Fin N) (i, b) = 0 := by
      have hnI : (n : Fin N) ∉ indexSet f z i := by
        intro hn
        have : (n : Fin N) ∈ indexSet fhat zhat j0 ∩ indexSet f z i := ⟨n.property, hn⟩
        have : (n : Fin N) ∈ (∅ : Set (Fin N)) := by simpa [hdis] using this
        exact this.elim
      have : slotGrad f z (n : Fin N) i = 0 := by
        by_contra hne0; exact hnI (by simpa [indexSet] using hne0)
      simpa [slotGrad] using congrArg (fun v : Fin M → ℝ => v b) this
    have hR := jac_eq_slotJac_mul_slotBlock_apply (X:=X) f g hf ghat fhat hhat hfhatc
      z j0 i (n : Fin N) n.property b
    have : (∑ a : Fin M, Ak n a * B a b) = 0 := by
      simpa [Ak, B, hL, mul_comm, zhat] using hR.symm
    simpa [Matrix.mul_apply] using this
  have hrank : Ak.rank = M := by
    simpa [Ak, S, zhat] using slotJac_rank hM (X:=X) ghat fhat hhat hfhatc zhat j0
  have : B = 0 := eq_zero_of_left_mul_eq_zero_of_rank Ak B hrank hmul
  exact hBne this

/-- Prop. 1 + Prop. 3. -/
lemma exists_unique_slotBlock
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (i : Fin K) :
    ∃! j : Fin K, slotBlock (H f ghat) z j i ≠ 0 := by
  classical
  obtain ⟨j0, hj0⟩ :=
    inferred_slot_depends_on_some_slot hM X f g hf hfc ghat fhat hhat z i
  have hj0' : slotBlock (H f ghat) z j0 i ≠ 0 := hj0
  refine ⟨j0, hj0', ?_⟩
  intro j1 hj1
  exact at_most_one_slotBlock hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc z i j1 j0
    hj1 hj0'


/-- Nonempty meeting from a nonzero slot-block (contrapositive of the Prop. 3 argument). -/
lemma meet_nonempty_of_slotBlock_ne
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (i j : Fin K)
    (hB : slotBlock (H f ghat) z j i ≠ 0) :
    (indexSet fhat (H f ghat z) j ∩ indexSet f z i).Nonempty := by
  classical
  by_contra hempty
  have hdis : indexSet fhat (H f ghat z) j ∩ indexSet f z i = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hempty
  let zhat := H f ghat z
  let S := indexSet fhat zhat j
  let Ak : Matrix S (Fin M) ℝ := fun n m => jac fhat zhat (n : Fin N) (j, m)
  let B := slotBlock (H f ghat) z j i
  have hmul : Ak * B = 0 := by
    ext n b
    have hL : jac f z (n : Fin N) (i, b) = 0 := by
      have hnI : (n : Fin N) ∉ indexSet f z i := by
        intro hn
        have hinter : (n : Fin N) ∈ indexSet fhat (H f ghat z) j ∩ indexSet f z i :=
          ⟨by simpa [zhat] using n.property, hn⟩
        rw [hdis] at hinter
        exact hinter.elim
      have hsg : slotGrad f z (n : Fin N) i = 0 := by
        by_contra hne0
        exact hnI (by simpa [indexSet] using hne0)
      simpa [slotGrad] using congrArg (fun v : Fin M → ℝ => v b) hsg
    have hR := jac_eq_slotJac_mul_slotBlock_apply (X:=X) f g hf ghat fhat hhat hfhatc
      z j i (n : Fin N) n.property b
    have : (∑ a : Fin M, Ak n a * B a b) = 0 := by
      simpa [Ak, B, hL, mul_comm, zhat] using hR.symm
    simpa [Matrix.mul_apply] using this
  have hrank : Ak.rank = M := by
    simpa [Ak, S, zhat] using slotJac_rank hM (X:=X) ghat fhat hhat hfhatc zhat j
  have : B = 0 := eq_zero_of_left_mul_eq_zero_of_rank Ak B hrank hmul
  exact hB this

noncomputable def slotPerm
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) : Fin K → Fin K :=
  fun i => Classical.choose (exists_unique_slotBlock hM (X:=X) f g hf hfc hfi
    ghat fhat hhat hfhatc z i).exists

lemma slotPerm_spec
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (i : Fin K) :
    slotBlock (H f ghat) z (slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc z i) i ≠ 0 :=
  Classical.choose_spec (exists_unique_slotBlock hM (X:=X) f g hf hfc hfi
    ghat fhat hhat hfhatc z i).exists

lemma slotPerm_eq
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (i j : Fin K) (hj : slotBlock (H f ghat) z j i ≠ 0) :
    slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc z i = j :=
  Eq.symm <| (exists_unique_slotBlock hM (X:=X) f g hf hfc hfi
    ghat fhat hhat hfhatc z i).unique hj
    (slotPerm_spec hM f g hf hfc hfi ghat fhat hhat hfhatc z i)

lemma slotPerm_injective
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) :
    Function.Injective (slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc z) := by
  intro i₁ i₂ heq
  let j := slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc z i₁
  have hj1 := slotPerm_spec hM f g hf hfc hfi ghat fhat hhat hfhatc z i₁
  have hj2 : slotBlock (H f ghat) z j i₂ ≠ 0 := by
    simpa [j, heq] using slotPerm_spec hM f g hf hfc hfi ghat fhat hhat hfhatc z i₂
  have hm1 := meet_nonempty_of_slotBlock_ne hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc
    z i₁ j hj1
  have hm2 := meet_nonempty_of_slotBlock_ne hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc
    z i₂ j hj2
  exact (unique_index_intersection hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc
    z j).unique hm1 hm2

lemma continuous_slotBlock_entry
    {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (j i : Fin K) (a b : Fin M) :
    Continuous fun z : Lat K M => slotBlock (H f ghat) z j i a b := by
  have hcf := (contDiff_H (X:=X) f g hf ghat fhat hhat).continuous_fderiv_apply (by decide)
  change Continuous fun z => fderiv ℝ (H f ghat) z (Pi.single i (Pi.single b 1)) j a
  exact (continuous_apply a).comp <|
    (continuous_apply j).comp <|
      hcf.comp (Continuous.prodMk continuous_id continuous_const)

lemma isOpen_slotBlock_ne
    {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (j i : Fin K) :
    IsOpen {z : Lat K M | slotBlock (H f ghat) z j i ≠ 0} := by
  have hcont : Continuous fun z : Lat K M => slotBlock (H f ghat) z j i :=
    continuous_matrix fun a b =>
      continuous_slotBlock_entry (X:=X) f g hf ghat fhat hhat j i a b
  exact isOpen_ne.preimage hcont

lemma isClosed_slotBlock_ne
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (j i : Fin K) :
    IsClosed {z : Lat K M | slotBlock (H f ghat) z j i ≠ 0} := by
  have hcompl :
      {z : Lat K M | slotBlock (H f ghat) z j i ≠ 0}ᶜ
        = ⋃ j' : Fin K, ⋃ (_ : j' ≠ j), {z | slotBlock (H f ghat) z j' i ≠ 0} := by
    ext z; constructor
    · intro hz
      obtain ⟨j', hj', _⟩ := exists_unique_slotBlock hM (X:=X) f g hf hfc hfi
        ghat fhat hhat hfhatc z i
      have hne : j' ≠ j := fun h => hz (by simpa [h] using hj')
      exact Set.mem_iUnion.mpr ⟨j', Set.mem_iUnion.mpr ⟨hne, hj'⟩⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨j', hj'⟩
      rcases Set.mem_iUnion.mp hj' with ⟨hne, hjne⟩
      intro hmem
      exact hne ((exists_unique_slotBlock hM (X:=X) f g hf hfc hfi
        ghat fhat hhat hfhatc z i).unique hjne hmem)
  refine isOpen_compl_iff.mp ?_
  simpa [hcompl] using
    isOpen_iUnion fun j' => isOpen_iUnion fun _ =>
      isOpen_slotBlock_ne (X:=X) f g hf ghat fhat hhat j' i

lemma slotPerm_constant
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z₁ z₂ : Lat K M) :
    slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc z₁ =
      slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc z₂ := by
  classical
  funext i
  let π₁ := slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc z₁
  let U := {z : Lat K M | slotBlock (H f ghat) z (π₁ i) i ≠ 0}
  have hclopen : IsClopen U :=
    ⟨isClosed_slotBlock_ne hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc (π₁ i) i,
      isOpen_slotBlock_ne (X:=X) f g hf ghat fhat hhat (π₁ i) i⟩
  haveI : PreconnectedSpace (Lat K M) := inferInstance
  have hUuniv : U = Set.univ :=
    IsClopen.eq_univ hclopen ⟨z₁, slotPerm_spec hM f g hf hfc hfi ghat fhat hhat hfhatc z₁ i⟩
  have hz2 : slotBlock (H f ghat) z₂ (π₁ i) i ≠ 0 := by
    have : z₂ ∈ U := by simpa [hUuniv]
    exact this
  exact (slotPerm_eq hM f g hf hfc hfi ghat fhat hhat hfhatc z₂ i (π₁ i) hz2).symm

noncomputable def globalPerm
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat) : Fin K → Fin K :=
  slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc (0 : Lat K M)

lemma slotBlock_eq_zero_of_ne_global
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (i j : Fin K)
    (hne : j ≠ globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc i) :
    slotBlock (H f ghat) z j i = 0 := by
  have hEq := slotPerm_constant hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc 0 z
  have hne' : j ≠ slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc z i := by
    simpa [globalPerm, hEq] using hne
  by_contra hne0
  exact hne' (slotPerm_eq hM f g hf hfc hfi ghat fhat hhat hfhatc z i j hne0).symm

lemma lat_eq_sum_single (w : Lat K M) :
    w = ∑ k : Fin K, ∑ m : Fin M, w k m • (Pi.single k (Pi.single m (1 : ℝ)) : Lat K M) := by
  classical
  ext k' m'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsingle : ∀ (k : Fin K) (m : Fin M),
      (Pi.single k (Pi.single m (1 : ℝ)) : Lat K M) k' m' =
        if k = k' then (if m = m' then (1 : ℝ) else 0) else 0 := by
    intro k m
    by_cases hk : k = k'
    · subst hk
      rw [Pi.single_eq_same]
      by_cases hm : m = m'
      · subst hm; rw [Pi.single_eq_same]; simp
      · rw [Pi.single_eq_of_ne (Ne.symm hm)]; simp [hm]
    · rw [Pi.single_eq_of_ne (Ne.symm hk)]; simp [hk]
  simp_rw [hsingle]
  rw [Finset.sum_eq_single (a:=k')]
  · rw [Finset.sum_eq_single (a:=m')]
    · simp
    · intro m _ hm; simp [hm]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro k _ hk
    refine Finset.sum_eq_zero fun m _ => by simp [hk]
  · intro h; exact (h (Finset.mem_univ _)).elim

lemma hasDerivAt_line (z v : Lat K M) (t : ℝ) :
    HasDerivAt (fun s : ℝ => z + s • v) v t := by
  simpa using ((hasDerivAt_id (𝕜:=ℝ) t).smul_const v).const_add z

lemma hasDerivAt_H_line
    (Hmap : Lat K M → Lat K M) (hH : Differentiable ℝ Hmap)
    (z v : Lat K M) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Hmap (z + s • v)) (fderiv ℝ Hmap (z + t • v) v) t := by
  have hlineF : HasFDerivAt (fun s : ℝ => z + s • v)
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) t :=
    (hasDerivAt_iff_hasFDerivAt).1 (hasDerivAt_line z v t)
  have hcomp := ((hH (z + t • v)).hasFDerivAt).comp t hlineF
  have hD := HasFDerivAt.hasDerivAt hcomp
  have hEq : ((fderiv ℝ Hmap (z + t • v)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight v)) 1 =
      fderiv ℝ Hmap (z + t • v) v := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  exact hEq ▸ hD

lemma hasDerivAt_H_line_slot
    (Hmap : Lat K M → Lat K M) (hH : Differentiable ℝ Hmap)
    (z v : Lat K M) (j : Fin K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Hmap (z + s • v) j)
      (fderiv ℝ Hmap (z + t • v) v j) t := by
  let p : Lat K M →L[ℝ] (Fin M → ℝ) :=
    ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin K => (Fin M → ℝ)) j
  have hHline := hasDerivAt_H_line Hmap hH z v t
  have hproj : HasFDerivAt (⇑p) p (Hmap (z + t • v)) :=
    ContinuousLinearMap.hasFDerivAt p
  exact HasFDerivAt.comp_hasDerivAt (x:=t) hproj hHline

lemma fderiv_v_slot_of_cross_zero
    (Hmap : Lat K M → Lat K M) (y : Lat K M) (j i : Fin K) (v : Lat K M)
    (hv_i : v i = 0)
    (hpartial : ∀ i' : Fin K, i' ≠ i → slotBlock Hmap y j i' = 0) :
    fderiv ℝ Hmap y v j = 0 := by
  classical
  have hv := lat_eq_sum_single v
  have hmap : fderiv ℝ Hmap y v =
      ∑ k : Fin K, ∑ m : Fin M,
        v k m • fderiv ℝ Hmap y (Pi.single k (Pi.single m (1 : ℝ))) := by
    calc
      fderiv ℝ Hmap y v
          = fderiv ℝ Hmap y
              (∑ k : Fin K, ∑ m : Fin M,
                v k m • (Pi.single k (Pi.single m (1 : ℝ)) : Lat K M)) := by
            conv_lhs => rw [hv]
      _ = ∑ k : Fin K, fderiv ℝ Hmap y
              (∑ m : Fin M, v k m • (Pi.single k (Pi.single m (1 : ℝ)) : Lat K M)) := by
            rw [map_sum]
      _ = ∑ k : Fin K, ∑ m : Fin M,
              fderiv ℝ Hmap y (v k m • (Pi.single k (Pi.single m (1 : ℝ)) : Lat K M)) := by
            refine Fintype.sum_congr _ _ fun k => by rw [map_sum]
      _ = ∑ k : Fin K, ∑ m : Fin M,
              v k m • fderiv ℝ Hmap y (Pi.single k (Pi.single m (1 : ℝ))) := by
            refine Fintype.sum_congr _ _ fun k => Fintype.sum_congr _ _ fun m =>
              ContinuousLinearMap.map_smul (fderiv ℝ Hmap y) _ _
  apply funext; intro a
  have hx : (fderiv ℝ Hmap y v j) a =
      ∑ k : Fin K, ∑ m : Fin M,
        v k m * fderiv ℝ Hmap y (Pi.single k (Pi.single m 1)) j a := by
    have := congrArg (fun w : Lat K M => w j a) hmap
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  rw [hx]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_
  by_cases hk : k = i
  · have : v k m = 0 := by
      rw [hk]
      simpa using congrArg (fun w : Fin M → ℝ => w m) hv_i
    simp [this]
  · have hB := hpartial k hk
    have : fderiv ℝ Hmap y (Pi.single k (Pi.single m 1)) j a = 0 := by
      have := congrArg (fun M : Matrix (Fin M) (Fin M) ℝ => M a m) hB
      simpa [slotBlock] using this
    simp [this]

lemma eq_of_cross_blocks_zero
    (Hmap : Lat K M → Lat K M) (hH : Differentiable ℝ Hmap)
    (j i : Fin K)
    (hpartial : ∀ (y : Lat K M) (i' : Fin K), i' ≠ i → slotBlock Hmap y j i' = 0)
    (z z' : Lat K M) (heq : z i = z' i) :
    Hmap z j = Hmap z' j := by
  classical
  let v : Lat K M := z' - z
  have hv_i : v i = 0 := by
    ext m; simp [v, heq]
  let ψ : ℝ → Fin M → ℝ := fun s => Hmap (z + s • v) j
  have hdiff : Differentiable ℝ ψ := fun t =>
    (hasDerivAt_H_line_slot Hmap hH z v j t).differentiableAt
  have hderiv0 : ∀ t, deriv ψ t = 0 := by
    intro t
    have hD := hasDerivAt_H_line_slot Hmap hH z v j t
    have hval : fderiv ℝ Hmap (z + t • v) v j = 0 :=
      fderiv_v_slot_of_cross_zero Hmap (z + t • v) j i v hv_i
        (fun i' hi => hpartial _ i' hi)
    rw [hD.deriv, hval]
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv0
  have hz : ψ 0 = Hmap z j := by simp [ψ]
  have hz' : ψ 1 = Hmap z' j := by
    change Hmap (z + (1 : ℝ) • (z' - z)) j = Hmap z' j
    simp
  exact hz.symm.trans ((hconst 0 1).trans hz')


noncomputable def embedSlot (k : Fin K) (v : Fin M → ℝ) : Lat K M :=
  fun i => if i = k then v else 0

lemma contDiff_embedSlot (k : Fin K) : ContDiff ℝ 1 (embedSlot (K:=K) (M:=M) k) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i = k
  · convert (contDiff_id : ContDiff ℝ 1 (id : (Fin M → ℝ) → Fin M → ℝ))
    funext v; simp [embedSlot, h]
  · convert (contDiff_const : ContDiff ℝ 1 (fun _ : Fin M → ℝ => (0 : Fin M → ℝ)))
    funext v; simp [embedSlot, h]

noncomputable def slotMap
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) : (Fin M → ℝ) → (Fin M → ℝ) :=
  fun v => H f ghat (embedSlot k v) (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k)

lemma contDiff_slotMap
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) :
    ContDiff ℝ 1 (slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k) := by
  let j := globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k
  have h1 : ContDiff ℝ 1 (H f ghat ∘ embedSlot k) :=
    (contDiff_H (X:=X) f g hf ghat fhat hhat).comp (contDiff_embedSlot k)
  exact (contDiff_apply (ι := Fin K) (E := Fin M → ℝ) (𝕜 := ℝ) j).comp h1

/-- Slice that freezes slot `k` to a fixed value. -/
noncomputable def freezeSlot (k : Fin K) (vk : Fin M → ℝ) (w : Lat K M) : Lat K M :=
  fun i => if i = k then vk else w i

lemma contDiff_freezeSlot (k : Fin K) (vk : Fin M → ℝ) :
    ContDiff ℝ 1 (freezeSlot (K:=K) (M:=M) k vk) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i = k
  · subst h; simpa [freezeSlot] using contDiff_const
  · simpa [freezeSlot, h] using contDiff_apply (ι := Fin K) (E := Fin M → ℝ) (𝕜 := ℝ) i

/-- The partner component depends only on its ground-truth slot. -/
lemma H_eq_slotMap
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (z : Lat K M) (k : Fin K) :
    H f ghat z (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k) =
      slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k (z k) := by
  classical
  let j := globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k
  let z0 : Lat K M := embedSlot k (z k)
  have hpartial : ∀ (y : Lat K M) (i' : Fin K), i' ≠ k →
      slotBlock (H f ghat) y j i' = 0 := by
    intro y i' hi'
    have hne : j ≠ globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc i' := by
      intro hji
      have hinj := slotPerm_injective hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc 0
      have hπk : slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc 0 k = j := by
        simp [j, globalPerm]
      have hπi' : slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc 0 i' = j := hji.symm
      exact hi' (hinj (hπk.trans hπi'.symm)).symm
    exact slotBlock_eq_zero_of_ne_global hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc
      y i' j hne
  have hHdiff := differentiable_H (X:=X) f g hf ghat fhat hhat
  have heq_slot : z k = z0 k := by simp [z0, embedSlot]
  have hEq := eq_of_cross_blocks_zero (H f ghat) hHdiff j k hpartial z z0 heq_slot
  simpa [j, z0, slotMap] using hEq


/-- Base latent used for the slot-map inverse section. -/
noncomputable def baseLat : Lat K M := 0

/-- Section for the inverse: update the partner slot of `H baseLat` to `w`. -/
noncomputable def invSection
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) (w : Fin M → ℝ) : Lat K M :=
  Function.update (H f ghat baseLat)
    (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k) w

lemma contDiff_invSection
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) :
    ContDiff ℝ 1 (invSection hM f g hf hfc hfi ghat fhat hhat hfhatc k) := by
  change ContDiff ℝ 1
    (Function.update (H f ghat baseLat)
      (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k))
  exact contDiff_update (𝕜:=ℝ) (1 : WithTop ℕ∞) (H f ghat baseLat)
    (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k)

noncomputable def slotMapInv
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) : (Fin M → ℝ) → (Fin M → ℝ) :=
  fun w => Ginv g fhat (invSection hM f g hf hfc hfi ghat fhat hhat hfhatc k w) k

lemma contDiff_slotMapInv
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) :
    ContDiff ℝ 1 (slotMapInv hM f g hf hfc hfi ghat fhat hhat hfhatc k) := by
  have h1 : ContDiff ℝ 1
      (Ginv g fhat ∘ invSection hM f g hf hfc hfi ghat fhat hhat hfhatc k) :=
    (contDiff_Ginv (X:=X) f g hf ghat fhat hhat).comp
      (contDiff_invSection hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc k)
  exact (contDiff_apply (ι := Fin K) (E := Fin M → ℝ) (𝕜 := ℝ) k).comp h1

lemma H_embed_other_eq_base
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) (v : Fin M → ℝ) (k' : Fin K) (hk : k' ≠ k) :
    H f ghat (embedSlot k v)
        (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k') =
      H f ghat baseLat
        (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k') := by
  have h1 := H_eq_slotMap hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc
    (embedSlot k v) k'
  have h0 := H_eq_slotMap hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc baseLat k'
  have hv : (embedSlot k v) k' = (0 : Fin M → ℝ) := by simp [embedSlot, hk]
  have hbase : baseLat k' = (0 : Fin M → ℝ) := by simp [baseLat]
  calc
    H f ghat (embedSlot k v) (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k')
        = slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k' ((embedSlot k v) k') := h1
    _ = slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k' 0 := by simp [hv]
    _ = slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k' (baseLat k') := by simp [hbase]
    _ = H f ghat baseLat (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k') := h0.symm

lemma invSection_eq_H_embed
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) (v : Fin M → ℝ) :
    invSection hM f g hf hfc hfi ghat fhat hhat hfhatc k
        (slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k v) =
      H f ghat (embedSlot k v) := by
  classical
  let j := globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k
  apply funext; intro jout
  by_cases hj : jout = j
  · subst hj
    simp [invSection, Function.update_self, j, slotMap]
  · have hjne : jout ≠ j := hj
    have hinj := slotPerm_injective hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc 0
    have hsurj : Function.Surjective
        (slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc 0) :=
      (Finite.injective_iff_surjective (f :=
        slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc 0)).1 hinj
    obtain ⟨k', hk'⟩ := (by simpa [globalPerm] using hsurj jout :
      ∃ k' : Fin K, globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k' = jout)
    have hk'ne : k' ≠ k := by
      intro hkk
      exact hjne (by simpa [j, hkk] using hk'.symm)
    have hupd :
        Function.update (H f ghat baseLat) j
          (slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k v) jout =
          H f ghat baseLat jout :=
      Function.update_of_ne hjne _ _
    calc
      invSection hM f g hf hfc hfi ghat fhat hhat hfhatc k
          (slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k v) jout
          = H f ghat baseLat jout := by simpa [invSection] using hupd
      _ = H f ghat baseLat
            (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k') := by simp [hk']
      _ = H f ghat (embedSlot k v)
            (globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k') :=
          (H_embed_other_eq_base hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc
            k v k' hk'ne).symm
      _ = H f ghat (embedSlot k v) jout := by simp [hk']

lemma leftInverse_slotMap
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) :
    Function.LeftInverse
      (slotMapInv hM f g hf hfc hfi ghat fhat hhat hfhatc k)
      (slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k) := by
  intro v
  have hsec := invSection_eq_H_embed hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc k v
  have hL := leftInverse_Ginv_H (X:=X) f g hf ghat fhat hhat (embedSlot k v)
  calc
    slotMapInv hM f g hf hfc hfi ghat fhat hhat hfhatc k
        (slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k v)
        = Ginv g fhat (H f ghat (embedSlot k v)) k := by
          simp [slotMapInv, hsec]
    _ = embedSlot k v k := by simpa using congrArg (fun z : Lat K M => z k) hL
    _ = v := by simp [embedSlot]

lemma rightInverse_slotMap
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) :
    Function.RightInverse
      (slotMapInv hM f g hf hfc hfi ghat fhat hhat hfhatc k)
      (slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k) := by
  intro w
  let j := globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k
  let zhat := invSection hM f g hf hfc hfi ghat fhat hhat hfhatc k w
  let u := Ginv g fhat zhat k
  have hR := rightInverse_Ginv_H (X:=X) f g hf ghat fhat hhat zhat
  have hzj : zhat j = w := by
    simp [zhat, invSection, j, Function.update_self]
  have h1 : H f ghat (Ginv g fhat zhat) j = w := by
    simp [hR, hzj]
  have h2 : H f ghat (Ginv g fhat zhat) j =
      slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k u := by
    simpa [j] using
      H_eq_slotMap hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc (Ginv g fhat zhat) k
  simpa [slotMapInv, zhat, u] using (h2.symm.trans h1)

lemma isSlotDiffeo_slotMap
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat)
    (k : Fin K) :
    IsSlotDiffeo (slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k) := by
  refine ⟨contDiff_slotMap hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc k, ?_⟩
  refine ⟨slotMapInv hM f g hf hfc hfi ghat fhat hhat hfhatc k,
    contDiff_slotMapInv hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc k, ?_, ?_⟩
  · exact leftInverse_slotMap hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc k
  · exact rightInverse_slotMap hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc k

lemma slotBlock_ne_of_slotDiffeo_dep
    (hM : 0 < M)
    (Hmap : Lat K M → Lat K M) (_hH : Differentiable ℝ Hmap)
    (k j : Fin K) (h : (Fin M → ℝ) → (Fin M → ℝ)) (hh : IsSlotDiffeo h)
    (hdep : ∀ z : Lat K M, Hmap z j = h (z k)) :
    slotBlock Hmap (0 : Lat K M) j k ≠ 0 := by
  classical
  obtain ⟨h', hh', hL, _hR⟩ := hh.2
  have hAt : DifferentiableAt ℝ h (0 : Fin M → ℝ) :=
    (hh.1.differentiable (by decide)).differentiableAt
  have hAt' : DifferentiableAt ℝ h' (h (0 : Fin M → ℝ)) :=
    (hh'.differentiable (by decide)).differentiableAt
  have hinv : (fderiv ℝ h' (h 0)).comp (fderiv ℝ h 0) =
      ContinuousLinearMap.id ℝ (Fin M → ℝ) := by
    have heq : h' ∘ h = id := funext hL
    have hcomp := fderiv_comp (𝕜:=ℝ) (f:=h) (g:=h') (0 : Fin M → ℝ) hAt' hAt
    calc
      (fderiv ℝ h' (h 0)).comp (fderiv ℝ h 0)
          = fderiv ℝ (h' ∘ h) 0 := hcomp.symm
      _ = fderiv ℝ (id : (Fin M → ℝ) → Fin M → ℝ) 0 := by rw [heq]
      _ = ContinuousLinearMap.id ℝ (Fin M → ℝ) := fderiv_id
  have hfd_ne : fderiv ℝ h (0 : Fin M → ℝ) ≠ 0 := by
    intro hf0
    have : (0 : (Fin M → ℝ) →L[ℝ] Fin M → ℝ) =
        ContinuousLinearMap.id ℝ (Fin M → ℝ) := by simpa [hf0] using hinv
    have hid0 := this.symm
    have h1 : (fun _ : Fin M => (1 : ℝ)) = (0 : Fin M → ℝ) := by
      simpa using congrArg (fun L : (Fin M → ℝ) →L[ℝ] Fin M → ℝ => L (fun _ => 1)) hid0
    have : (1 : ℝ) = 0 := by
      simpa using congrArg (fun v : Fin M → ℝ => v ⟨0, hM⟩) h1
    exact one_ne_zero this
  -- Chain rule: fderiv (z ↦ Hmap z j) 0 (Pi.single k e_b) = fderiv h 0 e_b
  let pk : Lat K M →L[ℝ] (Fin M → ℝ) :=
    ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin K => Fin M → ℝ) k
  have hprojDiff : DifferentiableAt ℝ (⇑pk) (0 : Lat K M) :=
    (pk.contDiff (n:=(1 : WithTop ℕ∞)).differentiable (by decide)).differentiableAt
  have hchain := fderiv_comp (𝕜:=ℝ) (f:=⇑pk) (g:=h) (0 : Lat K M) hAt hprojDiff
  have hproj0 : fderiv ℝ (⇑pk) (0 : Lat K M) = pk := ContinuousLinearMap.fderiv pk
  have hEq : fderiv ℝ (fun z : Lat K M => Hmap z j) 0 =
      fderiv ℝ (h ∘ ⇑pk) 0 := by
    apply Filter.EventuallyEq.fderiv_eq
    refine Filter.EventuallyEq.of_eq ?_
    funext z; simpa [pk] using hdep z
  have hdir : ∀ b, fderiv ℝ (fun z : Lat K M => Hmap z j) 0
      (Pi.single k (Pi.single b 1)) = fderiv ℝ h 0 (Pi.single b 1) := by
    intro b
    rw [hEq, hchain, hproj0]
    simp [ContinuousLinearMap.comp_apply, pk, ContinuousLinearMap.proj_apply,
      Pi.single_eq_same]
  intro hB0
  apply hfd_ne
  apply ContinuousLinearMap.ext
  intro δ
  have hδ : δ = ∑ b : Fin M, δ b • Pi.single b (1 : ℝ) := by
    ext b0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_single b0 (fun b _ hb => by simp [Ne.symm hb])
      (fun hh => (hh (Finset.mem_univ _)).elim)]
    simp
  have hsum : fderiv ℝ h 0 δ =
      ∑ b : Fin M, δ b • fderiv ℝ h 0 (Pi.single b 1) := by
    calc
      fderiv ℝ h 0 δ
          = fderiv ℝ h 0 (∑ b : Fin M, δ b • Pi.single b (1 : ℝ)) := by
            conv_lhs => rw [hδ]
      _ = ∑ b : Fin M, fderiv ℝ h 0 (δ b • Pi.single b (1 : ℝ)) := by rw [map_sum]
      _ = ∑ b : Fin M, δ b • fderiv ℝ h 0 (Pi.single b (1 : ℝ)) := by
            refine Fintype.sum_congr _ _ fun b =>
              ContinuousLinearMap.map_smul (fderiv ℝ h 0) _ _
  rw [hsum]
  refine Finset.sum_eq_zero fun b _ => ?_
  have : fderiv ℝ h 0 (Pi.single b 1) = 0 := by
    funext a
    have hsb : slotBlock Hmap 0 j k a b = 0 := by
      simpa using congrArg (fun M : Matrix (Fin M) (Fin M) ℝ => M a b) hB0
    -- slotBlock = (fderiv Hmap 0 e) j a
    have h1 : (fderiv ℝ Hmap 0 (Pi.single k (Pi.single b 1)) j) a = 0 := by
      simpa [slotBlock] using hsb
    -- relate to fderiv of projected map
    let pj : Lat K M →L[ℝ] (Fin M → ℝ) :=
      ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin K => Fin M → ℝ) j
    have hH0 : DifferentiableAt ℝ Hmap (0 : Lat K M) := _hH.differentiableAt
    have hpj : DifferentiableAt ℝ (⇑pj) (Hmap 0) :=
      (pj.contDiff (n:=(1 : WithTop ℕ∞)).differentiable (by decide)).differentiableAt
    have hcompj := fderiv_comp (𝕜:=ℝ) (f:=Hmap) (g:=⇑pj) (0 : Lat K M) hpj hH0
    have hpj0 : fderiv ℝ (⇑pj) (Hmap 0) = pj := ContinuousLinearMap.fderiv pj
    have hfunj : (fun z : Lat K M => Hmap z j) = ⇑pj ∘ Hmap := by
      funext z; simp [pj]
    have : fderiv ℝ (fun z : Lat K M => Hmap z j) 0
        (Pi.single k (Pi.single b 1)) a = 0 := by
      have hEq : fderiv ℝ (fun z => Hmap z j) 0 = fderiv ℝ (⇑pj ∘ Hmap) 0 := by
        apply Filter.EventuallyEq.fderiv_eq
        exact Filter.EventuallyEq.of_eq hfunj
      have : fderiv ℝ (⇑pj ∘ Hmap) 0 (Pi.single k (Pi.single b 1)) =
          pj (fderiv ℝ Hmap 0 (Pi.single k (Pi.single b 1))) := by
        rw [hcompj, hpj0]; rfl
      have : fderiv ℝ (fun z => Hmap z j) 0 (Pi.single k (Pi.single b 1)) =
          fderiv ℝ Hmap 0 (Pi.single k (Pi.single b 1)) j := by
        rw [hEq, this]; simp [pj]
      simpa [this] using h1
    exact (congrArg (fun v : Fin M → ℝ => v a) (hdir b)).symm.trans this
  simp [this]


lemma slot_identifies_H
    (hM : 0 < M) {X : Set (Obs N)}
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat) :
    SlotIdentifies f ghat := by
  classical
  intro k
  refine ⟨globalPerm hM f g hf hfc hfi ghat fhat hhat hfhatc k, ?_, ?_⟩
  · refine ⟨slotMap hM f g hf hfc hfi ghat fhat hhat hfhatc k, ?_⟩
    refine ⟨isSlotDiffeo_slotMap hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc k, ?_⟩
    intro z
    have hEq := H_eq_slotMap hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc z k
    simpa [H] using hEq
  · intro j hj
    rcases hj with ⟨h, hh, hdep⟩
    have hne : slotBlock (H f ghat) (0 : Lat K M) j k ≠ 0 :=
      slotBlock_ne_of_slotDiffeo_dep hM (H f ghat)
        (differentiable_H (X:=X) f g hf ghat fhat hhat) k j h hh
        (fun z => by simpa [H] using hdep z)
    have : slotPerm hM f g hf hfc hfi ghat fhat hhat hfhatc 0 k = j :=
      slotPerm_eq hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc 0 k j hne
    simpa [globalPerm] using this.symm

end SlotId

open SlotId

/-- Official Theorem 1: slot identifiability. -/
theorem solution {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat) :
    SlotIdentifies f ghat :=
  slot_identifies_H hM (X:=X) f g hf hfc hfi ghat fhat hhat hfhatc
