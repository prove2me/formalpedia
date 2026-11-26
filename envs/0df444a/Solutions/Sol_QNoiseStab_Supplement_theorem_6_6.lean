-- Prove2me | solution 1 for QNoiseStab.Supplement.theorem_6_6
-- status  : ACCEPTED   (prove)
-- author  : @blake-holman
-- created : 2026-11-26T04:04:19.729882+00:00
-- url     : https://prove2.me/submissions/2af48f21-0c31-46f5-838b-25a65c610352

import Mathlib
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_FitsInSpace
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_successProb
import Definitions.Def_QNoiseStab_Supplement_IsRigid
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Definitions.Def_QNoiseStab_noiseProb
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QNoiseStab_phaseQuery
import Definitions.Def_QNoiseStab_fourierWeight
import Definitions.Def_QNoiseStab_fourierVec
import Definitions.Def_QNoiseStab_successProb
import Definitions.Def_QNoiseStab_eventSet
import Definitions.Def_QNoiseStab_projLowDeg
import Definitions.Def_QNoiseStab_projEvent
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QNoiseStab_noiseOp
import Definitions.Def_QNoiseStab_noiseKernel
import Definitions.Def_QNoiseStab_coordNoise
import Definitions.Def_QNoiseStab_singleNoiseOp
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Order.Floor.Div

-- Paper.MatrixVector.Rigidity
section
/-! Rigidity and counting solutions over a finite subset of an arbitrary field. -/

namespace QuantumNoiseStability.MatrixVector

open Finset
open scoped Classical

variable {F : Type*} [Field F] {m n : ℕ}

/-- Rank after restricting to the rows in `K` and columns in `L`. -/
noncomputable def submatrixRank (M : Matrix (Fin m) (Fin n) F)
    (K : Finset (Fin m)) (L : Finset (Fin n)) : ℕ :=
  (M.submatrix (fun i : K => i.val) (fun j : L => j.val)).rank

/-- Definition 6.1. -/
def IsRigid (M : Matrix (Fin m) (Fin n) F) (g h : ℕ) (c : ℝ) : Prop :=
  ∀ K L, K.card ≤ g → n - h ≤ L.card → c * K.card ≤ (submatrixRank M K L : ℝ)

private def columnSpan (M : Matrix (Fin m) (Fin n) F) (K : Finset (Fin m))
    (L : Finset (Fin n)) : Submodule F (K → F) :=
  Submodule.span F ((fun j (i : K) => M i j) '' (L : Set (Fin n)))

private theorem submatrixRank_eq (M : Matrix (Fin m) (Fin n) F)
    (K : Finset (Fin m)) (L : Finset (Fin n)) :
    submatrixRank M K L = Module.finrank F (columnSpan M K L) := by
  rw [submatrixRank, Matrix.rank_eq_finrank_span_cols, columnSpan, Set.image_eq_range]
  rfl

private theorem columnSpan_mono (M : Matrix (Fin m) (Fin n) F) (K : Finset (Fin m))
    {L U : Finset (Fin n)} (h : L ⊆ U) : columnSpan M K L ≤ columnSpan M K U :=
  Submodule.span_mono (Set.image_mono h)

theorem submatrixRank_mono (M : Matrix (Fin m) (Fin n) F) (K : Finset (Fin m)) :
    Monotone (submatrixRank M K) := by
  intro L U h
  simp only [submatrixRank_eq]
  exact Submodule.finrank_mono (columnSpan_mono M K h)

@[simp] theorem submatrixRank_empty (M : Matrix (Fin m) (Fin n) F) (K : Finset (Fin m)) :
    submatrixRank M K ∅ = 0 := by
  rw [submatrixRank_eq, columnSpan, Finset.coe_empty, Set.image_empty, Submodule.span_empty]
  simp

/-- Testing a single row on all columns and on the empty set gives the parameter
bounds used in the query proof. -/
theorem IsRigid.parameter_bounds {M : Matrix (Fin m) (Fin n) F} {g h : ℕ} {c : ℝ}
    (hr : IsRigid M g h c) (hm : 0 < m) (hg : 0 < g) (hc : 0 < c) :
    c ≤ 1 ∧ h < n := by
  let K : Finset (Fin m) := {⟨0, hm⟩}
  have hK : K.card = 1 := card_singleton _
  have hKg : K.card ≤ g := hK ▸ hg
  have hfull := hr K univ hKg (by simp)
  have hrow : submatrixRank M K univ ≤ K.card := by
    simpa only [submatrixRank, Fintype.card_coe] using
      Matrix.rank_le_card_height (M.submatrix (fun i : K => i.val)
        (fun j : (univ : Finset (Fin n)) => j.val))
  rw [hK, Nat.cast_one, mul_one] at hfull
  rw [hK] at hrow
  refine ⟨hfull.trans (by exact_mod_cast hrow), ?_⟩
  by_contra! hh
  have he := hr K ∅ hKg (by simp [Nat.sub_eq_zero_of_le hh])
  simp [hK] at he
  exact hc.not_ge he

private theorem col_mem_span (M : Matrix (Fin m) (Fin n) F) (K : Finset (Fin m))
    {L : Finset (Fin n)} {j : Fin n} (hj : j ∈ L) :
    (fun i : K => M i j) ∈ columnSpan M K L :=
  Submodule.subset_span ⟨j, hj, rfl⟩

/-- Below the rigidity threshold, at least `h + 1` unselected columns increase rank. -/
theorem IsRigid.lt_card_increasing {M : Matrix (Fin m) (Fin n) F} {g h : ℕ} {c : ℝ}
    (hr : IsRigid M g h c) {K : Finset (Fin m)} (hK : K.card ≤ g)
    (L : Finset (Fin n)) (hlow : (submatrixRank M K L : ℝ) < c * K.card) :
    h < (Lᶜ.filter (fun j => submatrixRank M K L < submatrixRank M K (insert j L))).card := by
  classical
  let C := Lᶜ.filter (fun j => submatrixRank M K L < submatrixRank M K (insert j L))
  change h < C.card
  by_contra! hsmall
  have hwide : n - h ≤ Cᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hspan : columnSpan M K Cᶜ ≤ columnSpan M K L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    by_contra hnot
    have outside : j ∉ L := fun h => hnot (col_mem_span M K h)
    have hlt : columnSpan M K L < columnSpan M K (insert j L) :=
      lt_of_le_not_ge (columnSpan_mono M K (Finset.subset_insert _ _))
        (fun h => hnot (h (col_mem_span M K (Finset.mem_insert_self _ _))))
    have inc : submatrixRank M K L < submatrixRank M K (insert j L) := by
      simpa only [submatrixRank_eq] using Submodule.finrank_lt_finrank_of_lt hlt
    exact Finset.mem_compl.mp hj (Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr outside, inc⟩)
  have hle : submatrixRank M K Cᶜ ≤ submatrixRank M K L := by
    simpa only [submatrixRank_eq] using Submodule.finrank_mono hspan
  exact hlow.not_ge ((hr K Cᶜ hK hwide).trans (by exact_mod_cast hle))

variable {I J : Type*} [Fintype J]

/-- There is a set of pivot columns of cardinality equal to the matrix rank. -/
theorem exists_pivot_columns (A : Matrix I J F) :
    ∃ P : Finset J, P.card = A.rank ∧
      LinearIndependent F (fun j : P => A.col j.val) := by
  classical
  obtain ⟨s, -, -, hspan, hli⟩ := exists_linearIndepOn_extension
    (v := A.col) (K := F) (linearIndepOn_empty F A.col) (Set.empty_subset (Set.univ : Set J))
  let P := s.toFinset
  have heq : (P : Set J) = s := Set.coe_toFinset _
  have hi : LinearIndependent F (fun j : P => A.col j.val) := by
    change LinearIndepOn F A.col (P : Set J)
    rwa [heq]
  refine ⟨P, ?_, hi⟩
  rw [Matrix.rank_eq_finrank_span_cols]
  have hs : Submodule.span F (Set.range A.col) =
      Submodule.span F (A.col '' (P : Set J)) := by
    rw [heq]
    apply le_antisymm
    · exact Submodule.span_le.mpr (by simpa using hspan)
    · exact Submodule.span_mono (Set.image_subset_range _ _)
  rw [hs, Set.image_eq_range]
  rw [← Fintype.card_coe P]
  exact (finrank_span_eq_card hi).symm

/-- Fixing coordinates outside independent columns makes the product injective on
the remaining coordinates. -/
theorem eq_of_mulVec_eq_of_eq_off_pivots (A : Matrix I J F) (P : Finset J)
    (hi : LinearIndependent F (fun j : P => A.col j.val)) {x z : J → F}
    (hout : ∀ j ∉ P, x j = z j) (hy : A.mulVec x = A.mulVec z) : x = z := by
  classical
  let B := A.submatrix id (fun j : P => j.val)
  have hinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.mpr hi
  have he : (fun j : P => x j.val) = fun j : P => z j.val := by
    apply hinj
    funext i
    have heq := congrFun hy i
    change ∑ j, A i j * x j = ∑ j, A i j * z j at heq
    rw [← Finset.sum_add_sum_compl P (fun j => A i j * x j),
        ← Finset.sum_add_sum_compl P (fun j => A i j * z j)] at heq
    have hsame : (∑ j ∈ Pᶜ, A i j * x j) = ∑ j ∈ Pᶜ, A i j * z j :=
      Finset.sum_congr rfl fun j hj => by rw [hout j (Finset.mem_compl.mp hj)]
    rw [hsame] at heq
    exact (P.sum_attach (fun j => A i j * x j)).trans
      ((add_right_cancel heq).trans (P.sum_attach (fun j => A i j * z j)).symm)
  funext j
  by_cases hj : j ∈ P
  · exact congrFun he ⟨j, hj⟩
  · exact hout j hj

/-- Number of inputs from an arbitrary finite field subset with a prescribed output. -/
theorem card_mulVec_eq_le (A : Matrix I J F) (D : Finset F) (y : I → F) :
    Fintype.card {x : J → D // A.mulVec (fun j => (x j : F)) = y} ≤
      D.card ^ (Fintype.card J - A.rank) := by
  classical
  obtain ⟨P, hP, hi⟩ := exists_pivot_columns A
  let restrict (x : {x : J → D // A.mulVec (fun j => (x j : F)) = y}) (j : {j // j ∉ P}) :=
    x.val j.val
  have inj : Function.Injective restrict := by
    intro x z he
    have heq := eq_of_mulVec_eq_of_eq_off_pivots A P hi
      (x := fun j => (x.val j : F)) (z := fun j => (z.val j : F))
      (fun j hj => congrArg Subtype.val (congrFun he ⟨j, hj⟩))
      (x.property.trans z.property.symm)
    exact Subtype.ext (funext fun j => Subtype.ext (congrFun heq j))
  simpa [Fintype.card_fun, Fintype.card_subtype_compl, hP] using Fintype.card_le_of_injective _ inj

theorem natCard_mulVec_eq_le (A : Matrix I J F) (D : Finset F) (y : I → F) :
    Nat.card {x : J → D // A.mulVec (fun j => (x j : F)) = y} ≤
      D.card ^ (Fintype.card J - A.rank) := by
  rw [Nat.card_eq_fintype_card]
  exact card_mulVec_eq_le A D y

/-- Conditional point probability for a uniform input in the product alphabet. -/
theorem uniform_mulVec_eq_le (A : Matrix I J F) (D : Finset F) (hD : D.Nonempty)
    (y : I → F) :
    (Fintype.card {x : J → D // A.mulVec (fun j => (x j : F)) = y} : ℝ) /
      D.card ^ Fintype.card J ≤ ((D.card : ℝ) ^ A.rank)⁻¹ := by
  have hd : (0 : ℝ) < D.card := by exact_mod_cast hD.card_pos
  have h := card_mulVec_eq_le A D y
  have hr : A.rank ≤ Fintype.card J := Matrix.rank_le_card_width _
  rw [div_le_iff₀ (by positivity), ← Nat.sub_add_cancel hr, pow_add]
  field_simp
  exact_mod_cast h

end QuantumNoiseStability.MatrixVector
end

-- Paper.Probability.RankSampling
section
/-!
# Rank under uniform sampling without replacement

For a fixed set of rows, regard column rank as a natural-valued function of the selected
columns. The sample space for `k` draws is `U.powersetCard k`, with equal weight on each
subset. The one-step success probability may depend on all the selected columns.
-/


namespace QuantumNoiseStability.Probability.RankSampling

open Finset
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- The remaining columns whose insertion strictly increases rank. -/
def improvingColumns (U : Finset α) (rank : Finset α → ℕ) (s : Finset α) : Finset α :=
  (U \ s).filter fun x => rank s < rank (insert x s)

/-- Below the rigidity threshold, more than `h` remaining columns increase rank.
The closure property says that a dependent column stays dependent after adding columns. -/
theorem lt_card_improvingColumns_of_rigid
    (U : Finset α) (rank : Finset α → ℕ) (threshold : ℝ) (h : ℕ)
    (mono : Monotone rank)
    (closure : ∀ s t : Finset α, s ⊆ t → ∀ x,
      rank (insert x s) = rank s → rank (insert x t) = rank t)
    (rigid : ∀ t ⊆ U, U.card - h ≤ t.card → threshold ≤ rank t)
    {s : Finset α} (hs : s ⊆ U) (low : (rank s : ℝ) < threshold) :
    h < (improvingColumns U rank s).card := by
  let good := improvingColumns U rank s
  let flat := U \ good
  have hsflat : s ⊆ flat := by
    intro x hx
    exact mem_sdiff.mpr ⟨hs hx, fun hg => (mem_sdiff.mp (mem_filter.mp hg).1).2 hx⟩
  have dep (x : α) (hx : x ∈ flat) : rank (insert x s) = rank s := by
    apply le_antisymm _ (mono (subset_insert _ _))
    by_contra! inc
    have hxs : x ∉ s := fun hm => by simp [insert_eq_of_mem hm] at inc
    exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1, hxs⟩, inc⟩)
  have same (t : Finset α) (ht : t ⊆ flat) : rank (t ∪ s) = rank s := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert x t _ ih =>
      rw [insert_union, closure s (t ∪ s) subset_union_right x (dep x (ht (mem_insert_self x t)))]
      exact ih ((subset_insert _ _).trans ht)
  have hflat : rank flat = rank s := by simpa [union_eq_left.mpr hsflat] using same flat Subset.rfl
  by_contra! few
  have hsize : U.card - h ≤ flat.card := by
    rw [card_sdiff_of_subset (show good ⊆ U from
      fun x hx => (mem_sdiff.mp (mem_filter.mp hx).1).1)]
    exact Nat.sub_le_sub_left few _
  exact low.not_ge (hflat ▸ rigid flat sdiff_subset hsize)

/-- Each set of size `j+1` is produced by exactly `j+1` single insertions from size `j`. -/
private theorem sum_insert_layer (U : Finset α) (j : ℕ) (f : Finset α → ℝ) :
    (∑ s ∈ U.powersetCard j, ∑ x ∈ U \ s, f (insert x s)) =
      (j + 1 : ℝ) * ∑ t ∈ U.powersetCard (j+1), f t := by
  calc
    _ = ∑ t ∈ U.powersetCard (j+1), ∑ _x ∈ t, f t := by
      rw [sum_sigma', sum_sigma']
      apply sum_nbij' (fun ⟨s,x⟩ => ⟨insert x s, x⟩) (fun ⟨t,x⟩ => ⟨t.erase x, x⟩)
      · rintro ⟨s,x⟩ hm
        obtain ⟨⟨hs, hc⟩, hx, hxs⟩ := (mem_sigma.trans
          (mem_powersetCard.and mem_sdiff)).mp hm
        exact mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨insert_subset hx hs,
          (card_insert_of_notMem hxs).trans (by rw [hc])⟩, mem_insert_self _ _⟩
      · rintro ⟨t,x⟩ hm
        obtain ⟨ht, hx⟩ := mem_sigma.mp hm
        obtain ⟨hU, hc⟩ := mem_powersetCard.mp ht
        exact mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨(erase_subset _ _).trans hU, by
          rw [card_erase_of_mem hx, hc, Nat.add_one_sub_one]⟩,
          mem_sdiff.mpr ⟨hU hx, notMem_erase _ _⟩⟩
      · rintro ⟨s,x⟩ hm
        simp [erase_insert (mem_sdiff.mp (mem_sigma.mp hm).2).2]
      · rintro ⟨t,x⟩ hm
        simp [insert_erase (mem_sigma.mp hm).2]
      · intros; rfl
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro t ht
      simp [(mem_powersetCard.mp ht).2]

/-- Exponential weight restricted to the event that the rank is still below threshold. -/
private noncomputable def weight (rank : Finset α → ℕ) (threshold : ℝ) (s : Finset α) : ℝ :=
  if (rank s : ℝ) < threshold then Real.exp (-(rank s : ℝ)) else 0

omit [DecidableEq α] in
private theorem weight_nonneg (rank : Finset α → ℕ) (threshold : ℝ) (s : Finset α) :
    0 ≤ weight rank threshold s := by
  unfold weight
  split <;> positivity

private theorem weight_step (U s : Finset α) (rank : Finset α → ℕ) (threshold p : ℝ)
    (mono : Monotone rank)
    (success : (rank s : ℝ) < threshold →
      p * (U \ s).card ≤ (improvingColumns U rank s).card) :
    (∑ x ∈ U \ s, weight rank threshold (insert x s)) ≤
      (U \ s).card * Real.exp (-p/2) * weight rank threshold s := by
  by_cases low : (rank s : ℝ) < threshold
  · have half : Real.exp (-1) ≤ 1/2 := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 2)]
      linarith [Real.add_one_le_exp 1]
    have step (x : α) :
        weight rank threshold (insert x s) ≤
          (1 - (if rank s < rank (insert x s) then 1 else 0) / 2) *
            weight rank threshold s := by
      simp only [weight, if_pos low]
      have inc := mono (subset_insert x s)
      by_cases improves : rank s < rank (insert x s)
      · simp only [if_pos improves]
        split
        · have h : (rank s : ℝ) + 1 ≤ rank (insert x s) := by exact_mod_cast improves
          calc
            _ ≤ Real.exp (-(rank s : ℝ) + (-1)) := Real.exp_le_exp.mpr (by linarith)
            _ = _ := Real.exp_add _ _
            _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left half (Real.exp_pos (-(rank s : ℝ))).le]
        · positivity
      · rw [if_neg improves, le_antisymm (le_of_not_gt improves) inc, if_pos low]
        simp
    calc
      _ ≤ ∑ x ∈ U \ s, (1 - (if rank s < rank (insert x s) then 1 else 0) / 2) *
          weight rank threshold s := sum_le_sum fun x _ => step x
      _ = ((U \ s).card - (improvingColumns U rank s).card / 2) * weight rank threshold s := by
        rw [← sum_mul, sum_sub_distrib, ← sum_div, sum_boole]
        simp [improvingColumns]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (weight_nonneg ..)
        have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-p/2))
          (Nat.cast_nonneg (U \ s).card : (0:ℝ) ≤ _)
        linarith only [he, success low]
  · have dead (x : α) : ¬ (rank (insert x s) : ℝ) < threshold :=
      not_lt.mpr ((le_of_not_gt low).trans (by exact_mod_cast mono (subset_insert x s)))
    simp [weight, low, dead]

private theorem sum_weight_le (U : Finset α) (rank : Finset α → ℕ) (threshold p : ℝ)
    (mono : Monotone rank) (k : ℕ)
    (success : ∀ s ⊆ U, s.card < k → (rank s : ℝ) < threshold →
      p * (U \ s).card ≤ (improvingColumns U rank s).card) :
    ∑ s ∈ U.powersetCard k, weight rank threshold s ≤
      (U.card.choose k : ℝ) * Real.exp (-(k : ℝ) * p / 2) := by
  induction k with
  | zero =>
    simp only [powersetCard_zero, sum_singleton, Nat.choose_zero_right, Nat.cast_one,
      Nat.cast_zero, neg_zero, zero_mul, zero_div, Real.exp_zero, one_mul]
    unfold weight
    split
    · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
    · norm_num
  | succ j ih =>
    have prev := ih fun s hs hj => success s hs (by omega)
    let count : ℝ := (U.card - j : ℕ)
    have count_nonneg : 0 ≤ count := Nat.cast_nonneg _
    have choose_id : count * (U.card.choose j : ℝ) =
        ((j : ℝ) + 1) * U.card.choose (j+1) := by
      dsimp [count]
      exact_mod_cast (by simpa [Nat.mul_comm] using
        (Nat.choose_succ_right_eq U.card j).symm :
        (U.card - j) * U.card.choose j = (j + 1) * U.card.choose (j + 1))
    apply le_of_mul_le_mul_left (a := (j : ℝ) + 1) _ (by positivity)
    calc
      _ = ∑ s ∈ U.powersetCard j, ∑ x ∈ U \ s, weight rank threshold (insert x s) :=
        (sum_insert_layer ..).symm
      _ ≤ ∑ s ∈ U.powersetCard j, count * Real.exp (-p/2) * weight rank threshold s := by
        apply sum_le_sum
        intro s hs
        obtain ⟨hU,hj⟩ := mem_powersetCard.mp hs
        simpa only [card_sdiff_of_subset hU, hj, count] using
          weight_step U s rank threshold p mono (success s hU (by omega))
      _ = count * Real.exp (-p/2) * ∑ s ∈ U.powersetCard j, weight rank threshold s :=
        (mul_sum ..).symm
      _ ≤ count * Real.exp (-p/2) * ((U.card.choose j : ℝ) * Real.exp (-(j : ℝ) * p / 2)) :=
        mul_le_mul_of_nonneg_left prev (mul_nonneg count_nonneg (Real.exp_pos _).le)
      _ = _ := by
        rw [show count * Real.exp (-p/2) * ((U.card.choose j : ℝ) * Real.exp (-(j : ℝ) * p / 2)) =
          (count * U.card.choose j) * (Real.exp (-p/2) * Real.exp (-(j : ℝ) * p / 2)) by ring,
          choose_id, ← Real.exp_add, Nat.cast_succ]
        ring_nf

/-- Lower tail for a uniform subset of `k` columns. Given any selected set below threshold,
the next uniform remaining column increases rank with probability at least `p`.
The numerator counts the bad subsets and the denominator counts all samples. -/
theorem uniformSubset_rank_lowerTail (U : Finset α) (rank : Finset α → ℕ) (threshold p : ℝ)
    (mono : Monotone rank) {k : ℕ} (hk : k ≤ U.card)
    (success : ∀ s ⊆ U, s.card < k → (rank s : ℝ) < threshold →
      p * (U \ s).card ≤ (improvingColumns U rank s).card) :
    (((U.powersetCard k).filter fun s => (rank s : ℝ) < min threshold (k * p / 4)).card : ℝ) /
      U.card.choose k ≤ Real.exp (-(k : ℝ) * p / 4) := by
  have bound := sum_weight_le U rank threshold p mono k success
  apply (div_le_iff₀ (by exact_mod_cast Nat.choose_pos hk : (0 : ℝ) < U.card.choose k)).mpr
  rw [← sum_boole]
  calc
    _ ≤ ∑ s ∈ U.powersetCard k, weight rank threshold s * Real.exp (k * p / 4) := by
      apply sum_le_sum
      intro s _
      split_ifs with bad
      · obtain ⟨ht, hr⟩ := lt_min_iff.mp bad
        rw [weight, if_pos ht, ← Real.exp_add, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      · exact mul_nonneg (weight_nonneg ..) (Real.exp_pos _).le
    _ = (∑ s ∈ U.powersetCard k, weight rank threshold s) * Real.exp (k * p / 4) :=
      (sum_mul ..).symm
    _ ≤ ((U.card.choose k : ℝ) * Real.exp (-(k : ℝ) * p / 2)) * Real.exp (k * p / 4) :=
      mul_le_mul_of_nonneg_right bound (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf

/-- Count form of the lower tail. It suffices that at least `h` remaining columns
increase rank before the threshold is reached. -/
theorem uniformSubset_rank_lowerTail_of_card
    (U : Finset α) (rank : Finset α → ℕ) (threshold : ℝ) (h : ℕ)
    (mono : Monotone rank) {k : ℕ} (hk : k ≤ U.card)
    (success : ∀ s ⊆ U, s.card < k → (rank s : ℝ) < threshold →
      h ≤ (improvingColumns U rank s).card) :
    (((U.powersetCard k).filter fun s =>
      (rank s : ℝ) < min threshold (k * h / (4 * (U.card : ℝ)))).card : ℝ) /
      U.card.choose k ≤ Real.exp (-(k : ℝ) * h / (4 * (U.card : ℝ))) := by
  have tail := uniformSubset_rank_lowerTail U rank threshold (h / (U.card : ℝ)) mono hk
  have hsuccess (s : Finset α) (hs : s ⊆ U) (hj : s.card < k) (low : (rank s : ℝ) < threshold) :
      (h / (U.card : ℝ)) * (U \ s).card ≤ (improvingColumns U rank s).card := by
    have hn : (0 : ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
    calc
      _ ≤ (h / (U.card : ℝ)) * U.card := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast card_le_card (sdiff_subset : U \ s ⊆ U)
      _ = h := div_mul_cancel₀ _ hn.ne'
      _ ≤ _ := by exact_mod_cast success s hs hj low
  convert tail hsuccess using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring_nf

/-- Lemma 6.4 for the rank observable of a fixed set of rows. Rigidity is required only
on subsets of these columns of size at least `U.card - h`. Take `threshold = c * kRows`. -/
theorem uniformSubset_rank_lowerTail_of_rigid
    (U : Finset α) (rank : Finset α → ℕ) (threshold : ℝ) (h : ℕ)
    (mono : Monotone rank)
    (closure : ∀ s t : Finset α, s ⊆ t → ∀ x,
      rank (insert x s) = rank s → rank (insert x t) = rank t)
    (rigid : ∀ t ⊆ U, U.card - h ≤ t.card → threshold ≤ rank t)
    {k : ℕ} (hk : k ≤ U.card) :
    (((U.powersetCard k).filter fun s =>
      (rank s : ℝ) < min threshold (k * h / (4 * (U.card : ℝ)))).card : ℝ) /
      U.card.choose k ≤ Real.exp (-(k : ℝ) * h / (4 * (U.card : ℝ))) := by
  exact uniformSubset_rank_lowerTail_of_card U rank threshold h mono hk fun _ hs _ low =>
    (lt_card_improvingColumns_of_rigid U rank threshold h mono closure rigid hs low).le

end QuantumNoiseStability.Probability.RankSampling
end

-- Paper.MatrixVector.RankSampling
section
namespace QuantumNoiseStability.MatrixVector

open Finset
open scoped Classical

variable {F : Type*} [Field F] {m n g h : ℕ} {c : ℝ} {M : Matrix (Fin m) (Fin n) F}

/-- Lemma 6.4. Each set of exactly `j` columns has the same probability. -/
theorem lemma_6_4 (hr : IsRigid M g h c) (K : Finset (Fin m)) (hK : K.card ≤ g)
    {j : ℕ} (hj : j ≤ n) :
    (((univ.powersetCard j).filter fun L =>
      (submatrixRank M K L : ℝ) < min (c * K.card) (j * h / (4 * (n : ℝ)))).card : ℝ) /
      n.choose j ≤ Real.exp (-(j : ℝ) * h / (4 * n)) := by
  have ht := Probability.RankSampling.uniformSubset_rank_lowerTail_of_card
    (univ : Finset (Fin n)) (submatrixRank M K) (c * K.card) h (submatrixRank_mono M K)
    (k := j) (by simpa using hj) (fun s _ _ low => (hr.lt_card_increasing hK s low).le)
  simpa using ht

/-- Averaging over all masks by cardinality, including the Bernoulli weights. -/
theorem mask_sum_by_size (p : ℝ) (f : Finset (Fin n) → ℝ) :
    (∑ L, p ^ L.card * (1-p) ^ (n-L.card) * f L) =
    ∑ j ∈ range (n+1), p ^ j * (1-p) ^ (n-j) * ∑ L ∈ univ.powersetCard j, f L := by
  rw [← powerset_univ, sum_powerset]
  simp only [card_univ, Fintype.card_fin]
  apply sum_congr rfl
  intro j _
  rw [mul_sum]
  exact sum_congr rfl fun L hL => by rw [(mem_powersetCard.mp hL).2]

private theorem sum_binomial_moment (n : ℕ) (p a : ℝ) :
    (∑ j ∈ range (n+1), p^j * (1-p)^(n-j) * (n.choose j : ℝ) * a^j) =
      (p*a + (1-p))^n := by
  rw [add_pow]
  apply sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

/-- Per-layer Markov bound used when the sampled mask is too small for Lemma 6.4. -/
private theorem one_le_small_mask_weight {p : ℝ} {j n : ℕ} (hj : (j : ℝ) ≤ p*n/2) :
    1 ≤ Real.exp (Real.log 2 * (p*n/2)) * (1/2 : ℝ)^j := by
  have he : (1/2 : ℝ)^j = Real.exp (-(Real.log 2) * j) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [he, ← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hj (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]

private theorem mask_moment_le {n : ℕ} {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    Real.exp (Real.log 2 * (p*n/2)) * (p*(1/2)+(1-p))^n ≤ Real.exp (-p*n/8) := by
  have step : p*(1/2)+(1-p) ≤ Real.exp (-p/2) := by linarith [Real.add_one_le_exp (-p/2)]
  calc
    _ ≤ Real.exp (Real.log 2 * (p*n/2)) * (Real.exp (-p/2))^n := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) step n) (Real.exp_pos _).le
    _ = Real.exp (Real.log 2 * (p*n/2) + n * (-p/2)) := by
      rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log 2 ≤ 3/4 := by linarith [Real.log_two_lt_d9]
      nlinarith [mul_le_mul_of_nonneg_right hlog (mul_nonneg hp₀ (Nat.cast_nonneg n))]

/-- Average of a point probability over independent resampling masks. -/
theorem bernoulli_rank_bound (hr : IsRigid M g h c) (K : Finset (Fin m)) (hK : K.card ≤ g)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hn : 0 < n) (hhn : h ≤ n)
    (hsize : c * K.card ≤ p*h/8)
    (f : Finset (Fin n) → ℝ)
    (hf : ∀ L, f L ≤ ((2 : ℝ) ^ submatrixRank M K L)⁻¹) :
    (∑ L, p ^ L.card * (1-p) ^ (n-L.card) * f L) ≤
      (2 : ℝ) ^ (-(c*K.card)) + 2 * Real.exp (-(c*K.card)) := by
  let a := c * K.card
  let B := (2 : ℝ)^(-a) + Real.exp (-a)
  let E := Real.exp (Real.log 2 * (p*n/2))
  have hle (L) : f L ≤ 1 := (hf L).trans (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hlayer (j : ℕ) (hj : j ≤ n) :
      (∑ L ∈ univ.powersetCard j, f L) ≤ (n.choose j : ℝ) * (B + E*(1/2 : ℝ)^j) := by
    let U : Finset (Finset (Fin n)) := univ.powersetCard j
    have hU : U.card = n.choose j := by simp [U]
    change ∑ L ∈ U, f L ≤ _
    by_cases hsmall : (j : ℝ) ≤ p*n/2
    · calc
        _ ≤ ∑ _L ∈ U, (1:ℝ) := sum_le_sum fun L _ => hle L
        _ = (n.choose j : ℝ) := by simp [hU]
        _ ≤ _ := by
          have hh := one_le_small_mask_weight hsmall
          have hB : 0 ≤ B := by dsimp [B]; positivity
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (show 1 ≤ B + E * (1 / 2 : ℝ) ^ j by dsimp [E]; linarith) (Nat.cast_nonneg (n.choose j) : (0:ℝ) ≤ _)
    · have hw : a ≤ j * h / (4 * (n : ℝ)) := by
        apply (le_div_iff₀ (by positivity)).2
        have hh := mul_le_mul_of_nonneg_right (le_of_not_ge hsmall) (Nat.cast_nonneg h : (0:ℝ) ≤ _)
        have ha := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg n : (0:ℝ) ≤ _)
        dsimp [a]
        nlinarith only [hh, ha]
      have tail := lemma_6_4 hr K hK hj
      rw [min_eq_left hw] at tail
      have bad : ((U.filter fun L => (submatrixRank M K L : ℝ) < a).card : ℝ) ≤
          Real.exp (-a) * (n.choose j : ℝ) := by
        apply ((div_le_iff₀ (show (0:ℝ) < n.choose j by exact_mod_cast Nat.choose_pos hj)).mp)
        exact tail.trans (Real.exp_le_exp.mpr (by simpa only [neg_mul, neg_div] using neg_le_neg hw))
      have point (L) : f L ≤ (2 : ℝ)^(-a) + (if (submatrixRank M K L : ℝ) < a then 1 else 0) := by
        split_ifs with hlow
        · linarith [hle L, Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-a)]
        · rw [add_zero]
          apply (hf L).trans
          rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      calc
        _ ≤ ∑ L ∈ U, ((2 : ℝ)^(-a) + if (submatrixRank M K L : ℝ) < a then 1 else 0) :=
          sum_le_sum fun L _ => point L
        _ ≤ (n.choose j : ℝ) * B := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, hU, sum_boole]
          dsimp [B]
          linarith
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact le_add_of_nonneg_right (by dsimp [E]; positivity)
  rw [mask_sum_by_size]
  have heval :
      (∑ j ∈ range (n+1), p^j * (1-p)^(n-j) *
        ((n.choose j : ℝ) * (B + E*(1/2 : ℝ)^j))) =
      B + E * (p*(1/2)+(1-p))^n := by
    have hsum := sum_binomial_moment n p 1
    simp at hsum
    calc
      _ = (∑ j ∈ range (n+1), p^j * (1-p)^(n-j) * (n.choose j : ℝ)) * B +
          E * ∑ j ∈ range (n+1), p^j * (1-p)^(n-j) * (n.choose j : ℝ) * (1/2 : ℝ)^j := by
            rw [sum_mul, mul_sum, ← sum_add_distrib]
            exact sum_congr rfl fun j _ => by ring
      _ = _ := by rw [hsum, one_mul, sum_binomial_moment]
  apply (sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
    (hlayer j (by have := mem_range.mp hj; omega)) (by positivity)).trans
  rw [heval]
  have hmoment := mask_moment_le (n := n) hp₀ hp₁
  have hh : Real.exp (-p*n/8) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    have hnh : (h : ℝ) ≤ n := by exact_mod_cast hhn
    dsimp [a]
    nlinarith [mul_le_mul_of_nonneg_left hnh hp₀]
  dsimp [E, B, a] at *
  linarith

end QuantumNoiseStability.MatrixVector
end

-- Paper.Query
section
namespace QuantumNoiseStability

/-- The phase of a query can depend on the basis label and one input symbol. -/
structure PhaseQuery (W ι G : Type*) where
  address : W → ι
  phase : W → G → ℂ
  norm_phase : ∀ w a, ‖phase w a‖ = 1

namespace PhaseQuery

variable {W ι G : Type*} [Fintype W]

noncomputable def operator (q : PhaseQuery W ι G) (x : ι → G) :
    EuclideanSpace ℂ W →ₗᵢ[ℂ] EuclideanSpace ℂ W where
  toFun v := WithLp.toLp 2 (fun w => q.phase w (x (q.address w)) * v w)
  map_add' u v := by ext w; exact mul_add _ _ _
  map_smul' c v := by ext w; exact mul_left_comm _ _ _
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ w, ‖q.phase w (x (q.address w)) * v w‖ ^ 2) = _
    simp [q.norm_phase]

@[simp] theorem operator_apply (q : PhaseQuery W ι G) (x : ι → G)
    (v : EuclideanSpace ℂ W) (w : W) :
    q.operator x v w = q.phase w (x (q.address w)) * v w := rfl

end PhaseQuery
end QuantumNoiseStability
end

-- Paper.TimeSpace.Execution
section
/-!
# Quantum queries with intermediate outputs

A finite instrument may write any list of outputs. Subsequent steps can use only the
state in `W`. The history labels index the sum in the Born rule and are absent from
the input to each step. Subnormalized instruments also allow aborting a computation.
-/

noncomputable section

namespace QuantumNoiseStability.TimeSpace

abbrev State (W : Type*) := EuclideanSpace ℂ W

/-- An input-independent operation, with one Kraus operator for each recorded outcome. -/
structure Instrument (W O : Type) [Fintype W] where
  outcomes : ℕ
  kraus : Fin outcomes → State W →ₗ[ℂ] State W
  emit : Fin outcomes → List O
  subnormalized : ∀ v, ∑ j, ‖kraus j v‖ ^ 2 ≤ ‖v‖ ^ 2

inductive Step (W ι G O : Type) [Fintype W] where
  | op : Instrument W O → Step W ι G O
  | query : PhaseQuery W ι G → Step W ι G O

variable {W ι G O : Type} [Fintype W]

/-- A complete sequence of outcomes has a finite type depending on the program. -/
def Hist : List (Step W ι G O) → Type
  | [] => Unit
  | .op op :: rest => Fin op.outcomes × Hist rest
  | .query _ :: rest => Hist rest

instance instFintypeHist : (l : List (Step W ι G O)) → Fintype (Hist l)
  | [] => inferInstanceAs (Fintype Unit)
  | .op op :: rest =>
      haveI := instFintypeHist rest
      inferInstanceAs (Fintype (Fin op.outcomes × Hist rest))
  | .query _ :: rest => instFintypeHist rest


/-- The unnormalized linear evolution along a single history. -/
def branchMap : (l : List (Step W ι G O)) → (ι → G) → Hist l → State W →ₗ[ℂ] State W
  | [], _, _ => LinearMap.id
  | .op op :: rest, x, h => (branchMap rest x h.2).comp (op.kraus h.1)
  | .query q :: rest, x, h => (branchMap rest x h).comp (q.operator x).toLinearMap

def run (l : List (Step W ι G O)) (x : ι → G) (v : State W) (h : Hist l) : State W :=
  branchMap l x h v

/-- The ordered transcript of the write-only output tape. -/
def claims : (l : List (Step W ι G O)) → Hist l → List O
  | [], _ => []
  | .op op :: rest, h => op.emit h.1 ++ claims rest h.2
  | .query _ :: rest, h => claims rest h

def queries : List (Step W ι G O) → ℕ
  | [] => 0
  | .op _ :: rest => queries rest
  | .query _ :: rest => queries rest + 1

@[simp] theorem queries_nil : queries ([] : List (Step W ι G O)) = 0 := rfl
@[simp] theorem queries_op (op : Instrument W O) (rest : List (Step W ι G O)) :
    queries (.op op :: rest) = queries rest := rfl
@[simp] theorem queries_query (q : PhaseQuery W ι G) (rest : List (Step W ι G O)) :
    queries (.query q :: rest) = queries rest + 1 := rfl

theorem queries_append (a b : List (Step W ι G O)) :
    queries (a ++ b) = queries a + queries b := by
  induction a with
  | nil => simp
  | cons s a ih => cases s <;> simp [ih, Nat.add_right_comm]

/-- The probabilities of all histories sum to at most the mass of the initial state. -/
theorem sum_mass_run_le (l : List (Step W ι G O)) (x : ι → G) (v : State W) :
    ∑ h, ‖run l x v h‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  induction l generalizing v with
  | nil =>
    change ∑ _ : Unit, ‖v‖ ^ 2 ≤ ‖v‖ ^ 2
    simp
  | cons s rest ih =>
    cases s with
    | op op =>
      change (∑ h : Fin op.outcomes × Hist rest, ‖run rest x (op.kraus h.1 v) h.2‖ ^ 2) ≤ _
      rw [Fintype.sum_prod_type]
      exact (Finset.sum_le_sum fun j _ => ih (op.kraus j v)).trans (op.subnormalized v)
    | query q =>
      change ∑ h : Hist rest, ‖run rest x (q.operator x v) h‖ ^ 2 ≤ _
      simpa using ih (q.operator x v)

/-- Histories factor at any cut in the list of steps. -/
def histAppend : (a b : List (Step W ι G O)) → Hist (a ++ b) ≃ Hist a × Hist b
  | [], b => (Equiv.punitProd (Hist b)).symm
  | .op op :: a, b =>
      ((Equiv.refl (Fin op.outcomes)).prodCongr (histAppend a b)).trans
        (Equiv.prodAssoc (Fin op.outcomes) (Hist a) (Hist b)).symm
  | .query _ :: a, b => histAppend a b

theorem run_append (a b : List (Step W ι G O)) (x : ι → G) (v : State W)
    (h : Hist (a ++ b)) :
    run (a ++ b) x v h = run b x (run a x v (histAppend a b h).1) (histAppend a b h).2 := by
  induction a generalizing v with
  | nil => rfl
  | cons s a ih => cases s <;> exact ih _ _

theorem claims_append (a b : List (Step W ι G O)) (h : Hist (a ++ b)) :
    claims (a ++ b) h = claims a (histAppend a b h).1 ++ claims b (histAppend a b h).2 := by
  induction a with
  | nil => rfl
  | cons s a ih =>
    cases s with
    | op op =>
      change op.emit _ ++ claims (a ++ b) _ = (op.emit _ ++ claims a _) ++ _
      rw [ih, List.append_assoc]
      rfl
    | query q => exact ih _

theorem sum_hist_append {M : Type*} [AddCommMonoid M] (a b : List (Step W ι G O))
    (f : Hist (a ++ b) → M) :
    ∑ h, f h = ∑ h₁ : Hist a, ∑ h₂ : Hist b, f ((histAppend a b).symm (h₁, h₂)) := by
  calc ∑ h, f h = ∑ p : Hist a × Hist b, f ((histAppend a b).symm p) :=
        Fintype.sum_equiv (histAppend a b) _ _ (fun h => by simp)
    _ = _ := Fintype.sum_prod_type _

/-- Probability of a transcript event on a fixed input and initial state. -/
def eventMass (l : List (Step W ι G O)) (x : ι → G) (v : State W) (P : List O → Prop) : ℝ := by
  classical
  exact ∑ h, if P (claims l h) then ‖run l x v h‖ ^ 2 else 0

/-- Success on a uniformly random input. -/
def success [Fintype ι] [DecidableEq ι] [Fintype G] (l : List (Step W ι G O)) (v : State W)
    (P : (ι → G) → List O → Prop) : ℝ :=
  (Fintype.card (ι → G) : ℝ)⁻¹ * ∑ x, eventMass l x v (P x)

/-- A transcript event has probability at most the squared norm of the initial state. -/
theorem eventMass_le_norm_sq (l : List (Step W ι G O)) (x : ι → G) (v : State W)
    (P : List O → Prop) : eventMass l x v P ≤ ‖v‖ ^ 2 := by
  apply le_trans _ (sum_mass_run_le l x v)
  unfold eventMass
  exact Finset.sum_le_sum fun h _ => by split_ifs <;> first | rfl | positivity

/-- The average probability of any success event is at most one. -/
theorem success_le_one [Fintype ι] [DecidableEq ι] [Fintype G] [Nonempty G]
    (l : List (Step W ι G O)) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    (P : (ι → G) → List O → Prop) : success l v P ≤ 1 := by
  calc success l v P ≤ (Fintype.card (ι → G) : ℝ)⁻¹ * ∑ _ : ι → G, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x _ => (eventMass_le_norm_sq l x v (P x)).trans hv) (by positivity)
    _ = 1 := by simp

end QuantumNoiseStability.TimeSpace
end
end

-- Paper.TimeSpace.Encoding
section
/-! # Relabeling the input alphabet of a measured query program -/

noncomputable section

namespace QuantumNoiseStability

namespace PhaseQuery

variable {W ι X G : Type*}

/-- On an encoded symbol, apply the phase of the original symbol. -/
def reindex (q : PhaseQuery W ι X) (E : X ≃ G) : PhaseQuery W ι G where
  address := q.address
  phase w b := q.phase w (E.symm b)
  norm_phase w b := q.norm_phase w (E.symm b)

@[simp] theorem operator_reindex [Fintype W] (q : PhaseQuery W ι X) (E : X ≃ G) (x : ι → X) :
    (q.reindex E).operator (E ∘ x) = q.operator x := by
  ext v w
  simp [reindex, Function.comp_def]

end PhaseQuery

namespace TimeSpace

/-- Encode each input coordinate by the same alphabet equivalence. -/
def inputEquiv {ι X G : Type*} (E : X ≃ G) : (ι → X) ≃ (ι → G) :=
  Equiv.piCongrRight fun _ => E

@[simp] theorem inputEquiv_apply {ι X G : Type*} (E : X ≃ G) (x : ι → X) :
    inputEquiv E x = E ∘ x := rfl

@[simp] theorem inputEquiv_symm_apply {ι X G : Type*} (E : X ≃ G) (y : ι → G) :
    (inputEquiv E).symm y = E.symm ∘ y := rfl

/-- Choose a cyclic alphabet of the same cardinality as a finite nonempty alphabet. -/
def equivZMod (X : Type*) [Fintype X] [Nonempty X] : X ≃ ZMod (Fintype.card X) :=
  (Fintype.equivFin X).trans (ZMod.finEquiv _).toEquiv

variable {W ι X G O : Type} [Fintype W] (E : X ≃ G)

def Step.reindex : Step W ι X O → Step W ι G O
  | .op instr => .op instr
  | .query q => .query (q.reindex E)

def reindexSteps (l : List (Step W ι X O)) : List (Step W ι G O) :=
  l.map (Step.reindex E)

@[simp] theorem queries_reindex (l : List (Step W ι X O)) :
    queries (reindexSteps E l) = queries l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | op _ => exact ih
    | query _ => exact congrArg (· + 1) ih

/-- Match each instrument outcome with the same outcome in the encoded program. -/
def histReindex : (l : List (Step W ι X O)) → Hist l ≃ Hist (reindexSteps E l)
  | [] => Equiv.refl _
  | .op op :: l => (Equiv.refl (Fin op.outcomes)).prodCongr (histReindex l)
  | .query _ :: l => histReindex l

@[simp] theorem claims_reindex (l : List (Step W ι X O)) (h : Hist l) :
    claims (reindexSteps E l) (histReindex E l h) = claims l h := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | op op => exact congrArg (op.emit h.1 ++ ·) (ih h.2)
    | query _ => exact ih h

@[simp] theorem branchMap_reindex (l : List (Step W ι X O)) (x : ι → X) (h : Hist l) :
    branchMap (reindexSteps E l) (E ∘ x) (histReindex E l h) = branchMap l x h := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | op op => exact congrArg (·.comp (op.kraus h.1)) (ih h.2)
    | query q =>
      change Hist l at h
      change (branchMap (reindexSteps E l) (E ∘ x) (histReindex E l h)).comp
        ((q.reindex E).operator (E ∘ x)).toLinearMap = (branchMap l x h).comp _
      rw [ih, PhaseQuery.operator_reindex]

@[simp] theorem run_reindex (l : List (Step W ι X O)) (x : ι → X) (v : State W) (h : Hist l) :
    run (reindexSteps E l) (E ∘ x) v (histReindex E l h) = run l x v h := by
  simp [run]

@[simp] theorem eventMass_reindex (l : List (Step W ι X O)) (x : ι → X) (v : State W)
    (P : List O → Prop) : eventMass (reindexSteps E l) (E ∘ x) v P = eventMass l x v P := by
  classical
  unfold eventMass
  symm
  exact Fintype.sum_equiv (histReindex E l) _ _ (fun h => by simp)

/-- Uniform Born success is preserved when the event decodes its input before testing it. -/
@[simp] theorem success_reindex [Fintype ι] [DecidableEq ι] [Fintype X] [Fintype G]
    (l : List (Step W ι X O)) (v : State W) (P : (ι → X) → List O → Prop) :
    success (reindexSteps E l) v (fun y => P (E.symm ∘ y)) = success l v P := by
  unfold success
  rw [Fintype.card_congr (inputEquiv (ι := ι) E)]
  congr 1
  symm
  apply Fintype.sum_equiv (inputEquiv E)
  intro x
  simp [← Function.comp_assoc]

end TimeSpace
end QuantumNoiseStability
end
end

-- Paper.Noise.Kernel
section
noncomputable section

namespace QuantumNoiseStability.Noise

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]

/-- The one-symbol transition probability of Proposition 3.1. -/
def symbolKernel (p : ℝ) (a b : G) : ℝ :=
  (if a = b then 1 - p else 0) + p / Fintype.card G

/-- The transition at coordinate `i`, with the identity transition outside `A`. -/
def coordKernel (A : Finset ι) (p : ℝ) (i : ι) (a b : G) : ℝ :=
  if i ∈ A then symbolKernel p a b else if a = b then 1 else 0

/-- Probability of obtaining `y` from `x` by resampling on `A` at rate `p`. -/
def kernel (A : Finset ι) (p : ℝ) (x y : ι → G) : ℝ :=
  ∏ i, coordKernel A p i (x i) (y i)

theorem kernel_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset ι) (x y : ι → G) :
    0 ≤ kernel A p x y := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : i ∈ A <;> by_cases h : x i = y i <;>
    simp [coordKernel, symbolKernel, hi, h] <;> positivity

theorem kernel_comm (A : Finset ι) (p : ℝ) (x y : ι → G) :
    kernel A p x y = kernel A p y x := by
  unfold kernel
  exact Finset.prod_congr rfl fun i _ => by simp only [coordKernel, symbolKernel, eq_comm]

omit [Fintype ι] in
private theorem coordKernel_sum [Nonempty G] (A : Finset ι) (p : ℝ) (i : ι) (a : G) :
    ∑ b, coordKernel A p i a b = 1 := by
  by_cases hi : i ∈ A
  · have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [coordKernel, symbolKernel, hi, Finset.sum_add_distrib, mul_div_cancel₀ p hcard]
  · simp [coordKernel, hi]

theorem kernel_row_sum [Nonempty G] (A : Finset ι) (p : ℝ) (x : ι → G) :
    ∑ y, kernel A p x y = 1 := by
  unfold kernel
  rw [← Fintype.prod_sum (fun i b => coordKernel A p i (x i) b)]
  simp [coordKernel_sum]

theorem kernel_col_sum [Nonempty G] (A : Finset ι) (p : ℝ) (y : ι → G) :
    ∑ x, kernel A p x y = 1 := by
  simp_rw [kernel_comm A p _ y]
  exact kernel_row_sum A p y

/-- The number of coordinates in `A` on which the two inputs differ. -/
def hammingOn (A : Finset ι) (x y : ι → G) : ℕ :=
  (A.filter fun i => x i ≠ y i).card

/-- Proposition 3.2, including the zero probability of changing a fixed coordinate. -/
theorem kernel_eq_hamming (A : Finset ι) (p : ℝ) (x y : ι → G) :
    kernel A p x y = if ∀ i ∉ A, x i = y i then
      (1 - p + p / Fintype.card G) ^ (A.card - hammingOn A x y) *
        (p / Fintype.card G) ^ hammingOn A x y else 0 := by
  split_ifs with hagree
  · have hprod : kernel A p x y = ∏ i ∈ A,
        (if x i = y i then 1 - p + p / Fintype.card G else p / Fintype.card G) := by
      rw [← Fintype.prod_ite_mem]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ A
      · by_cases h : x i = y i <;> simp [coordKernel, symbolKernel, hi, h]
      · simp [coordKernel, hi, hagree i hi]
    rw [hprod, Finset.prod_ite]
    simp only [Finset.prod_const, hammingOn]
    have hc := Finset.card_filter_add_card_filter_not (s := A) (fun i => x i = y i)
    conv_rhs => rw [← hc, Nat.add_sub_cancel]
  · push Not at hagree
    obtain ⟨i, hi, hne⟩ := hagree
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coordKernel, hi, hne])

/-- The Hamming formula when all coordinates are resampled. -/
theorem kernel_univ_eq_hamming (p : ℝ) (x y : ι → G) :
    kernel Finset.univ p x y =
      (1 - p + p / Fintype.card G) ^ (Fintype.card ι - hammingOn Finset.univ x y) *
        (p / Fintype.card G) ^ hammingOn Finset.univ x y := by
  simp [kernel_eq_hamming]

theorem kernel_eq_site {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Finset (Fin n)) (p : ℝ) (x y : Fin n → X) :
    kernel A p x y = QNoiseStab.noiseKernel p A x y := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases ha : i ∈ A <;> by_cases h : x i = y i <;>
    simp [coordKernel, symbolKernel, QNoiseStab.coordNoise, ha, h, div_eq_mul_inv, add_comm]

end QuantumNoiseStability.Noise
end
end

-- Paper.TimeSpace.EncodingNoise
section
/-! # Alphabet reindexing for restricted-coordinate resampling -/

namespace QuantumNoiseStability.Noise

/-- Relabeling both inputs preserves every restricted resampling transition probability. -/
@[simp] theorem kernel_reindex {ι X G : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
    (E : X ≃ G) (A : Finset ι) (p : ℝ) (x y : ι → X) :
    kernel A p (E ∘ x) (E ∘ y) = kernel A p x y := by
  simp only [kernel_eq_hamming, hammingOn, Function.comp_apply, ne_eq, E.apply_eq_iff_eq,
    Fintype.card_congr E]

end QuantumNoiseStability.Noise
end

-- Paper.Noise.Success
section
/-! # Uniform inputs and measured answers -/

noncomputable section

namespace QuantumNoiseStability.Noise

variable {K X : Type*} [Fintype K] [Fintype X]

/-- For each measurement outcome, sum its Born probabilities over the inputs on which it
is correct, and average over the uniform input. Outcomes can have overlapping events. -/
def success (amp : K → X → ℂ) (events : K → Finset X) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * ∑ k, ∑ x ∈ events k, ‖amp k x‖ ^ 2

theorem success_le_of_branch_bound [Nonempty X] (amp : K → X → ℂ) (events : K → Finset X)
    {c : ℝ} (hc : 0 ≤ c) (hnorm : ∀ x, ∑ k, ‖amp k x‖ ^ 2 ≤ 1)
    (hbranch : ∀ k, ∑ x ∈ events k, ‖amp k x‖ ^ 2 ≤ c * ∑ x, ‖amp k x‖ ^ 2) :
    success amp events ≤ c := by
  have hcard : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have htotal : ∑ k, ∑ x, ‖amp k x‖ ^ 2 ≤ Fintype.card X := by
    rw [Finset.sum_comm]
    simpa using Finset.sum_le_sum (s := Finset.univ) fun x _ => hnorm x
  calc success amp events
      ≤ (Fintype.card X : ℝ)⁻¹ * ∑ k, c * ∑ x, ‖amp k x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hbranch k) (by positivity)
    _ ≤ (Fintype.card X : ℝ)⁻¹ * (c * Fintype.card X) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htotal hc) (by positivity)
    _ = c := by field_simp

/-- On a conceded input, the sum of the probabilities of all correct outcomes is at most one. -/
theorem success_le_sdiff_add [DecidableEq X] (amp : K → X → ℂ) (events : K → Finset X)
    (free : Finset X) (hnorm : ∀ x, ∑ k, ‖amp k x‖ ^ 2 ≤ 1) :
    success amp events ≤ success amp (fun k => events k \ free) +
      (Fintype.card X : ℝ)⁻¹ * free.card := by
  classical
  have hsplit (k : K) : ∑ x ∈ events k, ‖amp k x‖ ^ 2 ≤
      ∑ x ∈ events k \ free, ‖amp k x‖ ^ 2 + ∑ x ∈ free, ‖amp k x‖ ^ 2 := by
    have hdis : Disjoint (events k \ free) free :=
      Finset.disjoint_left.mpr fun _ h => (Finset.mem_sdiff.mp h).2
    rw [← Finset.sum_union hdis, Finset.sdiff_union_self_eq_union]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => sq_nonneg _
  have hfree : ∑ k, ∑ x ∈ free, ‖amp k x‖ ^ 2 ≤ (free.card : ℝ) := by
    rw [Finset.sum_comm]
    simpa using Finset.sum_le_sum (s := free) fun x _ => hnorm x
  unfold success
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ∑ k, ∑ x ∈ events k, ‖amp k x‖ ^ 2
      ≤ ∑ k, (∑ x ∈ events k \ free, ‖amp k x‖ ^ 2 + ∑ x ∈ free, ‖amp k x‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => hsplit k
    _ ≤ _ := by rw [Finset.sum_add_distrib]; exact add_le_add le_rfl hfree

end QuantumNoiseStability.Noise
end
end

-- Solutions.Corollary29
section
namespace QNoiseStab

section

variable {n d : ℕ}

/-- Finite sums of functions that each depend on at most `t` coordinates. -/
inductive JuntaSum (t : ℕ) : ((Fin n → ZMod d) → ℂ) → Prop where
  | junta (s : Finset (Fin n)) (hs : s.card ≤ t) (f : (Fin n → ZMod d) → ℂ)
      (hf : ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y) : JuntaSum t f
  | sum {ι : Type} [Fintype ι] (f : ι → (Fin n → ZMod d) → ℂ)
      (hf : ∀ j, JuntaSum t (f j)) : JuntaSum t (fun x => ∑ j, f j x)

theorem JuntaSum.mul_unary {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f)
    (i : Fin n) (g : ZMod d → ℂ) : JuntaSum (t + 1) (fun x => g (x i) * f x) := by
  induction hf with
  | junta s hs f hf =>
    apply JuntaSum.junta (insert i s) ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ hs))
    intro x y h
    rw [h i (Finset.mem_insert_self ..), hf x y (fun j hj => h j (Finset.mem_insert_of_mem hj))]
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    exact JuntaSum.sum _ ih

theorem JuntaSum.const (t : ℕ) (c : ℂ) :
    JuntaSum (n := n) (d := d) t (fun _ => c) :=
  .junta ∅ (by simp) _ (fun _ _ _ => rfl)

theorem JuntaSum.const_mul {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f) (c : ℂ) :
    JuntaSum t (fun x => c * f x) := by
  induction hf with
  | junta s hs f hf => exact .junta s hs _ (fun x y h => congrArg (c * ·) (hf x y h))
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    exact .sum _ ih

theorem JuntaSum.matrix_mulVec {I J : Type} [Fintype J] {t : ℕ} (M : Matrix I J ℂ)
    (v : (Fin n → ZMod d) → J → ℂ) (h : ∀ j, JuntaSum t (fun x => v x j)) (i : I) :
    JuntaSum t (fun x => M.mulVec (v x) i) :=
  .sum _ (fun j => (h j).const_mul (M i j))

variable [NeZero d]

private lemma phase_act {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ)
    (x : Fin n → ZMod d) (ψ : EuclideanSpace ℂ ((Fin n × ZMod d) × W))
    (p : (Fin n × ZMod d) × W) :
    QAlgorithms.act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ)) ψ p =
      ω ^ (p.1.2 * x p.1.1).val * ψ p := by
  unfold phaseQuery Matrix.kronecker
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  exact (Matrix.mulVec_diagonal _ _ _).trans (by simp)

private lemma state_juntaSum {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (ω : ℂ) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1)) :
    ∀ q, JuntaSum t.val (fun x => alg.stateAt (phaseQuery ω x) t q) := by
  induction t using Fin.induction with
  | zero =>
    intro q
    exact JuntaSum.junta ∅ (by simp) _ (fun _ _ _ => rfl)
  | succ i ih =>
    intro q
    simp only [QAlgorithms.QueryAlg.stateAt, Fin.induction_succ]
    change JuntaSum (i.val + 1) (fun x => ∑ p, (alg.U i.succ : Matrix _ _ ℂ) q p *
      QAlgorithms.act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ))
        (alg.stateAt (phaseQuery ω x) i.castSucc) p)
    simp only [phase_act, ← mul_assoc]
    exact JuntaSum.sum _ (fun p => JuntaSum.mul_unary (ih p) p.1.1
      (fun a => (alg.U i.succ : Matrix _ _ ℂ) q p * ω ^ (p.1.2 * a).val))

private lemma sum_star_ket {w : ZMod d} (hw : w ≠ 0) :
    ∑ a : ZMod d, star (fourierKet w a) = 0 := by
  have hchar (a : ZMod d) :
      Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (d : ℂ)) = ZMod.stdAddChar a := by
    simpa using (ZMod.stdAddChar_coe (N := d) (a.val : ℤ)).symm
  have hzero : ∑ a : ZMod d, ZMod.stdAddChar (w * a) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d hw)
  rw [← star_sum]
  change star (∑ a : ZMod d, ((Real.sqrt d)⁻¹ : ℂ) * _) = 0
  simp only [hchar, ← Finset.mul_sum, hzero, mul_zero, star_zero]

private lemma junta_fourier_zero (s : Finset (Fin n)) (f : (Fin n → ZMod d) → ℂ)
    (hf : ∀ x y, (∀ j ∈ s, x j = y j) → f x = f y)
    (z : Fin n → ZMod d) (hz : s.card < fourierWeight z) :
    ∑ x, star (fourierVec z x) * f x = 0 := by
  classical
  obtain ⟨i, hzi, his⟩ := Finset.exists_mem_notMem_of_card_lt_card hz
  have hne : z i ≠ 0 := (Finset.mem_filter.mp hzi).2
  let e := Equiv.funSplitAt i (ZMod d)
  rw [← e.symm.sum_comp (fun x => star (fourierVec z x) * f x), Fintype.sum_prod_type_right]
  apply Finset.sum_eq_zero
  intro y _
  let x (a : ZMod d) := e.symm (a, y)
  have hxi (a) : x a i = a := by simp [x, e, Equiv.funSplitAt_symm_apply]
  have hoff (a) (j : Fin n) (hj : j ≠ i) : x a j = x 0 j := by
    simp [x, e, Equiv.funSplitAt_symm_apply, hj]
  have hproduct (a) : fourierVec z (x a) =
      fourierKet (z i) a * ∏ j ∈ Finset.univ.erase i, fourierKet (z j) (x 0 j) := by
    change ∏ j, fourierKet (z j) (x a j) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hxi]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => by rw [hoff a j (Finset.ne_of_mem_erase hj)])
  have hf' (a) : f (x a) = f (x 0) := hf _ _ (fun j hj => hoff a j (fun h => his (h ▸ hj)))
  change ∑ a, star (fourierVec z (x a)) * f (x a) = 0
  simp only [hproduct, star_mul', hf', mul_assoc, ← Finset.sum_mul, sum_star_ket hne, zero_mul]

theorem JuntaSum.fourier_zero {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f)
    (z : Fin n → ZMod d) (hz : t < fourierWeight z) :
    ∑ x, star (fourierVec z x) * f x = 0 := by
  induction hf with
  | junta s hs f hf => exact junta_fourier_zero s f hf z (lt_of_le_of_lt hs hz)
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun j _ => ih j)

end

-- The published statement assumes a root of unity. The degree bound uses only locality.
set_option linter.unusedVariables false in
/-- **Corollary 2.9** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.10, in the setting of p.9: "We focus on the domain X = Zm and the input
distribution being the uniform distribution on Xn"). The state of any quantum query algorithm
that makes at most `t` queries to its input is a linear combination of states whose input register
in the Fourier basis `|ẑ⟩` has the property that `z` contains at most `t` non-0 entries.

Stated for every `T`-query algorithm `alg` with phase queries `phaseQuery ω x` (`ω ^ d = 1`) on
inputs `x ∈ Z_dⁿ`, every number of queries `t ≤ T` (the intermediate state `alg.stateAt _ t`),
every computational basis state `q` of the algorithm registers `QPW`, and every frequency `z` with
more than `t` nonzero entries: `Σ_x conj(⟨x|ẑ⟩) · ⟨q|ψ_t^x⟩ = 0`.

**Formalization Note** For the uniform input the joint state after `t` queries is
`Σ_x d^{-n/2} |ψ_t^x⟩|x⟩`; its input-register component at the basis state `q` is
`φ_q = Σ_x d^{-n/2} ψ_t^x(q) |x⟩`, and `⟨ẑ|φ_q⟩` is `d^{-n/2}` times the displayed sum. "A linear
combination of `|q⟩ ⊗ |ẑ⟩` with at most `t` nonzero `z_i`" is exactly the vanishing of this sum for
every `q` and every `z` of weight `> t`. The Fourier basis uses the primitive root `exp(2πi/d)`;
the oracle root `ω` is any `d`-th root of unity. -/
theorem corollary_2_9 {W : Type} [Fintype W] [DecidableEq W] {n d T : ℕ} [NeZero d] (ω : ℂ)
    (hω : ω ^ d = 1) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1))
    (q : (Fin n × ZMod d) × W) (z : Fin n → ZMod d) (hz : t.val < fourierWeight z) :
    ∑ x : Fin n → ZMod d, star (fourierVec z x) * alg.stateAt (phaseQuery ω x) t q = 0 := by
  exact JuntaSum.fourier_zero (state_juntaSum ω alg t q) z hz

end QNoiseStab
end

-- Solutions.QuerySuccess
section
/-! # Fourier projection, normalisation and summation of the output probabilities -/

noncomputable section

namespace QNoiseStab.SolutionSuccess

open Finset QAlgorithms

variable {n d T : ℕ} [NeZero d]

theorem projLow_fixed (t : ℕ) (v : EuclideanSpace ℂ (Fin n → ZMod d))
    (hcoeff : ∀ z, t < fourierWeight z → ∑ y, star (fourierVec z y) * v y = 0)
    (hcomplete : ∀ x y : Fin n → ZMod d,
      ∑ z, fourierVec z x * star (fourierVec z y) = if x = y then 1 else 0) :
    act (projLowDeg t) v = v := by
  classical
  ext x
  let coeff (z : Fin n → ZMod d) := ∑ y, star (fourierVec z y) * v y
  have expand (s : Finset (Fin n → ZMod d)) :
      (act (∑ z ∈ s, ketBra (fourierVec z)) v) x = ∑ z ∈ s, fourierVec z x * coeff z := by
    change ∑ y, (∑ z ∈ s, ketBra (fourierVec z)) x y * v y = _
    simp only [Matrix.sum_apply, ketBra, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [coeff, Finset.mul_sum, mul_assoc]
  rw [projLowDeg, expand, Finset.sum_filter]
  calc ∑ z, (if fourierWeight z ≤ t then fourierVec z x * coeff z else 0) =
          ∑ z, fourierVec z x * coeff z := by
        apply sum_congr rfl
        intro z _
        split_ifs with hz
        · rfl
        · rw [show coeff z = 0 from hcoeff z (lt_of_not_ge hz), mul_zero]
    _ = ∑ y, (∑ z, fourierVec z x * star (fourierVec z y)) * v y := by
      simp only [coeff, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact sum_comm
    _ = v x := by simp_rw [hcomplete]; simp [ite_mul]

theorem event_projection_norm (E : Finset (Fin n → ZMod d)) (v : EuclideanSpace ℂ (Fin n → ZMod d)) :
    ‖act (projEvent E) v‖ ^ 2 = ∑ x ∈ E, ‖v x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ x, ‖act (projEvent E) v x‖ ^ 2 = ∑ x, if x ∈ E then ‖v x‖ ^ 2 else 0 := by
        apply sum_congr rfl
        intro x _
        by_cases hx : x ∈ E <;> simp [act, projEvent, Matrix.mulVec_diagonal, hx]
    _ = _ := by rw [← sum_filter]; simp

theorem act_product {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  unfold act
  simp [Matrix.mulVec_mulVec]

theorem phase_norm {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ) (hω : ω ^ d = 1)
    (x : Fin n → ZMod d) (v : EuclideanSpace ℂ ((Fin n × ZMod d) × W)) :
    ‖act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ)) v‖ = ‖v‖ := by
  have hroot : ‖ω‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ω) (NeZero.ne d)).mp
      (by simpa only [norm_pow, norm_one] using congrArg norm hω)
  let f (q : Fin n × ZMod d) := ω ^ (q.2 * x q.1).val
  have hmat : Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ) =
      Matrix.diagonal (fun q : (Fin n × ZMod d) × W => f q.1) := by
    change Matrix.kronecker (Matrix.diagonal f) (1 : Matrix W W ℂ) = _
    unfold Matrix.kronecker
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hmat, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [act, Matrix.mulVec_diagonal, f, norm_pow, hroot]

theorem state_norm {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ) (hω : ω ^ d = 1)
    (alg : QueryAlg (Fin n) (ZMod d) W T) (x : Fin n → ZMod d) (t : Fin (T+1)) :
    ‖alg.stateAt (phaseQuery ω x) t‖ = 1 := by
  induction t using Fin.induction with
  | zero =>
    change ‖act _ alg.start‖ = 1
    exact (act_norm_of_mem_unitaryGroup (alg.U 0).property _).trans alg.start_unit
  | succ t ih =>
    change ‖act (alg.U t.succ : Matrix _ _ ℂ) (act (Matrix.kronecker (phaseQuery ω x) 1)
      (alg.stateAt (phaseQuery ω x) t.castSucc))‖ = 1
    rw [act_norm_of_mem_unitaryGroup (alg.U t.succ).property, phase_norm ω hω, ih]

theorem mass_sum {X K : Type} [Fintype X] [Fintype K] [DecidableEq X]
    (w : X → K → ℝ) (hw : ∀ x k, 0 ≤ w x k) (hone : ∀ x, ∑ k, w x k = 1)
    (free : Finset X) (R : X → K → Prop) [DecidableRel R] {c : ℝ}
    (hbound : ∀ k, ∑ x ∈ univ.filter (fun x => x ∉ free ∧ R x k), w x k ≤ c * ∑ x, w x k) :
    ∑ x, ∑ k, (if R x k then w x k else 0) ≤ c * Fintype.card X + free.card := by
  classical
  calc ∑ x, ∑ k, (if R x k then w x k else 0)
      ≤ ∑ x, ((∑ k, if x ∉ free ∧ R x k then w x k else 0) + if x ∈ free then 1 else 0) := by
        apply sum_le_sum
        intro x _
        by_cases hx : x ∈ free
        · simp only [hx, not_true_eq_false, false_and, if_false, sum_const_zero, if_true, zero_add]
          rw [← hone x]
          exact sum_le_sum fun k _ => by split_ifs <;> first | rfl | exact hw x k
        · simp [hx]
    _ = (∑ k, ∑ x ∈ univ.filter (fun x => x ∉ free ∧ R x k), w x k) + free.card := by
        rw [sum_add_distrib, sum_comm]
        simp [sum_filter]
    _ ≤ ∑ k, (c * ∑ x, w x k) + free.card := by
        exact add_le_add (sum_le_sum fun k _ => hbound k) le_rfl
    _ = c * Fintype.card X + free.card := by
        rw [← mul_sum, sum_comm]
        simp [hone]

end QNoiseStab.SolutionSuccess
end
end

-- Solutions.Fourier
section
namespace QNoiseStab.SolutionFourier

open scoped BigOperators

variable {m n : ℕ} [NeZero m]

private theorem ket_apply (z x : ZMod m) :
    fourierKet z x = (Real.sqrt m : ℂ)⁻¹ * ZMod.stdAddChar (z * x) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

private theorem star_char (x : ZMod m) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  change starRingEnd ℂ (ZMod.toCircle x : ℂ) = (ZMod.toCircle (-x) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem sum_ket_star (x y : ZMod m) :
    ∑ z, fourierKet z x * star (fourierKet z y) = if x = y then 1 else 0 := by
  have hs : (Real.sqrt m : ℂ) * (Real.sqrt m : ℂ) = (m : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hterm (z : ZMod m) :
      fourierKet z x * star (fourierKet z y) =
        (m : ℂ)⁻¹ * ZMod.stdAddChar (z * (x - y)) := by
    rw [ket_apply, ket_apply, star_mul, star_char, star_inv₀, Complex.star_def,
      Complex.conj_ofReal, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← hs, mul_inv]
    ring
  simp only [hterm, ← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar m),
    sub_eq_zero, ZMod.card]
  split_ifs <;> simp [NeZero.ne m]

theorem sum_vec_star_vec (x y : Fin n → ZMod m) :
    ∑ z, fourierVec z x * star (fourierVec z y) = if x = y then 1 else 0 := by
  classical
  change ∑ z : Fin n → ZMod m, (∏ i, fourierKet (z i) (x i)) *
    star (∏ i, fourierKet (z i) (y i)) = _
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i t => fourierKet t (x i) * star (fourierKet t (y i)))]
  simp only [sum_ket_star, Fintype.prod_ite_zero, Finset.prod_const_one, ← funext_iff]

theorem sum_star_vec_vec (z s : Fin n → ZMod m) :
    ∑ x, star (fourierVec z x) * fourierVec s x = if z = s then 1 else 0 := by
  classical
  have symm (u v : Fin n → ZMod m) : fourierVec u v = fourierVec v u := by
    change (∏ i, fourierKet (u i) (v i)) = ∏ i, fourierKet (v i) (u i)
    simp only [ket_apply, mul_comm (u _) (v _)]
  simpa only [symm s _, symm z _, mul_comm, eq_comm] using sum_vec_star_vec s z

end QNoiseStab.SolutionFourier
end

-- Solutions.Lemma33
section
open scoped ComplexOrder

namespace QNoiseStab

/-- **Lemma 3.3** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity
and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…),
p.12). For `A ⊆ [n]`, `0 ≤ p < 1`, and every nonnegative integer `t`,
`Π_{B_t} ⪯ (1 − p)^{-t} T_p^A`.

**Formalization Note** The Loewner order `P ⪯ Q` is `(Q − P).PosSemidef`. `(1 − p)^{-t}` is
`((1 − p)^t)⁻¹` (positive since `p < 1`). `t` ranges over all of `ℕ`, including `t > n`. -/
theorem lemma_3_3 {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (t : ℕ) :
    Matrix.PosSemidef (((((1 - p) ^ t)⁻¹ : ℝ) : ℂ) • (noiseOp p A : Matrix (Fin n → ZMod m)
      (Fin n → ZMod m) ℂ) - projLowDeg t) := by
  classical
  have hpos : 0 < 1 - p := sub_pos.mpr hp1
  have hunit : 1 - p ≤ 1 := by linarith
  unfold noiseOp projLowDeg
  rw [Finset.smul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro z _
  have hket : (ketBra (fourierVec z)).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star (fun x => fourierVec z x)
  rw [smul_smul]
  by_cases hz : fourierWeight z ≤ t
  · have hcount : (A.filter fun i => z i ≠ 0).card ≤ fourierWeight z :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
    have hpow := pow_le_pow_of_le_one hpos.le hunit (hcount.trans hz)
    have hscale : 1 ≤ ((1 - p) ^ t)⁻¹ * (1 - p) ^ (A.filter fun i => z i ≠ 0).card := by
      rw [← div_eq_inv_mul, le_div_iff₀ (pow_pos hpos t), one_mul]
      exact hpow
    rw [if_pos hz, ← one_smul ℂ (ketBra (fourierVec z))]
    -- Combine the scalar coefficients of this rank-one matrix.
    simp only [smul_smul, mul_one, ← sub_smul]
    apply hket.smul
    exact_mod_cast sub_nonneg.mpr hscale
  · rw [if_neg hz, sub_zero]
    apply hket.smul
    exact_mod_cast mul_nonneg (inv_nonneg.mpr (pow_nonneg hpos.le t)) (pow_nonneg hpos.le _)

end QNoiseStab
end

-- Solutions.Proposition31
section
namespace QNoiseStab

/-- **Proposition 3.1** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.11). For any `x, y ∈ [m]`,
`Pr[N_p(x) = y] = ⟨x| T_p |y⟩ = (1 − p) δ_{x,y} + p/m`, where `T_p = p |0̂⟩⟨0̂| + (1 − p) I`.

**Formalization Note** `[m]` is `ZMod m`; `Pr[N_p(x) = y]` is `coordNoise p x y`, cast to `ℂ`; the
matrix entry `⟨x|T_p|y⟩` is `singleNoiseOp p x y`. Both equalities are identities valid for every
real `p`. -/
theorem proposition_3_1 {m : ℕ} [NeZero m] (p : ℝ) (x y : ZMod m) :
    ((coordNoise p x y : ℝ) : ℂ) = singleNoiseOp p x y ∧
      singleNoiseOp p x y = ((1 - p) * (if x = y then 1 else 0) + p / m : ℝ) := by
  have hzero (a : ZMod m) : fourierKet (0 : ZMod m) a = ((Real.sqrt m : ℝ) : ℂ)⁻¹ := by
    simp [fourierKet]
  have hnorm : ((Real.sqrt m : ℝ) : ℂ) * (Real.sqrt m : ℝ) = (m : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg m : 0 ≤ (m : ℝ))
  have hentry : ketBra (fourierKet (0 : ZMod m)) x y = (m : ℂ)⁻¹ := by
    simp only [ketBra, Matrix.of_apply, hzero, star_inv₀, Complex.star_def, Complex.conj_ofReal,
      ← mul_inv, hnorm]
  have hformula : singleNoiseOp p x y = ((1 - p) * (if x = y then 1 else 0) + p / m : ℝ) := by
    simp only [singleNoiseOp, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hentry,
      Matrix.one_apply]
    push_cast
    split <;> simp_all [div_eq_mul_inv, add_comm]
  refine ⟨?_, hformula⟩
  rw [hformula]
  simp [coordNoise, ZMod.card, div_eq_mul_inv, add_comm]

end QNoiseStab
end

-- Solutions.Proposition32
section
namespace QNoiseStab

private theorem weighted_ket_sum {m : ℕ} [NeZero m] (p : ℝ) (x y : ZMod m) :
    ∑ z : ZMod m, (if z ≠ 0 then (1 - p : ℂ) else 1) *
      (fourierKet z x * star (fourierKet z y)) = coordNoise p x y := by
  let f (z : ZMod m) := fourierKet z x * star (fourierKet z y)
  have expand (z : ZMod m) :
      (if z ≠ 0 then (1 - p : ℂ) else 1) * f z =
        (if z = 0 then (p : ℂ) * f 0 else 0) + (1 - p) * f z := by
    by_cases hz : z = 0
    · subst z
      simp
      ring
    · simp [hz]
  change ∑ z, (if z ≠ 0 then (1 - p : ℂ) else 1) * f z = _
  simp only [expand, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [show ∑ z, f z = _ from SolutionFourier.sum_ket_star x y, (proposition_3_1 p x y).1]
  simp [singleNoiseOp, ketBra, Matrix.one_apply, f]

private theorem noiseOp_entry {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) : noiseOp p A y x = (noiseKernel p A x y : ℂ) := by
  classical
  let w (i : Fin n) (z : ZMod m) : ℂ :=
    if i ∈ A then (if z ≠ 0 then 1 - p else 1) else 1
  have weight (z : Fin n → ZMod m) :
      (((1 - p) ^ (A.filter fun i => z i ≠ 0).card : ℝ) : ℂ) = ∏ i, w i (z i) := by
    simp only [w, Fintype.prod_ite_mem]
    simp only [← Finset.prod_filter, Finset.prod_const,
      Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  unfold noiseOp noiseKernel
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, weight, ketBra, Matrix.of_apply,
    fourierVec, WithLp.ofLp_toLp, star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [← Fintype.prod_sum (fun i z => w i z * (fourierKet z (y i) * star (fourierKet z (x i))))]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · simp only [w, if_pos hi, weighted_ket_sum]
    simp [coordNoise, eq_comm]
  · simp only [w, if_neg hi, one_mul, SolutionFourier.sum_ket_star]
    by_cases hxy : x i = y i <;> simp [hxy, eq_comm]

/-- **Proposition 3.2** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.12). Let `x, y ∈ [m]ⁿ`. Then `Pr[N_p^A(x) = y] = ⟨y| T_p^A |x⟩`; if
`x_{[n]∖A} = y_{[n]∖A}` then
`Pr[N_p^A(x) = y] = (1 − p + p/m)^{|A| − d_A(x,y)} (p/m)^{d_A(x,y)}`, where
`d_A(x, y) = Σ_{i∈A} (1 − δ_{x_i,y_i}) = d(x, y)` is the Hamming distance between `x_A` and `y_A`;
when `x_{[n]∖A} ≠ y_{[n]∖A}`, `Pr[N_p^A(x) = y] = 0`.

**Formalization Note** `[m]` is `ZMod m`; `Pr[N_p^A(x) = y]` is `noiseKernel p A x y`; the matrix
entry `⟨y|T_p^A|x⟩` is `noiseOp p A y x`. `d_A(x, y)` is the number of `i ∈ A` with `x_i ≠ y_i`, so
the natural-number subtraction `|A| − d_A` is exact. The identities hold for every real `p`. -/
theorem proposition_3_2 {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) :
    let dA : ℕ := (A.filter fun i => x i ≠ y i).card
    ((noiseKernel p A x y : ℝ) : ℂ) = noiseOp p A y x ∧
      ((∀ i, i ∉ A → x i = y i) →
        noiseKernel p A x y = (1 - p + p / m) ^ (A.card - dA) * (p / m) ^ dA ∧
          dA = hammingDist x y) ∧
      ((∃ i, i ∉ A ∧ x i ≠ y i) → noiseKernel p A x y = 0) := by
  classical
  dsimp only
  refine ⟨(noiseOp_entry p A x y).symm, ?_, ?_⟩
  · intro hagree
    have hdist : A.filter (fun i => x i ≠ y i) = Finset.univ.filter (fun i => x i ≠ y i) := by
      ext i
      by_cases hi : i ∈ A <;> simp [hi, hagree]
    refine ⟨?_, congrArg Finset.card hdist⟩
    have hcoord (i : Fin n) : coordNoise p (x i) (y i) =
        if x i = y i then 1 - p + p / m else p / m := by
      by_cases h : x i = y i <;> simp [coordNoise, ZMod.card, h, div_eq_mul_inv, add_comm]
    have hcount := A.card_filter_add_card_filter_not (fun i => x i = y i)
    have hmatch : (A.filter fun i => x i = y i).card =
        A.card - (A.filter fun i => x i ≠ y i).card := Nat.eq_sub_of_add_eq hcount
    calc
      noiseKernel p A x y =
          ∏ i, (if i ∈ A then coordNoise p (x i) (y i) else 1) := by
        unfold noiseKernel
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ A <;> simp [hi, hagree]
      _ = _ := by
        rw [Fintype.prod_ite_mem]
        simp only [hcoord, Finset.prod_ite, Finset.prod_const, hmatch]
  · rintro ⟨i, hi, hxy⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hxy])

end QNoiseStab
end

-- Solutions.Theorem34
section
namespace QNoiseStab
namespace Compression34

open scoped BigOperators NNReal Matrix MatrixOrder ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The maximum absolute row sum bounds the spectrum in the ℓ∞ operator norm.
open scoped Matrix.Norms.Operator in
private theorem spectrum_le_rows [Nonempty ι] (M : Matrix ι ι ℂ) {r b : ℝ}
    (hr : r ∈ spectrum ℝ M) (hb : 0 ≤ b) (hrow : ∀ i, ∑ j, ‖M i j‖ ≤ b) : r ≤ b := by
  refine (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans ?_)
  rw [Matrix.linfty_opNorm_def]
  change (Finset.univ.sup fun i : ι => ∑ j : ι, ‖M i j‖₊) ≤ (⟨b, hb⟩ : ℝ≥0)
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_sum, coe_nnnorm]
  exact hrow i

open scoped Matrix.Norms.L2Operator

-- For a positive semidefinite matrix, the ℓ² operator norm belongs to this spectrum.
private theorem psd_norm_le_rows [Nonempty ι] (M : Matrix ι ι ℂ) (hM : M.PosSemidef)
    {b : ℝ} (hb : 0 ≤ b) (hrow : ∀ i, ∑ j, ‖M i j‖ ≤ b) : ‖M‖ ≤ b :=
  spectrum_le_rows M (CStarAlgebra.norm_mem_spectrum_of_nonneg hM.nonneg) hb hrow

private theorem projector_norm_sq (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) :
    ‖P * Q‖ ^ 2 = ‖P * Q * P‖ := by
  rw [sq, ← CStarRing.norm_self_mul_star]
  change ‖P * Q * (P * Q)ᴴ‖ = _
  rw [Matrix.conjTranspose_mul, hQ.eq, hP.eq, ← mul_assoc, mul_assoc P Q Q, hQQ]

private theorem compression_bound [Nonempty ι] (P Q R : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hRQ : (R - Q).PosSemidef) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ i, ∑ j, ‖(P * R * P) i j‖ ≤ b) (v : EuclideanSpace ℂ ι) :
    ‖QAlgorithms.act (P * Q) v‖ ^ 2 ≤ b * ‖v‖ ^ 2 := by
  have hQpos := Matrix.posSemidef_self_mul_conjTranspose Q
  rw [hQ.eq, hQQ] at hQpos
  have hpos := hQpos.mul_mul_conjTranspose_same P
  rw [hP.eq] at hpos
  have hle := hRQ.mul_mul_conjTranspose_same P
  rw [hP.eq, mul_sub, sub_mul] at hle
  have hcomp := Matrix.le_iff.mpr hle
  have hRpos : 0 ≤ P * R * P := hpos.nonneg.trans hcomp
  have hnorm : ‖P * Q‖ ^ 2 ≤ b := calc
    _ = _ := projector_norm_sq P Q hP hQ hQQ
    _ ≤ ‖P * R * P‖ := CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos.nonneg hcomp
    _ ≤ b := psd_norm_le_rows _ (Matrix.nonneg_iff_posSemidef.mp hRpos) hb hrow
  calc
    _ ≤ (‖P * Q‖ * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (Matrix.l2_opNorm_mulVec (P * Q) v) 2
    _ ≤ _ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)

variable {n m : ℕ} [NeZero m]
private theorem lowDeg_hermitian (t : ℕ) :
    (projLowDeg (n := n) (m := m) t).IsHermitian := by
  change (∑ z ∈ _, ketBra (fourierVec z))ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro z _
  change (Matrix.vecMulVec (WithLp.ofLp (fourierVec z)) (star (WithLp.ofLp (fourierVec z))))ᴴ = _
  rw [Matrix.conjTranspose_vecMulVec, star_star]
  rfl

private theorem lowDeg_idempotent (t : ℕ) :
    projLowDeg (n := n) (m := m) t * projLowDeg t = projLowDeg t := by
  classical
  have hprod (z s : Fin n → ZMod m) :
      ketBra (fourierVec z) * ketBra (fourierVec s) =
        if z = s then ketBra (fourierVec z) else 0 := by
    change Matrix.vecMulVec _ (star (WithLp.ofLp (fourierVec z))) *
      Matrix.vecMulVec (WithLp.ofLp (fourierVec s)) _ = _
    rw [Matrix.vecMulVec_mul_vecMulVec]
    change Matrix.vecMulVec _ ((∑ x, star (fourierVec z x) * fourierVec s x) • _) = _
    rw [SolutionFourier.sum_star_vec_vec]
    split_ifs with h
    · subst s
      rw [one_smul]
      rfl
    · simp
  unfold projLowDeg
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  simp_rw [Finset.mul_sum, hprod]
  simp [hz]

omit [NeZero m] in
private theorem event_hermitian (E : Finset (Fin n → ZMod m)) : (projEvent E).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext x
  change star (if x ∈ E then (1 : ℂ) else 0) = _
  split_ifs <;> simp_all

private theorem kernel_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) : 0 ≤ noiseKernel p A x y := by
  apply Finset.prod_nonneg
  intro i _
  have hp : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
  simp only [coordNoise]
  split_ifs <;> positivity

private theorem kernel_symm (p : ℝ) (A : Finset (Fin n)) (x y : Fin n → ZMod m) :
    noiseKernel p A y x = noiseKernel p A x y := by
  unfold noiseKernel
  apply Finset.prod_congr rfl
  intro i _
  simp only [coordNoise, @eq_comm _ (y i) (x i)]

private theorem event_rows (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (A : Finset (Fin n))
    (E : Finset (Fin n → ZMod m)) {β c : ℝ} (hβ0 : 0 ≤ β) (hc : 0 ≤ c)
    (hβ : ∀ x ∈ E, noiseProb p A x E ≤ β)
    (x : Fin n → ZMod m) :
    ∑ y, ‖(projEvent E * ((c : ℂ) • noiseOp (m := m) p A) * projEvent E) x y‖ ≤ c * β := by
  classical
  simp only [projEvent, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ E
  · simp only [hx, if_true, one_mul]
    calc
      _ = ∑ y, if y ∈ E then c * noiseKernel p A x y else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ E
        · simp [hy, ← (proposition_3_2 p A y x).1, kernel_symm p A x y, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg (kernel_nonneg p hp0 hp1 A x y)]
        · simp [hy]
      _ = c * noiseProb p A x E := by simp [noiseProb, Finset.mul_sum]
      _ ≤ c * β := mul_le_mul_of_nonneg_left (hβ x hx) hc
  · simpa [hx] using mul_nonneg hc hβ0

end Compression34
open Compression34

-- The platform includes ht, while Lemma 3.3 applies to every natural degree bound.
set_option linter.unusedVariables false in
/-- **Theorem 3.4** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.12). Let `A ⊆ [n]` and `E ⊆ [m]ⁿ` be some event. If `Π_E` is the projection onto the
input states that correspond to `E`, then for `0 ≤ t ≤ n`,
`‖Π_E Π_{B_t}‖² ≤ (1 − p)^{-t} max_{x∈E} Pr[N_p^A(x) ∈ E]`.

**Formalization Note** `[m]` is `ZMod m`. The range `0 ≤ p < 1` is that of Lemma 3.3, which the
proof applies (`N_p^A` is a random variable for `p ∈ [0, 1]`, and `(1 − p)^{-t}` is undefined at
`p = 1`). The squared operator norm is stated in its equivalent pointwise form
`‖Π_E Π_{B_t} ψ‖² ≤ c ‖ψ‖²` for every vector `ψ`. The maximum is encoded by any `β ≥ 0` bounding
`Pr[N_p^A(x) ∈ E]` for every `x ∈ E` (the maximum itself is such a `β`, and `max ∅ = 0`). -/
theorem theorem_3_4 {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (E : Finset (Fin n → ZMod m))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (t : ℕ) (ht : t ≤ n) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ x ∈ E, noiseProb p A x E ≤ β) (ψ : EuclideanSpace ℂ (Fin n → ZMod m)) :
    ‖QAlgorithms.act (projEvent E * projLowDeg t) ψ‖ ^ 2 ≤
      ((1 - p) ^ t)⁻¹ * β * ‖ψ‖ ^ 2 := by
  have hc : 0 ≤ ((1 - p) ^ t)⁻¹ := inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr hp1.le) _)
  exact compression_bound (projEvent E) (projLowDeg t) _ (event_hermitian E)
    (lowDeg_hermitian t) (lowDeg_idempotent t) (lemma_3_3 A p hp0 hp1 t)
    (mul_nonneg hc hβ0) (event_rows p hp0 hp1 A E hβ0 hc hβ) ψ

end QNoiseStab
end

-- Paper.TimeSpace.MeasuredNoise
section
noncomputable section
namespace QuantumNoiseStability.TimeSpace

variable {W ι G O : Type} [Fintype W] [Fintype ι] [DecidableEq ι] [Fintype G]

/-- Inputs on which a particular transcript is successful. -/
def eventInputs (P : (ι → G) → List O → Prop) (out : List O) : Finset (ι → G) := by
  classical
  exact Finset.univ.filter (fun x => P x out)

@[simp] theorem mem_eventInputs (P : (ι → G) → List O → Prop) (out : List O) (x : ι → G) :
    x ∈ eventInputs P out ↔ P x out := by classical simp [eventInputs]

/-- Measuring the workspace at the end refines every history into pairs of an instrument
history and a final basis state. Summing these Born weights gives the original event. -/
theorem success_eq_branch (l : List (Step W ι G O)) (v : State W) (P : (ι → G) → List O → Prop) :
    success l v P = Noise.success
      (fun (b : Hist l × W) x => run l x v b.1 b.2)
      (fun b => eventInputs P (claims l b.1)) := by
  classical
  unfold success Noise.success
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [eventInputs, Finset.sum_filter, eventMass]
  calc ∑ x, ∑ h, (if P x (claims l h) then ‖run l x v h‖ ^ 2 else 0) =
        ∑ x, ∑ h, ∑ w, (if P x (claims l h) then ‖run l x v h w‖ ^ 2 else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro h _
          by_cases he : P x (claims l h) <;> simp [he, EuclideanSpace.norm_sq_eq]
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [Fintype ι] [DecidableEq ι] [Fintype G] in
theorem branch_mass_le_one (l : List (Step W ι G O)) (v : State W)
    (hv : ‖v‖ ^ 2 ≤ 1) (x : ι → G) :
    ∑ b : Hist l × W, ‖run l x v b.1 b.2‖ ^ 2 ≤ 1 := by
  simp only [Fintype.sum_prod_type, ← EuclideanSpace.norm_sq_eq]
  exact (sum_mass_run_le _ _ _).trans hv

variable {n d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem degree_run (l : List (Step W (Fin n) (ZMod d) O)) (h : Hist l)
    {t : ℕ} (u : (Fin n → ZMod d) → State W)
    (hu : ∀ w, QNoiseStab.JuntaSum t (fun x => u x w)) (w : W) :
    QNoiseStab.JuntaSum (t + queries l) (fun x => run l x (u x) h w) := by
  classical
  induction l generalizing t u with
  | nil => simpa [queries, run, branchMap] using hu w
  | cons step rest ih =>
    cases step with
    | op instr =>
      apply ih h.2 (fun x => instr.kraus h.1 (u x))
      intro j
      let M : Matrix W W ℂ := Matrix.toEuclideanLin.symm (instr.kraus h.1)
      have heq : Matrix.toEuclideanLin M = instr.kraus h.1 := LinearEquiv.apply_symm_apply _ _
      rw [← heq]
      exact QNoiseStab.JuntaSum.matrix_mulVec M (fun x j => u x j) hu j
    | query q =>
      have hq (j : W) : QNoiseStab.JuntaSum (t + 1) (fun x => q.operator x (u x) j) :=
        (hu j).mul_unary (q.address j) (q.phase j)
      change QNoiseStab.JuntaSum (t + (queries rest + 1)) _
      rw [show t + (queries rest + 1) = (t + 1) + queries rest by omega]
      exact ih h (fun x => q.operator x (u x)) hq

private theorem measured_cyclic (l : List (Step W (Fin n) (ZMod d) O)) (v : State W)
    (hv : ‖v‖ ^ 2 ≤ 1) (P : (Fin n → ZMod d) → List O → Prop) (A : Finset (Fin n))
    {p β : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 ≤ β)
    (hrow : ∀ out x, P x out → ∑ y ∈ eventInputs P out, Noise.kernel A p x y ≤ β) :
    success l v P ≤ ((1 - p) ^ queries l)⁻¹ * β := by
  classical
  rw [success_eq_branch]
  apply Noise.success_le_of_branch_bound _ _ (mul_nonneg (by positivity) hβ) (branch_mass_le_one l v hv)
  intro b
  let E := eventInputs P (claims l b.1)
  let ψ : EuclideanSpace ℂ (Fin n → ZMod d) := WithLp.toLp 2 (fun x => run l x v b.1 b.2)
  let t := min (queries l) n
  have deg : QNoiseStab.JuntaSum (queries l) (fun x => ψ x) := by
    simpa [ψ] using degree_run l b.1 (t := 0) (fun _ => v)
      (fun w => QNoiseStab.JuntaSum.const 0 (v w)) b.2
  have fixed := QNoiseStab.SolutionSuccess.projLow_fixed t ψ (fun z hz => by
    apply deg.fourier_zero
    have hw : QNoiseStab.fourierWeight z ≤ n := by
      simpa [QNoiseStab.fourierWeight] using
        (Finset.card_le_univ (Finset.univ.filter (fun i => z i ≠ 0)))
    dsimp [t] at hz
    omega) QNoiseStab.SolutionFourier.sum_vec_star_vec
  have rows (x) (hx : x ∈ E) : QNoiseStab.noiseProb p A x E ≤ β := by
    simpa only [QNoiseStab.noiseProb, ← Noise.kernel_eq_site] using
      hrow (claims l b.1) x ((mem_eventInputs _ _ _).mp hx)
  have main := QNoiseStab.theorem_3_4 A E p hp0.le hp1 t (min_le_right _ _) β hβ rows ψ
  rw [QNoiseStab.SolutionSuccess.act_product, fixed, QNoiseStab.SolutionSuccess.event_projection_norm,
    EuclideanSpace.norm_sq_eq] at main
  have hc : ((1-p)^t)⁻¹ ≤ ((1-p)^queries l)⁻¹ := by
    simp only [← inv_pow]
    exact pow_le_pow_right₀ ((one_le_inv₀ (by linarith : 0 < 1-p)).mpr (by linarith))
      (min_le_left _ _)
  exact main.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hβ)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

private theorem event_row_reindex {X : Type} [Fintype X] [DecidableEq X] [DecidableEq G]
    (E : X ≃ G) (P : (ι → X) → List O → Prop) (out : List O) (A : Finset ι) (p : ℝ)
    (x : ι → X) :
    ∑ z ∈ eventInputs (fun z => P (E.symm ∘ z)) out, Noise.kernel A p (E ∘ x) z =
      ∑ y ∈ eventInputs P out, Noise.kernel A p x y := by
  classical
  simp only [eventInputs, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (inputEquiv E)
  intro y
  change (if P y out then _ else _) = (if P (E.symm ∘ E ∘ y) out then _ else _)
  simp [← Function.comp_assoc]

private theorem measured_noise_reindex {X : Type} [Fintype X] [DecidableEq X]
    (E : X ≃ ZMod d)
    (l : List (Step W (Fin n) X O)) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    (P : (Fin n → X) → List O → Prop) (A : Finset (Fin n)) {p β : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 ≤ β)
    (hrow : ∀ out x, P x out → ∑ y ∈ eventInputs P out, Noise.kernel A p x y ≤ β) :
    success l v P ≤ ((1 - p) ^ queries l)⁻¹ * β := by
  let P' := fun (z : Fin n → ZMod d) out => P (E.symm ∘ z) out
  have rows (out : List O) (z : Fin n → ZMod d) (hz : P' z out) :
      ∑ y ∈ eventInputs P' out, Noise.kernel A p z y ≤ β := by
    obtain ⟨x, rfl⟩ := (inputEquiv E).surjective z
    change ∑ y ∈ eventInputs P' out, Noise.kernel A p (E ∘ x) y ≤ β
    rw [event_row_reindex E P out A p x]
    exact hrow out x (by simpa only [P', inputEquiv_apply, ← Function.comp_assoc,
      E.symm_comp_self, Function.id_comp] using hz)
  rw [← success_reindex E l v P, ← queries_reindex E l]
  exact measured_cyclic (reindexSteps E l) v hv P' A hp0 hp1 hβ rows

/-- Theorem 3.5 for any finite nonempty alphabet and arbitrary measured transcripts.
The stability premise only ranges over the inputs on which the transcript is correct. -/
theorem measured_success_le_noise [Nonempty G] [DecidableEq G]
    (l : List (Step W (Fin n) G O)) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    (P : (Fin n → G) → List O → Prop) (A : Finset (Fin n)) {p β : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 ≤ β)
    (hrow : ∀ out x, P x out → ∑ y ∈ eventInputs P out, Noise.kernel A p x y ≤ β) :
    success l v P ≤ ((1 - p) ^ queries l)⁻¹ * β := by
  have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  exact measured_noise_reindex (equivZMod G) l v hv P A hp0 hp1 hβ hrow

/-- Removing conceded inputs costs at most their probability under the uniform law. -/
theorem success_le_remove_inputs [DecidableEq G] (l : List (Step W (Fin n) G O)) (v : State W)
    (hv : ‖v‖ ^ 2 ≤ 1) (P : (Fin n → G) → List O → Prop) (free : Finset (Fin n → G)) :
    success l v P ≤ success l v (fun x out => P x out ∧ x ∉ free) +
      (Fintype.card (Fin n → G) : ℝ)⁻¹ * free.card := by
  classical
  let amp (b : Hist l × W) (x : Fin n → G) := run l x v b.1 b.2
  let events (b : Hist l × W) := eventInputs P (claims l b.1)
  have he (b : Hist l × W) : events b \ free =
      eventInputs (fun x out => P x out ∧ x ∉ free) (claims l b.1) := by
    ext x
    simp [events]
  rw [success_eq_branch l v P, success_eq_branch l v (fun x out => P x out ∧ x ∉ free)]
  simpa only [he] using Noise.success_le_sdiff_add amp events free (branch_mass_le_one l v hv)

/-- Theorem 3.5(a) with coefficient one, for the measured query model. -/
theorem measured_success_le_noise_with_free [Nonempty G] [DecidableEq G]
    (l : List (Step W (Fin n) G O)) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    (P : (Fin n → G) → List O → Prop) (free : Finset (Fin n → G)) (A : Finset (Fin n)) {p β : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 ≤ β)
    (hrow : ∀ out x, P x out → x ∉ free →
      ∑ y ∈ eventInputs (fun y out => P y out ∧ y ∉ free) out, Noise.kernel A p x y ≤ β) :
    success l v P ≤ ((1 - p) ^ queries l)⁻¹ * β +
      (Fintype.card (Fin n → G) : ℝ)⁻¹ * free.card :=
  (success_le_remove_inputs l v hv P free).trans (add_le_add_left
    (measured_success_le_noise l v hv _ A hp0 hp1 hβ (fun out x h => hrow out x h.1 h.2)) _)

end QuantumNoiseStability.TimeSpace
end
end

-- Paper.TimeSpace.Claims
section
/-! Correctness of outputs written at arbitrary times and indices. -/

namespace QuantumNoiseStability.TimeSpace

open Finset

variable {C Y : Type*} [DecidableEq C]

/-- The coordinates of a list of claims. -/
def coords (l : List (C × Y)) : Finset C := (l.map Prod.fst).toFinset

theorem mem_coords {l : List (C × Y)} {c : C} : c ∈ coords l ↔ ∃ b, (c, b) ∈ l := by
  unfold coords
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨c', b⟩, h, rfl⟩
    exact ⟨b, h⟩
  · rintro ⟨b, h⟩
    exact ⟨(c, b), h, rfl⟩

theorem coords_append (l l' : List (C × Y)) : coords (l ++ l') = coords l ∪ coords l' := by
  unfold coords
  rw [List.map_append, List.toFinset_append]

/-- A short run succeeds when it commits to at least `k` distinct coordinates
and all of its claims agree with the target. -/
def ShortSuccess (k : ℕ) (target : C → Y) (l : List (C × Y)) : Prop :=
  k ≤ (coords l).card ∧ ∀ p ∈ l, target p.1 = p.2

/-- Every coordinate must be produced, and every value ever committed must be correct. -/
def FullSuccess (target : C → Y) (l : List (C × Y)) : Prop :=
  (∀ c, ∃ y, (c, y) ∈ l) ∧ ∀ p ∈ l, target p.1 = p.2

/-- **Pigeonhole over slices.** If the records of `ls` together claim every coordinate of
`C` correctly and `|C| > |ls| (k - 1)`, then some record in `ls` has at least `k` distinct
correct claims, hence satisfies the short event. -/
theorem exists_shortSuccess_of_cover (k : ℕ) (a : C → Y) :
    ∀ (ls : List (List (C × Y))) (s : Finset C),
      (∀ c ∈ s, ∃ b, (c, b) ∈ ls.flatten) → (∀ p ∈ ls.flatten, a p.1 = p.2) →
      ls.length * (k - 1) < s.card → ∃ l ∈ ls, ShortSuccess k a l
  | [], s, hcover, _, hcard => by
    exfalso
    have : s = ∅ := by
      ext c
      simp only [Finset.notMem_empty, iff_false]
      intro hc
      obtain ⟨b, hb⟩ := hcover c hc
      simp at hb
    rw [this] at hcard
    simp at hcard
  | l :: ls, s, hcover, hcorrect, hcard => by
    simp only [List.flatten_cons, List.mem_append] at hcover hcorrect
    by_cases hk : k ≤ (coords l).card
    · exact ⟨l, List.mem_cons_self, ⟨hk, fun p hp => hcorrect p (Or.inl hp)⟩⟩
    · push Not at hk
      have hrest := exists_shortSuccess_of_cover k a ls (s \ coords l) ?_ ?_ ?_
      · obtain ⟨l', hl', hs⟩ := hrest
        exact ⟨l', List.mem_cons_of_mem _ hl', hs⟩
      · intro c hc
        rw [Finset.mem_sdiff] at hc
        obtain ⟨b, hb⟩ := hcover c hc.1
        rcases hb with hb | hb
        · exact absurd (mem_coords.mpr ⟨b, hb⟩) hc.2
        · exact ⟨b, hb⟩
      · intro p hp
        exact hcorrect p (Or.inr hp)
      · have h1 := Finset.card_sdiff_add_card_inter s (coords l)
        have h2 : (s ∩ coords l).card ≤ (coords l).card :=
          Finset.card_le_card Finset.inter_subset_right
        simp only [List.length_cons] at hcard
        have : (ls.length + 1) * (k - 1) = ls.length * (k - 1) + (k - 1) := by ring
        omega

end QuantumNoiseStability.TimeSpace
end

-- Paper.MatrixVector.QueryBound
section
namespace QuantumNoiseStability.MatrixVector

open Finset
open scoped Classical

variable {F G : Type*} [Field F] [Fintype G] [DecidableEq G] {m n : ℕ}

/-- Expand the independent resampling kernel as a mixture over the set of resampled positions. -/
theorem kernel_eq_sum_masks (p : ℝ) (x z : Fin n → G) :
    Noise.kernel univ p x z = ∑ L : Finset (Fin n),
      if ∀ j ∉ L, x j = z j then
        p^L.card * (1-p)^(n-L.card) / (Fintype.card G : ℝ)^L.card else 0 := by
  have expand : Noise.kernel univ p x z =
      ∏ j, (p / Fintype.card G + (if x j = z j then 1-p else 0)) := by
    apply prod_congr rfl
    intro i _
    change (if i ∈ (univ : Finset (Fin n)) then Noise.symbolKernel p (x i) (z i) else _) = _
    simp [Noise.symbolKernel, add_comm]
  rw [expand, Fintype.prod_add (fun _ : Fin n => p / Fintype.card G)]
  apply sum_congr rfl
  intro L _
  by_cases ha : ∀ j ∉ L, x j = z j
  · rw [if_pos ha, prod_const, div_pow]
    have eq : (∏ j ∈ Lᶜ, if x j = z j then 1-p else 0) = (1-p)^(n-L.card) := by
      rw [prod_congr rfl (g := fun _ => 1-p) (fun i hi => if_pos (ha i (mem_compl.mp hi)))]
      simp [Finset.card_compl]
    rw [eq]
    ring
  · rw [if_neg ha]
    push Not at ha
    obtain ⟨i, hi, hne⟩ := ha
    rw [prod_eq_zero (mem_compl.mpr hi) (if_neg hne), mul_zero]

/-- Matrix output on field elements named by symbols of a finite alphabet. -/
def matrixOutput (M : Matrix (Fin m) (Fin n) F) (decode : G → F) (x : Fin n → G) :
    Fin m → F := M.mulVec (decode ∘ x)

private theorem card_mask_event (M : Matrix (Fin m) (Fin n) F) (D : Finset F)
    (e : G ≃ D) (K : Finset (Fin m)) (L : Finset (Fin n)) (x : Fin n → G) (y : K → F) :
    ((univ : Finset (Fin n → G)).filter fun z =>
      (∀ j ∉ L, x j = z j) ∧ (∀ i : K, matrixOutput M (fun a => (e a : F)) z i = y i)).card ≤
      D.card ^ (L.card - submatrixRank M K L) := by
  let A := M.submatrix (fun i : K => i.val) (fun j : L => j.val)
  let outside := fun i : K => ∑ j ∈ Lᶜ, M i j * (e (x j) : F)
  let H := (univ : Finset (Fin n → G)).filter fun z =>
    (∀ j ∉ L, x j = z j) ∧ (∀ i : K, matrixOutput M (fun a => (e a : F)) z i = y i)
  have good (z : H) : (∀ j ∉ L, x j = z.val j) ∧
      (∀ i : K, matrixOutput M (fun a => (e a : F)) z.val i = y i) := (mem_filter.mp z.property).2
  let res (z : H) : L → D := fun j => e (z.val j)
  have eq (z : H) : A.mulVec (fun j => (res z j : F)) = y - outside := by
    funext i
    have hh := (good z).2 i
    change (∑ j, M i j * (e (z.val j) : F)) = y i at hh
    rw [← sum_add_sum_compl L] at hh
    have hout : (∑ j ∈ Lᶜ, M i j * (e (z.val j) : F)) = outside i :=
      sum_congr rfl fun j hj => by rw [← (good z).1 j (mem_compl.mp hj)]
    rw [hout] at hh
    exact (L.sum_attach (fun j => M i j * (e (z.val j) : F))).trans (eq_sub_of_add_eq hh)
  let f (z : H) : {u : L → D // A.mulVec (fun j => (u j : F)) = y - outside} := ⟨res z, eq z⟩
  have inj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ L
    · exact e.injective (congrFun (congrArg Subtype.val h) ⟨j,hj⟩)
    · exact ((good v).1 j hj).symm.trans ((good w).1 j hj)
  have count₁ := Nat.card_le_card_of_injective f inj
  have count₂ := natCard_mulVec_eq_le A D (y-outside)
  have count := count₁.trans count₂
  rw [Nat.card_eq_fintype_card] at count
  change H.card ≤ D.card ^ (L.card - A.rank)
  simpa only [Fintype.card_coe] using count

/-- Noise stability of `k` prescribed rows at resampling rate `p`. -/
theorem kernel_matrix_event_le {g h : ℕ} {c p : ℝ} {M : Matrix (Fin m) (Fin n) F}
    (hr : IsRigid M g h c) (D : Finset F) (hd : 2 ≤ D.card) (e : G ≃ D)
    (K : Finset (Fin m)) (hK : K.card ≤ g) (hn : 0 < n) (hhn : h ≤ n)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hsize : c*K.card ≤ p*h/8)
    (x : Fin n → G) (y : K → F) :
    (∑ z : Fin n → G, if ∀ i : K, matrixOutput M (fun a => (e a : F)) z i = y i
      then Noise.kernel univ p x z else 0) ≤
      (2:ℝ)^(-(c*K.card)) + 2 * Real.exp (-(c*K.card)) := by
  let H (L : Finset (Fin n)) := (univ : Finset (Fin n → G)).filter fun z =>
    (∀ j ∉ L, x j = z j) ∧ (∀ i : K, matrixOutput M (fun a => (e a : F)) z i = y i)
  let prob (L : Finset (Fin n)) : ℝ := ((H L).card : ℝ) / (D.card : ℝ)^L.card
  have hdpos : (0 : ℝ) < D.card := by exact_mod_cast (show 0 < D.card by omega)
  have hpivot (L) : prob L ≤ ((2 : ℝ)^submatrixRank M K L)⁻¹ := by
    have hc : ((H L).card : ℝ) ≤ (D.card : ℝ) ^ (L.card-submatrixRank M K L) := by
      exact_mod_cast card_mask_event M D e K L x y
    have hrank : submatrixRank M K L ≤ L.card := by
      simpa [submatrixRank] using Matrix.rank_le_card_width (M.submatrix (fun i : K => i.val) (fun j : L => j.val))
    calc
      prob L ≤ ((D.card : ℝ)^submatrixRank M K L)⁻¹ := by
        apply (div_le_iff₀ (by positivity)).mpr
        conv_rhs => rw [← Nat.sub_add_cancel hrank, pow_add]
        field_simp
        exact hc
      _ ≤ _ := by gcongr; exact_mod_cast hd
  have hcard : Fintype.card G = D.card := (Fintype.card_congr e).trans (Fintype.card_coe D)
  apply le_trans _ (bernoulli_rank_bound hr K hK hp₀ hp₁ hn hhn hsize prob hpivot)
  apply le_of_eq
  simp_rw [kernel_eq_sum_masks, hcard]
  have distribute (P : Prop) [Decidable P] (f : Finset (Fin n) → ℝ) :
      (if P then ∑ L, f L else 0) = ∑ L, if P then f L else 0 := by split_ifs <;> simp_all
  simp_rw [distribute]
  rw [sum_comm]
  apply sum_congr rfl
  intro L _
  let w := p^L.card * (1-p)^(n-L.card)
  calc
    _ = ∑ z : Fin n → G, if z ∈ H L then w / (D.card : ℝ)^L.card else 0 := by
      apply sum_congr rfl
      intro z _
      simp only [H, mem_filter, mem_univ, true_and]
      split_ifs <;> first | rfl | tauto
    _ = _ := by simp [prob, div_eq_mul_inv, w]; ring

open TimeSpace

/-- Conditioning on a correct transcript fixes the values of any `k` of its distinct rows. -/
theorem kernel_shortSuccess_le {g h k : ℕ} {c p : ℝ} {M : Matrix (Fin m) (Fin n) F}
    (hr : IsRigid M g h c) (D : Finset F) (hd : 2 ≤ D.card) (e : G ≃ D)
    (hk : k ≤ g) (hn : 0 < n) (hhn : h ≤ n) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hsize : c*k ≤ p*h/8) (x : Fin n → G) (record : List (Fin m × F))
    (hx : ShortSuccess k (matrixOutput M (fun a => (e a : F)) x) record) :
    (∑ z : Fin n → G, if ShortSuccess k (matrixOutput M (fun a => (e a : F)) z) record
      then Noise.kernel univ p x z else 0) ≤
      (2:ℝ)^(-(c*k)) + 2 * Real.exp (-(c*k)) := by
  obtain ⟨K, hK, hcard⟩ := exists_subset_card_eq hx.1
  let f := matrixOutput M (fun a => (e a : F))
  have hh := kernel_matrix_event_le hr D hd e K (hcard ▸ hk) hn hhn hp₀ hp₁
    (hcard ▸ hsize) x (fun i : K => f x i)
  rw [hcard] at hh
  apply le_trans _ hh
  apply sum_le_sum
  intro z _
  by_cases hz : ShortSuccess k (f z) record
  · have agree (i : K) : f z i = f x i := by
      obtain ⟨b, hb⟩ := mem_coords.mp (hK i.property)
      exact (hz.2 (i,b) hb).trans (hx.2 (i,b) hb).symm
    change (if ShortSuccess k (f z) record then _ else _) ≤
      (if ∀ i : K, f z i = f x i then _ else _)
    rw [if_pos hz, if_pos agree]
  · change (if ShortSuccess k (f z) record then _ else _) ≤ _
    rw [if_neg hz]
    split_ifs
    · exact Noise.kernel_nonneg hp₀ hp₁ _ _ _
    · rfl

private theorem noise_penalty_le {a p : ℝ} {t h : ℕ} (hp : 0 ≤ p) (hp' : p ≤ 1/4)
    (hpa : p*h = 8*a) (ht : 32*t ≤ h) :
    ((1-p)^t)⁻¹ ≤ Real.exp (a/3) := by
  have ht' : 32 * (t : ℝ) ≤ h := by exact_mod_cast ht
  have hfrac : (1-p)⁻¹ ≤ 1 + 4*p/3 := by
    apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1-p)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hp' hp]
  have hstep := hfrac.trans (by linarith [Real.add_one_le_exp (4*p/3)] :
    1 + 4*p/3 ≤ Real.exp (4*p/3))
  rw [← inv_pow]
  calc
    _ ≤ (Real.exp (4*p/3))^t := pow_le_pow_left₀ (inv_nonneg.mpr (by linarith)) hstep t
    _ = Real.exp (t*(4*p/3)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left ht' hp])

private theorem query_exponents {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (a/3) * ((2 : ℝ)^(-a) + 2*Real.exp (-a)) ≤ 3*(2:ℝ)^(-a/4) := by
  have hlog₀ := mul_le_mul_of_nonneg_right Real.log_two_gt_d9.le ha
  have hlog₁ := mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le ha
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    mul_add, show Real.exp (a/3) * (2*Real.exp (-a)) = 2*(Real.exp (a/3) * Real.exp (-a)) by ring,
    ← Real.exp_add, ← Real.exp_add]
  have h₁ : Real.exp (a/3 + Real.log 2 * -a) ≤ Real.exp (Real.log 2 * (-a/4)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h₂ : Real.exp (a/3 + -a) ≤ Real.exp (Real.log 2 * (-a/4)) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Lemma 6.5 for a finite alphabet contained in any field. The circuit can choose
which rows to report and can perform measurements between queries. -/
theorem lemma_6_5 {F W : Type} [Field F] [Fintype W] {m n g h k : ℕ}
    {M : Matrix (Fin m) (Fin n) F} {c : ℝ} (hr : IsRigid M g h c)
    (D : Finset F) (hd : 2 ≤ D.card)
    (hkg : k ≤ g) (hkh : 32*k ≤ h)
    (l : List (Step W (Fin n) D (Fin m × F))) (ht : 32*queries l ≤ h)
    (v : State W) (hv : ‖v‖^2 ≤ 1) :
    success l v (fun x => ShortSuccess k (matrixOutput M Subtype.val x)) ≤
      3*(2:ℝ)^(-(c*k)/4) := by
  classical
  have : Nonempty D := (Finset.card_pos.mp (by omega : 0 < D.card)).coe_sort
  let P := fun (x : Fin n → D) => ShortSuccess k (matrixOutput M Subtype.val x)
  let a := c*(k:ℝ)
  by_cases ha : 0 < a
  · have hk : 0 < k := by
      by_contra! hh
      simp [a, Nat.eq_zero_of_le_zero hh] at ha
    by_cases hkm : k ≤ m
    case neg =>
      have impossible (x : Fin n → D) (out : List (Fin m × F)) : ¬ P x out :=
        fun hx => hkm (hx.1.trans (by simpa using (coords out).card_le_univ))
      change success l v P ≤ _
      simp [success, eventMass, impossible]
      positivity
    have hcpos : 0 < c := pos_of_mul_pos_left ha (Nat.cast_nonneg k)
    obtain ⟨hc, hhn⟩ := hr.parameter_bounds (hk.trans_le hkm) (hk.trans_le hkg) hcpos
    have hh : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
    have hn : 0 < n := by omega
    let p := 8*a/h
    have hpa : p*h = 8*a := div_mul_cancel₀ _ hh.ne'
    have hp : 0 < p := div_pos (by positivity) hh
    have hp' : p ≤ 1/4 := by
      apply (div_le_iff₀ hh).mpr
      have hh' : 32*(k:ℝ) ≤ h := by exact_mod_cast hkh
      dsimp [a]
      nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg k : (0:ℝ) ≤ _)]
    let β := (2:ℝ)^(-a) + 2*Real.exp (-a)
    have hβ : 0 ≤ β := by dsimp [β]; positivity
    have hnoise := measured_success_le_noise l v hv P univ hp (by linarith : p < 1) hβ (by
      intro rec x hx
      simp only [eventInputs, sum_filter]
      exact kernel_shortSuccess_le hr D hd (Equiv.refl D) hkg hn hhn.le hp.le (by linarith)
        (by change a ≤ p*h/8; linarith) x rec hx)
    exact hnoise.trans ((mul_le_mul_of_nonneg_right (noise_penalty_le hp.le hp' hpa ht) hβ).trans
      (query_exponents ha.le))
  · have one : success l v P ≤ 1 := by
      rw [success_eq_branch]
      apply Noise.success_le_of_branch_bound _ _ zero_le_one (branch_mass_le_one l v hv)
      intro b
      rw [one_mul]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
    apply one.trans
    have hh : (1:ℝ) ≤ (2:ℝ)^(-a/4) := Real.one_le_rpow (by norm_num) (by linarith)
    change 1 ≤ 3 * (2:ℝ)^(-a/4)
    linarith

end QuantumNoiseStability.MatrixVector
end

-- Paper.TimeSpace.BasisMass
section
namespace QuantumNoiseStability.TimeSpace

/-- Squared norms after a linear map, summed over a family of total squared norm at most one. -/
theorem map_sum_le_basis_sum {W J : Type} [Fintype W] [Fintype J]
    (L : EuclideanSpace ℂ W →ₗ[ℂ] EuclideanSpace ℂ W)
    (v : J → EuclideanSpace ℂ W) (hv : ∑ j, ‖v j‖ ^ 2 ≤ 1) :
    ∑ j, ‖L (v j)‖ ^ 2 ≤ ∑ w, ‖L ((EuclideanSpace.basisFun W ℂ) w)‖ ^ 2 := by
  classical
  let b := EuclideanSpace.basisFun W ℂ
  let total := ∑ w, ‖L (b w)‖ ^ 2
  have bound (u : EuclideanSpace ℂ W) : ‖L u‖ ^ 2 ≤ ‖u‖ ^ 2 * total := by
    have expand : L u = ∑ w, u w • L (b w) := by
      calc L u = L (∑ w, (b.repr u w) • b w) := congrArg L (b.sum_repr u).symm
           _ = _ := by simp [b]
    have tri : ‖L u‖ ≤ ∑ w, ‖u w‖ * ‖L (b w)‖ := by
      rw [expand]
      exact (norm_sum_le _ _).trans_eq (by simp [norm_smul])
    calc
      ‖L u‖ ^ 2 ≤ (∑ w, ‖u w‖ * ‖L (b w)‖) ^ 2 := by gcongr
      _ ≤ (∑ w, ‖u w‖ ^ 2) * total := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by rw [EuclideanSpace.norm_sq_eq]
  calc
    ∑ j, ‖L (v j)‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 * total := Finset.sum_le_sum fun j _ => bound _
    _ = (∑ j, ‖v j‖ ^ 2) * total := (Finset.sum_mul ..).symm
    _ ≤ 1 * total := mul_le_mul_of_nonneg_right hv (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := one_mul _

end QuantumNoiseStability.TimeSpace
end

-- Paper.TimeSpace.Partition
section
/-! Contiguous partitions by query count. Intermediate measurements have zero query cost. -/

namespace QuantumNoiseStability.TimeSpace

variable {W ι G O : Type} [Fintype W]

/-! ## Chunking a step list into slices -/

/-- A step list with at least `t` query steps splits as `a ++ b` with exactly `t` query
steps in `a`. -/
theorem exists_split_queries :
    ∀ (l : List (Step W ι G O)) (t : ℕ), t ≤ queries l →
      ∃ a b, l = a ++ b ∧ queries a = t
  | [], t, ht => by
    refine ⟨[], [], rfl, ?_⟩
    simp at ht
    simp [ht]
  | s :: l, t, ht => by
    cases t with
    | zero => exact ⟨[], s :: l, rfl, rfl⟩
    | succ t' =>
      cases s with
      | op K =>
        simp only [queries_op] at ht
        obtain ⟨a, b, hab, ha⟩ := exists_split_queries l (t' + 1) ht
        exact ⟨Step.op K :: a, b, by rw [hab]; rfl, by simp [ha]⟩
      | query q =>
        simp only [queries_query] at ht
        obtain ⟨a, b, hab, ha⟩ := exists_split_queries l t' (by omega)
        exact ⟨Step.query q :: a, b, by rw [hab]; rfl, by simp [ha]⟩

/-- The number of slices of at most `t` queries each: `max 1 ⌈T / t⌉`. -/
def sliceCount (T t : ℕ) : ℕ := max 1 ((T + t - 1) / t)

theorem queries_flatten (cs : List (List (Step W ι G O))) :
    queries cs.flatten = (cs.map queries).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatten_cons, queries_append, ih, List.map_cons, List.sum_cons]

/-- **Chunking.** Every step list splits into contiguous slices with at most `t` query
steps each, using at most `max 1 ⌈T/t⌉` slices, where `T` is the number of query steps. -/
theorem exists_chunks (t : ℕ) (ht : 1 ≤ t) (l : List (Step W ι G O)) :
    ∃ cs : List (List (Step W ι G O)), cs.flatten = l ∧ (∀ c ∈ cs, queries c ≤ t) ∧
      cs.length ≤ sliceCount (queries l) t := by
  induction hN : queries l using Nat.strong_induction_on generalizing l with
  | _ N ih =>
    by_cases hle : queries l ≤ t
    · refine ⟨[l], by simp, ?_, ?_⟩
      · intro c hc
        rw [List.mem_singleton] at hc
        rw [hc]; exact hle
      · simp [sliceCount]
    · push Not at hle
      obtain ⟨a, b, hab, ha⟩ := exists_split_queries l t hle.le
      have hqb : queries b = queries l - t := by
        rw [hab, queries_append, ha] at *
        omega
      have hlt : queries b < N := by omega
      obtain ⟨cs, hflat, hcs, hlen⟩ := ih (queries b) hlt b rfl
      refine ⟨a :: cs, ?_, ?_, ?_⟩
      · rw [List.flatten_cons, hflat, hab]
      · intro c hc
        rw [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ha.le
        · exact hcs c hc
      · rw [List.length_cons]
        unfold sliceCount at hlen ⊢
        rw [hqb] at hlen
        have h1 : 1 ≤ (queries l - t + t - 1) / t := by
          apply Nat.le_div_iff_mul_le (by omega) |>.mpr
          omega
        rw [max_eq_right h1] at hlen
        have h2 : (queries l - t + t - 1) / t + 1 = (queries l + t - 1) / t := by
          have : queries l + t - 1 = (queries l - t + t - 1) + 1 * t := by omega
          rw [this, Nat.add_mul_div_right _ _ (by omega)]
        have h3 : (queries l + t - 1) / t ≤ max 1 ((queries l + t - 1) / t) := le_max_right _ _
        rw [← hN]
        omega

end QuantumNoiseStability.TimeSpace
end

-- Paper.TimeSpace.Slicing
section
/-!
# Slicing a quantum computation

A correct full transcript covers every output coordinate. If the computation has few
slices then at least one slice prints many distinct correct outputs. At each boundary
the input-dependent memory is a family of subnormalized states. Replacing the initial state by a sum over basis states costs one factor of the memory dimension per slice.

The list and history argument generalizes the earlier `GeneralHashing.Slicing` proof.
-/

noncomputable section

namespace QuantumNoiseStability.TimeSpace

open Finset
open scoped Classical

variable {W ι G Y : Type} {m : ℕ} [Fintype W]

private theorem sum_comm_rotate {α β γ M : Type*} [AddCommMonoid M] [Fintype α] [Fintype β]
    [Fintype γ] (F : α → β → γ → M) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ x, ∑ y, F x y z := by
  calc ∑ x, ∑ y, ∑ z, F x y z = ∑ x, ∑ z, ∑ y, F x y z := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, F x y z := Finset.sum_comm

/-! ## The slice event -/

/-- The event that some slice's own record satisfies the short event for `k`. -/
def SliceEvent (k : ℕ) (a : Fin m → Y) :
    (cs : List (List (Step W ι G (Fin m × Y)))) → Hist cs.flatten → Prop
  | [], _ => False
  | c :: cs, h =>
      ShortSuccess k a (claims c (histAppend c cs.flatten h).1) ∨
        SliceEvent k a cs (histAppend c cs.flatten h).2

/-- The records of the slices along a history. -/
def records : (cs : List (List (Step W ι G (Fin m × Y)))) → Hist cs.flatten → List (List (Fin m × Y))
  | [], _ => []
  | c :: cs, h =>
      claims c (histAppend c cs.flatten h).1 :: records cs (histAppend c cs.flatten h).2

theorem flatten_records : ∀ (cs : List (List (Step W ι G (Fin m × Y)))) (h : Hist cs.flatten),
    (records cs h).flatten = claims cs.flatten h
  | [], h => by
    show [] = claims [] h
    rfl
  | c :: cs, h => by
    show claims c _ ++ (records cs _).flatten = claims (c ++ cs.flatten) h
    rw [flatten_records cs, claims_append]

theorem length_records : ∀ (cs : List (List (Step W ι G (Fin m × Y)))) (h : Hist cs.flatten),
    (records cs h).length = cs.length
  | [], _ => rfl
  | c :: cs, h => by
    show (records cs _).length + 1 = cs.length + 1
    rw [length_records cs]

theorem sliceEvent_of_mem_records (k : ℕ) (a : Fin m → Y) :
    ∀ (cs : List (List (Step W ι G (Fin m × Y)))) (h : Hist cs.flatten),
      (∃ l ∈ records cs h, ShortSuccess k a l) → SliceEvent k a cs h
  | [], _, ⟨l, hl, _⟩ => by simp [records] at hl
  | c :: cs, h, ⟨l, hl, hs⟩ => by
    simp only [records, List.mem_cons] at hl
    show ShortSuccess k a (claims c _) ∨ SliceEvent k a cs _
    rcases hl with rfl | hl
    · exact Or.inl hs
    · exact Or.inr (sliceEvent_of_mem_records k a cs _ ⟨l, hl, hs⟩)

/-- **Pigeonhole.** A fully successful history with `m > |cs| (k - 1)` has a slice whose
own record has at least `k` distinct correct claims, hence satisfies the short event. -/
theorem sliceEvent_of_fullSuccess {k : ℕ} {a : Fin m → Y} (cs : List (List (Step W ι G (Fin m × Y))))
    (h : Hist cs.flatten) (hfull : FullSuccess a (claims cs.flatten h))
    (hm : cs.length * (k - 1) < m) : SliceEvent k a cs h := by
  apply sliceEvent_of_mem_records
  apply exists_shortSuccess_of_cover k a (records cs h) univ
  · intro c _
    rw [flatten_records]
    exact hfull.1 c
  · rw [flatten_records]
    exact hfull.2
  · rw [length_records, Finset.card_univ, Fintype.card_fin]
    exact hm


private theorem sum_run_le_basis {J : Type} [Fintype J]
    (l : List (Step W ι G (Fin m × Y))) (x : ι → G) (h : Hist l)
    (v : J → State W) (hv : ∑ j, ‖v j‖ ^ 2 ≤ 1) :
    ∑ j, ‖run l x (v j) h‖ ^ 2 ≤
      ∑ w, ‖run l x ((EuclideanSpace.basisFun W ℂ) w) h‖ ^ 2 :=
  map_sum_le_basis_sum (branchMap l x h) v hv

variable [Fintype ι] [DecidableEq ι] [Fintype G] [Nonempty G]

private theorem sum_basis_short_le
    (f : (ι → G) → Fin m → Y) {k t : ℕ} {β : ℝ}
    (hshort : ∀ c : List (Step W ι G (Fin m × Y)), queries c ≤ t → ∀ w : W,
      success c ((EuclideanSpace.basisFun W ℂ) w) (fun x => ShortSuccess k (f x)) ≤ β)
    (c : List (Step W ι G (Fin m × Y))) (hc : queries c ≤ t) :
    ∑ w, ∑ x, eventMass c x ((EuclideanSpace.basisFun W ℂ) w) (ShortSuccess k (f x)) ≤
      (Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)) := by
  calc ∑ w, ∑ x, eventMass c x ((EuclideanSpace.basisFun W ℂ) w) (ShortSuccess k (f x))
      ≤ ∑ _w : W, β * (Fintype.card (ι → G) : ℝ) := by
        apply Finset.sum_le_sum
        intro w _
        have h := hshort c hc w
        unfold success at h
        rwa [← div_eq_inv_mul, div_le_iff₀ (by positivity)] at h
    _ = _ := by simp

private theorem sliceEvent_sum_le (f : (ι → G) → Fin m → Y) {k t : ℕ} {β : ℝ}
    (hshort : ∀ c : List (Step W ι G (Fin m × Y)), queries c ≤ t → ∀ w : W,
      success c ((EuclideanSpace.basisFun W ℂ) w) (fun x => ShortSuccess k (f x)) ≤ β) :
    ∀ (cs : List (List (Step W ι G (Fin m × Y)))), (∀ c ∈ cs, queries c ≤ t) →
      ∀ {J : Type} [Fintype J] (ψ : J → (ι → G) → State W), (∀ x, ∑ j, ‖ψ j x‖ ^ 2 ≤ 1) →
      ∑ x, ∑ j, ∑ h : Hist cs.flatten,
        (if SliceEvent k (f x) cs h then ‖run cs.flatten x (ψ j x) h‖ ^ 2 else 0) ≤
        (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)))
  | [], _, J, _, ψ, _ => by
    simp [SliceEvent]
  | c :: cs, hcs, J, _, ψ, hψ => by
    have hc : queries c ≤ t := hcs c List.mem_cons_self
    have hcs' : ∀ c' ∈ cs, queries c' ≤ t := fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')
    set F := cs.flatten with hF
    show ∑ x, ∑ j, ∑ h : Hist (c ++ F),
        (if SliceEvent k (f x) (c :: cs) h then ‖run (c ++ F) x (ψ j x) h‖ ^ 2
          else 0) ≤ _
    -- split every history of `c ++ F` into its `c` part and its `F` part
    have hsplit : ∀ x j, ∑ h : Hist (c ++ F),
        (if SliceEvent k (f x) (c :: cs) h then ‖run (c ++ F) x (ψ j x) h‖ ^ 2
          else 0) =
        ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if ShortSuccess k (f x) (claims c h₁) ∨ SliceEvent k (f x) cs h₂ then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) := by
      intro x j
      rw [sum_hist_append c F]
      apply Finset.sum_congr rfl
      intro h₁ _
      apply Finset.sum_congr rfl
      intro h₂ _
      have e1 : histAppend c F ((histAppend c F).symm (h₁, h₂)) = (h₁, h₂) :=
        (histAppend c F).apply_symm_apply _
      have hev : SliceEvent k (f x) (c :: cs) ((histAppend c F).symm (h₁, h₂)) ↔
          ShortSuccess k (f x) (claims c h₁) ∨ SliceEvent k (f x) cs h₂ := by
        show ShortSuccess k (f x) (claims c (histAppend c F _).1) ∨
          SliceEvent k (f x) cs (histAppend c F _).2 ↔ _
        rw [e1]
      rw [run_append c F, e1]
      simp only [hev]
    simp_rw [hsplit]
    -- union bound
    have hunion : ∀ x j h₁ h₂,
        (if ShortSuccess k (f x) (claims c h₁) ∨ SliceEvent k (f x) cs h₂ then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) ≤
        (if ShortSuccess k (f x) (claims c h₁) then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) +
        (if SliceEvent k (f x) cs h₂ then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) := by
      intro x j h₁ h₂
      have h0 := sq_nonneg ‖run F x (run c x (ψ j x) h₁) h₂‖
      split_ifs <;> first | linarith | (exfalso; tauto)
    -- the first-slice term
    have hA : ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
        (if ShortSuccess k (f x) (claims c h₁) then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) ≤
        (Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)) := by
      calc ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
            (if ShortSuccess k (f x) (claims c h₁) then
              ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)
          ≤ ∑ x, ∑ j, ∑ h₁ : Hist c,
            (if ShortSuccess k (f x) (claims c h₁) then
              ‖run c x (ψ j x) h₁‖ ^ 2 else 0) := by
            gcongr with x _ j _ h₁ _
            split_ifs
            · exact sum_mass_run_le F x _
            · simp
        _ = ∑ x, ∑ h₁ : Hist c, ∑ j,
            (if ShortSuccess k (f x) (claims c h₁) then
              ‖run c x (ψ j x) h₁‖ ^ 2 else 0) := by
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ ≤ ∑ x, ∑ h₁ : Hist c, ∑ w : W,
            (if ShortSuccess k (f x) (claims c h₁) then
              ‖run c x ((EuclideanSpace.basisFun W ℂ) w) h₁‖ ^ 2 else 0) := by
            apply Finset.sum_le_sum
            intro x _
            apply Finset.sum_le_sum
            intro h₁ _
            by_cases he : ShortSuccess k (f x) (claims c h₁)
            · simpa only [if_pos he] using sum_run_le_basis c x h₁ (fun j => ψ j x) (hψ x)
            · simp [he]
        _ = ∑ w, ∑ x, eventMass c x ((EuclideanSpace.basisFun W ℂ) w) (ShortSuccess k (f x)) :=
            sum_comm_rotate _
        _ ≤ (Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)) :=
            sum_basis_short_le f hshort c hc
    -- the remaining slices, by the induction hypothesis with the new starting family
    have hB : ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
        (if SliceEvent k (f x) cs h₂ then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) ≤
        (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) := by
      have hψ' : ∀ x, ∑ p : J × Hist c, ‖run c x (ψ p.1 x) p.2‖ ^ 2 ≤ 1 := by
        intro x
        rw [Fintype.sum_prod_type]
        calc ∑ j, ∑ h₁ : Hist c, ‖run c x (ψ j x) h₁‖ ^ 2
            ≤ ∑ j, ‖ψ j x‖ ^ 2 := Finset.sum_le_sum fun j _ => sum_mass_run_le c x _
          _ ≤ 1 := hψ x
      have := sliceEvent_sum_le f hshort cs hcs' (fun p : J × Hist c => fun x =>
        run c x (ψ p.1 x) p.2) hψ'
      simp_rw [Fintype.sum_prod_type] at this
      exact this
    calc ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if ShortSuccess k (f x) (claims c h₁) ∨ SliceEvent k (f x) cs h₂ then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)
        ≤ ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          ((if ShortSuccess k (f x) (claims c h₁) then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) +
          (if SliceEvent k (f x) cs h₂ then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)) := by
          gcongr with x _ j _ h₁ _ h₂ _
          exact hunion x j h₁ h₂
      _ = (∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if ShortSuccess k (f x) (claims c h₁) then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)) +
          (∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if SliceEvent k (f x) cs h₂ then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)) := by
          simp_rw [Finset.sum_add_distrib]
      _ ≤ (Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)) +
          (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) :=
          add_le_add hA hB
      _ = ((c :: cs).length : ℝ) *
          ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) := by
          rw [List.length_cons]
          push_cast
          ring


/-- If each short computation from an input-independent basis state succeeds with
probability at most `β`, a full computation that needs one such successful slice
has success probability at most the number of slices times `2 ^ S * β`. -/
theorem success_le_slices (f : (ι → G) → Fin m → Y)
    (l : List (Step W ι G (Fin m × Y))) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    {t k S : ℕ} {β : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hmem : Fintype.card W ≤ 2 ^ S)
    (hshort : ∀ c : List (Step W ι G (Fin m × Y)), queries c ≤ t → ∀ w : W,
      success c ((EuclideanSpace.basisFun W ℂ) w) (fun x => ShortSuccess k (f x)) ≤ β)
    (hcount : sliceCount (queries l) t * (k - 1) < m) :
    success l v (fun x => FullSuccess (f x)) ≤ (sliceCount (queries l) t : ℝ) * (2 : ℝ)^S * β := by
  obtain ⟨cs, rfl, hcs, hlen⟩ := exists_chunks t ht l
  have hm := (Nat.mul_le_mul_right (k - 1) hlen).trans_lt hcount
  have hmain := sliceEvent_sum_le f hshort cs hcs (J := Unit) (fun _ _ => v) (fun _ => by simpa using hv)
  simp only [Finset.univ_unique, Finset.sum_singleton] at hmain
  have hfull : ∑ x, eventMass cs.flatten x v (FullSuccess (f x)) ≤
      (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) := by
    refine le_trans ?_ hmain
    apply Finset.sum_le_sum
    intro x _
    unfold eventMass
    apply Finset.sum_le_sum
    intro h _
    by_cases hf : FullSuccess (f x) (claims cs.flatten h)
    · simp [hf, sliceEvent_of_fullSuccess cs h hf hm]
    · simp only [if_neg hf]
      split_ifs <;> positivity
  have hN : (0 : ℝ) < Fintype.card (ι → G) := by positivity
  have hdim : (Fintype.card W : ℝ) ≤ (2 : ℝ) ^ S := by exact_mod_cast hmem
  have hlen' : (cs.length : ℝ) ≤ sliceCount (queries cs.flatten) t := by exact_mod_cast hlen
  unfold success
  rw [← div_eq_inv_mul, div_le_iff₀ hN]
  calc ∑ x, eventMass cs.flatten x v (FullSuccess (f x))
      ≤ (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) := hfull
    _ ≤ (sliceCount (queries cs.flatten) t : ℝ) *
          ((2 : ℝ) ^ S * (β * (Fintype.card (ι → G) : ℝ))) := by gcongr
    _ = _ := by ring

end QuantumNoiseStability.TimeSpace
end
end

-- Paper.TimeSpace.Arithmetic
section
/-!
# Arithmetic of time-space lower bounds

The circuit-specific input is a bound on a segment's success probability and the
pigeonhole implication for complete success. The three application theorems derive time
lower bounds from these numerical inputs. The sorting and hashing theorems also use
a whole-computation short-query bound. The segment count is the one from
`TimeSpace.Partition`, including the final short segment.
-/

namespace QuantumNoiseStability.TimeSpace

/-- The segment count used in the sorting parameter bounds. -/
abbrev segmentCount := sliceCount

/-- If a successful computation needs more than `r * (k - 1)` outputs, one of its
segments produces at least `k` correct outputs. Here `q` bounds the probability
before advice, and `p` is the complete-success probability. -/
def SlicedBound (m k r S : ℕ) (p q : ℝ) : Prop :=
  r * (k - 1) < m → p ≤ r * (2 : ℝ) ^ S * q

theorem slicedBound_of_segment_probabilities {m k r S : ℕ} {p q : ℝ}
    (prob : Fin r → ℝ) (hpigeon : r * (k - 1) < m → p ≤ ∑ i, prob i)
    (hseg : ∀ i, prob i ≤ (2 : ℝ) ^ S * q) : SlicedBound m k r S p q := by
  intro h
  apply (hpigeon h).trans
  simpa [mul_assoc] using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r))) (fun i _ => hseg i)

/-- The strict segment budget permits equality in the required success probability. -/
theorem output_count_of_exponential_bound {m k r S : ℕ} {p C b d ℓ : ℝ}
    (hslice : SlicedBound m k r S p (C * (2 : ℝ) ^ (-d)))
    (hbudget : r * C < (2 : ℝ) ^ b) (hexp : b + S + ℓ ≤ d)
    (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p) : m ≤ r * (k - 1) := by
  by_contra! h
  have hlt : (r : ℝ) * (2 : ℝ) ^ S * (C * (2 : ℝ) ^ (-d)) < (2 : ℝ) ^ (-ℓ) := by
    calc _ = (r * C) * ((2 : ℝ) ^ (S : ℝ) * 2 ^ (-d)) := by rw [Real.rpow_natCast]; ring
         _ < 2 ^ b * (2 ^ (S : ℝ) * 2 ^ (-d)) :=
           mul_lt_mul_of_pos_right hbudget (by positivity)
         _ = (2 : ℝ) ^ (b + S + -d) := by
           rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
           ring
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  exact (not_lt_of_ge hsucc) ((hslice h).trans_lt hlt)

theorem sliceCount_le_of_queries_le {T t r : ℕ} (ht : 0 < t) (hr : 1 ≤ r)
    (h : T ≤ t * r) : sliceCount T t ≤ r :=
  max_le hr ((ceilDiv_le_iff_le_mul ht).2 h)

theorem sliceCount_le_queries {T t : ℕ} (hT : 0 < T) (ht : 0 < t) :
    sliceCount T t ≤ T :=
  sliceCount_le_of_queries_le ht hT (Nat.le_mul_of_pos_left _ ht)

/-- Enough outputs for the threshold `k` force at least two segments. This also
justifies absorbing the ceiling without a separate hypothesis `t ≤ T`. -/
theorem work_le_of_output_count {m k r T t : ℕ} (ht : 0 < t) (hk : 0 < k)
    (hkm : k ≤ m) (hr : r ≤ sliceCount T t) (hout : m ≤ r * (k - 1)) :
    m * t ≤ 2 * T * (k - 1) := by
  have htwo : 1 < r := by
    by_contra! h
    have := Nat.mul_le_mul_right (k - 1) h
    simp only [one_mul] at this
    omega
  have hr' : r ≤ T ⌈/⌉ t := by change r ≤ max 1 (T ⌈/⌉ t) at hr; omega
  have htT : t ≤ T := by
    by_contra! h
    have hle : T ⌈/⌉ t ≤ 1 := (ceilDiv_le_iff_le_mul ht).2 (by simpa using h.le)
    omega
  have hrt : r * t ≤ 2 * T := by
    have h := Nat.mul_le_mul_right t hr'
    rw [Nat.ceilDiv_eq_add_pred_div] at h
    have := Nat.div_mul_le_self (T + t - 1) t
    omega
  calc m * t ≤ (r * (k - 1)) * t := Nat.mul_le_mul_right _ hout
       _ = (r * t) * (k - 1) := by ring
       _ ≤ _ := Nat.mul_le_mul_right _ hrt

/-- Rounding a segment length down loses at most a factor of two once it reaches one. -/
theorem le_two_mul_floor {x : ℝ} (hx : 1 ≤ x) : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
  have h : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).2 (by simpa using hx)
  have h' : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h
  linarith [Nat.lt_floor_add_one x]

noncomputable section

/-- Query budget in Lemma 5.4, rounded down to an integer. -/
def sortingSegmentLength (α : ℝ) (k n : ℕ) : ℕ :=
  ⌊α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊

/-- Conversion of the segment output count in the small-space case of §5.2.
Here `L` is the rounded logarithmic factor. -/
theorem sorting_of_output_count {α : ℝ} {n k L T r : ℕ}
    (hk : 0 < k) (hL : 0 < L) (hcap : 8 * L * k ≤ n)
    (hlen : 1 ≤ α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ))
    (hr : r ≤ sliceCount T (sortingSegmentLength α k n))
    (hout : n ≤ r * (8 * L * k - 1)) :
    α * (n : ℝ) ^ (4 / 3 : ℝ) ≤ 32 * T * L * (k : ℝ) ^ (1 / 3 : ℝ) := by
  let t := sortingSegmentLength α k n
  have ht : 1 ≤ t := (Nat.le_floor_iff (by linarith : 0 ≤
    α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ))).2 (by simpa using hlen)
  have hw := work_le_of_output_count ht (by positivity) hcap hr hout
  have hw' : n * t ≤ 2 * T * (8 * L * k) :=
    hw.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hreal : (n : ℝ) * t ≤ 2 * T * (8 * L * k) := by exact_mod_cast hw'
  have hf : α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) ≤ 2 * t :=
    le_two_mul_floor hlen
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply le_of_mul_le_mul_right (a := (k : ℝ) ^ (2 / 3 : ℝ)) _ (by positivity)
  rw [mul_assoc (32 * (T : ℝ) * L), ← Real.rpow_add hk', show (1 / 3 + 2 / 3 : ℝ) = 1 by norm_num,
    Real.rpow_one, show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num,
    Real.rpow_add_of_nonneg (Nat.cast_nonneg n) (by norm_num) (by norm_num), Real.rpow_one]
  linarith [mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg n)]

/-- Above the allowed range of `k` in Lemma 5.4, a linear query lower bound
already gives the same tradeoff. -/
theorem sorting_of_large_space {α : ℝ} {n k L T : ℕ} (hα : 0 ≤ α)
    (hlarge : α * n ≤ (k : ℝ) * (8 * L : ℝ) ^ 3) (hlinear : n ≤ 3 * T) :
    α ^ (1 / 3 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) ≤ 32 * T * L * (k : ℝ) ^ (1 / 3 : ℝ) := by
  have hroot := Real.rpow_le_rpow (mul_nonneg hα (Nat.cast_nonneg n)) hlarge
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [Real.mul_rpow hα (Nat.cast_nonneg n), Real.mul_rpow (Nat.cast_nonneg k) (by positivity),
    show (1 / 3 : ℝ) = (↑(3 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by decide : (3 : ℕ) ≠ 0)] at hroot
  have h' : α ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) ≤
      (k : ℝ) ^ (1 / 3 : ℝ) * (8 * L) := by norm_num [one_div] at hroot ⊢; exact hroot
  have hT : (n : ℝ) ≤ 3 * T := by exact_mod_cast hlinear
  rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num,
    Real.rpow_add_of_nonneg (Nat.cast_nonneg n) (by norm_num) (by norm_num), Real.rpow_one]
  have h := mul_le_mul hT h' (by positivity) (by positivity)
  linarith [show 0 ≤ (T : ℝ) * L * (k : ℝ) ^ (1 / 3 : ℝ) by positivity]

/-- Proposition 3.7 supplies the bound for reading the input when `3T ≤ n`.
This arithmetic step compares it with the required success probability. -/
theorem linear_time_of_recovery_bound {n m T : ℕ} {p ℓ : ℝ} (hm : 2 ≤ m)
    (hℓ : ℓ < n / (15 : ℝ)) (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p)
    (hshort : 3 * T ≤ n → p ≤ (m : ℝ) ^ (-(n : ℝ) / 15)) : n < 3 * T := by
  by_contra! h
  have hbase : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hprob := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hbase
    (show -(n : ℝ) / 15 ≤ 0 by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact (not_lt_of_ge hsucc) (((hshort h).trans hprob).trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)))

/-- The numerical conversion in §5.2, with `k = A*S` and output threshold
`8*⌈u⌉*k`. The ratio `u` can use any logarithm convention for which the
short-segment bound holds. The constants `α` and `β` specify the query length
and the allowed range of `k`, respectively. The input recovery and sliced success
bounds are the two circuit-specific hypotheses. -/
theorem sorting_time_lower_bound_of_range {n m S T A : ℕ} {α β γ u ℓ p : ℝ}
    (hn : 1 < n) (hm : 2 ≤ m) (hS : 0 < S) (hreg : n ^ 2 ≤ 2 ^ S)
    (hA : 4 ≤ A) (hγ : 3 ≤ γ * A) (hα : 0 < α) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hsize : 1 ≤ α * (n : ℝ) ^ (1 / 3 : ℝ)) (hu : 1 ≤ u)
    (hℓS : ℓ ≤ S) (hℓn : ℓ < n / (15 : ℝ)) (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p)
    (hshort : 3 * T ≤ n → p ≤ (m : ℝ) ^ (-(n : ℝ) / 15))
    (hslice : let k := A * S
      4 ≤ k → (k : ℝ) * (8 * (⌈u⌉₊ : ℝ)) ^ 3 ≤ β * n →
      SlicedBound n (8 * ⌈u⌉₊ * k) (sliceCount T (sortingSegmentLength α k n)) S p
        ((2 : ℝ) ^ (-(γ * k)))) :
    min α β * (n : ℝ) ^ (4 / 3 : ℝ) / (64 * (A : ℝ) ^ (1 / 3 : ℝ) *
      (S : ℝ) ^ (1 / 3 : ℝ) * u) ≤ T := by
  let k := A * S
  let L := ⌈u⌉₊
  let t := sortingSegmentLength α k n
  have hk4 : 4 ≤ k := hA.trans (Nat.le_mul_of_pos_right _ hS)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hL : 1 ≤ L := Nat.ceil_pos.2 (by linarith)
  have hlinear := linear_time_of_recovery_bound hm hℓn hsucc hshort
  have hmain : min α β * (n : ℝ) ^ (4 / 3 : ℝ) ≤
      32 * T * L * (k : ℝ) ^ (1 / 3 : ℝ) := by
    by_cases hlarge : β * n ≤ (k : ℝ) * (8 * L : ℝ) ^ 3
    · have hcoef := (min_le_right α β).trans
          (Real.self_le_rpow_of_le_one hβ.le hβ1 (by norm_num : (1 / 3 : ℝ) ≤ 1))
      exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
        (sorting_of_large_space hβ.le hlarge hlinear.le)
    by_cases hbig : n ^ 2 ≤ T
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
      have hpow : (n : ℝ) ^ (4 / 3 : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [← Real.rpow_natCast _ 2]
        exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      have hT : (n : ℝ) ^ 2 ≤ T := by exact_mod_cast hbig
      have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hcoef := (min_le_right α β).trans hβ1
      calc _ ≤ 1 * (n : ℝ) ^ 2 := mul_le_mul hcoef hpow (by positivity) zero_le_one
           _ ≤ T := by simpa using hT
           _ ≤ 32 * T * L * (k : ℝ) ^ (1 / 3 : ℝ) := by
             have h := mul_le_mul hL' (Real.one_le_rpow hk1 (by norm_num : (0 : ℝ) ≤ 1/3))
               zero_le_one (Nat.cast_nonneg L)
             nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg T)]
    have hsmall := (lt_of_not_ge hlarge).le
    have hlen : 1 ≤ α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
      calc 1 ≤ α * (n : ℝ) ^ (1 / 3 : ℝ) := hsize
           _ ≤ α * (n : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ) :=
             le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hk1 (by norm_num))
           _ = _ := by ring
    have ht : 0 < t := (Nat.le_floor_iff (by linarith :
      0 ≤ α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ))).2 (by simpa using hlen)
    have hr : sliceCount T t < 2 ^ S :=
      (sliceCount_le_queries (by omega) ht).trans_lt ((lt_of_not_ge hbig).trans_le hreg)
    have hb : (sliceCount T t : ℝ) * 1 < (2 : ℝ) ^ (S : ℝ) := by
      rw [mul_one, Real.rpow_natCast]
      exact_mod_cast hr
    have hd : (S : ℝ) + S + ℓ ≤ γ * k := by
      dsimp [k]
      push_cast
      linarith [mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg S)]
    have hs := hslice hk4 hsmall
    have hout : n ≤ sliceCount T t * (8 * L * k - 1) :=
      output_count_of_exponential_bound (C := 1) (by simpa only [one_mul] using hs) hb hd hsucc
    have hcap : 8 * L * k ≤ n := by
      have hnat : (8 * L : ℝ) ≤ (8 * L : ℝ) ^ 3 :=
        le_self_pow₀ (by exact_mod_cast (show 1 ≤ 8 * L by omega)) (by decide)
      have h := (mul_le_mul_of_nonneg_left hnat (Nat.cast_nonneg k)).trans
        (hsmall.trans (mul_le_of_le_one_left (Nat.cast_nonneg n) hβ1))
      exact_mod_cast (by simpa [mul_comm] using h : (8 * (L : ℝ)) * k ≤ n)
    exact (mul_le_mul_of_nonneg_right (min_le_left α β) (by positivity)).trans
      (sorting_of_output_count (by omega) hL hcap hlen le_rfl hout)
  have hround : (L : ℝ) ≤ 2 * u := by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ u)]
  have hkpow : (k : ℝ) ^ (1 / 3 : ℝ) = (A : ℝ) ^ (1 / 3 : ℝ) * (S : ℝ) ^ (1 / 3 : ℝ) := by
    simp [k, Real.mul_rpow]
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  apply (div_le_iff₀ (by positivity)).2
  rw [hkpow] at hmain
  have h := mul_le_mul_of_nonneg_right hround
    (show 0 ≤ 32 * (T : ℝ) * ((A : ℝ) ^ (1 / 3 : ℝ) * (S : ℝ) ^ (1 / 3 : ℝ)) by positivity)
  linarith

/-- Specialization when Lemma 5.4 uses the same constant for the query budget
and the admissible range of output thresholds. -/
theorem sorting_time_lower_bound {n m S T A : ℕ} {α γ u ℓ p : ℝ}
    (hn : 1 < n) (hm : 2 ≤ m) (hS : 0 < S) (hreg : n ^ 2 ≤ 2 ^ S)
    (hA : 4 ≤ A) (hγ : 3 ≤ γ * A) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsize : 1 ≤ α * (n : ℝ) ^ (1 / 3 : ℝ)) (hu : 1 ≤ u)
    (hℓS : ℓ ≤ S) (hℓn : ℓ < n / (15 : ℝ)) (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p)
    (hshort : 3 * T ≤ n → p ≤ (m : ℝ) ^ (-(n : ℝ) / 15))
    (hslice : ∀ k : ℕ, 4 ≤ k → (k : ℝ) * (8 * (⌈u⌉₊ : ℝ)) ^ 3 ≤ α * n →
      SlicedBound n (8 * ⌈u⌉₊ * k) (sliceCount T (sortingSegmentLength α k n)) S p
        ((2 : ℝ) ^ (-(γ * k)))) :
    α * (n : ℝ) ^ (4 / 3 : ℝ) / (64 * (A : ℝ) ^ (1 / 3 : ℝ) *
      (S : ℝ) ^ (1 / 3 : ℝ) * u) ≤ T := by
  simpa only [min_self] using sorting_time_lower_bound_of_range hn hm hS hreg hA hγ hα hα hα1
    hsize hu hℓS hℓn hsucc hshort (hslice (A * S))

-- These expressions agree by definition with the budgets in Sorting.Parameters,
-- which imports the numeric conversion above.
local notation "widthFactor" => (fun n : ℕ => ⌈Real.log n / Real.log (Real.log n)⌉₊)
local notation "queryBudget" => (fun n k : ℕ =>
  ⌊(k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) / 128⌋₊)

/-- Theorem 5.1 at the numeric interface of `Sorting.lemma54_parameters`.
Only the input recovery probability and the sliced probability implication for
`k = 36S` are required from the circuit. Both constants and the cutoff are explicit. -/
theorem sorting_log_time_lower_bound {n m S T : ℕ} {p : ℝ}
    (hn : 128 ^ 3 ≤ n) (hm : 2 ≤ m) (hreg : n ^ 2 ≤ 2 ^ S)
    (hsucc : (2 : ℝ) ^ (-min (S : ℝ)
      (n / (32 * (Real.log n / Real.log (Real.log n)) ^ 3))) ≤ p)
    (hshort : 3 * T ≤ n → p ≤ (m : ℝ) ^ (-(n : ℝ) / 15))
    (hslice : (36 * S) * (4096 * widthFactor n) ^ 3 ≤ n →
      SlicedBound n (8 * widthFactor n * (36 * S)) (sliceCount T (queryBudget n (36 * S)))
        S p ((2 : ℝ) ^ (-((36 * S : ℕ) : ℝ) / 12))) :
    (n : ℝ) ^ (4 / 3 : ℝ) * Real.log (Real.log n) /
      (512 ^ 3 * 64 * (36 : ℝ) ^ (1 / 3 : ℝ) * (S : ℝ) ^ (1 / 3 : ℝ) *
        Real.log n) ≤ T := by
  let u := Real.log n / Real.log (Real.log n)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := (Real.lt_log_iff_exp_lt hn0).2 (Real.exp_one_lt_three.trans_le hn')
  have hll := Real.log_pos hlog
  have hu : 1 ≤ u := by
    apply (one_le_div hll).2
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log n)]
  have hℓ : (n : ℝ) / (32 * u ^ 3) < n / 15 := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith only [hn0, mul_le_mul_of_nonneg_left (one_le_pow₀ hu (n := 3)) hn0.le]
  have hS : 0 < S := by
    by_contra! h
    have : S = 0 := by omega
    simp [this] at hreg
    nlinarith
  have hroot := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128 ^ 3)
    (by exact_mod_cast hn : (128 : ℝ) ^ 3 ≤ n) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [one_div, ← Nat.cast_ofNat (R := ℝ) (n := 3),
    Real.pow_rpow_inv_natCast (by norm_num) (by decide)] at hroot
  have hsize : 1 ≤ 1 / 128 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    norm_num [one_div] at hroot ⊢
    linarith
  have hbound := sorting_time_lower_bound_of_range (A := 36) (γ := 1/12) (α := 1/128) (β := 1/512^3)
    (by omega : 1 < n) hm hS hreg (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hsize hu (min_le_left _ _) ((min_le_right _ _).trans_lt hℓ) hsucc hshort
  have happ : (min (1/128 : ℝ) (1/512^3)) * (n : ℝ) ^ (4/3 : ℝ) /
      (64 * (36 : ℝ) ^ (1/3 : ℝ) * (S : ℝ) ^ (1/3 : ℝ) * u) ≤ T := by
    apply hbound
    intro k _ hk
    have hrange : k * (4096 * widthFactor n) ^ 3 ≤ n := by
      change (k : ℝ) * (8 * (widthFactor n : ℝ)) ^ 3 ≤ 1 / 512^3 * n at hk
      exact_mod_cast (by linarith only [hk] :
        (k : ℝ) * (4096 * (widthFactor n : ℝ)) ^ 3 ≤ n)
    have ht : sortingSegmentLength (1/128) k n = queryBudget n k := by
      unfold sortingSegmentLength
      congr 1
      ring
    rw [ht]
    have he : -(1 / 12 * (k : ℝ)) = -(k : ℝ) / 12 := by ring
    rw [he]
    exact hslice hrange
  apply le_trans _ happ
  apply le_of_eq
  dsimp [u]
  rw [min_eq_right (by norm_num : (1 / 512 ^ 3 : ℝ) ≤ 1 / 128)]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The final conversion for a fixed hash in §4.1. The whole-program short-query
bound uses `⌊m/32⌋` outputs. The slice bound uses `32S` outputs in the small-space
case. The success exponent `ℓ` may be any real up to `min S (m/1024)`. -/
theorem hashing_time_lower_bound {n m S T : ℕ} {α ℓ p : ℝ}
    (hm : 1024 ≤ m) (hmn : m ≤ n) (hreg : n ≤ 2 ^ S)
    (hα1 : α ≤ 1) (hlen : 1 ≤ α * n)
    (hℓS : ℓ ≤ S) (hℓm : ℓ ≤ m / (1024 : ℝ)) (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p)
    (hshort : T ≤ ⌊α * n⌋₊ → p ≤ (2 : ℝ) ^ (-((m / 32 : ℕ) : ℝ) / 8))
    (hslice : 1024 * S ≤ m → SlicedBound m (32 * S) (sliceCount T ⌊α * n⌋₊) S p
      ((2 : ℝ) ^ (-((32 * S : ℕ) : ℝ) / 8))) :
    α * n * m ≤ 1024 * T * S := by
  let t := ⌊α * n⌋₊
  have hS : 0 < S := by
    by_contra! h
    have : S = 0 := by omega
    simp [this] at hreg
    omega
  have hf : (m : ℝ) ≤ 64 * ((m / 32 : ℕ) : ℝ) := by
    exact_mod_cast (show m ≤ 64 * (m / 32) by omega)
  have hT : t < T := by
    by_contra! h
    have hstrict : -(↑(m / 32) : ℝ) / 8 < -ℓ := by
      linarith [show (0 : ℝ) < m by exact_mod_cast (show 0 < m by omega)]
    exact (not_lt_of_ge hsucc) ((hshort h).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hstrict))
  have hlin : α * (n : ℝ) ≤ T := by
    have : t + 1 ≤ T := hT
    have h' : (t : ℝ) + 1 ≤ T := by exact_mod_cast this
    exact (Nat.lt_floor_add_one _).le.trans h'
  by_cases hsmall : 1024 * S ≤ m
  · by_cases hbig : n * m ≤ T
    · have hnm : (n : ℝ) * m ≤ T := by exact_mod_cast hbig
      have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
      calc _ ≤ 1 * (n : ℝ) * m := by gcongr
           _ ≤ T := by simpa using hnm
           _ ≤ 1024 * T * S := by nlinarith [mul_le_mul_of_nonneg_left hS1 (Nat.cast_nonneg T)]
    have ht : 0 < t := (Nat.le_floor_iff (by linarith : 0 ≤ α * n)).2 (by simpa using hlen)
    have hn2 : n * m ≤ 2 ^ (2 * S) := by
      rw [mul_comm 2 S, pow_mul, sq]
      exact Nat.mul_le_mul hreg (hmn.trans hreg)
    have hr := (sliceCount_le_queries (by omega : 0 < T) ht).trans_lt
      ((lt_of_not_ge hbig).trans_le hn2)
    have hb : (sliceCount T t : ℝ) * 1 < (2 : ℝ) ^ ((2 * S : ℕ) : ℝ) := by
      rw [mul_one, Real.rpow_natCast]
      exact_mod_cast hr
    have hd : ((2 * S : ℕ) : ℝ) + S + ℓ ≤ ((32 * S : ℕ) : ℝ) / 8 := by
      push_cast
      linarith
    have hs := hslice hsmall
    have hout := output_count_of_exponential_bound (C := 1) (by simpa [neg_div] using hs) hb hd hsucc
    have hw := work_le_of_output_count ht (by omega : 0 < 32 * S) (by omega : 32 * S ≤ m)
      le_rfl hout
    have hw' : m * t ≤ 2 * T * (32 * S) := hw.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have hw'' : (m : ℝ) * t ≤ 2 * T * (32 * S) := by exact_mod_cast hw'
    linarith [mul_le_mul_of_nonneg_right (le_two_mul_floor hlen) (Nat.cast_nonneg m),
      show 0 ≤ (T : ℝ) * S by positivity]
  · have hspace : (m : ℝ) ≤ 1024 * S := by exact_mod_cast (le_of_not_ge hsmall)
    linarith [mul_le_mul hlin hspace (Nat.cast_nonneg m) (Nat.cast_nonneg T)]

/-- The final conversion in §6.1 for integer segment length `h / 32`.
Rounding the length down gives the explicit constant `1 / 2048`.
The sliced bound is needed only at `k = ⌈16S/c⌉`; the numeric restrictions on
this choice are derived from the stated space bounds. -/
theorem matrix_time_lower_bound {n g h S T : ℕ} {c p : ℝ} (hn : 193 ≤ n)
    (hhn : h ≤ n) (hreg : n ≤ 2 ^ S) (hc : 0 < c) (hc1 : c ≤ 1)
    (hkg : ⌈16 * (S : ℝ) / c⌉₊ ≤ g) (hkh : 32 * ⌈16 * (S : ℝ) / c⌉₊ ≤ h)
    (hsucc : (2 : ℝ) ^ (-(S : ℝ)) ≤ p)
    (hslice : let k := ⌈16 * S / c⌉₊
      k ≤ g → 32 * k ≤ h → SlicedBound n k (sliceCount T (h / 32)) S p
        (3 * (2 : ℝ) ^ (-(c * k) / 4))) :
    c * n * h ≤ 2048 * T * S := by
  have hS : 0 < S := by
    by_contra! hh
    have : S = 0 := by omega
    simp [this] at hreg
    omega
  by_cases hbig : n * h ≤ T
  · have hnh : (n : ℝ) * h ≤ T := by exact_mod_cast hbig
    calc _ ≤ 1 * (n : ℝ) * h := by gcongr
         _ ≤ T := by simpa using hnh
         _ ≤ 2048 * T * S := by nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ S by exact_mod_cast hS) (Nat.cast_nonneg T)]
  let k := ⌈16 * S / c⌉₊
  have hkpos : 0 < k := Nat.ceil_pos.2 (by positivity)
  have hklo : 16 * (S : ℝ) ≤ (k : ℝ) * c :=
    (div_le_iff₀ hc).1 (Nat.le_ceil _)
  have hkhi : (k : ℝ) * c < 16 * S + c := by
    have hh := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ 16 * (S : ℝ) / c)) hc
    rwa [add_mul, div_mul_cancel₀ _ hc.ne', one_mul] at hh
  have hround : h ≤ 64 * (h / 32) := by omega
  have hrbound : sliceCount T (h / 32) ≤ 64 * n := by
    apply sliceCount_le_of_queries_le (by omega) (by omega)
    calc T ≤ n * h := le_of_not_ge hbig
         _ ≤ n * (64 * (h / 32)) := Nat.mul_le_mul_left _ hround
         _ = _ := by ring
  have hr : sliceCount T (h / 32) * 3 < 2 ^ (2 * S) := by
    rw [mul_comm 2 S, pow_mul, sq]
    calc _ ≤ 64 * n * 3 := Nat.mul_le_mul_right _ hrbound
         _ < n * n := by nlinarith [Nat.mul_le_mul_left n hn]
         _ ≤ _ := Nat.mul_le_mul hreg hreg
  have hb : (sliceCount T (h / 32) : ℝ) * 3 < (2 : ℝ) ^ ((2 * S : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hr
  have hd : ((2 * S : ℕ) : ℝ) + S + S ≤ c * k / 4 := by push_cast; linarith
  have hs := hslice hkg hkh
  have hout := output_count_of_exponential_bound (by simpa [neg_div] using hs) hb hd hsucc
  have hw := work_le_of_output_count (by omega : 0 < h / 32) hkpos (by omega : k ≤ n) le_rfl hout
  have hnwork : n * h ≤ 128 * T * (k - 1) := by
    calc n * h ≤ n * (64 * (h / 32)) := Nat.mul_le_mul_left _ hround
         _ = 64 * (n * (h / 32)) := by ring
         _ ≤ 64 * (2 * T * (k - 1)) := Nat.mul_le_mul_left _ hw
         _ = _ := by ring
  have hw' : (n : ℝ) * h ≤ 128 * T * ((k : ℝ) - 1) := by
    have hh : (n : ℝ) * h ≤ 128 * T * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hnwork
    simpa only [Nat.cast_sub hkpos, Nat.cast_one] using hh
  calc c * (n : ℝ) * h ≤ c * (128 * T * ((k : ℝ) - 1)) := by
         rw [mul_assoc]
         exact mul_le_mul_of_nonneg_left hw' hc.le
       _ = (128 * T) * ((k : ℝ) * c - c) := by ring
       _ ≤ (128 * T) * (16 * S) := by gcongr; linarith
       _ = _ := by ring

end

end QuantumNoiseStability.TimeSpace
end

-- Paper.MatrixVector.Tradeoff
section
namespace QuantumNoiseStability.MatrixVector

open TimeSpace

/-- Theorem 6.6 with an explicit constant for integer-length query segments.
The address register and the total workspace must fit in `S` qubits. -/
theorem theorem_6_6 {F W : Type} [Field F] [Fintype W] {n g h S : ℕ}
    {M : Matrix (Fin n) (Fin n) F} {c : ℝ} (hr : IsRigid M g h c)
    (D : Finset F) (hd : 2 ≤ D.card) (hn : 193 ≤ n) (hreg : n ≤ 2^S) (hmem : Fintype.card W ≤ 2^S)
    (hc : 0 < c) (hkg : ⌈16 * (S : ℝ) / c⌉₊ ≤ g) (hkh : 32 * ⌈16 * (S : ℝ) / c⌉₊ ≤ h)
    (l : List (Step W (Fin n) D (Fin n × F))) (v : State W) (hv : ‖v‖^2 ≤ 1)
    (hsucc : (2:ℝ)^(-(S:ℝ)) ≤ success l v (fun x => FullSuccess (matrixOutput M Subtype.val x))) :
    c*n*h/(2048*(S:ℝ)) ≤ queries l := by
  classical
  have : Nonempty D := (Finset.card_pos.mp (by omega : 0 < D.card)).coe_sort
  have hS : 0 < S := by
    by_contra! hz
    have := Nat.eq_zero_of_le_zero hz
    simp [this] at hreg
    omega
  have hg : 0 < g := (Nat.ceil_pos.mpr (by positivity : 0 < 16*(S:ℝ)/c)).trans_le hkg
  obtain ⟨hc1, hhn⟩ := hr.parameter_bounds (by omega) hg hc
  apply (div_le_iff₀ (by positivity)).mpr
  rw [show (queries l : ℝ) * (2048*S) = 2048*queries l*S by ring]
  apply matrix_time_lower_bound hn hhn.le hreg hc hc1 hkg hkh hsucc
  let k := ⌈16*(S:ℝ)/c⌉₊
  change k ≤ g → 32*k ≤ h → SlicedBound _ k _ _ _ _
  intro hkg hkh hcount
  have hk : 0 < k := Nat.ceil_pos.mpr (by positivity)
  have ht : 0 < h / 32 := by omega
  have bound := success_le_slices (matrixOutput M Subtype.val) l v hv (k := k) ht
    (β := 3*(2:ℝ)^(-(c*k)/4)) (by positivity) hmem (by
      intro s hs w
      apply lemma_6_5 hr D hd hkg hkh s (by omega)
      simp) hcount
  simpa [mul_assoc] using bound

end QuantumNoiseStability.MatrixVector
end

-- Paper.MatrixVector.SiteParameters
section
/-! Passing from the real rigidity thresholds in the mission to integer submatrix sizes. -/

namespace QNoiseStab.Supplement

theorem rigid_floor {n : ℕ} {F : Type} [Field F] {M : Matrix (Fin n) (Fin n) F}
    {g h c : ℝ} (hg : 0 ≤ g) (hh : 0 ≤ h) (hr : IsRigid M g h c) :
    QuantumNoiseStability.MatrixVector.IsRigid M ⌊g⌋₊ ⌊h⌋₊ c := by
  intro R C hR hC
  apply hr R C
  · exact (Nat.cast_le.mpr hR).trans (Nat.floor_le hg)
  · have hwide : n ≤ C.card + ⌊h⌋₊ := by omega
    have hwidth : (n : ℝ) ≤ C.card + (⌊h⌋₊ : ℝ) := by exact_mod_cast hwide
    linarith [Nat.floor_le hh]

theorem rigid_slice_sizes {S : ℕ} (hS : 0 < S) {g h c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hbudget : (S:ℝ) < min (c*g/17) (c*h/544)) :
    ⌈16*(S:ℝ)/c⌉₊ ≤ ⌊g⌋₊ ∧ 32*⌈16*(S:ℝ)/c⌉₊ ≤ ⌊h⌋₊ ∧ h ≤ 2*(⌊h⌋₊ : ℝ) := by
  let k := ⌈16*(S:ℝ)/c⌉₊
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
  obtain ⟨hg, hh⟩ := lt_min_iff.mp hbudget
  have hkpos : 0 < k := Nat.ceil_pos.mpr (by positivity)
  have hk : (k:ℝ)*c < 16*S+c := by
    have h := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ 16*(S:ℝ)/c)) hc
    simpa [k, add_mul, div_mul_cancel₀ _ hc.ne'] using h
  have kg : (k:ℝ) ≤ g := (le_of_lt ((mul_lt_mul_iff_of_pos_right hc).mp
    (by linarith : (k:ℝ)*c < g*c)))
  have kh : ((32*k : ℕ) : ℝ) ≤ h := by
    push_cast
    apply (le_of_lt ((mul_lt_mul_iff_of_pos_right hc).mp _))
    linarith
  have hkh := Nat.le_floor kh
  have hfloor : 1 ≤ ⌊h⌋₊ := by omega
  have hfloor' : (1:ℝ) ≤ (⌊h⌋₊:ℝ) := by exact_mod_cast hfloor
  exact ⟨Nat.le_floor kg, hkh, by linarith [Nat.lt_floor_add_one h]⟩

end QNoiseStab.Supplement
end

-- Paper.TimeSpace.SitePreparation
section
noncomputable section

namespace QNoiseStab.Supplement.SiteExecution

open QuantumNoiseStability QuantumNoiseStability.TimeSpace

variable {M I G O : Type} [Fintype M] [DecidableEq M]

private def prepareBranch (L : Matrix M M ℂ) (w j : M) : State M →ₗ[ℂ] State M where
  toFun v := WithLp.toLp 2 (fun i => L i j * v w)
  map_add' u v := by ext i; exact mul_add _ _ _
  map_smul' c v := by ext i; exact mul_left_comm _ _ _

/-- Prepare the columns of a density matrix factor from the basis state at `w`. -/
def prepare {M O : Type} [Fintype M] [DecidableEq M] (L : Matrix M M ℂ) (w : M)
    (hL : ∑ j, ∑ i, ‖L i j‖ ^ 2 = 1) : TimeSpace.Instrument M O where
  outcomes := Fintype.card M
  kraus k := prepareBranch L w ((Fintype.equivFin M).symm k)
  emit _ := []
  subnormalized v := by
    rw [Equiv.sum_comp (Fintype.equivFin M).symm (fun j => ‖prepareBranch L w j v‖ ^ 2)]
    simp only [EuclideanSpace.norm_sq_eq]
    change (∑ j, ∑ i, ‖L i j * v w‖ ^ 2) ≤ ∑ i, ‖v i‖ ^ 2
    simp only [norm_mul, mul_pow, ← Finset.sum_mul, hL, one_mul]
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖v i‖) (Finset.mem_univ w)

/-- Summing over the silent preparation outcome runs the remaining steps on each column. -/
theorem sum_prepare (L : Matrix M M ℂ) (w : M) (hL : ∑ j, ∑ i, ‖L i j‖ ^ 2 = 1)
    (l : List (TimeSpace.Step M I G O)) (x : I → G) (g : List O → TimeSpace.State M → ℝ) :
    (∑ h : Hist (.op (prepare L w hL) :: l),
      g (claims _ h) (run _ x (EuclideanSpace.single w 1) h)) =
    ∑ j, ∑ h : Hist l, g (claims l h) (run l x (WithLp.toLp 2 (fun i => L i j)) h) := by
  change (∑ p : Fin (Fintype.card M) × Hist l, g (claims l p.2)
    (run l x (prepareBranch L w ((Fintype.equivFin M).symm p.1)
      (EuclideanSpace.single w 1)) p.2)) = _
  rw [Fintype.sum_prod_type, Equiv.sum_comp (Fintype.equivFin M).symm
    (fun j => ∑ h : Hist l, g (claims l h) (run l x (prepareBranch L w j
      (EuclideanSpace.single w 1)) h))]
  simp [prepareBranch]

end QNoiseStab.Supplement.SiteExecution
end
end

-- Solutions.MatrixMass
section
namespace QNoiseStab.Supplement.MatrixMass

open Matrix
open scoped ComplexOrder MatrixOrder

variable {I J : Type*} [Fintype I] [Fintype J]

theorem trace_mmstar_re (M : Matrix I J ℂ) :
    (M * Mᴴ).trace.re = ∑ j, ∑ i, ‖M i j‖ ^ 2 := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, Complex.star_def,
    Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  exact Finset.sum_comm

theorem posSemidef_factor {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) :
    ∃ L : Matrix I I ℂ, ρ = L * Lᴴ := by
  classical
  exact CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hρ.nonneg

theorem kraus_mass [DecidableEq I] (A : J → Matrix I I ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (v : I → ℂ) :
    ∑ j, ∑ i, ‖(A j).mulVec v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have h : ∑ j, star ((A j) *ᵥ v) ⬝ᵥ ((A j) *ᵥ v) = star v ⬝ᵥ v := calc
    _ = ∑ j, star v ⬝ᵥ (((A j)ᴴ * A j) *ᵥ v) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← mulVec_mulVec, dotProduct_mulVec (star v), star_mulVec]
    _ = star v ⬝ᵥ v := by rw [← dotProduct_sum, ← sum_mulVec, hA, one_mulVec]
  have re_star_mul (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  simpa only [dotProduct, Complex.re_sum, Pi.star_apply, re_star_mul] using congrArg Complex.re h

theorem trace_of_kraus_product (A : Matrix I I ℂ) {ρ : Matrix I I ℂ}
    (L : Matrix I J ℂ) (hρ : ρ = L * Lᴴ) :
    (A * ρ * Aᴴ).trace.re = ∑ j, ∑ i, ‖A.mulVec (fun k => L k j) i‖ ^ 2 := by
  have h : A * ρ * Aᴴ = (A * L) * (A * L)ᴴ := by
    simp only [hρ, conjTranspose_mul, Matrix.mul_assoc]
  rw [h, trace_mmstar_re]
  rfl

end QNoiseStab.Supplement.MatrixMass
end

-- Solutions.BranchExecution
section
namespace QNoiseStab.Supplement.BranchExecution

open Matrix

variable {J : Type*} [Fintype J] {T : ℕ}

/-- The final vector for one sequence of Kraus matrices, with an oracle between steps. -/
noncomputable def pathState (K : Fin (T + 1) → Matrix J J ℂ) (O : Matrix J J ℂ)
    (v : J → ℂ) : J → ℂ :=
  Fin.induction (motive := fun _ => J → ℂ) (K 0 *ᵥ v)
    (fun t w => K t.succ *ᵥ (O *ᵥ w)) (Fin.last T)

@[simp] theorem pathState_zero (K : Fin 1 → Matrix J J ℂ) (O : Matrix J J ℂ) (v : J → ℂ) :
    pathState K O v = K 0 *ᵥ v := rfl

private theorem induction_castSucc {S : Type*} (a : S) (step : Fin (T + 1) → S → S)
    (i : Fin (T + 1)) :
    Fin.induction (motive := fun _ => S) a step i.castSucc =
      Fin.induction (motive := fun _ => S) a (fun t => step t.castSucc) i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact congrArg (step i.castSucc) ih

private theorem induction_last_succ {S : Type*} (a : S) (step : Fin (T + 1) → S → S) :
    Fin.induction (motive := fun _ => S) a step (Fin.last (T + 1)) =
      step (Fin.last T)
        (Fin.induction (motive := fun _ => S) a (fun t => step t.castSucc) (Fin.last T)) :=
  congrArg (step (Fin.last T)) (induction_castSucc a step (Fin.last T))

theorem pathState_succ (K : Fin (T + 2) → Matrix J J ℂ) (O : Matrix J J ℂ) (v : J → ℂ) :
    pathState K O v =
      K (Fin.last (T + 1)) *ᵥ (O *ᵥ pathState (fun t => K t.castSucc) O v) :=
  induction_last_succ (K 0 *ᵥ v) (fun t w => K t.succ *ᵥ (O *ᵥ w))

variable {κ : Type*} [Fintype κ]

/-- Column `j` is the path starting from column `j` of the initial factor. -/
private noncomputable def pathMatrix (K : Fin (T + 1) → Matrix J J ℂ) (O L : Matrix J J ℂ) :
    Matrix J J ℂ :=
  of fun i j => pathState K O (fun k => L k j) i

private theorem pathMatrix_succ (K : Fin (T + 2) → Matrix J J ℂ) (O L : Matrix J J ℂ) :
    pathMatrix K O L =
      K (Fin.last (T + 1)) * (O * pathMatrix (fun t => K t.castSucc) O L) := by
  ext i j
  exact congrFun (pathState_succ K O (fun k => L k j)) i

private noncomputable def applyKraus (K : κ → Matrix J J ℂ) (ρ : Matrix J J ℂ) :
    Matrix J J ℂ := ∑ r, K r * ρ * (K r)ᴴ

private noncomputable def density (K : Fin (T + 1) → κ → Matrix J J ℂ) (O ρ : Matrix J J ℂ) :
    Matrix J J ℂ :=
  Fin.induction (motive := fun _ => Matrix J J ℂ) (applyKraus (K 0) ρ)
    (fun t σ => applyKraus (K t.succ) (O * σ * Oᴴ)) (Fin.last T)

private theorem density_eq_sum (K : Fin (T + 1) → κ → Matrix J J ℂ) (O L : Matrix J J ℂ) :
    density K O (L * Lᴴ) = ∑ r : Fin (T + 1) → κ,
      let M := pathMatrix (fun t => K t (r t)) O L
      M * Mᴴ := by
  classical
  induction T with
  | zero =>
    change (∑ r, K 0 r * (L * Lᴴ) * (K 0 r)ᴴ) = _
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) κ).symm
    intro r
    change K 0 r * (L * Lᴴ) * (K 0 r)ᴴ = (K 0 r * L) * (K 0 r * L)ᴴ
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  | succ T ih =>
    unfold density
    rw [induction_last_succ]
    change applyKraus (K (Fin.last (T + 1)))
      (O * density (fun t => K t.castSucc) O (L * Lᴴ) * Oᴴ) = _
    rw [ih]
    simp only [applyKraus, Matrix.mul_sum, Matrix.sum_mul]
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T + 2) => κ))
    intro ⟨s, r⟩
    simp only [Fin.snocEquiv_apply, pathMatrix_succ, Fin.snoc_last, Fin.snoc_castSucc,
      conjTranspose_mul, Matrix.mul_assoc]

variable {n d : ℕ} {W : Type} [DecidableEq W]

/-- The published phase query on the full memory. -/
noncomputable abbrev oracle (ω : ℂ) (y : Fin n → ZMod d) :=
  Matrix.kronecker (QNoiseStab.phaseQuery ω y) (1 : Matrix W W ℂ)

local notation "Mem" => (Fin n × ZMod d) × W

variable [NeZero d] [Fintype W] {K V ι : Type} [Fintype K] [Fintype V] [Fintype ι]

/-- Every initial density matrix has a factor whose columns have total squared norm one. -/
theorem exists_start_factor (A : SpaceBoundedAlg n d W K V ι T) :
    ∃ L : Matrix Mem Mem ℂ, A.start = L * Lᴴ ∧ ∑ j, ∑ i, ‖L i j‖ ^ 2 = 1 := by
  obtain ⟨L, hL⟩ := MatrixMass.posSemidef_factor A.start_psd
  refine ⟨L, hL, ?_⟩
  rw [← MatrixMass.trace_mmstar_re, ← hL, A.start_trace, Complex.one_re]

/-- Sum the squared final amplitudes over Kraus paths and columns of the initial factor. -/
theorem commitProb_eq_sum (A : SpaceBoundedAlg n d W K V ι T) (ω : ℂ) (y : Fin n → ZMod d)
    (o : Fin (T + 1) → Option (K × V)) (L : Matrix Mem Mem ℂ)
    (hL : A.start = L * Lᴴ) :
    A.commitProb ω y o = ∑ r : Fin (T + 1) → ι, ∑ j : Mem, ∑ i : Mem,
      ‖pathState (fun t => (A.step t).kraus (o t) (r t)) (oracle ω y) (fun k => L k j) i‖ ^ 2 := by
  change (density (fun t => (A.step t).kraus (o t)) (oracle ω y) A.start).trace.re = _
  rw [hL, density_eq_sum, trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun r _ => MatrixMass.trace_mmstar_re _

open Classical in
/-- Average the path expansion over inputs and sum over correct commit sequences. -/
theorem successProb_eq_sum {X Y : Type} [Fintype X] (A : SpaceBoundedAlg n d W K V ι T)
    (enc : X ≃ ZMod d) (ω : ℂ) (q : V → Y) (f : (Fin n → X) → K → Y)
    (L : Matrix Mem Mem ℂ) (hL : A.start = L * Lᴴ) :
    A.successProb enc ω q f = ((Fintype.card X : ℝ) ^ n)⁻¹ *
      ∑ x : Fin n → X, ∑ o : Fin (T + 1) → Option (K × V),
        if CommitsCorrect q (f x) o then
          ∑ r : Fin (T + 1) → ι, ∑ j : Mem, ∑ i : Mem,
            ‖pathState (fun t => (A.step t).kraus (o t) (r t))
              (oracle ω (fun k => enc (x k))) (fun k => L k j) i‖ ^ 2
        else 0 := by
  simp only [SpaceBoundedAlg.successProb, commitProb_eq_sum A ω _ _ L hL]

end QNoiseStab.Supplement.BranchExecution
end

-- Paper.TimeSpace.SiteRuns
section
/-! Simulation of the site oracle and instruments with a chronological output tape. -/

noncomputable section

namespace QNoiseStab.Supplement.SiteExecution

open QuantumNoiseStability QuantumNoiseStability.TimeSpace Matrix
open scoped Classical

variable {K V Y X W κ : Type} {n d T : ℕ}

/-- Each commit emits its coordinate and decoded value. -/
def record (q : V → Y) (o : Option (K × V)) : List (K × Y) :=
  (o.map (fun p => (p.1, q p.2))).toList

/-- The records in instrument order, including repeated commits. -/
def transcript {k : ℕ} (q : V → Y) (o : Fin k → Option (K × V)) : List (K × Y) :=
  (List.ofFn o).flatMap (record q)

private theorem mem_record (q : V → Y) (j : K) (b : Y) (o : Option (K × V)) :
    (j, b) ∈ record q o ↔ ∃ v, o = some (j, v) ∧ b = q v := by
  cases o with
  | none => simp [record]
  | some p =>
    rcases p with ⟨k, v⟩
    simp [record, eq_comm (a := k), @eq_comm V v]

private theorem mem_transcript {k : ℕ} (q : V → Y) (o : Fin k → Option (K × V))
    (j : K) (b : Y) :
    (j, b) ∈ transcript q o ↔ ∃ t v, o t = some (j, v) ∧ b = q v := by
  simp [transcript, List.mem_flatMap, List.mem_ofFn, mem_record]

theorem fullSuccess_transcript (q : V → Y) (z : K → Y) (o : Fin (T + 1) → Option (K × V)) :
    TimeSpace.FullSuccess z (transcript q o) ↔ CommitsCorrect q z o := by
  constructor
  · rintro ⟨cover, agree⟩
    refine ⟨fun t j v h => (agree (j, q v) ((mem_transcript ..).2 ⟨t, v, h, rfl⟩)).symm, ?_⟩
    intro j
    obtain ⟨b, h⟩ := cover j
    obtain ⟨t, v, h, _⟩ := (mem_transcript ..).1 h
    exact ⟨t, v, h⟩
  · rintro ⟨agree, cover⟩
    constructor
    · intro j
      obtain ⟨t, v, h⟩ := cover j
      exact ⟨q v, (mem_transcript ..).2 ⟨t, v, h, rfl⟩⟩
    · rintro ⟨j, b⟩ h
      obtain ⟨t, v, ho, hb⟩ := (mem_transcript ..).1 h
      exact (agree t j v ho).symm.trans hb.symm

local notation "Mem" => (Fin n × ZMod d) × W
local notation "Branch" => Option (K × V) × κ
local notation "Inst" => KAQROM.Instrument (Option (K × V)) Mem Mem κ

variable [NeZero d] (enc : X ≃ ZMod d) (ω : ℂ) (hω : ω ^ d = 1)

/-- The phase uses the encoded symbol at the address in the query register. -/
def siteQuery : PhaseQuery Mem (Fin n) X where
  address w := w.1.1
  phase w a := ω ^ (w.1.2 * enc a).val
  norm_phase w a := by
    have hroot : ‖ω‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg ω) (NeZero.ne d)).mp
        (by simpa only [norm_pow, norm_one] using congrArg norm hω)
    simp [norm_pow, hroot]

variable [Fintype W] [DecidableEq W]

theorem siteQuery_apply (x : Fin n → X) (v : TimeSpace.State Mem) :
    (siteQuery enc ω hω).operator x v =
      WithLp.toLp 2 ((BranchExecution.oracle ω (enc ∘ x)) *ᵥ v.ofLp) := by
  ext w
  unfold BranchExecution.oracle phaseQuery Matrix.kronecker
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  simp [Matrix.mulVec_diagonal, siteQuery]

variable [Fintype K] [Fintype V] [Fintype κ] (q : V → Y)

private def measure (I : Inst) : TimeSpace.Instrument Mem (K × Y) where
  outcomes := Fintype.card Branch
  kraus j := let b := (Fintype.equivFin Branch).symm j
             (I.kraus b.1 b.2).toEuclideanLin
  emit j := record q ((Fintype.equivFin Branch).symm j).1
  subnormalized v := by
    let A (b : Branch) := I.kraus b.1 b.2
    have hc : ∑ b, (A b)ᴴ * A b = 1 := by
      rw [Fintype.sum_prod_type]
      exact I.complete
    change (∑ j, ‖(A ((Fintype.equivFin Branch).symm j)).toEuclideanLin v‖ ^ 2) ≤ ‖v‖ ^ 2
    rw [Equiv.sum_comp (Fintype.equivFin Branch).symm (fun b => ‖(A b).toEuclideanLin v‖ ^ 2)]
    simp_rw [EuclideanSpace.norm_sq_eq]
    exact (MatrixMass.kraus_mass A hc v.ofLp).le

/-- The initial instrument is followed by one query and one instrument at every later time. -/
def compiledSteps : {T : ℕ} → (I : Fin (T + 1) → Inst) → List (TimeSpace.Step Mem (Fin n) X (K × Y))
  | 0, I => [.op (measure q (I 0))]
  | T + 1, I => compiledSteps (fun i => I i.castSucc) ++
      [.query (siteQuery enc ω hω), .op (measure q (I (Fin.last (T + 1))))]

theorem queries_compiledSteps (I : Fin (T + 1) → Inst) :
    queries (compiledSteps enc ω hω q I) = T := by
  induction T with
  | zero => rfl
  | succ T ih => simp [compiledSteps, queries_append, ih]

private theorem sum_measure (I : Inst) (x : Fin n → X) (v : TimeSpace.State Mem)
    (g : List (K × Y) → TimeSpace.State Mem → ℝ) :
    (∑ h, g (claims [.op (measure q I)] h) (run [.op (measure q I)] x v h)) =
      ∑ b : Branch, g (record q b.1) (WithLp.toLp 2 ((I.kraus b.1 b.2) *ᵥ v.ofLp)) := by
  let f (b : Branch) := g (record q b.1) (WithLp.toLp 2 ((I.kraus b.1 b.2) *ᵥ v.ofLp))
  change (∑ h : Fin (Fintype.card Branch) × Unit,
    g (record q ((Fintype.equivFin Branch).symm h.1).1 ++ claims [] h.2) _) = ∑ b, f b
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, claims, List.append_nil]
  exact Equiv.sum_comp (Fintype.equivFin Branch).symm f

private theorem sum_last (a : List (TimeSpace.Step Mem (Fin n) X (K × Y))) (I : Inst)
    (x : Fin n → X) (v : TimeSpace.State Mem) (g : List (K × Y) → TimeSpace.State Mem → ℝ) :
    let tail := [.query (siteQuery enc ω hω), .op (measure q I)]
    (∑ h, g (claims (a ++ tail) h) (run (a ++ tail) x v h)) =
      ∑ b : Branch, ∑ h, g (claims a h ++ record q b.1)
        (WithLp.toLp 2 ((I.kraus b.1 b.2) *ᵥ
          (BranchExecution.oracle ω (enc ∘ x) *ᵥ (run a x v h).ofLp))) := by
  dsimp only
  rw [sum_hist_append]
  simp only [claims_append, run_append, Equiv.apply_symm_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  change (∑ k, g (claims a h ++ claims [.op (measure q I)] k)
    (run [.op (measure q I)] x ((siteQuery enc ω hω).operator x (run a x v h)) k)) = _
  rw [siteQuery_apply]
  exact sum_measure q I x _ (fun l w => g (claims a h ++ l) w)

/-- Sum a function of the chronological transcript and final state over instrument branches. -/
theorem sum_compiledSteps (I : Fin (T + 1) → Inst) (x : Fin n → X) (v : TimeSpace.State Mem)
    (g : List (K × Y) → TimeSpace.State Mem → ℝ) :
    (∑ h, g (claims (compiledSteps enc ω hω q I) h) (run (compiledSteps enc ω hω q I) x v h)) =
      ∑ p : Fin (T + 1) → Branch, g (transcript q (fun t => (p t).1))
        (WithLp.toLp 2 (BranchExecution.pathState (fun t => (I t).kraus (p t).1 (p t).2)
          (BranchExecution.oracle ω (enc ∘ x)) v.ofLp)) := by
  induction T generalizing g with
  | zero =>
    rw [compiledSteps, sum_measure]
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) Branch).symm
    intro b
    simp [transcript, Equiv.funUnique, Equiv.piUnique]
  | succ T ih =>
    rw [compiledSteps, sum_last]
    have hpre (b : Branch) := ih (fun i => I i.castSucc)
      (fun l w => g (l ++ record q b.1)
        (WithLp.toLp 2 ((I (Fin.last (T + 1))).kraus b.1 b.2 *ᵥ
          (BranchExecution.oracle ω (enc ∘ x) *ᵥ w.ofLp))))
    simp_rw [hpre]
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T + 2) => Branch))
    rintro ⟨b, p⟩
    rw [BranchExecution.pathState_succ]
    simp only [Fin.snocEquiv_apply, Fin.snoc_last, Fin.snoc_castSucc]
    congr 1
    simp only [transcript, List.ofFn_succ' (n := T + 1), Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

end QNoiseStab.Supplement.SiteExecution
end
end

-- Solutions.SpaceAccounting
section
/-! Physical memory and the address register in the public instrument model. -/

namespace QNoiseStab.Supplement

/-- The trace-one start state requires at least one physical memory basis state. -/
theorem SpaceBoundedAlg.memory_nonempty {n d T : ℕ} [NeZero d] {W K V κ : Type}
    [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
    (A : SpaceBoundedAlg n d W K V κ T) : Nonempty ((Fin n × ZMod d) × W) := by
  by_contra h
  have : IsEmpty ((Fin n × ZMod d) × W) := ⟨fun w => h ⟨w⟩⟩
  simpa [Matrix.trace] using A.start_trace

/-- The address register must fit along with the phase register and the workspace. -/
theorem SpaceBoundedAlg.address_fits {n d T S : ℕ} [NeZero d] {W K V κ : Type}
    [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
    (A : SpaceBoundedAlg n d W K V κ T) (hA : A.FitsInSpace S) : n ≤ 2^S := by
  obtain ⟨⟨⟨_, _⟩, w⟩⟩ := A.memory_nonempty
  have : Nonempty W := ⟨w⟩
  have h₁ : n ≤ n*d := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne d))
  exact (h₁.trans (Nat.le_mul_of_pos_right _ Fintype.card_pos)).trans hA

theorem SpaceBoundedAlg.card_memory_le {n d T S : ℕ} [NeZero d] {W K V κ : Type}
    [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
    (A : SpaceBoundedAlg n d W K V κ T) (hA : A.FitsInSpace S) :
    Fintype.card ((Fin n × ZMod d) × W) ≤ 2^S := by
  simpa only [SpaceBoundedAlg.FitsInSpace, Fintype.card_prod, Fintype.card_fin, ZMod.card] using hA

end QNoiseStab.Supplement
end

-- Paper.TimeSpace.SiteExecution
section
/-! # Exact simulation of the published mixed-state query model on its original registers -/

noncomputable section

namespace QNoiseStab.Supplement.SiteExecution

open QuantumNoiseStability.TimeSpace
open BranchExecution
open scoped Classical

variable {n d T : ℕ} [NeZero d] {W K V κ X Y : Type}
  [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
local notation "Mem" => (Fin n × ZMod d) × W
local notation "Outcome" => Option (K × V)

variable (A : SpaceBoundedAlg n d W K V κ T) (enc : X ≃ ZMod d) (ω : ℂ) (hω : ω ^ d = 1)
  (q : V → Y)

/-- A silent first instrument prepares the public input-independent density matrix. -/
def programSteps : List (Step Mem (Fin n) X (K × Y)) :=
  let L : Matrix Mem Mem ℂ := (exists_start_factor A).choose
  .op (prepare L (Classical.choice A.memory_nonempty) (exists_start_factor A).choose_spec.2) ::
    compiledSteps enc ω hω q A.step

/-- The silent preparation starts from a fixed, normalized memory basis vector. -/
def initialVector : State Mem := EuclideanSpace.single (Classical.choice A.memory_nonempty) 1

theorem queries_programSteps : queries (programSteps A enc ω hω q) = T :=
  queries_compiledSteps enc ω hω q A.step

private theorem sum_pair_paths {O κ : Type} [Fintype O] [Fintype κ] {k : ℕ}
    (weight : (Fin k → O) → (Fin k → κ) → ℝ) :
    (∑ p : Fin k → O × κ, weight (fun t => (p t).1) (fun t => (p t).2)) =
      ∑ o, ∑ r, weight o r := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => O) (fun _ => κ))
    _ _ (fun _ => rfl)

/-- The two computations assign the same probability to a complete correct record on every input. -/
theorem eventMass_programSteps (x : Fin n → X) (z : K → Y) :
    eventMass (programSteps A enc ω hω q) x (initialVector A) (FullSuccess z) =
      ∑ o, if CommitsCorrect q z o then A.commitProb ω (enc ∘ x) o else 0 := by
  let L : Matrix Mem Mem ℂ := (exists_start_factor A).choose
  let w := Classical.choice A.memory_nonempty
  let l := compiledSteps enc ω hω q A.step
  let score := fun (c : List (K × Y)) (v : State Mem) => if FullSuccess z c then ‖v‖^2 else 0
  change (∑ h, score (claims (Step.op (prepare L w _) :: l) h)
    (run _ x (EuclideanSpace.single w 1) h)) = _
  rw [sum_prepare L w (exists_start_factor A).choose_spec.2 l x score]
  dsimp only [l]
  simp_rw [sum_compiledSteps enc ω hω q A.step x _ score]
  rw [Finset.sum_comm]
  let weight (o : Fin (T+1) → Outcome) (r : Fin (T+1) → κ) :=
    ∑ j, score (transcript q o) (WithLp.toLp 2
      (pathState (fun t => (A.step t).kraus (o t) (r t)) (oracle ω (enc ∘ x)) (fun i => L i j)))
  change (∑ p : Fin (T+1) → Outcome × κ, weight (fun t => (p t).1) (fun t => (p t).2)) = _
  rw [sum_pair_paths]
  apply Finset.sum_congr rfl
  intro o _
  by_cases hc : CommitsCorrect q z o <;>
    simp [weight, score, fullSuccess_transcript, hc, EuclideanSpace.norm_sq_eq,
      commitProb_eq_sum A ω _ o L (exists_start_factor A).choose_spec.1]

/-- Uniform success is preserved for every target, including targets with repeated values. -/
theorem success_programSteps [Fintype X] (f : (Fin n → X) → K → Y) :
    A.successProb enc ω q f = success (programSteps A enc ω hω q) (initialVector A)
      (fun x => FullSuccess (f x)) := by
  simp [SpaceBoundedAlg.successProb, success, eventMass_programSteps, Function.comp_def]

include hω in
/-- Every published algorithm gives a program with the same workspace and query count. -/
theorem exists_program [Fintype X] (f : (Fin n → X) → K → Y) :
    ∃ l : List (Step Mem (Fin n) X (K × Y)), ∃ v : State Mem,
      ‖v‖ ^ 2 ≤ 1 ∧ queries l = T ∧
        A.successProb enc ω q f ≤ success l v (fun x => FullSuccess (f x)) :=
  ⟨programSteps A enc ω hω q, initialVector A, by simp [initialVector], queries_programSteps A enc ω hω q,
    (success_programSteps A enc ω hω q f).le⟩

end QNoiseStab.Supplement.SiteExecution
end
end

-- Solutions.Theorem66
section
set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- **Theorem 6.6** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §6, p.42): "There is a constant C > 0 such that the following holds:
Let M be an n × n matrix over a field F that is (g, h, c)-rigid with n sufficiently large. Then any
quantum algorithm using time T and space S < min(cg/17, ch/544) that computes the function
f_M : D^n → F^n for D ⊆ F with |D| ≥ 2 given by f_M(x) = Mx with success probability larger than
2^{−S} requires that T ≥ C · cnh/S."

There are an absolute constant `C > 0` and a threshold `n₀` such that for every `n ≥ n₀`, every
field `F`, every `(g, h, c)`-rigid `n × n` matrix `M` over `F` with `0 < c ≤ 1`, every finite `D ⊆ F`
with `|D| ≥ 2` and every `S < min(cg/17, ch/544)`, every `T`-query algorithm using at most `S`
qubits that computes `x ↦ Mx` on `D^n` (all `n` output coordinates committed, all commits
correct) with success probability larger than `2^{−S}` on a uniform input has `T ≥ C·c·n·h/S`.

**Formalization Note** "Time T" is the number of queries, as in the proof (p.42). `0 < c ≤ 1` is
added (the paper's implicit range for the rank fraction `c`; `(g, h, 1)`-rigid is its top case):
with `c < 0` and `g, h` very negative, or with `c` large, `g < 1` and `h` large, every matrix (the
zero matrix included) is `(g, h, c)`-rigid vacuously and the printed bound fails for `f_0 = 0`. `D` is encoded into `ZMod |D|` by any bijection
`enc`, the root `ω` is any `ω` with `ω^{|D|} = 1`, and `[NeZero D.card]` (implied by `|D| ≥ 2`) is
needed for the phase register. -/
private theorem submission_proof :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (F : Type) [Field F] (M : Matrix (Fin n) (Fin n) F) (g h c : ℝ), 0 < c → c ≤ 1 →
        IsRigid M g h c →
      ∀ (D : Finset F) [NeZero D.card], 2 ≤ D.card →
      ∀ S : ℕ, (S : ℝ) < min (c * g / 17) (c * h / 544) →
      ∀ (W V κ : Type) [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ] (T : ℕ)
        (A : SpaceBoundedAlg n D.card W (Fin n) V κ T) (q : V → F) (enc : D ≃ ZMod D.card)
        (ω : ℂ), ω ^ D.card = 1 → A.FitsInSpace S →
        ((2 : ℝ) ^ S)⁻¹ < A.successProb enc ω q (fun x => M.mulVec fun j => (x j : F)) →
        C * c * n * h / S ≤ T := by
  refine ⟨1/4096, by norm_num, 193, ?_⟩
  intro n hn F _ M g h c hc hc1 hr D _ hd S hbudget W V κ _ _ _ _ T A q enc ω hω hfit hsucc
  have hreg := A.address_fits hfit
  have hS : 0 < S := by
    by_contra! h
    simp [show S = 0 by omega] at hreg
    omega
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  obtain ⟨hgpos, hhpos⟩ := lt_min_iff.mp hbudget
  have hg : 0 ≤ g := by
    by_contra! h
    linarith [mul_neg_of_pos_of_neg hc h]
  have hh : 0 ≤ h := by
    by_contra! h'
    linarith [mul_neg_of_pos_of_neg hc h']
  obtain ⟨hkg, hkh, hfloor⟩ := rigid_slice_sizes hS hc hc1 hbudget
  obtain ⟨l, v, hv, hT, hsim⟩ :=
    SiteExecution.exists_program A enc ω hω q (fun x => M.mulVec fun j => (x j : F))
  have hp : (2:ℝ)^(-(S:ℝ)) ≤
      QuantumNoiseStability.TimeSpace.success l v
        (fun x => QuantumNoiseStability.TimeSpace.FullSuccess
          (QuantumNoiseStability.MatrixVector.matrixOutput M Subtype.val x)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
    exact hsucc.le.trans hsim
  have hbound := QuantumNoiseStability.MatrixVector.theorem_6_6
    (rigid_floor hg hh hr) D hd hn hreg (A.card_memory_le hfit) hc hkg hkh l v hv hp
  rw [hT] at hbound
  have hden : (0:ℝ) < 2048*S := by positivity
  have hmain := (div_le_iff₀ hden).mp hbound
  apply (div_le_iff₀ hS').mpr
  have hscale := mul_le_mul_of_nonneg_left hfloor
    (mul_nonneg hc.le (Nat.cast_nonneg n : (0:ℝ) ≤ n))
  linarith

end QNoiseStab.Supplement
end

section
set_option autoImplicit false
open QNoiseStab QNoiseStab.Supplement

set_option linter.unusedVariables false in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (F : Type) [Field F] (M : Matrix (Fin n) (Fin n) F) (g h c : ℝ), 0 < c → c ≤ 1 →
        IsRigid M g h c →
      ∀ (D : Finset F) [NeZero D.card], 2 ≤ D.card →
      ∀ S : ℕ, (S : ℝ) < min (c * g / 17) (c * h / 544) →
      ∀ (W V κ : Type) [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ] (T : ℕ)
        (A : SpaceBoundedAlg n D.card W (Fin n) V κ T) (q : V → F) (enc : D ≃ ZMod D.card)
        (ω : ℂ), ω ^ D.card = 1 → A.FitsInSpace S →
        ((2 : ℝ) ^ S)⁻¹ < A.successProb enc ω q (fun x => M.mulVec fun j => (x j : F)) →
        C * c * n * h / S ≤ T :=
  @QNoiseStab.Supplement.submission_proof

end
