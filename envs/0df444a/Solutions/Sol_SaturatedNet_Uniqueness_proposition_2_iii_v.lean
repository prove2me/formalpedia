-- Prove2me | solution 1 for SaturatedNet.Uniqueness.proposition_2_iii_v
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T10:15:04.135816+00:00
-- url     : https://prove2.me/submissions/5cd13929-b113-4edd-858c-48e07f75c8f8

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_2_i_ii
open Matrix

-- Complete inline local helper: Hypotheses.lean

open Matrix

namespace SaturatedNet.Uniqueness.IrreducibleProof

universe u

/-- The exact universally quantified proposition of existing Proposition 2(i–ii). -/
def GeneralPerron : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j),
    (Nonempty n → ∃ p π : n → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ 0 ≤ π ∧ π ≠ 0 ∧
      P *ᵥ p = (specRad P).toReal • p ∧ π ᵥ* P = (specRad P).toReal • π) ∧
    (∀ S : Finset n, specRad (block P S) ≤ specRad P)

end SaturatedNet.Uniqueness.IrreducibleProof

-- Complete inline local helper: Eigenvectors.lean

open Matrix

namespace SaturatedNet.Uniqueness.IrreducibleProof

lemma pow_mulVec_eigen {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (p : n → ℝ) (r : ℝ) (h : P *ᵥ p = r • p) (l : ℕ) :
    P ^ l *ᵥ p = r ^ l • p := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul]
    congr 1

lemma nonneg_eigenvector_pos {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (r : ℝ) (p : n → ℝ) (hp : 0 ≤ p) (hp0 : p ≠ 0) (he : P *ᵥ p = r • p) :
    ∀ i, 0 < p i := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra! h
    exact hp0 (funext h)
  have hjpos : 0 < p j := lt_of_le_of_ne (hp j) (Ne.symm hj)
  intro i
  by_contra! hi
  have hiz : p i = 0 := le_antisymm hi (hp i)
  obtain ⟨l, _, hl⟩ := hirr i j
  have hsum : 0 < (P ^ l *ᵥ p) i := by
    exact (Finset.sum_pos_iff_of_nonneg
      (fun a _ => mul_nonneg (Matrix.pow_apply_nonneg hP l i a) (hp a))).2
      ⟨j, Finset.mem_univ j, mul_pos hl hjpos⟩
  rw [pow_mulVec_eigen P p r he l] at hsum
  simp [hiz] at hsum

lemma eigenspace_one_dimensional {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (r : ℝ) (p : n → ℝ) (hp : 0 ≤ p) (hp0 : p ≠ 0) (he : P *ᵥ p = r • p)
    (q : n → ℝ) (hq : P *ᵥ q = r • q) : ∃ t : ℝ, q = t • p := by
  classical
  have hpp := nonneg_eigenvector_pos P hP hirr r p hp hp0 he
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra! h
    exact hp0 (funext h)
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun j => q j / p j) ⟨j, Finset.mem_univ j⟩
  let t : ℝ := q i / p i
  have hw : 0 ≤ q - t • p := by
    intro a
    change 0 ≤ q a - t * p a
    exact sub_nonneg.mpr ((le_div_iff₀ (hpp a)).mp (hmin a (Finset.mem_univ a)))
  have hwe : P *ᵥ (q - t • p) = r • (q - t • p) := by
    rw [mulVec_sub, mulVec_smul, hq, he, smul_sub, smul_comm t r]
  have hwz : (q - t • p) i = 0 := by
    change q i - (q i / p i) * p i = 0
    rw [div_mul_cancel₀ _ (ne_of_gt (hpp i)), sub_self]
  have hz : q - t • p = 0 := by
    by_contra hn
    have hi := nonneg_eigenvector_pos P hP hirr r (q-t•p) hw hn hwe i
    rw [hwz] at hi
    exact (lt_irrefl 0) hi
  exact ⟨t, sub_eq_zero.mp hz⟩

lemma positive_unique {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (r : ℝ) (p : n → ℝ) (hp : 0 ≤ p) (hp0 : p ≠ 0) (he : P *ᵥ p = r • p) :
    (∀ i, 0 < p i) ∧ ∀ q : n → ℝ, 0 ≤ q → q ≠ 0 → P *ᵥ q = r • q →
      ∃ t : ℝ, 0 < t ∧ q = t • p := by
  have hpp := nonneg_eigenvector_pos P hP hirr r p hp hp0 he
  refine ⟨hpp, ?_⟩
  intro q hq hq0 hqe
  have hqp := nonneg_eigenvector_pos P hP hirr r q hq hq0 hqe
  obtain ⟨t, ht⟩ := eigenspace_one_dimensional P hP hirr r p hp hp0 he q hqe
  refine ⟨t, ?_, ht⟩
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra! h
    exact hp0 (funext h)
  have h := hqp i
  rw [ht] at h
  change 0 < t * p i at h
  exact (mul_pos_iff_of_pos_right (hpp i)).mp h

lemma irreducible_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hirr : IsIrreducible P) : IsIrreducible Pᵀ := by
  intro i j
  obtain ⟨l, hl, hpow⟩ := hirr j i
  exact ⟨l, hl, by simpa only [← Matrix.transpose_pow, Matrix.transpose_apply] using hpow⟩

end SaturatedNet.Uniqueness.IrreducibleProof

-- Complete inline local helper: Fredholm.lean

open Matrix

namespace SaturatedNet.Uniqueness.IrreducibleProof

/-- The orthogonal compatibility condition gives an affine line of transpose solutions. -/
theorem fredholm_infinite {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (p π : n → ℝ) (hp : p ≠ 0)
    (hker : LinearMap.ker A.mulVecLin = Submodule.span ℝ {p})
    (hπ : π ≠ 0) (hπker : A.transpose *ᵥ π = 0)
    (c : n → ℝ) (hc : p ⬝ᵥ c = 0) :
    {x : n → ℝ | A.transpose *ᵥ x = c}.Infinite := by
  have _ := hp
  have hcann : dotProductEquiv ℝ n c ∈ (LinearMap.ker A.mulVecLin).dualAnnihilator := by
    rw [hker]
    change dotProductEquiv ℝ n c ∈
      ((Submodule.span ℝ {p}).dualAnnihilator : Set (Module.Dual ℝ (n → ℝ)))
    rw [Submodule.coe_dualAnnihilator_span]
    simpa [Set.singleton_subset_iff, LinearMap.mem_ker, dotProduct_comm] using hc
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hcann
  obtain ⟨φ, hφ⟩ := hcann
  obtain ⟨x, rfl⟩ := (dotProductEquiv ℝ n).surjective φ
  have hsol : A.transpose *ᵥ x = c := by
    apply (dotProductEquiv ℝ n).injective
    apply LinearMap.ext
    intro y
    have h := LinearMap.congr_fun hφ y
    simpa [LinearMap.dualMap_apply, dotProduct_mulVec, mulVec_transpose] using h
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℝ => x + t • π) ?_ ?_
  · intro s t hst
    exact (smul_left_injective ℝ hπ) (add_left_cancel hst)
  · intro t
    change A.transpose *ᵥ (x + t • π) = c
    rw [mulVec_add, mulVec_smul, hsol, hπker, smul_zero, add_zero]

end SaturatedNet.Uniqueness.IrreducibleProof

-- Complete inline local helper: Solvability.lean

open Matrix

namespace SaturatedNet.Uniqueness.IrreducibleProof

universe u

lemma eigenspace_kernel {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (r : ℝ) (p : n → ℝ) (hp : 0 ≤ p) (hp0 : p ≠ 0) (he : P *ᵥ p = r • p) :
    LinearMap.ker (r • (1 : Matrix n n ℝ) - P).mulVecLin = Submodule.span ℝ {p} := by
  ext q
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Submodule.mem_span_singleton]
  constructor
  · intro hq
    obtain ⟨t, ht⟩ := eigenspace_one_dimensional P hP hirr r p hp hp0 he q
      (sub_eq_zero.mp hq).symm
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, rfl⟩
    rw [Matrix.mulVec_smul, he, smul_comm r t, sub_self]

lemma solutions_infinite (hPF : GeneralPerron.{u})
    {n : Type u} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (p : n → ℝ) (hp : 0 ≤ p) (hp0 : p ≠ 0)
    (he : P *ᵥ p = (specRad P).toReal • p)
    (c : n → ℝ) (hc : p ⬝ᵥ c = 0) :
    {x : n → ℝ | (specRad P).toReal • x = x ᵥ* P + c}.Infinite := by
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra! h
    exact hp0 (funext h)
  obtain ⟨_, π, _, _, _, hπ0, _, hπe⟩ := (hPF P hP).1 ⟨i⟩
  let A : Matrix n n ℝ := (specRad P).toReal • 1 - P
  have hker : LinearMap.ker A.mulVecLin = Submodule.span ℝ {p} :=
    eigenspace_kernel P hP hirr (specRad P).toReal p hp hp0 he
  have hπker : Aᵀ *ᵥ π = 0 := by
    simp only [A, transpose_sub, transpose_smul, transpose_one, sub_mulVec,
      smul_mulVec, one_mulVec, mulVec_transpose, hπe, sub_self]
  have hinf := fredholm_infinite A p π hp0 hker hπ0 hπker c hc
  convert hinf using 1
  ext x
  simp only [Set.mem_ofPred_eq, A, transpose_sub, transpose_smul, transpose_one,
    sub_mulVec, smul_mulVec, one_mulVec, mulVec_transpose, sub_eq_iff_eq_add, add_comm]

end SaturatedNet.Uniqueness.IrreducibleProof

-- Complete inline local helper: Principal.lean

open Matrix

namespace SaturatedNet.Uniqueness.IrreducibleProof

universe u

lemma eigenvalue_pos {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (r : ℝ) (hr : 0 ≤ r) (p : n → ℝ) (hp : 0 ≤ p) (hp0 : p ≠ 0)
    (he : P *ᵥ p = r • p) : 0 < r := by
  have hpp := nonneg_eigenvector_pos P hP hirr r p hp hp0 he
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra! h
    exact hp0 (funext h)
  by_contra! hn
  have hr0 : r = 0 := le_antisymm hn hr
  obtain ⟨l, hl, hpow⟩ := hirr i i
  have hsum : 0 < (P ^ l *ᵥ p) i := by
    exact (Finset.sum_pos_iff_of_nonneg
      (fun a _ => mul_nonneg (Matrix.pow_apply_nonneg hP l i a) (hp a))).2
      ⟨i, Finset.mem_univ i, mul_pos hpow (hpp i)⟩
  rw [pow_mulVec_eigen P p r he l, hr0, zero_pow (by omega : l ≠ 0), zero_smul] at hsum
  exact (lt_irrefl 0) hsum

lemma principal_strict (hPF : GeneralPerron.{u})
    {n : Type u} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (S : Finset n) (hS : S ≠ Finset.univ) : specRad (block P S) < specRad P := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : n, j ∉ S := by
    by_contra! h
    exact hS (Finset.eq_univ_of_forall h)
  obtain ⟨p, π, hp, hp0, hπ, hπ0, hpe, hπe⟩ := (hPF P hP).1 ⟨j⟩
  have hπpos : ∀ i, 0 < π i := nonneg_eigenvector_pos Pᵀ (fun i j => hP j i)
    (irreducible_transpose P hirr) (specRad P).toReal π hπ hπ0
    (by simpa only [mulVec_transpose] using hπe)
  have hrpos := eigenvalue_pos P hP hirr (specRad P).toReal ENNReal.toReal_nonneg p hp hp0 hpe
  by_cases hSne : S.Nonempty
  · have : Nonempty S := hSne.to_subtype
    have hB : ∀ i j : S, 0 ≤ block P S i j := fun i j => hP i j
    obtain ⟨q, _, hq, hq0, _, _, hqe, _⟩ := (hPF (block P S) hB).1 inferInstance
    apply lt_of_le_of_ne ((hPF P hP).2 S)
    intro heq
    have hr : (specRad (block P S)).toReal = (specRad P).toReal := congrArg ENNReal.toReal heq
    let x : n → ℝ := fun i => if hi : i ∈ S then q ⟨i, hi⟩ else 0
    have hx : 0 ≤ x := by
      intro i
      dsimp [x]
      split_ifs with hi
      · exact hq ⟨i, hi⟩
      · exact le_rfl
    have hx0 : x ≠ 0 := by
      intro hz
      apply hq0
      funext i
      have hi := congrFun hz i
      simpa [x, i.property] using hi
    have hinside (i : S) : (P *ᵥ x) i = (block P S *ᵥ q) i := by
      change (∑ a, P i a * x a) = ∑ a : S, P i a * q a
      calc
        (∑ a, P i a * x a) = ∑ a ∈ S, P i a * x a := by
          symm
          apply Finset.sum_subset (Finset.subset_univ S)
          intro a _ ha
          simp [x, ha]
        _ = ∑ a : S, P i a * x a := Finset.sum_subtype S (fun _ => Iff.rfl) _
        _ = ∑ a : S, P i a * q a := by simp [x]
    have hsub : (specRad P).toReal • x ≤ P *ᵥ x := by
      intro i
      by_cases hi : i ∈ S
      · have h := hinside ⟨i, hi⟩
        rw [hqe, hr] at h
        simpa [x, hi] using h.symm.le
      · change (specRad P).toReal * x i ≤ ∑ a, P i a * x a
        rw [show x i = 0 by simp [x, hi], mul_zero]
        exact Finset.sum_nonneg (fun a _ => mul_nonneg (hP i a) (hx a))
    have hdot : π ⬝ᵥ (P *ᵥ x - (specRad P).toReal • x) = 0 := by
      rw [dotProduct_sub, dotProduct_mulVec, hπe, smul_dotProduct, dotProduct_smul, sub_self]
    have hzero : ∀ i, π i * (P *ᵥ x - (specRad P).toReal • x) i = 0 := by
      exact fun i => (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => mul_nonneg (hπ a) (sub_nonneg.mpr (hsub a)))).1 hdot i (Finset.mem_univ i)
    have hxe : P *ᵥ x = (specRad P).toReal • x := by
      funext i
      exact sub_eq_zero.mp ((mul_eq_zero.mp (hzero i)).resolve_left (ne_of_gt (hπpos i)))
    have hxpos := nonneg_eigenvector_pos P hP hirr (specRad P).toReal x hx hx0 hxe j
    simp [x, hj] at hxpos
  · have : IsEmpty S := ⟨fun i => hSne ⟨i, i.property⟩⟩
    have hzero : specRad (block P S) = 0 := by simp [specRad]
    rw [hzero]
    exact (ENNReal.toReal_pos_iff.mp hrpos).1

end SaturatedNet.Uniqueness.IrreducibleProof

namespace SaturatedNet.Uniqueness.IrreducibleProof

universe u

theorem conditional (hPF : GeneralPerron.{u}) {n : Type u} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P) :
    (∀ p : n → ℝ, 0 ≤ p → p ≠ 0 → P *ᵥ p = (specRad P).toReal • p →
      (∀ i, 0 < p i) ∧
      ∀ q : n → ℝ, 0 ≤ q → q ≠ 0 → P *ᵥ q = (specRad P).toReal • q →
        ∃ t : ℝ, 0 < t ∧ q = t • p) ∧
    (∀ π : n → ℝ, 0 ≤ π → π ≠ 0 → π ᵥ* P = (specRad P).toReal • π →
      (∀ i, 0 < π i) ∧
      ∀ σ : n → ℝ, 0 ≤ σ → σ ≠ 0 → σ ᵥ* P = (specRad P).toReal • σ →
        ∃ t : ℝ, 0 < t ∧ σ = t • π) ∧
    (∀ p : n → ℝ, 0 ≤ p → p ≠ 0 → P *ᵥ p = (specRad P).toReal • p →
      ∀ c : n → ℝ, p ⬝ᵥ c = 0 →
        {x : n → ℝ | (specRad P).toReal • x = x ᵥ* P + c}.Infinite) ∧
    (∀ S : Finset n, S ≠ Finset.univ → specRad (block P S) < specRad P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp hp0 hpe
    exact positive_unique P hP hirr (specRad P).toReal p hp hp0 hpe
  · intro π hπ hπ0 hπe
    have ht := positive_unique Pᵀ (fun i j => hP j i) (irreducible_transpose P hirr)
      (specRad P).toReal π hπ hπ0 (by simpa only [mulVec_transpose] using hπe)
    simpa only [mulVec_transpose] using ht
  · intro p hp hp0 hpe c hc
    exact solutions_infinite hPF P hP hirr p hp hp0 hpe c hc
  · exact principal_strict hPF P hP hirr

end SaturatedNet.Uniqueness.IrreducibleProof

namespace SaturatedNet.Uniqueness

theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P) :
    (∀ p : n → ℝ, 0 ≤ p → p ≠ 0 → P *ᵥ p = (specRad P).toReal • p →
      (∀ i, 0 < p i) ∧
      ∀ q : n → ℝ, 0 ≤ q → q ≠ 0 → P *ᵥ q = (specRad P).toReal • q →
        ∃ t : ℝ, 0 < t ∧ q = t • p) ∧
    (∀ π : n → ℝ, 0 ≤ π → π ≠ 0 → π ᵥ* P = (specRad P).toReal • π →
      (∀ i, 0 < π i) ∧
      ∀ σ : n → ℝ, 0 ≤ σ → σ ≠ 0 → σ ᵥ* P = (specRad P).toReal • σ →
        ∃ t : ℝ, 0 < t ∧ σ = t • π) ∧
    (∀ p : n → ℝ, 0 ≤ p → p ≠ 0 → P *ᵥ p = (specRad P).toReal • p →
      ∀ c : n → ℝ, p ⬝ᵥ c = 0 →
        {x : n → ℝ | (specRad P).toReal • x = x ᵥ* P + c}.Infinite) ∧
    (∀ S : Finset n, S ≠ Finset.univ → specRad (block P S) < specRad P) := by
  exact IrreducibleProof.conditional (@proposition_2_i_ii) P hP hirr

end SaturatedNet.Uniqueness
