-- Prove2me | solution 1 for Transcendence.singular_matrix_subspace_annihilating_pair
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:46:01.027003+00:00
-- url     : https://prove2.me/submissions/d72dec22-74f6-431e-834b-d9f07ac89a0c

import Mathlib

open Matrix

namespace RoyLemma

variable {F : Type*} [Field F]

/-- `det (1 + X • K)`, evaluated at `a`, is `det (1 + a • K)`. -/
theorem eval_det_one_add_X_smul {m : ℕ} (K : Matrix (Fin m) (Fin m) F) (a : F) :
    ((1 + (Polynomial.X : Polynomial F) • K.map Polynomial.C).det).eval a = (1 + a • K).det := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, mul_comm a]

/-- Over an infinite field, `det (1 + a • K) ≠ 0` for some non-zero `a`: the polynomial
`det (1 + X • K)` takes the value `1` at `0`, so it has finitely many roots. -/
theorem exists_ne_zero_det_one_add_smul_ne_zero [Infinite F] {m : ℕ}
    (K : Matrix (Fin m) (Fin m) F) : ∃ a : F, a ≠ 0 ∧ (1 + a • K).det ≠ 0 := by
  classical
  set p : Polynomial F := (1 + (Polynomial.X : Polynomial F) • K.map Polynomial.C).det with hp_def
  have hp : p ≠ 0 := by
    intro h
    have h0 := eval_det_one_add_X_smul K 0
    rw [← hp_def, h, Polynomial.eval_zero, zero_smul, add_zero, det_one] at h0
    exact zero_ne_one h0
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (insert 0 p.roots.toFinset)
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset, Polynomial.mem_roots hp,
    Polynomial.IsRoot.def] at ha
  exact ⟨a, ha.1, by rw [← eval_det_one_add_X_smul]; exact ha.2⟩

/-- Perturbing an independent family: over an infinite field, `f + a • g` is still linearly
independent for some non-zero `a`. With `P` a left inverse of `c ↦ ∑ cᵢ fᵢ`, the map
`c ↦ P (∑ cᵢ (fᵢ + a gᵢ))` has matrix `1 + a • K`. -/
theorem exists_ne_zero_linearIndependent_add_smul [Infinite F] {V : Type*} [AddCommGroup V]
    [Module F V] {m : ℕ} (f g : Fin m → V) (hf : LinearIndependent F f) :
    ∃ a : F, a ≠ 0 ∧ LinearIndependent F (fun i => f i + a • g i) := by
  classical
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F f)
    (LinearMap.ker_eq_bot.2 hf.fintypeLinearCombination_injective)
  set K := LinearMap.toMatrix' (P ∘ₗ Fintype.linearCombination F g)
  obtain ⟨a, ha, hdet⟩ := exists_ne_zero_det_one_add_smul_ne_zero K
  refine ⟨a, ha, Fintype.linearIndependent_iff.2 fun c hc => ?_⟩
  have hc' : (1 + a • K) *ᵥ c = 0 := by
    have h1 : Fintype.linearCombination F f c + a • Fintype.linearCombination F g c = 0 := by
      rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, Finset.smul_sum,
        ← Finset.sum_add_distrib, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_add, smul_comm]
    have h2 := congrArg P h1
    rw [map_add, map_smul, ← LinearMap.comp_apply P, hP, LinearMap.id_apply, map_zero] at h2
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      LinearMap.toMatrix'_mulVec]
    exact h2
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hc')

/-- **Key claim** (Roy). If `A₀ ∈ E` has maximal rank, `B ∈ E` and `A₀ v = 0`, then
`B v ∈ range A₀`. Otherwise `B v, A₀ x₁, …, A₀ x_r` are independent, and so are
`B v, (A₀ + a B) x₁, …, (A₀ + a B) x_r` for some `a ≠ 0`; these lie in the range of `A₀ + a B`
(as `B v = (A₀ + a B) (a⁻¹ v)`), which then has rank `> r`. -/
theorem mulVec_mem_range [Infinite F] {n : ℕ} (E : Submodule F (Matrix (Fin n) (Fin n) F))
    {A₀ : Matrix (Fin n) (Fin n) F} (hA₀ : A₀ ∈ E) (hmax : ∀ A ∈ E, A.rank ≤ A₀.rank)
    {B : Matrix (Fin n) (Fin n) F} (hB : B ∈ E) {v : Fin n → F} (hv : A₀ *ᵥ v = 0) :
    B *ᵥ v ∈ LinearMap.range A₀.mulVecLin := by
  by_contra hu
  set W := LinearMap.range A₀.mulVecLin
  -- a basis `A₀ x₁, …, A₀ x_r` of the range of `A₀`
  let b := Module.finBasisOfFinrankEq F W (rfl : Module.finrank F W = A₀.rank)
  choose x hx using fun j => LinearMap.mem_range.1 (b j).2
  -- the vectors `B v, A₀ x₁, …, A₀ x_r` are independent, since `B v ∉ range A₀`
  let f : Fin (A₀.rank + 1) → Fin n → F := Fin.cons (B *ᵥ v) fun j => (b j : Fin n → F)
  let g : Fin (A₀.rank + 1) → Fin n → F := Fin.cons 0 fun j => B *ᵥ x j
  have hf : LinearIndependent F f := by
    refine linearIndependent_finCons.2 ⟨b.linearIndependent.map' W.subtype W.ker_subtype, ?_⟩
    intro hmem
    refine hu (Submodule.span_le.2 ?_ hmem)
    rintro _ ⟨j, rfl⟩
    exact (b j).2
  obtain ⟨a, ha, hli⟩ := exists_ne_zero_linearIndependent_add_smul f g hf
  -- `B v, (A₀ + a B) x₁, …, (A₀ + a B) x_r` lie in the range of `A₀ + a B`
  have hspan : Submodule.span F (Set.range fun i => f i + a • g i) ≤
      LinearMap.range (A₀ + a • B).mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    induction i using Fin.cases with
    | zero =>
      refine ⟨a⁻¹ • v, ?_⟩
      simp [f, g, hv, ha]
    | succ j =>
      refine ⟨x j, ?_⟩
      simp [f, g, hx j]
  have hle := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_fin] at hle
  exact absurd (hle.trans (hmax _ (E.add_mem hA₀ (E.smul_mem a hB)))) (Nat.not_succ_le_self _)

end RoyLemma

open RoyLemma in
/-- **Roy's lemma** (Dasgupta–Kakde II, Thm 2.2; Waldschmidt, Prop. 12.5). Take `A₀ ∈ E` of
maximal rank, `v ≠ 0` in its kernel and `w ≠ 0` in its left kernel. For `B ∈ E`, `B v` lies in
the range of `A₀`, which `w` annihilates. -/
theorem solution {F : Type*} [Field F] [Infinite F] {n : ℕ}
    (E : Submodule F (Matrix (Fin n) (Fin n) F)) (hE : ∀ A ∈ E, A.det = 0) :
    ∃ v w : Fin n → F, v ≠ 0 ∧ w ≠ 0 ∧ ∀ A ∈ E, w ⬝ᵥ (A *ᵥ v) = 0 := by
  -- a matrix `A₀ ∈ E` of maximal rank
  obtain ⟨A₀, hA₀, hmax⟩ : ∃ A₀ ∈ E, ∀ A ∈ E, A.rank ≤ A₀.rank := by
    have hne : {k | ∃ A ∈ E, A.rank = k}.Nonempty := ⟨_, 0, E.zero_mem, rfl⟩
    have hbdd : BddAbove {k | ∃ A ∈ E, A.rank = k} :=
      ⟨n, by rintro _ ⟨A, -, rfl⟩; exact A.rank_le_width⟩
    obtain ⟨A₀, hA₀, hr⟩ := Nat.sSup_mem hne hbdd
    exact ⟨A₀, hA₀, fun A hA => hr ▸ le_csSup hbdd ⟨A, hA, rfl⟩⟩
  -- `A₀` is singular: a kernel vector `v` and a left kernel vector `w`
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (hE A₀ hA₀)
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.2 (hE A₀ hA₀)
  refine ⟨v, w, hv0, hw0, fun B hB => ?_⟩
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 (mulVec_mem_range E hA₀ hmax hB hv)
  rw [← hx, Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, hw, zero_dotProduct]
