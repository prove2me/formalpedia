-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P34.coefficientSpace_intersection_integerBasis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:20:35.211117+00:00
-- url     : https://prove2.me/submissions/3dce8d42-423b-4376-892e-0689172d2674

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P34
noncomputable section
open scoped BigOperators

open QAlgorithms.Papers.Independent.Next46.P34

namespace G62R

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} (α : Fin n → K)

def P (t : ℕ) (c : Fin (t + 1) → ℚ) (k : Fin n) : K := ∑ i : Fin (t + 1), c i • α k ^ (i : ℕ)

def φ (t : ℕ) (c : Fin (t + 1) → ℚ) : (Fin n → ℚ) →ₗ[ℚ] K :=
  ∑ k, (LinearMap.proj k : (Fin n → ℚ) →ₗ[ℚ] ℚ).smulRight (P α t c k)

theorem φ_apply (t : ℕ) (c : Fin (t + 1) → ℚ) (e : Fin n → ℚ) :
    φ α t c e = ∑ k, e k • P α t c k := by
  simp [φ]

theorem mem_M (t : ℕ) (c : Fin (t + 1) → ℚ) (e : Fin n → ℚ) :
    c ∈ momentRelationSpace α t e ↔ φ α t c e = 0 := by
  rw [momentRelationSpace, LinearMap.mem_ker, φ_apply]
  have : momentFunctional α t e c = ∑ k, e k • P α t c k := by
    simp only [momentFunctional, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply, rootPowerMoment, P, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
    exact smul_comm _ _ _
  rw [this]

theorem rf_apply (e : Fin n → ℚ) : rootFunctional α e = ∑ k, e k • α k := by
  simp [rootFunctional]

theorem irf_apply (z : Fin n → ℤ) : integerRootFunctional α z = ∑ k, z k • α k := by
  simp [integerRootFunctional]

theorem cast_rel (z : Fin n → ℤ) (hz : z ∈ integerRelations α) :
    (fun k => (z k : ℚ)) ∈ rationalRelations α := by
  rw [rationalRelations, LinearMap.mem_ker, rf_apply]
  rw [integerRelations, LinearMap.mem_ker, irf_apply] at hz
  rw [← hz]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact Int.cast_smul_eq_zsmul ℚ (z k) (α k)

theorem denom (e : Fin n → ℚ) : ∃ D : ℕ, 0 < D ∧ ∃ m : Fin n → ℤ, ∀ k, (m k : ℚ) = D * e k := by
  classical
  refine ⟨∏ k, (e k).den, Finset.prod_pos (fun k _ => (e k).den_pos), ?_⟩
  have h : ∀ k, ∃ z : ℤ, (z : ℚ) = (∏ l, (e l).den : ℕ) * e k := by
    intro k
    refine ⟨(∏ l ∈ Finset.univ.erase k, ((e l).den : ℤ)) * (e k).num, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    push_cast
    rw [mul_assoc, mul_comm ((e k).den : ℚ), Rat.mul_den_eq_num]
  choose m hm using h
  exact ⟨m, hm⟩

theorem main {r : ℕ} (t : ℕ) (b : Module.Basis (Fin r) ℤ (integerRelations α)) :
    coefficientSpace α t =
      ⨅ j : Fin r, momentRelationSpace α t (fun k => (((b j : Fin n → ℤ) k) : ℚ)) := by
  ext c
  simp only [coefficientSpace, Submodule.mem_iInf, mem_M, Subtype.forall]
  constructor
  · intro h j
    exact h _ (cast_rel α _ (b j).2)
  · intro h e he
    obtain ⟨D, hD, m, hm⟩ := denom e
    have hmrel : m ∈ integerRelations α := by
      rw [integerRelations, LinearMap.mem_ker, irf_apply]
      rw [rationalRelations, LinearMap.mem_ker, rf_apply] at he
      have : ∑ k, m k • α k = (D : ℚ) • ∑ k, e k • α k := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Int.cast_smul_eq_zsmul ℚ, hm, mul_smul]
      rw [this, he, smul_zero]
    have hsum := b.sum_repr ⟨m, hmrel⟩
    have hm' : m = ∑ j, (b.repr ⟨m, hmrel⟩ j) • (b j : Fin n → ℤ) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hcast : (fun k => (m k : ℚ)) = ∑ j, ((b.repr ⟨m, hmrel⟩ j : ℤ) : ℚ) • (fun k => ((b j : Fin n → ℤ) k : ℚ)) := by
      funext k
      conv_lhs => rw [hm']
      simp [Finset.sum_apply]
    have h1 : φ α t c (fun k => (m k : ℚ)) = 0 := by
      rw [hcast, map_sum]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [map_smul, h j, smul_zero]
    have h2 : (fun k => (m k : ℚ)) = (D : ℚ) • e := by
      funext k; rw [hm k]; simp
    rw [h2, map_smul] at h1
    exact (smul_eq_zero.1 h1).resolve_left (by exact_mod_cast hD.ne')

end G62R

theorem solution
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {n : ℕ} (hn : 0 < n) (X : Matrix (Fin n) (Fin n) ℚ)
    (hsemisimple : Module.End.IsSemisimple (Matrix.toLin' X))
    (hsquarefree : Squarefree X.charpoly)
    (alpha : Fin n → K)
    (hroots : X.charpoly.map (algebraMap ℚ K) =
      ∏ k, (Polynomial.X - Polynomial.C (alpha k)))
    (t : ℕ) (hdegree : (minpoly ℚ X).natDegree = t + 1)
    {r : ℕ} (b : Module.Basis (Fin r) ℤ (integerRelations alpha)) :
    coefficientSpace alpha t =
      ⨅ j : Fin r, momentRelationSpace alpha t
        (fun k => (((b j : Fin n → ℤ) k) : ℚ)) := by
  exact G62R.main alpha t b
