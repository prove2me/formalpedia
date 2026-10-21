-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P03.conjugation_basis_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:40:16.337438+00:00
-- url     : https://prove2.me/submissions/b545a454-03a7-441a-b966-c6f482f197f5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03
noncomputable section

open QAlgorithms.Papers.Independent.Renew46.P03

universe u v

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)


open QAlgorithms.Papers.Independent.Renew46.P03

section G64C
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem g64k_formula {ι : Type*} (K : H →L⋆[ℂ] H) (e : HilbertBasis ι ℂ H) (he : ∀ i, K (e i) = e i)
    (x : H) : HasSum (fun i => inner ℂ x (e i) • e i) (K x) := by
  have h := (e.hasSum_repr x).mapL K
  convert h using 1
  funext i
  simp only [Function.comp_apply, map_smulₛₗ, he, HilbertBasis.repr_apply_apply]
  rw [inner_conj_symm]

theorem g64k_coef {ι : Type*} (K : H →L⋆[ℂ] H) (e : HilbertBasis ι ℂ H) (he : ∀ i, K (e i) = e i)
    (x : H) (i : ι) : inner ℂ (e i) (K x) = inner ℂ x (e i) := by
  classical
  have h := (g64k_formula K e he x).mapL (innerSL ℂ (e i))
  have h2 : HasSum (fun j => (innerSL ℂ (e i)) (inner ℂ x (e j) • e j)) (inner ℂ x (e i)) := by
    convert hasSum_ite_eq i (inner ℂ x (e i)) using 1
    funext j
    simp only [innerSL_apply_apply, inner_smul_right]
    by_cases hj : j = i
    · subst hj; simp [e.orthonormal.1]
    · rw [if_neg hj, e.orthonormal.2 (Ne.symm hj), mul_zero]
  exact h.unique h2

theorem g64k_ext {ι : Type*} (e : HilbertBasis ι ℂ H) {x y : H}
    (h : ∀ i, inner ℂ (e i) x = inner ℂ (e i) y) : x = y := by
  apply e.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply, h]

theorem g64k_invol {ι : Type*} (K : H →L⋆[ℂ] H) (e : HilbertBasis ι ℂ H) (he : ∀ i, K (e i) = e i)
    (x : H) : K (K x) = x := by
  apply g64k_ext e
  intro i
  rw [g64k_coef K e he, ← inner_conj_symm, g64k_coef K e he, inner_conj_symm]

theorem g64k_inner {ι : Type*} (K : H →L⋆[ℂ] H) (e : HilbertBasis ι ℂ H) (he : ∀ i, K (e i) = e i)
    (x y : H) : inner ℂ (K x) (K y) = inner ℂ y x := by
  rw [← e.tsum_inner_mul_inner (K x) (K y), ← e.tsum_inner_mul_inner y x]
  congr 1; funext i
  rw [g64k_coef K e he, ← inner_conj_symm (K x) (e i), g64k_coef K e he, inner_conj_symm, mul_comm]

theorem g64k_adj {ι : Type*} (K : H →L⋆[ℂ] H) (e : HilbertBasis ι ℂ H) (he : ∀ i, K (e i) = e i)
    (x y : H) : inner ℂ (K x) y = inner ℂ (K y) x := by
  conv_lhs => rw [← g64k_invol K e he y]
  rw [g64k_inner K e he]
end G64C

section G64D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem g64k_maps {ι κ : Type*} (K : H →L⋆[ℂ] H) (e : HilbertBasis ι ℂ H) (he : ∀ i, K (e i) = e i)
    (b : HilbertBasis κ ℂ H) : ∃ c : HilbertBasis κ ℂ H, ∀ i, c i = K (b i) := by
  classical
  have hon : Orthonormal ℂ (fun i => K (b i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [g64k_inner K e he, (orthonormal_iff_ite.mp b.orthonormal) j i]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hsp : (Submodule.span ℂ (Set.range fun i => K (b i)))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have h1 : ∀ i, inner ℂ (K (b i)) y = 0 := fun i =>
      Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i)) hy
    have h2 : K y = 0 := by
      apply g64k_ext b
      intro i
      rw [inner_zero_right, ← inner_conj_symm, ← g64k_adj K e he, h1 i, map_zero]
    rw [← g64k_invol K e he y, h2, map_zero]
  exact ⟨HilbertBasis.mkOfOrthogonalEqBot hon hsp,
    fun i => by rw [HilbertBasis.coe_mkOfOrthogonalEqBot]⟩

theorem g64k_conv {ι : Type*} (K : H →L⋆[ℂ] H) (b : HilbertBasis ι ℂ H)
    (hb : ∀ x : H, HasSum (fun i => inner ℂ x (b i) • b i) (K x)) (i : ι) : K (b i) = b i := by
  classical
  refine (hb (b i)).unique ?_
  convert hasSum_ite_eq i (b i) using 1
  funext j
  by_cases h : j = i
  · subst h; simp [b.orthonormal.1]
  · rw [if_neg h, b.orthonormal.2 (Ne.symm h), zero_smul]
end G64D

/-- Lemma 1.3, PDF p.3, interpreted for bounded anti-linear maps as in its proof.
The series converges in the Hilbert norm, including finite and empty bases. -/
theorem solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (K : H →L⋆[ℂ] H) :
    IsConjugation K ↔
      ∃ (ι : Type u) (_ : Countable ι) (b : HilbertBasis ι ℂ H),
        ∀ x : H, HasSum (fun i => inner ℂ x (b i) • b i) (K x) := by
  constructor
  · rintro ⟨ι, hι, e, he⟩
    exact ⟨ι, hι, e, g64k_formula K e he⟩
  · rintro ⟨ι, hι, b, hb⟩
    exact ⟨ι, hι, b, g64k_conv K b hb⟩


end
