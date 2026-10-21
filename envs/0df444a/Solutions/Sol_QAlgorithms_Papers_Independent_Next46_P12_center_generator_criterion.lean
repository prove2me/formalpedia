-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P12.center_generator_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:12:31.167978+00:00
-- url     : https://prove2.me/submissions/4600841b-9ba7-4f87-8df3-f4e987c002dc

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12
noncomputable section

open scoped BigOperators Classical

open Filter

open QAlgorithms.Papers.Independent.Next46.P12

universe u v w

namespace G62K
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

lemma block (D : SplitPresentation k A) {z : A} (hz : z ∈ Subalgebra.center k A) (i : D.Label) :
    D.equiv z i = algebraMap k _ (centralSpectrum D z i) := by
  have hc : ∀ M, Commute M (D.equiv z i) := by
    intro M
    have := (Subalgebra.mem_center_iff.mp hz) (D.equiv.symm (Pi.single i M))
    have h2 := congrArg (fun x => D.equiv x i) this
    simp only [map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.single_eq_same] at h2
    exact h2
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr (fun a b => hc _)
  have : centralSpectrum D z i = r := by
    simp [centralSpectrum, ← hr]
  rw [this, ← hr]; rfl

lemma mem_center_of (D : SplitPresentation k A) (z : A) (c : D.Label → k)
    (h : ∀ i, D.equiv z i = algebraMap k _ (c i)) : z ∈ Subalgebra.center k A := by
  rw [Subalgebra.mem_center_iff]
  intro b
  apply D.equiv.injective
  funext i
  simp only [map_mul, Pi.mul_apply, h i]
  exact (Algebra.commutes _ _).symm

lemma spec_alg (D : SplitPresentation k A) (z : A) (c : D.Label → k)
    (h : ∀ i, D.equiv z i = algebraMap k _ (c i)) (i : D.Label) : centralSpectrum D z i = c i := by
  simp only [centralSpectrum, h i, Matrix.algebraMap_matrix_apply]; simp

lemma spec_aeval (D : SplitPresentation k A) {z : A} (hz : z ∈ Subalgebra.center k A)
    (p : Polynomial k) (j : D.Label) :
    D.equiv (Polynomial.aeval z p) j = algebraMap k _ (p.eval (centralSpectrum D z j)) := by
  have : D.equiv (Polynomial.aeval z p) j =
      ((Pi.evalAlgHom k _ j).comp D.equiv.toAlgHom) (Polynomial.aeval z p) := rfl
  rw [this, ← Polynomial.aeval_algHom_apply]
  change Polynomial.aeval (D.equiv z j) p = _
  rw [block D hz j, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

lemma ci_block (D : SplitPresentation k A) (i j : D.Label) :
    D.equiv (centralIdempotent D i) j = algebraMap k _ (if j = i then 1 else 0) := by
  simp only [centralIdempotent, blockElement, AlgEquiv.apply_symm_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma eval_cp (D : SplitPresentation k A) (z : A) (hinj : Function.Injective (centralSpectrum D z))
    (i j : D.Label) :
    (centralPolynomial D z i).eval (centralSpectrum D z j) = if j = i then 1 else 0 := by
  unfold centralPolynomial
  rw [Polynomial.eval_prod]
  by_cases h : j = i
  · subst h
    simp only [if_true]
    apply Finset.prod_eq_one
    intro l hl
    have hne : centralSpectrum D z j - centralSpectrum D z l ≠ 0 :=
      sub_ne_zero.mpr (fun e => (Finset.ne_of_mem_erase hl) (hinj e).symm)
    simp [interpolationFactor, hne]
  · simp only [h, if_false]
    apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
    simp [interpolationFactor]

theorem crit [FiniteDimensional k A] (D : SplitPresentation k A) (z : A)
    (hz : z ∈ Subalgebra.center k A) :
    GeneratesCenter (k := k) z ↔ Function.Injective (centralSpectrum D z) := by
  constructor
  · intro hg i j hij
    by_contra hne
    have hm : centralIdempotent D i ∈ Algebra.adjoin k ({z} : Set A) := by
      rw [hg]; exact mem_center_of D _ _ (ci_block D i)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨p, hp⟩ := hm
    have h1 := spec_alg D _ _ (ci_block D i) i
    have h2 := spec_alg D _ _ (ci_block D i) j
    have e1 := spec_alg D _ _ (spec_aeval D hz p) i
    have e2 := spec_alg D _ _ (spec_aeval D hz p) j
    change Polynomial.aeval z p = _ at hp
    rw [hp] at e1 e2
    rw [e1, if_pos rfl] at h1
    rw [e2, if_neg (Ne.symm hne), ← hij] at h2
    rw [h1] at h2; exact one_ne_zero h2
  · intro hinj
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]; intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact hz
    · intro w hw
      let P : Polynomial k := ∑ i, Polynomial.C (centralSpectrum D w i) * centralPolynomial D z i
      have : w = Polynomial.aeval z P := by
        apply D.equiv.injective
        funext j
        rw [spec_aeval D hz, block D hw]
        congr 1
        simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          eval_cp D z hinj]
        simp
      rw [this]; exact Polynomial.aeval_mem_adjoin_singleton k z

end G62K


open G62K

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Lemma 2.1(a,b), source PDF p. 8. The cardinality condition includes finite
fields of sufficient size, expressed by embedding the full set of simple labels. -/
theorem solution [FiniteDimensional k A] (D : SplitPresentation k A) :
    (∀ z : Subalgebra.center k A,
      GeneratesCenter (k := k) (z : A) ↔ Function.Injective (centralSpectrum D (z : A))) ∧
    (Nonempty (D.Label ↪ k) →
      ∃ z : Subalgebra.center k A, GeneratesCenter (k := k) (z : A)) := by
  refine ⟨fun z => G62K.crit D z z.2, fun ⟨f⟩ => ?_⟩
  have hm : ∀ i, D.equiv (D.equiv.symm (fun i => algebraMap k _ (f i))) i = algebraMap k _ (f i) := by
    intro i; simp
  refine ⟨⟨_, G62K.mem_center_of D _ _ hm⟩, (G62K.crit D _ (G62K.mem_center_of D _ _ hm)).mpr ?_⟩
  have : centralSpectrum D (D.equiv.symm (fun i => algebraMap k _ (f i))) = f :=
    funext (G62K.spec_alg D _ _ hm)
  rw [this]; exact f.injective



end
