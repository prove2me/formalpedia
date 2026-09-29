-- Prove2me | solution 1 for Submodule.natCard_quotient_eq_natCard_quotient_span_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c29bd675-f969-512f-86b2-173d67510a9f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_natCard_quotient_eq_natCard_quotient_span_det

set_option autoImplicit false

namespace P2mIndexDetPID

open Module Submodule

variable {R : Type} [CommRing R] [IsDomain R]

theorem natCard_quotient_span_mul (a : R) {b : R} (hb : b ≠ 0) :
    Nat.card (R ⧸ Ideal.span ({a * b} : Set R)) =
      Nat.card (R ⧸ Ideal.span ({a} : Set R)) * Nat.card (R ⧸ Ideal.span ({b} : Set R)) := by
  classical

  set T : Ideal R := Ideal.span ({a * b} : Set R) with hT
  set S : Ideal R := Ideal.span ({b} : Set R) with hS
  have hTS : T ≤ S := by
    rw [hT, hS, Ideal.span_singleton_le_span_singleton]
    exact Dvd.intro_left a rfl
  have key := Submodule.card_quotient_mul_card_quotient (S.restrictScalars R) (T.restrictScalars R)
    (by simpa using hTS)

  let φ : R →ₗ[R] (R ⧸ T.restrictScalars R) :=
    LinearMap.toSpanSingleton R (R ⧸ T.restrictScalars R) (Submodule.Quotient.mk b)
  have hφ : ∀ x, φ x = (Submodule.Quotient.mk (x * b) : R ⧸ T.restrictScalars R) := by
    intro x
    change x • (Submodule.Quotient.mk b : R ⧸ T.restrictScalars R) = _
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
  have hrange : LinearMap.range φ = (S.restrictScalars R).map (T.restrictScalars R).mkQ := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨x * b, ?_, ?_⟩
      · change x * b ∈ S
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton b))
      · rw [hφ]; rfl
    · rintro _ ⟨y, hy, rfl⟩
      change y ∈ S at hy
      rw [hS, Ideal.mem_span_singleton'] at hy
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, by rw [hφ]; rfl⟩
  have hker : LinearMap.ker φ = (Ideal.span ({a} : Set R)).restrictScalars R := by
    ext x
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem,
      Submodule.restrictScalars_mem, hT, Ideal.mem_span_singleton', Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have : (y * a) * b = x * b := by rw [mul_assoc]; exact hy
      exact mul_right_cancel₀ hb this
    · rintro ⟨y, rfl⟩
      exact ⟨y, by ring⟩
  have e1 := φ.quotKerEquivRange
  have hcardS : Nat.card ((S.restrictScalars R).map (T.restrictScalars R).mkQ) =
      Nat.card (R ⧸ Ideal.span ({a} : Set R)) := by
    rw [← hrange, ← Nat.card_congr e1.toEquiv, hker]
    rfl
  rw [hcardS] at key

  have h1 : Nat.card (R ⧸ T.restrictScalars R) = Nat.card (R ⧸ T) := rfl
  have h2 : Nat.card (R ⧸ S.restrictScalars R) = Nat.card (R ⧸ S) := rfl
  rw [h1, h2] at key
  exact key.symm

theorem natCard_quotient_span_prod {ι : Type} (s : Finset ι) (a : ι → R)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    Nat.card (R ⧸ Ideal.span ({∏ i ∈ s, a i} : Set R)) =
      ∏ i ∈ s, Nat.card (R ⧸ Ideal.span ({a i} : Set R)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [Ideal.span_singleton_one]
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Nat.card_of_subsingleton (0 : R ⧸ (⊤ : Ideal R))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have hs : ∀ j ∈ s, a j ≠ 0 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hprod : ∏ j ∈ s, a j ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
    rw [natCard_quotient_span_mul (a i) hprod, ih hs]

variable [IsPrincipalIdealRing R]
variable {M : Type} [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem natCard_quotient_eq_natCard_quotient_span_det
    (b : Basis ι R M) (N : Submodule R M) (bN : Basis ι R N) :
    Nat.card (M ⧸ N) = Nat.card (R ⧸ Ideal.span ({b.det ((↑) ∘ bN)} : Set R)) := by
  classical
  haveI : Module.Free R M := Module.Free.of_basis b
  haveI : Module.Finite R M := Module.Finite.of_basis b
  have h : Module.finrank R N = Module.finrank R M := by
    rw [Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis b]
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h

  have hMN : Nat.card (M ⧸ N) = ∏ i, Nat.card (R ⧸ Ideal.span ({a i} : Set R)) := by
    rw [Nat.card_congr (N.quotientEquivPiSpan b h).toEquiv, Nat.card_pi]

  let e : M ≃ₗ[R] N := b.equiv bN (Equiv.refl _)
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype.comp (e' : M →ₗ[R] N)
  have hf : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' f = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hf, map_smul, b'.repr_self, Finsupp.smul_single, smul_eq_mul,
        mul_one]
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [this, Matrix.det_diagonal]
  have hdet1 : b.det ((↑) ∘ bN) = LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N)) := by
    have := Basis.det_comp_basis bN b N.subtype
    simpa [e] using this
  have hassoc : Associated (b.det ((↑) ∘ bN)) (∏ i, a i) := by
    rw [hdet1, ← hdetf]
    exact LinearMap.associated_det_comp_equiv N.subtype e e'
  have hspan : Ideal.span ({b.det ((↑) ∘ bN)} : Set R) = Ideal.span ({∏ i, a i} : Set R) :=
    Ideal.span_singleton_eq_span_singleton.mpr hassoc
  rw [hMN, hspan, natCard_quotient_span_prod Finset.univ a
    (fun i _ => smithNormalFormCoeffs_ne_zero b h i)]

end P2mIndexDetPID

theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type} [AddCommGroup M] [Module R M]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (N : Submodule R M) (bN : Module.Basis ι R N) :
    Nat.card (M ⧸ N) = Nat.card (R ⧸ Ideal.span ({b.det (fun i => (bN i : M))} : Set R)) :=
  P2mIndexDetPID.natCard_quotient_eq_natCard_quotient_span_det b N bN

end S_Submodule_natCard_quotient_eq_natCard_quotient_span_det
end P2MW
export P2MW.S_Submodule_natCard_quotient_eq_natCard_quotient_span_det (solution)
