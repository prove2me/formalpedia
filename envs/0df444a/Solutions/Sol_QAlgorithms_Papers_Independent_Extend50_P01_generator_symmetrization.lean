-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P01.generator_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:08:44.926229+00:00
-- url     : https://prove2.me/submissions/0e8476ad-e2e7-47c5-a3c8-e6cbd86b49c3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01
set_option autoImplicit false
noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Extend50
open QAlgorithms.Papers.Independent.Extend50.P01

attribute [local instance] Classical.propDecidable Classical.decEq

-- PDF pp.3,8: reuse the accepted operator type, exp(-itH), and A X A†.
-- Notation specializes the imported interfaces without introducing duplicate declarations.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "evolve" => QAlgorithms.Papers.Independent.Information100.P32.evolution

local notation "conjugate" => QAlgorithms.conjSuperop

-- PDF pp.3,10–11: the imported quadratic form is Re(psi† A psi).

local notation "expectation" => QAlgorithms.Papers.Independent.Information100.P21.quad

-- PDF pp.5,16–19: accepted active-wire operator, with identities on all spectators.

local notation "onWire" => QAlgorithms.Papers.Independent.Advance50.P49.onWire

-- PDF p.5: the imported phase-free Pauli tensor uses 0=I,1=X,2=Y,3=Z.

local notation "pauliWord" => QAlgorithms.Papers.Independent.Gap48.P33.pauliWord

private lemma twirl_hermitian {S ι : Type*} [Fintype S] [Fintype ι]
    (U : S → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (finiteTwirl U A).IsHermitian := by
  unfold finiteTwirl
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  congr 1
  · simp [star_inv₀]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp only [QAlgorithms.conjSuperop, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hA.eq, Matrix.mul_assoc]

private lemma twirl_conj {S ι : Type*} [Group S] [Fintype S] [Fintype ι] [DecidableEq ι]
    (U : S →* Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (t : S) :
    U t * finiteTwirl U A * (U t)ᴴ = finiteTwirl U A := by
  unfold finiteTwirl
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  have : ∀ s, U t * conjugate (U s) A * (U t)ᴴ = conjugate (U (t * s)) A := by
    intro s
    simp only [QAlgorithms.conjSuperop, map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp_rw [this]
  exact Equiv.sum_comp (Equiv.mulLeft t) (fun s => conjugate (U s) A)

private lemma commute_of_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {V T : Matrix ι ι ℂ}
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) (h : V * T * Vᴴ = T) : Commute V T := by
  have h1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  show V * T = T * V
  calc V * T = V * T * (Vᴴ * V) := by rw [h1, Matrix.mul_one]
    _ = (V * T * Vᴴ) * V := by simp only [Matrix.mul_assoc]
    _ = T * V := by rw [h]

private lemma evolution_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    QAlgorithms.Papers.Independent.Information100.P32.evolution H t ∈ Matrix.unitaryGroup ι ℂ := by
  unfold QAlgorithms.Papers.Independent.Information100.P32.evolution
  set X : Matrix ι ι ℂ := (-(t : ℂ) * Complex.I) • H with hX
  have hXs : Xᴴ = -X := by
    rw [hX, Matrix.conjTranspose_smul, hH.eq]
    rw [← neg_smul]
    congr 1
    simp [Complex.conj_ofReal]
  rw [Matrix.mem_unitaryGroup_iff]
  change NormedSpace.exp X * (NormedSpace.exp X)ᴴ = 1
  rw [← Matrix.exp_conjTranspose, hXs, ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X)),
    add_neg_cancel, NormedSpace.exp_zero]

private lemma orderedProd_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    (W : Fin t → Matrix ι ι ℂ) (P : Submonoid (Matrix ι ι ℂ)) (hW : ∀ j, W j ∈ P) :
    QAlgorithms.orderedProd W ∈ P := by
  unfold QAlgorithms.orderedProd
  apply Submonoid.list_prod_mem
  intro x hx
  rw [List.mem_reverse, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  exact hW j

theorem solution {S : Type*} [Group S] [Fintype S]
    (n k : ℕ) (U : S →* Op n) (hU : ∀ s, U s ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (G : Fin k → Op n) (hG : ∀ j, (G j).IsHermitian) (theta : Fin k → ℝ) :
    (∀ j, (finiteTwirl U (G j)).IsHermitian ∧
      evolve (finiteTwirl U (G j)) (theta j) ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧
      ∀ s, Commute (evolve (finiteTwirl U (G j)) (theta j)) (U s)) ∧
    orderedProd (fun j => evolve (finiteTwirl U (G j)) (theta j)) ∈
      Matrix.unitaryGroup (Qubits n) ℂ ∧
    ∀ s, Commute (orderedProd (fun j => evolve (finiteTwirl U (G j)) (theta j))) (U s) := by
  have hcomm : ∀ j s, Commute (evolve (finiteTwirl U (G j)) (theta j)) (U s) := by
    intro j s
    unfold QAlgorithms.Papers.Independent.Information100.P32.evolution
    refine Commute.symm (Commute.exp_right ?_)
    exact (commute_of_conj (hU s) (twirl_conj U (G j) s)).smul_right _
  have hunit : ∀ j, evolve (finiteTwirl U (G j)) (theta j) ∈ Matrix.unitaryGroup (Qubits n) ℂ :=
    fun j => evolution_unitary _ (twirl_hermitian _ _ (hG j)) _
  refine ⟨fun j => ⟨twirl_hermitian _ _ (hG j), hunit j, hcomm j⟩,
    orderedProd_mem _ _ hunit, fun s => ?_⟩
  have hmem := orderedProd_mem (P := Submonoid.centralizer {U s})
    (fun j => evolve (finiteTwirl U (G j)) (theta j)) fun j => by
      rw [Submonoid.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (hcomm j s).eq.symm
  rw [Submonoid.mem_centralizer_iff] at hmem
  exact (hmem (U s) rfl).symm
