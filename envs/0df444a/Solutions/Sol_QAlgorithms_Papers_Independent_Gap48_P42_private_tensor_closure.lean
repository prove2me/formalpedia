-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P42.private_tensor_closure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:01:24.203758+00:00
-- url     : https://prove2.me/submissions/9919a3c8-81dc-4f3b-8cb7-a178ec26c2ac

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Gap48 QAlgorithms.Papers.Independent.Gap48.P42
open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

def g78b_pp {m : ℕ} {ι : Type} (A : Fin m → Matrix ι ι ℂ) :
    Matrix (Fin m → ι) (Fin m → ι) ℂ := fun x y => ∏ t, A t (x t) (y t)

theorem g78b_pp_mul {m : ℕ} {ι : Type} [Fintype ι] (A B : Fin m → Matrix ι ι ℂ) :
    g78b_pp A * g78b_pp B = g78b_pp (fun t => A t * B t) := by
  ext x y
  simp only [g78b_pp, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← Finset.prod_mul_distrib]

theorem g78b_pp_conjT {m : ℕ} {ι : Type} (A : Fin m → Matrix ι ι ℂ) :
    (g78b_pp A)ᴴ = g78b_pp (fun t => (A t)ᴴ) := by
  ext x y
  simp [g78b_pp, Matrix.conjTranspose_apply]

theorem g78b_pp_one {m : ℕ} {ι : Type} [DecidableEq ι] :
    g78b_pp (fun _ : Fin m => (1 : Matrix ι ι ℂ)) = 1 := by
  ext x y
  simp only [g78b_pp, Matrix.one_apply]
  rw [Fintype.prod_boole]
  congr 1
  exact propext ⟨fun h => funext h, fun h t => by rw [h]⟩

open scoped MatrixOrder in
theorem g78b_pp_psd {m : ℕ} {ι : Type} [Fintype ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (g78b_pp (fun _ : Fin m => A)).PosSemidef := by
  classical
  obtain ⟨c, hc⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have : g78b_pp (fun _ : Fin m => A) = (g78b_pp (fun _ : Fin m => c))ᴴ * g78b_pp (fun _ : Fin m => c) := by
    rw [g78b_pp_conjT, g78b_pp_mul, hc]; rfl
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

theorem g78b_pp_trace {m : ℕ} {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) :
    (g78b_pp (fun _ : Fin m => A)).trace = A.trace ^ m := by
  simp only [Matrix.trace, Matrix.diag, g78b_pp]
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- the copy-regrouping equivalence -/
def g78b_e (a b m : ℕ) : Fin (a ^ m) × Fin (b ^ m) ≃ (Fin m → Fin a × Fin b) :=
  ((QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex a m).symm.prodCongr (QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex b m).symm).trans
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin a) (fun _ => Fin b)).symm

theorem g78b_e_apply (a b m : ℕ) (p : Fin (a ^ m) × Fin (b ^ m)) (t : Fin m) :
    g78b_e a b m p t = ((QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex a m).symm p.1 t,
      (QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex b m).symm p.2 t) := rfl

theorem g78b_dP {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (m : ℕ) :
    QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower rho m =
      (g78b_pp (fun _ : Fin m => rho)).submatrix (g78b_e a b m) (g78b_e a b m) := by
  ext p q; rfl

theorem g78b_tw {d a b : ℕ} (U : Fin d → Matrix.unitaryGroup (Fin a × Fin b) ℂ) (m : ℕ)
    (key : Fin (d ^ m)) :
    tensorTwists U m key = (g78b_pp (fun t => (U ((QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm key t) :
      Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ))).submatrix (g78b_e a b m) (g78b_e a b m) := by
  ext p q; rfl

/-- PDF p.4, observation immediately before Property 1a: the actual regrouped
m-copy matrix is private with computed shield rho^tensor m and tensor twists.
The conclusion certifies normalization and both unitary identities of those
computed twists; no unrelated private target is existentially introduced. -/
theorem solution {d a b : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho)
    (U : Fin d → Matrix.unitaryGroup (Fin a × Fin b) ℂ) (m : ℕ) (hm : 0 < m) :
    IsDensityMatrix (Dependency50.P42.dimensionedPower rho m) ∧
    (∀ key, (tensorTwists U m key)ᴴ * tensorTwists U m key = 1 ∧
      tensorTwists U m key * (tensorTwists U m key)ᴴ = 1) ∧
    (fun x y : Fin (d ^ m * a ^ m) × Fin (d ^ m * b ^ m) =>
      Dependency50.P42.dimensionedPower (bipartitePrivate rho U) m
        (regroupIndex d a m x.1, regroupIndex d b m x.2)
        (regroupIndex d a m y.1, regroupIndex d b m y.2)) =
      bipartitePrivateRaw (Dependency50.P42.dimensionedPower rho m) (tensorTwists U m) := by
  have hdec : ∀ (K : Fin (d ^ m)) (t : Fin m), True := fun _ _ => trivial
  refine ⟨?_, ?_, ?_⟩
  · rw [g78b_dP]
    refine ⟨(g78b_pp_psd hrho.1).submatrix _, ?_⟩
    have := g78b_pp_trace (m := m) rho
    rw [hrho.2, one_pow] at this
    rw [← this]
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact Equiv.sum_comp (g78b_e a b m) (fun x => g78b_pp (fun _ : Fin m => rho) x x)
  · intro key
    rw [g78b_tw, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, g78b_pp_conjT, g78b_pp_mul, g78b_pp_mul]
    constructor
    · have : (fun t => ((U ((QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm key t) :
          Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ))ᴴ *
          (U ((QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm key t) :
          Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)) = fun _ => 1 := by
        funext t; rw [← Matrix.star_eq_conjTranspose]; exact Matrix.UnitaryGroup.star_mul_self _
      rw [this, g78b_pp_one, Matrix.submatrix_one_equiv]
    · have : (fun t => (U ((QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm key t) :
          Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) *
          (U ((QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm key t) :
          Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ) = fun _ => 1 := by
        funext t; rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp (U _).2
      rw [this, g78b_pp_one, Matrix.submatrix_one_equiv]
  · have hR : ∀ K K' : Fin (d ^ m), tensorTwists U m K *
        QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower rho m *
        (tensorTwists U m K')ᴴ = (g78b_pp (fun t =>
          (U ((QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm K t) :
            Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * rho *
          (U ((QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm K' t) :
            Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).submatrix (g78b_e a b m) (g78b_e a b m) := by
      intro K K'
      rw [g78b_tw, g78b_tw, g78b_dP, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
        Matrix.submatrix_mul_equiv, g78b_pp_conjT, g78b_pp_mul, g78b_pp_mul]
    funext x y
    simp only [bipartitePrivateRaw, QAlgorithms.Papers.Independent.Information100.P67.privateState]
    simp only [hR]
    simp only [bipartitePrivate, bipartitePrivateRaw,
      QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower,
      QAlgorithms.Papers.Independent.Information100.P80.groupedPower, regroupIndex,
      Equiv.symm_apply_apply, QAlgorithms.Papers.Independent.Information100.P67.privateState,
      Matrix.submatrix_apply, g78b_pp, g78b_e_apply]
    have key : ∀ P Q : Fin (d ^ m),
        (∀ i, (QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm P i =
          (QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm Q i) ↔ P = Q :=
      fun P Q => ⟨fun h => (QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex d m).symm.injective
        (funext h), fun h i => by rw [h]⟩
    rw [Fintype.prod_ite_zero]
    simp only [forall_and, key]
    split_ifs
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      push_cast
      rw [inv_pow]
    · rfl


end

