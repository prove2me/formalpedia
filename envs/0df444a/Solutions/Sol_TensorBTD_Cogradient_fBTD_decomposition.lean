-- Prove2me | solution 1 for TensorBTD.Cogradient.fBTD_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-12T13:28:06.753554+00:00
-- url     : https://prove2.me/submissions/83ff9eaa-5811-4a28-9323-509cc1392c95

import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring
import Definitions.Def_TensorBTD_Cogradient_Setting

open TensorBTD.Cogradient Matrix
open TensorBTD.Gramian (Tensor GIdx Unk Col)
set_option backward.isDefEq.respectTransparency false

private noncomputable def indices {P Q : ℕ} (I : Fin P ⊕ Fin Q → ℕ) (n : Fin P ⊕ Fin Q) :
    ((m : Fin P ⊕ Fin Q) → Fin (I m)) ≃ (Fin (I n) × KRIdx I {n}) := by
  classical
  exact
  { toFun := fun ι => (ι n, fun m => ι m.1)
    invFun := fun b m => if h : m = n then h ▸ b.1 else b.2 ⟨m, by simpa using h⟩
    left_inv := by intro ι; funext m; dsimp only; split_ifs with h <;> subst_vars <;> rfl
    right_inv := by
      rintro ⟨i,ρ⟩
      apply Prod.ext
      · simp
      · funext m; have hm : m.1 ≠ n := by simpa using m.2
        simp [hm] }

private lemma unfold_model {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) (i : Fin (I n)) (ρ : KRIdx I {n}) :
    (TensorBTD.Gramian.cpdFactor x n * (V {n} (TensorBTD.Gramian.cpdFactor x))ᵀ) i ρ =
      TensorBTD.Gramian.cpdModel (TensorBTD.Gramian.cpdFactor x) ((indices I n).symm (i,ρ)) := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, V, TensorBTD.Gramian.cpdModel,
    Finset.sum_apply, TensorBTD.Gramian.outer]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n)]
  have hn : (indices I n).symm (i,ρ) n = i := by simp [indices]
  rw [hn]
  congr 1
  rw [Finset.prod_subtype (p := fun m => m ∉ ({n} : Finset (Fin P ⊕ Fin Q)))
    (Finset.univ.erase n) (fun m => by simp)]
  apply Finset.prod_congr rfl
  intro m _
  have hm : m.1 ≠ n := by simpa using m.2
  simp [indices, hm]

private lemma norm_identity (a b : ℂ) :
    (Complex.normSq (a - b) : ℂ) =
      (Complex.normSq a : ℂ) - starRingEnd ℂ b * a -
        starRingEnd ℂ (starRingEnd ℂ b * a) + (Complex.normSq b : ℂ) := by
  simp [Complex.normSq_apply, Complex.ext_iff]
  constructor <;> ring

theorem solution {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (T : TensorBTD.Gramian.Tensor I) :
    (∀ z : TensorBTD.Gramian.Unk I L → ℂ, fBTD T z = fCPD T (TensorBTD.Gramian.fullVec z)) ∧
    ∀ (x : TensorBTD.Gramian.GIdx I L → ℂ) (n : Fin P ⊕ Fin Q),
      fCPD T x = (1 / 2 : ℂ) *
        (fOne n x - fTwo T n x - starRingEnd ℂ (fTwo T n x) + fThree T n) := by
  classical
  constructor
  · intro z
    rfl
  · intro x n
    let A := TensorBTD.Gramian.cpdFactor x n * (V {n} (TensorBTD.Gramian.cpdFactor x))ᵀ
    let B := unfolding T n
    have ht (i : Fin (I n)) (ρ : KRIdx I {n}) :
        B i ρ = T ((indices I n).symm (i,ρ)) := rfl
    have hs : (∑ ι, Complex.normSq (cpdResidual T x ι)) =
        ∑ i, ∑ ρ, Complex.normSq (A i ρ - B i ρ) := by
      calc
        _ = ∑ b : Fin (I n) × KRIdx I {n}, Complex.normSq (A b.1 b.2 - B b.1 b.2) := by
          apply Fintype.sum_equiv (indices I n)
          intro ι
          change Complex.normSq (cpdResidual T x ι) =
            Complex.normSq (A ((indices I n) ι).1 ((indices I n) ι).2 -
              B ((indices I n) ι).1 ((indices I n) ι).2)
          rw [ht, show A = TensorBTD.Gramian.cpdFactor x n * (V {n} (TensorBTD.Gramian.cpdFactor x))ᵀ from rfl,
            unfold_model]
          simp only [Prod.mk.eta, Equiv.symm_apply_apply]
          simp [cpdResidual, TensorBTD.Gramian.cpdModel, TensorBTD.Gramian.outer]
        _ = _ := Fintype.sum_prod_type _
    simp only [fCPD, hs, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one]
    congr 1
    simp only [fOne, fTwo, fThree, frobNormSq, frobInner, map_sum,
      Complex.ofReal_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [norm_identity]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, map_mul]
    rfl

#print axioms solution
