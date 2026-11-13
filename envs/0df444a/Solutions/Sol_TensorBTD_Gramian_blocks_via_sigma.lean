-- Prove2me | solution 1 for TensorBTD.Gramian.blocks_via_sigma
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-12T13:30:32.162249+00:00
-- url     : https://prove2.me/submissions/ffd2f3fb-7ec9-4257-841e-364c3ad3fbed

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Vec
import Definitions.Def_TensorBTD_Gramian_Setting

set_option backward.isDefEq.respectTransparency false

open TensorBTD.Gramian Matrix

private lemma directional {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x d : GIdx I L → ℂ) (ι : (n : Fin P ⊕ Fin Q) → Fin (I n)) :
    HasDerivAt (fun t : ℂ => cpdResidual T (x + t • d) ι)
      (∑ c, ∑ m, (∏ k ∈ Finset.univ.erase m, cpdFactor x k (ι k) c) *
        d ⟨m,(c,ι m)⟩) 0 := by
  classical
  have hf (c : Col L) (m : Fin P ⊕ Fin Q) :
      HasDerivAt (fun t : ℂ => cpdFactor (x + t • d) m (ι m) c)
        (d ⟨m,(c,ι m)⟩) 0 := by
    simpa [cpdFactor, smul_eq_mul] using (hasDerivAt_const (0 : ℂ) (x ⟨m,(c,ι m)⟩)).fun_add
      ((hasDerivAt_id (0 : ℂ)).mul_const (d ⟨m,(c,ι m)⟩))
  have hp (c : Col L) := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun m _ => hf c m)
  simpa [cpdResidual, cpdModel, outer, smul_eq_mul] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun c _ => hp c)).sub_const (T ι)

private lemma jac_formula {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (ι : (n : Fin P ⊕ Fin Q) → Fin (I n))
    (n : Fin P ⊕ Fin Q) (r : Col L) (i : Fin (I n)) :
    jac (cpdResidual T) x ι ⟨n,(r,i)⟩ =
      if ι n = i then ∏ k ∈ Finset.univ.erase n, cpdFactor x k (ι k) r else 0 := by
  classical
  change deriv _ 0 = _
  rw [(directional T x (Pi.single ⟨n,(r,i)⟩ 1) ι).deriv]
  have hd (c : Col L) (m : Fin P ⊕ Fin Q) :
      (Pi.single (⟨n,(r,i)⟩ : GIdx I L) 1 : GIdx I L → ℂ) ⟨m,(c,ι m)⟩ =
        if m = n ∧ c = r ∧ ι n = i then 1 else 0 := by
    by_cases hm : m = n
    · subst m; simp [Pi.single_apply]
    · have hn : (⟨m,(c,ι m)⟩ : GIdx I L) ≠ ⟨n,(r,i)⟩ := by
        intro h; exact hm (congrArg Sigma.fst h)
      simp [Pi.single_eq_of_ne hn, hm]
  simp_rw [hd]
  simp only [mul_ite, mul_one, mul_zero]
  by_cases hi : ι n = i
  · simp [hi, ite_and]
  · simp [hi]

private lemma directional_jac {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x d : GIdx I L → ℂ) (ι : (n : Fin P ⊕ Fin Q) → Fin (I n)) :
    HasDerivAt (fun t : ℂ => cpdResidual T (x + t • d) ι)
      (∑ g, jac (cpdResidual T) x ι g * d g) 0 := by
  classical
  have hh : (∑ g, jac (cpdResidual T) x ι g * d g) =
      ∑ m, ∑ c, (∏ k ∈ Finset.univ.erase m, cpdFactor x k (ι k) c) * d ⟨m,(c,ι m)⟩ := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro m _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro c _
    simp_rw [jac_formula]
    simp [ite_mul]
  rw [hh, Finset.sum_comm]
  exact directional T x d ι

private lemma fullVec_affine {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (z d : Unk I L → ℂ) (t : ℂ) : fullVec (z + t • d) = fullVec z + t • fullVec d := by
  classical
  funext g
  rcases g with ⟨n,c,i⟩
  cases n with
  | inl p => rfl
  | inr q =>
    simp only [fullVec, factor, cMat, Matrix.mul_apply, Matrix.of_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    congr 1
    simp_rw [mul_assoc]
    rw [Finset.mul_sum]

private lemma fullVec_single {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (b : Unk I L) (g : GIdx I L) :
    fullVec (Pi.single b 1) g = Sigma I L b g := by
  classical
  rcases b with ⟨n,b⟩
  rcases g with ⟨m,g⟩
  by_cases h : n = m
  · subst m
    rw [TensorBTD.Gramian.Sigma, Matrix.blockDiagonal'_apply_eq]
    cases n <;> dsimp only [UCol] at * <;> rcases b with ⟨c,i⟩ <;> rcases g with ⟨r,j⟩ <;>
      simp [fullVec, factor, aMat, cMat, E, SigmaBlock, F,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.mul_apply,
        Pi.single_apply, ite_and, eq_comm]
    all_goals split_ifs <;> rfl
  · rw [TensorBTD.Gramian.Sigma, Matrix.blockDiagonal'_apply_ne _ _ _ h]
    cases n <;> cases m <;>
      simp_all [fullVec, factor, aMat, cMat, Matrix.mul_apply, Pi.single_apply]

private lemma jac_chain {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (z : Unk I L → ℂ) :
    jac (residual T) z = jac (cpdResidual T) (fullVec z) * (Sigma I L)ᵀ := by
  classical
  ext ι b
  change deriv (fun t : ℂ => residual T (z + t • Pi.single b 1) ι) 0 = _
  have he : (fun t : ℂ => residual T (z + t • Pi.single b 1) ι) =
      (fun t : ℂ => cpdResidual T (fullVec z + t • fullVec (Pi.single b 1)) ι) := by
    funext t
    rw [← fullVec_affine]
    rfl
  rw [he, (directional_jac T (fullVec z) (fullVec (Pi.single b 1)) ι).deriv]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, fullVec_single]

private lemma sigma_real {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (a : Unk I L) (b : GIdx I L) :
    starRingEnd ℂ (Sigma I L a b) = Sigma I L a b := by
  classical
  rcases a with ⟨n,a⟩
  rcases b with ⟨m,b⟩
  by_cases h : n = m
  · subst m
    rw [TensorBTD.Gramian.Sigma, Matrix.blockDiagonal'_apply_eq]
    cases n <;> simp [SigmaBlock, F, E, Matrix.kroneckerMap_apply, Matrix.one_apply]
    all_goals split_ifs <;> simp
  · rw [TensorBTD.Gramian.Sigma, Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp

theorem solution {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (z : Unk I L → ℂ) :
    (jac (residual T) z)ᴴ * jac (residual T) z =
      Sigma I L * ((jac (cpdResidual T) (fullVec z))ᴴ * jac (cpdResidual T) (fullVec z)) *
        (Sigma I L)ᵀ := by
  classical
  have hs : ((Sigma I L)ᵀ)ᴴ = Sigma I L := by
    ext a b
    exact sigma_real a b
  rw [jac_chain, Matrix.conjTranspose_mul, hs]
  simp only [Matrix.mul_assoc]

#print axioms solution
