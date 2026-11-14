-- Prove2me | solution 1 for TensorBTD.Gramian.off_diagonal_blocks
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-13T12:16:43.701206+00:00
-- url     : https://prove2.me/submissions/e1477798-3bdf-420b-a914-f1bdbef587eb

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
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

private lemma inner_outer {K : Type*} [Fintype K] [DecidableEq K]
    {J : K → Type*} [∀ k, Fintype (J k)] (v w : (k : K) → J k → ℂ) :
    (∑ ι : (k : K) → J k, starRingEnd ℂ (∏ k, v k (ι k)) * (∏ k, w k (ι k))) =
      ∏ k, ∑ i, starRingEnd ℂ (v k i) * w k i := by
  simp_rw [map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun k j => starRingEnd ℂ (v k j) * w k j)).symm

private def jvec {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) (r : Col L) (i : Fin (I n))
    (m : Fin P ⊕ Fin Q) (k : Fin (I m)) : ℂ :=
  if h : m = n then if h ▸ k = i then 1 else 0 else cpdFactor x m k r

private lemma jac_outer {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (ι : (n : Fin P ⊕ Fin Q) → Fin (I n))
    (n : Fin P ⊕ Fin Q) (r : Col L) (i : Fin (I n)) :
    jac (cpdResidual T) x ι ⟨n,(r,i)⟩ = ∏ m, jvec x n r i m (ι m) := by
  classical
  rw [jac_formula, ← Finset.prod_erase_mul _ _ (Finset.mem_univ n)]
  have he : (∏ m ∈ Finset.univ.erase n, jvec x n r i m (ι m)) =
      ∏ m ∈ Finset.univ.erase n, cpdFactor x m (ι m) r := by
    apply Finset.prod_congr rfl
    intro m hm
    simp [jvec, (Finset.mem_erase.mp hm).1]
  rw [he]
  simp [jvec, mul_ite]

private lemma inner_jac {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (n1 n2 : Fin P ⊕ Fin Q)
    (r1 r2 : Col L) (i : Fin (I n1)) (j : Fin (I n2)) :
    tensorInner (fun ι => jac (cpdResidual T) x ι ⟨n1,(r1,i)⟩)
      (fun ι => jac (cpdResidual T) x ι ⟨n2,(r2,j)⟩) =
      ∏ m, ∑ k, starRingEnd ℂ (jvec x n1 r1 i m k) * jvec x n2 r2 j m k := by
  classical
  simp only [tensorInner, jac_outer]
  exact inner_outer _ _

private lemma off_inner {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (n1 n2 : Fin P ⊕ Fin Q) (hn : n1 ≠ n2)
    (r1 r2 : Col L) (i : Fin (I n1)) (j : Fin (I n2)) :
    tensorInner (fun ι => jac (cpdResidual T) x ι ⟨n1,(r1,i)⟩)
      (fun ι => jac (cpdResidual T) x ι ⟨n2,(r2,j)⟩) =
      W {n1,n2} (cpdFactor x) r1 r2 * cpdFactor x n1 i r2 *
        starRingEnd ℂ (cpdFactor x n2 j r1) := by
  classical
  rw [inner_jac, ← Finset.prod_erase_mul _ _ (Finset.mem_univ n1)]
  rw [← Finset.prod_erase_mul _ _ (show n2 ∈ Finset.univ.erase n1 by simp [hn.symm])]
  have he : (∏ m ∈ (Finset.univ.erase n1).erase n2,
      ∑ k, starRingEnd ℂ (jvec x n1 r1 i m k) * jvec x n2 r2 j m k) =
      W {n1,n2} (cpdFactor x) r1 r2 := by
    unfold W
    simp only [Matrix.of_apply]
    have hs : (Finset.univ.erase n1).erase n2 =
        Finset.univ.filter (· ∉ ({n1,n2} : Finset _)) := by ext; simp [ne_comm, and_comm]
    rw [← hs]
    apply Finset.prod_congr rfl
    intro m hm
    simp only [Finset.mem_erase] at hm
    simp [jvec, hm.1, hm.2.1, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [he]
  simp [jvec, hn, hn.symm, mul_ite, ite_mul]
  ring
theorem solution {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (n1 n2 : Fin P ⊕ Fin Q) (hn : n1 ≠ n2) (r1 r2 : Col L) :
    (∀ (i : Fin (I n1)) (j : Fin (I n2)),
      tensorInner (fun ι => jac (cpdResidual T) x ι ⟨n1, (r1, i)⟩)
          (fun ι => jac (cpdResidual T) x ι ⟨n2, (r2, j)⟩) =
        W {n1, n2} (cpdFactor x) r1 r2 * cpdFactor x n1 i r2 *
          starRingEnd ℂ (cpdFactor x n2 j r1)) ∧
    (Matrix.of fun (i : Fin (I n1)) (j : Fin (I n2)) =>
        ((jac (cpdResidual T) x)ᴴ * jac (cpdResidual T) x) ⟨n1, (r1, i)⟩ ⟨n2, (r2, j)⟩) =
      W {n1, n2} (cpdFactor x) r1 r2 •
        Matrix.vecMulVec (fun i => cpdFactor x n1 i r2)
          (fun j => starRingEnd ℂ (cpdFactor x n2 j r1)) := by
  classical
  constructor
  · exact off_inner T x n1 n2 hn r1 r2
  · ext i j
    change tensorInner (fun ι => jac (cpdResidual T) x ι ⟨n1,(r1,i)⟩)
      (fun ι => jac (cpdResidual T) x ι ⟨n2,(r2,j)⟩) = _
    rw [off_inner T x n1 n2 hn]
    simp [Matrix.vecMulVec, smul_eq_mul, mul_assoc]

#print axioms solution