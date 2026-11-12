-- Prove2me | solution 1 for TensorBTD.Gramian.partial_derivative_outer
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-11T12:25:23.027525+00:00
-- url     : https://prove2.me/submissions/e6783166-4144-4270-aad6-abc31eaebfe6

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_TensorBTD_Gramian_Setting

open TensorBTD.Gramian
open Matrix

theorem solution {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) (r : Col L) (i : Fin (I n)) :
    (fun ι => jac (cpdResidual T) x ι ⟨n, (r, i)⟩) =
      outer (Function.update (fun m k => cpdFactor x m k r) n (Pi.single i 1)) := by
  classical
  funext ι
  let β : GIdx I L := ⟨n, (r,i)⟩
  let d : GIdx I L → ℂ := Pi.single β 1
  have hFactor (c : Col L) (m : Fin P ⊕ Fin Q) :
      HasDerivAt (fun t : ℂ => cpdFactor (x + t • d) m (ι m) c)
        (d ⟨m,(c,ι m)⟩) 0 := by
    simpa [cpdFactor, smul_eq_mul] using (hasDerivAt_const (0 : ℂ) (x ⟨m,(c,ι m)⟩)).fun_add
      ((hasDerivAt_id (0 : ℂ)).mul_const (d ⟨m,(c,ι m)⟩))
  have hProduct (c : Col L) :
      HasDerivAt (fun t : ℂ => ∏ m, cpdFactor (x + t • d) m (ι m) c)
        (∑ m, (∏ k ∈ Finset.univ.erase m, cpdFactor x k (ι k) c) *
          d ⟨m,(c,ι m)⟩) 0 := by
    simpa [smul_eq_mul] using
      (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun m _ => hFactor c m))
  have hResidual :
      HasDerivAt (fun t : ℂ => cpdResidual T (x + t • d) ι)
        (∑ c, ∑ m, (∏ k ∈ Finset.univ.erase m, cpdFactor x k (ι k) c) *
          d ⟨m,(c,ι m)⟩) 0 := by
    simpa [cpdResidual, cpdModel, outer] using
      (HasDerivAt.fun_sum (u := Finset.univ) (fun c _ => hProduct c)).sub_const (T ι)
  change deriv (fun t : ℂ => cpdResidual T (x + t • d) ι) 0 = _
  rw [hResidual.deriv]
  have hDelta (c : Col L) (m : Fin P ⊕ Fin Q) :
      d ⟨m,(c,ι m)⟩ = if m = n ∧ c = r ∧ ι n = i then 1 else 0 := by
    by_cases hm : m = n
    · subst m
      simp [d, β, Pi.single_apply]
    · have hne : (⟨m,(c,ι m)⟩ : GIdx I L) ≠ β := by
        intro h
        exact hm (congrArg Sigma.fst h)
      simp [d, Pi.single_eq_of_ne hne, hm]
  simp_rw [hDelta]
  simp only [mul_ite, mul_one, mul_zero]
  by_cases hi : ι n = i
  · simp only [hi, and_true]
    simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [outer, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n)]
    simp only [Function.update_self, hi, Pi.single_eq_same, one_mul]
    apply Finset.prod_congr rfl
    intro m hm
    exact (congrArg (fun f : Fin (I m) → ℂ => f (ι m))
      (Function.update_of_ne (Finset.ne_of_mem_erase hm) (Pi.single i 1)
        (fun m k => cpdFactor x m k r))).symm
  · simp only [hi, and_false, if_false, Finset.sum_const_zero]
    rw [outer, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n)]
    simp [hi]

#print axioms solution
