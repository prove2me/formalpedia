-- Prove2me | solution 1 for PeresTerno.transpose_not_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:57:33.20601+00:00
-- url     : https://prove2.me/submissions/117f0408-1d95-45e3-8272-f442ce57eecf

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTernoCex1ad1

open PeresTerno Matrix

/-- maximally entangled (unnormalized) vector on `Fin 2 × Fin 2`. -/
def bellVec : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- antisymmetric test vector. -/
def testVec : Fin 2 × Fin 2 → ℂ := ![![0, 1], ![-1, 0]] |> fun f p => f p.1 p.2

lemma ampliate_transpose_apply {f : Type*} (R : Matrix (Fin 2 × f) (Fin 2 × f) ℂ)
    (p q : Fin 2 × f) :
    ampliate (fun ρ : Matrix (Fin 2) (Fin 2) ℂ => ρᵀ) R p q = R (q.1, p.2) (p.1, q.2) := rfl

lemma key :
    star testVec ⬝ᵥ (ampliate (fun ρ : Matrix (Fin 2) (Fin 2) ℂ => ρᵀ)
      (vecMulVec bellVec (star bellVec)) *ᵥ testVec) = -2 := by
  simp only [dotProduct, mulVec, ampliate_transpose_apply]
  simp [vecMulVec, bellVec, testVec, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end PeresTernoCex1ad1

open PeresTerno Matrix ComplexOrder in
theorem solution :
    ¬ IsCompletelyPositive (fun ρ : Matrix (Fin 2) (Fin 2) ℂ => ρᵀ) := by
  intro h
  have hR := h 2 (vecMulVec PeresTernoCex1ad1.bellVec (star PeresTernoCex1ad1.bellVec))
    (posSemidef_vecMulVec_self_star _)
  have h0 := hR.dotProduct_mulVec_nonneg PeresTernoCex1ad1.testVec
  rw [PeresTernoCex1ad1.key] at h0
  norm_num at h0
