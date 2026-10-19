-- Prove2me | solution 1 for QuantumMC.Cooling.chiSq_eq_sum_sq_div_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T08:20:36.30022+00:00
-- url     : https://prove2.me/submissions/1f8c17fa-5587-4640-986f-b182bd61efe5

import Definitions.Def_QuantumMC_Cooling_Setting
set_option autoImplicit false
open scoped ENNReal InnerProductSpace
open QuantumMC.Cooling

namespace QueeliusCooling

theorem chi_identity {Ω : Type*} [Fintype Ω] (ν π : Ω → ℝ)
    (hν : ∑ x, ν x = 1) (hπ : ∑ x, π x = 1) (hπpos : ∀ x, 0 < π x) :
    chiSq ν π = ∑ x, ν x ^ 2 / π x - 1 := by
  have he (x : Ω) : π x*(ν x/π x-1)^2=ν x^2/π x-2*ν x+π x := by
    field_simp [(hπpos x).ne']
    <;> ring
  simp only [chiSq,he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,hν,hπ]
  ring

end QueeliusCooling

theorem solution {Ω : Type*} [Fintype Ω] (ν π : Ω → ℝ)
    (hν : ∑ x, ν x=1) (hπ : ∑ x,π x=1) (hπpos : ∀ x,0 < π x) :
    chiSq ν π = ∑ x,ν x^2/π x-1 := QueeliusCooling.chi_identity ν π hν hπ hπpos
#print axioms solution
