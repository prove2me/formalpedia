-- Prove2me | solution 1 for StrategicPolicy.StochasticOpt.nonstrategic_optimum
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T08:35:16.150726+00:00
-- url     : https://prove2.me/submissions/2a9162af-83b2-4c86-aaf1-66e811d5cdad

import Definitions.Def_StrategicPolicy_StochasticOpt_Example
set_option autoImplicit false
open StrategicPolicy.StochasticOpt
namespace QueeliusStrategicSupport
@[simp] theorem fin_three_two (h : 2 < 3) : (⟨2,h⟩ : Fin 3)=2 := rfl

theorem cost : OMCost q0 c0 ∧ StandingI q0 c0 := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro i; fin_cases i <;> norm_num [c0,Matrix.cons_val_two]
    · intro i j k hij hjk hik
      fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [q0,c0,Matrix.cons_val_two] at *
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num [q0,c0,Matrix.cons_val_two] at *
  · intro i j hij hq
    fin_cases i <;> fin_cases j <;> norm_num [q0,c0,Matrix.cons_val_two] at *

theorem eval_ns (π : Fin 3 → ℝ) : uNS p0 q0 γ0 π=9/100*π 0+6/25*π 1+3/20*π 2 := by
  norm_num [uNS,p0,q0,γ0,Fin.sum_univ_succ,Matrix.cons_val_two]
  ring

theorem nonstrategic : ∀ π ∈ Policies 3,
    IsMaxOn (uNS p0 q0 γ0) (Policies 3) π ↔ π=fun _=>1 := by
  intro π hπ
  have h0 := hπ 0
  have h1 := hπ 1
  have h2 := hπ 2
  have hone : (fun _ : Fin 3 => (1:ℝ)) ∈ Policies 3 := fun _ => ⟨by norm_num,le_rfl⟩
  constructor
  · intro hm
    have hh := (isMaxOn_iff.mp hm) _ hone
    rw [eval_ns,eval_ns] at hh
    have hp0 : π 0=1 := by linarith [h0.2,h1.2,h2.2]
    have hp1 : π 1=1 := by linarith [h0.2,h1.2,h2.2]
    have hp2 : π 2=1 := by linarith [h0.2,h1.2,h2.2]
    funext i
    fin_cases i <;> simpa using (show π _=1 from by assumption)
  · rintro rfl
    apply isMaxOn_iff.mpr
    intro τ hτ
    rw [eval_ns,eval_ns]
    have ht0 := (hτ 0).2
    have ht1 := (hτ 1).2
    have ht2 := (hτ 2).2
    linarith

end QueeliusStrategicSupport
#print axioms QueeliusStrategicSupport.cost
#print axioms QueeliusStrategicSupport.nonstrategic

theorem solution : ∀ π ∈ Policies 3, IsMaxOn (uNS p0 q0 γ0) (Policies 3) π ↔ π=fun _=>1 := QueeliusStrategicSupport.nonstrategic
#print axioms solution
