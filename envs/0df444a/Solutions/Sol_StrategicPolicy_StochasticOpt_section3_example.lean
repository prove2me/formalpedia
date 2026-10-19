-- Prove2me | solution 1 for StrategicPolicy.StochasticOpt.section3_example
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T08:35:36.618388+00:00
-- url     : https://prove2.me/submissions/67bd180a-546e-45ed-b034-ee9d6256a6c6

import Definitions.Def_StrategicPolicy_StochasticOpt_Example
set_option autoImplicit false
open StrategicPolicy.StochasticOpt
namespace QueeliusStrategic

@[simp] theorem fin_three_two (h : 2 < 3) : (⟨2,h⟩ : Fin 3)=2 := rfl

theorem br_max {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ) (i j : Fin m) :
    π j-c i j ≤ π (br c q π i)-c i (br c q π i) := by
  classical
  have h := Finset.min'_mem (tieSet c q π i) (tieSet_nonempty c q π i)
  change br c q π i ∈ tieSet c q π i at h
  have ha := (Finset.mem_filter.mp h).1
  exact (Finset.mem_filter.mp ha).2 j

theorem br_eq_of_max {m : ℕ} [NeZero m] (c : Fin m → Fin m → ℝ) (q π : Fin m → ℝ) (i k : Fin m)
    (hmax : ∀ j, π j-c i j ≤ π k-c i k)
    (hq : ∀ j, j ≠ k → π k-c i k ≤ π j-c i j → q j < q k) : br c q π i=k := by
  classical
  have h := Finset.min'_mem (tieSet c q π i) (tieSet_nonempty c q π i)
  change br c q π i ∈ tieSet c q π i at h
  have ht := (Finset.mem_filter.mp h).2
  have hk : k ∈ argmaxSet c π i := by simp only [argmaxSet,Finset.mem_filter,Finset.mem_univ,true_and];exact hmax
  by_contra hn
  have hh := hq (br c q π i) hn (br_max c q π i k)
  exact (not_lt_of_ge (ht k hk)) hh

set_option maxHeartbeats 800000 in
theorem upper_rigid (π : Fin 3 → ℝ) (hπ : π ∈ Policies 3) :
    u p0 q0 γ0 c0 π ≤ 33/50 ∧
      (33/50 ≤ u p0 q0 γ0 c0 π → π 0=1 ∧ π 1=7/10 ∧ π 2≤2/5) := by
  have hp0 := hπ 0
  have hp1 := hπ 1
  have hp2 := hπ 2
  have hu0 : p0 0*(q0 (br c0 q0 π 0)-γ0)*π (br c0 q0 π 0) ≤ 9/100 := by
    generalize br c0 q0 π 0=b
    have hb := hπ b
    fin_cases b <;> norm_num [p0,q0,γ0,Matrix.cons_val_two] at hb ⊢ <;> linarith
  have h11 := br_max c0 q0 π 1 1
  have h22 := br_max c0 q0 π 2 2
  generalize hb1 : br c0 q0 π 1=b1 at *
  generalize hb2 : br c0 q0 π 2=b2 at *
  unfold u
  norm_num only [Fin.sum_univ_succ,Fin.isValue,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Finset.sum_empty,add_zero]
  rw [hb1,hb2]
  generalize hU : p0 0*(q0 (br c0 q0 π 0)-γ0)*π (br c0 q0 π 0)=U at hu0 ⊢
  clear hU hb1 hb2 hπ
  fin_cases b1 <;> fin_cases b2 <;>
    norm_num [p0,q0,γ0,c0,Fin.isValue,Matrix.cons_val_two] at * <;>
    constructor
  all_goals first | linarith | (intro hu; refine ⟨?_,?_,?_⟩ <;> linarith)

theorem value_of_shape (π : Fin 3 → ℝ) (hπ : π ∈ Policies 3)
    (h0 : π 0=1) (h1 : π 1=7/10) (h2 : π 2≤2/5) : u p0 q0 γ0 c0 π=33/50 := by
  have hp2 := hπ 2
  have hb0 : br c0 q0 π 0=0 := by
    apply br_eq_of_max
    · intro j; fin_cases j <;> norm_num [c0,Fin.isValue,Matrix.cons_val_two,h0,h1] <;> linarith only [h2]
    · intro j hj hs; fin_cases j <;> norm_num [q0,c0,Fin.isValue,Matrix.cons_val_two,h0,h1] at hs <;>
        norm_num [q0,c0,Fin.isValue,Matrix.cons_val_two,h0,h1] at hj <;>
        norm_num [q0,c0,Fin.isValue,Matrix.cons_val_two,h0,h1] <;> linarith only [hs]
  have hb1 : br c0 q0 π 1=0 := by
    apply br_eq_of_max
    · intro j; fin_cases j <;> norm_num [c0,Fin.isValue,Matrix.cons_val_two,h0,h1] <;> linarith only [h2]
    · intro j hj hs; fin_cases j <;> norm_num [q0,c0,Fin.isValue,Matrix.cons_val_two,h0,h1] at hs <;>
        norm_num [q0,c0,Fin.isValue,Matrix.cons_val_two,h0,h1] at hj <;>
        norm_num [q0,c0,Fin.isValue,Matrix.cons_val_two,h0,h1] <;> linarith only [hs]
  have hb2 : br c0 q0 π 2=1 := by
    apply br_eq_of_max
    · intro j; fin_cases j <;> norm_num [c0,Fin.isValue,Matrix.cons_val_two,h0,h1] <;> linarith only [h2]
    · intro j hj hs; fin_cases j <;> norm_num [q0,c0,Fin.isValue,Matrix.cons_val_two,h0,h1] at hs <;>
        norm_num [q0,c0,Fin.isValue,Matrix.cons_val_two,h0,h1] at hj <;>
        norm_num [q0,c0,Fin.isValue,Matrix.cons_val_two,h0,h1] <;> linarith only [hs]
  unfold u
  norm_num only [Fin.sum_univ_succ,Fin.isValue,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Finset.sum_empty,add_zero]
  rw [hb0,hb1,hb2]
  norm_num [p0,q0,γ0,Matrix.cons_val_two,h0,h1]

end QueeliusStrategic
#print axioms QueeliusStrategic.upper_rigid
#print axioms QueeliusStrategic.value_of_shape

theorem solution :
    (∀ π ∈ Policies 3,
      IsMaxOn (u p0 q0 γ0 c0) (Policies 3) π ↔ (π 0 = 1 ∧ π 1 = 7 / 10 ∧ π 2 ≤ 2 / 5)) ∧
    (∀ π ∈ Policies 3, IsMaxOn (u p0 q0 γ0 c0) (Policies 3) π → ¬ IsDeterministic π) ∧
    u p0 q0 γ0 c0 ![1, 7 / 10, 0] = 33 / 50 := by
  have hw : (![1,7/10,0] : Fin 3 → ℝ) ∈ Policies 3 := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_two]
  have hv : u p0 q0 γ0 c0 ![1,7/10,0]=33/50 :=
    QueeliusStrategic.value_of_shape _ hw (by norm_num) (by norm_num) (by norm_num [Matrix.cons_val_two])
  have hc (π : Fin 3 → ℝ) (hπ : π ∈ Policies 3) :
      IsMaxOn (u p0 q0 γ0 c0) (Policies 3) π ↔ π 0=1 ∧ π 1=7/10 ∧ π 2≤2/5 := by
    constructor
    · intro hmax
      apply (QueeliusStrategic.upper_rigid π hπ).2
      simpa only [hv] using (isMaxOn_iff.mp hmax) ![1,7/10,0] hw
    · rintro ⟨h0,h1,h2⟩
      apply isMaxOn_iff.mpr
      intro τ hτ
      rw [QueeliusStrategic.value_of_shape π hπ h0 h1 h2]
      exact (QueeliusStrategic.upper_rigid τ hτ).1
  refine ⟨hc,?_,hv⟩
  intro π hπ hmax hd
  have hp := ((hc π hπ).mp hmax).2.1
  rcases hd 1 with hh | hh <;> linarith only [hh,hp]

#print axioms solution
