-- Prove2me | solution 1 for TopDownParity1043.Main.random_restriction_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:07:37.256699+00:00
-- url     : https://prove2.me/submissions/b96a1ac3-523d-409d-b047-e915f653f6c1

import Mathlib
import Definitions.Def_TopDownParity1043_Main_RandomSets

set_option autoImplicit false
open TopDownParity1043.Main

private noncomputable def expOn {V : Type} [DecidableEq V]
    (p : ℝ) (U : Finset V) (f : Finset V → ℝ) : ℝ :=
  ∑ R ∈ U.powerset, p ^ R.card * (1-p) ^ (U.card-R.card) * f R

private theorem expOn_congr {V : Type} [DecidableEq V]
    (p : ℝ) (U : Finset V) (f g : Finset V → ℝ) (h : ∀ R ⊆ U, f R = g R) :
    expOn p U f = expOn p U g := by
  apply Finset.sum_congr rfl
  intro R hR
  rw [h R (Finset.mem_powerset.mp hR)]

private theorem expOn_add {V : Type} [DecidableEq V]
    (p : ℝ) (U : Finset V) (f g : Finset V → ℝ) :
    expOn p U (fun R => f R + g R) = expOn p U f + expOn p U g := by
  simp only [expOn, mul_add, Finset.sum_add_distrib]

private theorem expOn_mul {V : Type} [DecidableEq V]
    (p : ℝ) (U : Finset V) (c : ℝ) (f : Finset V → ℝ) :
    expOn p U (fun R => c * f R) = c * expOn p U f := by
  simp only [expOn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R hR
  ring

private theorem expOn_insert {V : Type} [DecidableEq V]
    (p : ℝ) (s : Finset V) (a : V) (ha : a ∉ s) (f : Finset V → ℝ) :
    expOn p (insert a s) f =
      (1-p) * expOn p s f + p * expOn p s (fun R => f (insert a R)) := by
  classical
  unfold expOn
  rw [Finset.powerset_insert, Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [Finset.card_insert_of_notMem ha, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro R hR
        have hc : R.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hR)
        rw [show s.card + 1 - R.card = s.card - R.card + 1 by omega, pow_succ]
        ring
      · apply Finset.sum_congr rfl
        intro R hR
        have haR := Finset.notMem_of_mem_powerset_of_notMem hR ha
        rw [Finset.card_insert_of_notMem haR]
        rw [show s.card + 1 - (R.card + 1) = s.card-R.card by omega, pow_succ]
        ring
    · intro R hR T hT heq
      ext x
      have haR := Finset.notMem_of_mem_powerset_of_notMem hR ha
      have haT := Finset.notMem_of_mem_powerset_of_notMem hT ha
      by_cases hx : x = a
      · subst x
        simp [haR, haT]
      · simpa [hx] using Finset.ext_iff.mp heq x
  · apply Finset.disjoint_left.mpr
    intro R hR hRi
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hRi
    exact (Finset.notMem_of_mem_powerset_of_notMem hR ha) (Finset.mem_insert_self a T)

private theorem expOn_comm {V : Type} [DecidableEq V]
    (p q : ℝ) (U : Finset V) (F : Finset V → Finset V → ℝ) :
    expOn p U (fun P => expOn q U (fun Q => F P Q)) =
      expOn q U (fun Q => expOn p U (fun P => F P Q)) := by
  unfold expOn
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Q hQ
  apply Finset.sum_congr rfl
  intro P hP
  ring

private theorem coupling_on {V : Type} [DecidableEq V]
    (U : Finset V) (p q s r : ℝ) (hs : s = p + q - p*q) (hr : s*r = p*(1-q))
    (F : Finset V → Finset V → ℝ) :
    expOn p U (fun P => expOn q U (fun Q => F (P ∪ Q) (P \ Q))) =
      expOn s U (fun S => expOn r U (fun T => F S (S ∩ T))) := by
  classical
  induction U using Finset.induction generalizing F with
  | empty => simp [expOn]
  | @insert a U ha ih =>
    rw [expOn_insert p U a ha, expOn_insert s U a ha]
    simp_rw [expOn_insert q U a ha, expOn_insert r U a ha]
    simp_rw [expOn_add, expOn_mul]
    have h00 := ih F
    have h10 := ih (fun S R => F (insert a S) (insert a R))
    have h01 := ih (fun S R => F (insert a S) R)
    have haP : ∀ P ⊆ U, a ∉ P := fun P hP => fun hh => ha (hP hh)
    have hleft10 :
        expOn p U (fun P => expOn q U (fun Q => F (insert a P ∪ Q) (insert a P \ Q))) =
          expOn p U (fun P => expOn q U (fun Q => F (insert a (P ∪ Q)) (insert a (P \ Q)))) := by
      apply expOn_congr
      intro P hP
      apply expOn_congr
      intro Q hQ
      congr 1 <;> ext x <;> by_cases hx : x = a <;> simp_all
    have hleft01 :
        expOn p U (fun P => expOn q U (fun Q => F (P ∪ insert a Q) (P \ insert a Q))) =
          expOn p U (fun P => expOn q U (fun Q => F (insert a (P ∪ Q)) (P \ Q))) := by
      apply expOn_congr
      intro P hP
      apply expOn_congr
      intro Q hQ
      congr 1 <;> ext x <;> by_cases hx : x = a <;> simp_all
    have hleft11 :
        expOn p U (fun P => expOn q U (fun Q => F (insert a P ∪ insert a Q) (insert a P \ insert a Q))) =
          expOn p U (fun P => expOn q U (fun Q => F (insert a (P ∪ Q)) (P \ Q))) := by
      apply expOn_congr
      intro P hP
      apply expOn_congr
      intro Q hQ
      congr 1 <;> ext x <;> by_cases hx : x = a <;> simp_all
    have hright01 :
        expOn s U (fun S => expOn r U (fun T => F S (S ∩ insert a T))) =
          expOn s U (fun S => expOn r U (fun T => F S (S ∩ T))) := by
      apply expOn_congr
      intro S hS
      apply expOn_congr
      intro T hT
      congr 1
      ext x
      by_cases hx : x = a <;> simp_all
    have hright10 :
        expOn s U (fun S => expOn r U (fun T => F (insert a S) (insert a S ∩ T))) =
          expOn s U (fun S => expOn r U (fun T => F (insert a S) (S ∩ T))) := by
      apply expOn_congr
      intro S hS
      apply expOn_congr
      intro T hT
      congr 1
      ext x
      by_cases hx : x = a <;> simp_all
    simp_rw [← Finset.insert_inter_distrib]
    rw [hleft10, hleft01, hleft11, hright01, hright10, h00, h10, h01]
    have hcoef : s*(1-r) = q := by nlinarith [hs, hr]
    let E0 := expOn s U (fun S => expOn r U (fun T => F S (S ∩ T)))
    let E1 := expOn s U (fun S => expOn r U (fun T => F (insert a S) (S ∩ T)))
    let E2 := expOn s U (fun S => expOn r U (fun T => F (insert a S) (insert a (S ∩ T))))
    change (1-p)*((1-q)*E0+q*E1) + p*((1-q)*E2+q*E1) =
      (1-s)*((1-r)*E0+r*E0) + s*((1-r)*E1+r*E2)
    calc
      _ = (1-s)*E0 + q*E1 + p*(1-q)*E2 := by rw [hs]; ring
      _ = _ := by rw [← hr, ← hcoef]; ring

private theorem expOn_univ {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (f : Finset V → ℝ) :
    expOn (p : ℝ) Finset.univ f = ∑ R : Finset V, setWeight p R * f R := by
  classical
  have hu : (Finset.univ : Finset V).powerset = Finset.univ := by ext R; simp
  simp only [expOn, hu, Finset.card_univ, setWeight]

private theorem expOn_inter {V : Type} [DecidableEq V]
    (U S : Finset V) (p : ℝ) (f : Finset V → ℝ) :
    expOn p U (fun T => f (T ∩ S)) = expOn p (U ∩ S) f := by
  classical
  induction U using Finset.induction generalizing f with
  | empty => simp [expOn]
  | @insert a U ha ih =>
    rw [expOn_insert p U a ha]
    by_cases haS : a ∈ S
    · rw [Finset.insert_inter_of_mem haS,
        expOn_insert p (U ∩ S) a (by simp [ha]), ih]
      congr 1
      congr 1
      calc
        expOn p U (fun R => f (insert a R ∩ S)) =
            expOn p U (fun R => f (insert a (R ∩ S))) := by
          apply expOn_congr
          intro R hR
          rw [Finset.insert_inter_of_mem haS]
        _ = _ := ih (fun R => f (insert a R))
    · rw [Finset.insert_inter_of_notMem haS, ih]
      have he : expOn p U (fun R => f (insert a R ∩ S)) = expOn p (U ∩ S) f := by
        calc
          expOn p U (fun R => f (insert a R ∩ S)) = expOn p U (fun R => f (R ∩ S)) := by
            apply expOn_congr
            intro R hR
            rw [Finset.insert_inter_of_notMem haS]
          _ = _ := ih f
      rw [he]
      ring

private noncomputable def subsetsEquiv {V : Type} [DecidableEq V] (S : Finset V) :
    Finset S ≃ ↥S.powerset where
  toFun R := ⟨R.map (Function.Embedding.subtype _), by
    rw [Finset.mem_powerset]
    intro v hv
    exact Finset.property_of_mem_map_subtype R hv⟩
  invFun T := T.1.subtype (fun v => v ∈ S)
  left_inv R := by
    ext v
    simp only [Finset.mem_subtype, Finset.mem_map]
    constructor
    · rintro ⟨w,hw,heq⟩
      have he : w = v := Subtype.ext heq
      simpa [he] using hw
    · intro hv
      exact ⟨v,hv,rfl⟩
  right_inv T := by
    apply Subtype.ext
    exact Finset.subtype_map_of_mem (Finset.mem_powerset.mp T.2)

private theorem expOn_subtype {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (p : Bias) (f : Finset V → ℝ) :
    expOn (p : ℝ) S f =
      ∑ R : Finset S, setWeight p R * f (R.map (Function.Embedding.subtype _)) := by
  classical
  unfold expOn
  rw [← Finset.sum_coe_sort, ← (subsetsEquiv S).sum_comp]
  apply Finset.sum_congr rfl
  intro R hR
  change _ * f (R.map (Function.Embedding.subtype _)) = _
  have hc : ((subsetsEquiv S) R).1.card = R.card := by
    change (R.map (Function.Embedding.subtype _)).card = R.card
    exact Finset.card_map _
  simp only [setWeight, hc, Fintype.card_coe]

theorem random_set_restriction (V : Type) [Fintype V] [DecidableEq V]
    (p : Bias) (S : Finset V) (f : Finset V → ℝ) :
    (∑ T : Finset V, setWeight p T * f (T ∩ S)) =
      ∑ R : Finset S, setWeight p R * f (R.map (Function.Embedding.subtype _)) := by
  rw [← expOn_univ p (fun T => f (T ∩ S)), expOn_inter, Finset.univ_inter,
    expOn_subtype]

theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (p q s r : Bias) (hs : (s : ℝ) = (p : ℝ) + (q : ℝ) - (p : ℝ)*(q : ℝ))
    (hr : (s : ℝ)*(r : ℝ) = (p : ℝ)*(1-(q : ℝ)))
    (F : Finset V → Finset V → ℝ) :
    (∑ P : Finset V, setWeight p P *
      ∑ Q : Finset V, setWeight q Q * F (P ∪ Q) (P \ Q)) =
    (∑ S : Finset V, setWeight s S *
      ∑ T : Finset V, setWeight r T * F S (S ∩ T)) := by
  have h := coupling_on (Finset.univ : Finset V) (p : ℝ) (q : ℝ) (s : ℝ) (r : ℝ) hs hr F
  simpa only [expOn_univ] using h
