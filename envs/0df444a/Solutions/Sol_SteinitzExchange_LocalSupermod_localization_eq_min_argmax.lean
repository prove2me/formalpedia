-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.localization_eq_min_argmax
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:58:49.316333+00:00
-- url     : https://prove2.me/submissions/3e40f730-559e-4856-9464-a9d8f4c07f45

import Definitions.Def_SteinitzExchange_LocalSupermod_Localization
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Mathlib.Tactic
open Set
open SteinitzExchange.LocalSupermod

private theorem finite_affine_min {J : Type*} [Fintype J] [Nonempty J] (a b : J → ℝ) :
    ∃ (j : J) (t : ℝ),0<t ∧ (∀ k,a j ≤ a k) ∧
      (∀ k,a k=a j → b j ≤ b k) ∧ ∀ k,a j+t*b j ≤ a k+t*b k := by
  classical
  obtain ⟨j₀,hj₀,hmin⟩ := Finset.univ.exists_min_image a Finset.univ_nonempty
  let S := Finset.univ.filter (fun j => a j=a j₀)
  have hS : S.Nonempty := ⟨j₀,by simp [S]⟩
  obtain ⟨j,hj,hb⟩ := S.exists_min_image b hS
  have ha : a j=a j₀ := (Finset.mem_filter.mp hj).2
  have hminj (k : J) : a j ≤ a k := ha.symm ▸ hmin k (Finset.mem_univ _)
  have hbmin (k : J) (hk : a k=a j) : b j ≤ b k := hb k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk.trans ha⟩)
  let e : J → ℝ := fun k => if a k=a j then 1 else (a k-a j)/(|b k-b j|+1)
  have hepos (k : J) : 0<e k := by
    dsimp [e]
    split_ifs with hk
    · norm_num
    · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hminj k) (Ne.symm hk))) (by positivity)
  let t := Finset.univ.inf' Finset.univ_nonempty e
  have ht : 0<t := (Finset.lt_inf'_iff _).mpr (fun k _ => hepos k)
  refine ⟨j,t,ht,hminj,hbmin,?_⟩
  intro k
  have htk : t ≤ e k := Finset.inf'_le _ (Finset.mem_univ k)
  by_cases hk : a k=a j
  · rw [hk]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hbmin k hk) ht.le)
  · simp only [e,if_neg hk] at htk
    have htk := (le_div_iff₀ (show 0 < |b k-b j|+1 by positivity)).mp htk
    have hab : b j-b k ≤ |b k-b j| := by rw [abs_sub_comm];exact le_abs_self _
    have hh := mul_le_mul_of_nonneg_left hab ht.le
    nlinarith only [htk,hh,ht]

private theorem pairing_add_left {V : Type*} [Fintype V] (p q z : V → ℝ) :
    pairing (p+q) z=pairing p z+pairing q z := by
  simp only [pairing,Pi.add_apply,add_mul,Finset.sum_add_distrib]

private theorem pairing_sub_left {V : Type*} [Fintype V] (p q z : V → ℝ) :
    pairing (p-q) z=pairing p z-pairing q z := by
  simp only [pairing,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]

private theorem pairing_smul_left {V : Type*} [Fintype V] (t : ℝ) (p z : V → ℝ) :
    pairing (t • p) z=t*pairing p z := by
  simp only [pairing,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]

private theorem perturb_neg {V : Type*} [Fintype V] (g : (V → ℤ) → ℝ) (p : V → ℝ) (x : V → ℤ) :
    perturb g (-p) x=-(pairing p (toReal x)-g x) := by
  simp [perturb,pairing,Finset.sum_neg_distrib]
  ring

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (p₀ p : V → ℝ) :
    IsLeast ((fun x => pairing p (toReal x)) '' (argmaxB B (perturb ω (-p₀)) : Set (V → ℤ)))
      (localization (concaveConj B ω) p₀ p) := by
  classical
  haveI : Nonempty (B : Set (V → ℤ)) := by obtain ⟨x,hx⟩:=hB.1;exact ⟨⟨x,hx⟩⟩
  let a : ↥(B : Set (V → ℤ)) → ℝ := fun x => pairing p₀ (toReal (x : V → ℤ))-ω x
  let b : ↥(B : Set (V → ℤ)) → ℝ := fun x => pairing p (toReal (x : V → ℤ))
  obtain ⟨x,t,ht,hmin,hbmin,htmin⟩ := finite_affine_min a b
  have h0 : concaveConj B ω p₀=a x := le_antisymm (ciInf_le (Set.finite_range a).bddBelow x) (le_ciInf hmin)
  have ht0 : concaveConj B ω (p₀+t • p)=a x+t*b x := by
    have hf (y : (B : Set (V → ℤ))) : pairing (p₀+t • p) (toReal (y : V → ℤ))-ω y=a y+t*b y := by
      rw [pairing_add_left,pairing_smul_left]
      dsimp [a,b]
      ring
    unfold concaveConj
    simp only [hf]
    exact le_antisymm (ciInf_le (Set.finite_range (fun y => a y+t*b y)).bddBelow x) (le_ciInf htmin)
  have hxarg : (x : V → ℤ) ∈ argmaxB B (perturb ω (-p₀)) := by
    apply Finset.mem_filter.mpr
    refine ⟨x.property,?_⟩
    intro y hy
    simp only [perturb_neg]
    exact neg_le_neg (hmin ⟨y,hy⟩)
  have hxsuper : toReal (x : V → ℤ) ∈ superdiff (concaveConj B ω) p₀ := by
    intro q
    have hh := ciInf_le (Set.finite_range (fun y : (B : Set (V → ℤ)) => pairing q (toReal (y : V → ℤ))-ω y)).bddBelow x
    change concaveConj B ω q ≤ pairing q (toReal (x : V → ℤ))-ω x at hh
    rw [h0,pairing_sub_left]
    dsimp [a]
    linarith only [hh]
  have hlow (z : V → ℝ) (hz : z ∈ superdiff (concaveConj B ω) p₀) : b x ≤ pairing p z := by
    have hh := hz (p₀+t • p)
    rw [ht0,h0,pairing_sub_left,pairing_add_left,pairing_smul_left] at hh
    nlinarith only [hh,ht]
  have he : localization (concaveConj B ω) p₀ p=b x := by
    unfold localization
    have hbd : BddBelow ((fun z => pairing p z) '' superdiff (concaveConj B ω) p₀) := by
      refine ⟨b x,?_⟩
      rintro _ ⟨z,hz,rfl⟩
      exact hlow z hz
    apply le_antisymm (csInf_le hbd ⟨toReal (x : V → ℤ),hxsuper,rfl⟩)
    apply le_csInf (show ((fun z => pairing p z) '' superdiff (concaveConj B ω) p₀).Nonempty from ⟨_,⟨_,hxsuper,rfl⟩⟩)
    rintro _ ⟨z,hz,rfl⟩
    exact hlow z hz
  rw [he]
  constructor
  · exact ⟨x,hxarg,rfl⟩
  · rintro _ ⟨y,hy,rfl⟩
    have hy := Finset.mem_filter.mp hy
    apply hbmin ⟨y,hy.1⟩
    apply le_antisymm _ (hmin _)
    have hh := hy.2 x x.property
    simp only [perturb_neg] at hh
    exact neg_le_neg_iff.mp hh
