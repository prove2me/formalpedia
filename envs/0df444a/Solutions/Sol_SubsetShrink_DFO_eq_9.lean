-- Prove2me | solution 1 for SubsetShrink.DFO.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:45:23.688283+00:00
-- url     : https://prove2.me/submissions/f75b9ccb-edbd-4557-bd85-f540e4883db8

import Mathlib
import Definitions.Def_SubsetShrink_DFO_Model

open scoped InnerProductSpace
namespace QueeliusSmooth

theorem scalar_upper (g dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (dg t) t)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, dg t-dg 0 ≤ L*t) :
    g 1-g 0 ≤ dg 0+L/2 := by
  let f := fun t => g t-dg 0*t-L/2*t^2
  have hf (t : ℝ) : HasDerivAt f (dg t-dg 0-L*t) t := by
    convert! ((hd t).sub ((hasDerivAt_id t).const_mul (dg 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (L/2)) using 1
    dsimp [f]
    ring
  have ha : AntitoneOn f (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hf t).continuousAt.continuousWithinAt
    · exact fun t _ => (hf t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hf t).deriv]
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      linarith only [hb t ht']
  have h := ha (by simp : (0 : ℝ) ∈ Set.Icc 0 1) (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  dsimp [f] at h
  norm_num at h
  linarith

theorem scalar_abs (g dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (dg t) t)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |dg t-dg 0| ≤ L*t) :
    |g 1-g 0-dg 0| ≤ L/2 := by
  have hu := scalar_upper g dg L hd (fun t ht => (le_abs_self _).trans (hb t ht))
  have hl := scalar_upper (fun t => -g t) (fun t => -dg t) L (fun t => (hd t).neg)
    (fun t ht => by have hh := (abs_le.mp (hb t ht)).1; linarith only [hh])
  apply abs_le.mpr
  constructor <;> linarith

theorem gradient_taylor {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (f : X → ℝ) (L : ℝ) (hf : Differentiable ℝ f)
    (hLip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x y : X) :
    |f y-f x-⟪gradient f x,y-x⟫_ℝ| ≤ L/2*‖y-x‖^2 := by
  let d := y-x
  let g := fun t : ℝ => f (x+t • d)
  let dg := fun t : ℝ => ⟪gradient f (x+t • d),d⟫_ℝ
  have hd (t : ℝ) : HasDerivAt g (dg t) t := by
    have hh := (hf _).hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const d).const_add x)
    convert! hh using 1
    simp only [dg,inner_gradient_left,id_eq,one_smul]
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : |dg t-dg 0| ≤ (L*‖d‖^2)*t := by
    dsimp [dg]
    simp only [zero_smul,add_zero,←inner_sub_left]
    calc
      _ ≤ ‖gradient f (x+t • d)-gradient f x‖*‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (L*‖(x+t • d)-x‖)*‖d‖ := mul_le_mul_of_nonneg_right (hLip _ _) (norm_nonneg _)
      _ = _ := by rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1]; ring
  have hh := scalar_abs g dg (L*‖d‖^2) hd hb
  dsimp [g,dg,d] at hh
  simp only [zero_smul,one_smul,add_zero,add_sub_cancel] at hh
  convert hh using 1 <;> ring


end QueeliusSmooth

open SubsetShrink.DFO

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Rahul Mazumder, Peter Radchenko and Antoine Dedieu.
theorem solution {p : ℕ} (f : E p → ℝ) (L0 L : ℝ)
    (hdiff : Differentiable ℝ f) (_hconv : ConvexOn ℝ Set.univ f) (_hL0nn : 0 ≤ L0)
    (hL0 : ∀ β α : E p, ‖gradient f β-gradient f α‖ ≤ L0*‖β-α‖)
    (hL : L0 ≤ L) : ∀ β α : E p, f β ≤ QL f L β α := by
  intro β α
  have ht := (le_abs_self _).trans (QueeliusSmooth.gradient_taylor f L0 hdiff hL0 α β)
  have hm := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖β-α‖)
  unfold QL
  linarith only [ht,hm]

#print axioms solution
