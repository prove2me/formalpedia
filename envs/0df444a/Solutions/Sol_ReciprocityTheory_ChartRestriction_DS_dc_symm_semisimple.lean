-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_symm_semisimple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:42.776561+00:00
-- url     : https://prove2.me/submissions/0723b36a-d083-4307-8420-517695521af6

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_symm_eig_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {T : Module.End ℂ Y} {S W : Submodule ℂ Y}
  {Q : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (Q f f).re)
    (hsym : ∀ f ∈ S, ∀ g ∈ S, Q (T f) g = Q f (T g)) (hTS : ∀ f ∈ S, T f ∈ S) (μ : ℂ) :
    ∀ k : ℕ, ∀ x ∈ S, ((T - μ • 1) ^ k) x = 0 → T x = μ • x := by
  intro k
  induction k with
  | zero => intro x _ hx; simp at hx; simp [hx]
  | succ k ih =>
    intro x hx h
    set u := T x - μ • x with hu
    have huS : u ∈ S := S.sub_mem (hTS x hx) (S.smul_mem μ hx)
    have hk : ((T - μ • 1) ^ k) u = 0 := by
      rw [pow_succ, Module.End.mul_apply] at h
      simpa [hu] using h
    have hue : T u = μ • u := ih u huS hk
    by_contra hne
    have hu0 : u ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
    have hr := dc_symm_eig_real hpos hsym huS hu0 hue
    have h1 : Q u u = 0 := by
      have e1 : Q u u = Q (T x) u - Q (μ • x) u := by
        rw [← LinearMap.sub_apply, ← Q.map_sub]
      rw [e1, hsym x hx u huS, hue, (Q x).map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        smul_eq_mul]
      rw [← hr]; simp
    have := hpos u huS hu0
    rw [h1] at this; simp at this
end ReciprocityTheory.ChartRestriction.DS
