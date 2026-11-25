-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_span_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:45:30.623803+00:00
-- url     : https://prove2.me/submissions/6b550e6e-526f-4866-977b-262f0ac532f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_isU_uMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_act_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_act_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_fg_div_eq_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution [IsCMField E] {X : PT E} (I : Submodule ℤ (Vsp X.dim)) (r1 : ℕ) (hr1 : 2 ≤ r1)
    (a yb : Fin X.r → Vsp X.dim) (hyb : ∀ j, yb j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) :
    Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E,
      IsU I (act α (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) w} = IR I := by
  have huniq : ∀ x w, IsU I x w → w = uMap I x := by
    rintro x w ⟨hw, hwa⟩
    have hu := isU_uMap I x
    have hd : w - uMap I x ∈ IR I := (IR I).sub_mem hw hu.1
    have horth : ∀ b ∈ IR I, inner ℝ (w - uMap I x) b = 0 := fun b hb => by
      rw [inner_sub_left, hwa b hb, hu.2 b hb, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero (𝕜 := ℝ).mp (horth _ hd))
  have hset : {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) w} =
      Set.range (fun p : Fin X.r × 𝓞 E =>
        uMap I (act p.2 (((r1 : ℂ) ^ 2) • a p.1 - ((r1 : ℂ) ^ 2) • yb p.1))) := by
    ext w
    constructor
    · rintro ⟨j, α, h⟩
      exact ⟨(j, α), (huniq _ _ h).symm⟩
    · rintro ⟨⟨j, α⟩, rfl⟩
      exact ⟨j, α, isU_uMap I _⟩
  set T : Submodule ℝ (Vsp X.dim) := Submodule.span ℝ (Set.range fun p : Fin X.r × 𝓞 E =>
    act p.2 (((r1 : ℂ) ^ 2) • a p.1 - ((r1 : ℂ) ^ 2) • yb p.1)) with hT
  let f0 : Vsp X.dim →ₗ[ℝ] Vsp X.dim := LinearMap.id - (T.starProjection : Vsp X.dim →ₗ[ℝ] Vsp X.dim)
  have hf0T : ∀ v ∈ T, f0 v = 0 := fun v hv => by
    have h := Submodule.starProjection_mem_subspace_eq_self (K := T) ⟨v, hv⟩
    show v - T.starProjection v = 0
    rw [show ((⟨v, hv⟩ : T) : Vsp X.dim) = v from rfl] at h
    rw [h, sub_self]
  have hf0inv : ∀ v, f0 v = 0 → v ∈ T := fun v hv => by
    have h : v - T.starProjection v = 0 := hv
    rw [sub_eq_zero.mp h]
    exact T.starProjection_apply_mem v
  let f : Vsp X.dim →ₗ[ℤ] Vsp X.dim := f0.toAddMonoidHom.toIntLinearMap
  have hsq : ∀ z : Vsp X.dim, ((r1 : ℂ) ^ 2) • z = r1 • r1 • z := fun z => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul ℂ, sq, mul_smul]
  have hLfg : X.L.FG := Submodule.fg_span (Set.finite_range X.b)
  have hM := tof_fg_div_eq_bot (X.L.map f) (hLfg.map f) r1 hr1 (by
    rintro m ⟨x, hx, rfl⟩
    obtain ⟨c, y, hy, hxe⟩ := hgen x hx
    refine ⟨f (y + ∑ j, r1 • act (c j) (yb j)),
      ⟨_, X.L.add_mem hy (X.L.sum_mem fun j _ => nsmul_mem (X.stable _ _ (hyb j)) r1), rfl⟩, ?_⟩
    have e1 : ∀ j, act (c j) (((r1 : ℂ) ^ 2) • a j) =
        act (c j) (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j) + r1 • r1 • act (c j) (yb j) := by
      intro j
      rw [← hsq, ← tof_act_smul, ← tof_act_add, sub_add_cancel]
    have hz : ∀ j, f (act (c j) (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) = 0 := fun j =>
      hf0T _ (Submodule.subset_span ⟨(j, c j), rfl⟩)
    rw [hxe]
    simp_rw [e1]
    rw [Finset.sum_add_distrib, Nat.cast_smul_eq_nsmul ℂ]
    simp only [map_add, map_sum, map_nsmul, hz, Finset.sum_const_zero, zero_add, smul_add, Finset.smul_sum]
    abel)
  have hLT : ∀ x ∈ X.L, x ∈ T := fun x hx => hf0inv x (by
    have h : f x ∈ X.L.map f := ⟨x, hx, rfl⟩
    rw [hM] at h
    exact (Submodule.mem_bot ℤ).mp h)
  have hTtop : T = ⊤ := by
    rw [eq_top_iff, ← X.b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hLT _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hset]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact (isU_uMap I _).1
  · intro v hv
    have hv' : uMap I (Complex.I • v) = v := by
      show (IR I).starProjection ((-Complex.I) • Complex.I • v) = v
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      exact Submodule.starProjection_mem_subspace_eq_self (K := IR I) ⟨v, hv⟩
    rw [← hv']
    have hIv : Complex.I • v ∈ T := by rw [hTtop]; exact Submodule.mem_top
    have h2 : uMap I (Complex.I • v) ∈ T.map (uMap I) := ⟨_, hIv, rfl⟩
    rw [hT, Submodule.map_span, ← Set.range_comp] at h2
    exact h2
end ReciprocityTheory.ChartRestriction.G.I2
