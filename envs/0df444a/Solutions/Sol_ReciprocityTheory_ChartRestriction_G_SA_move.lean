-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:22:37.903802+00:00
-- url     : https://prove2.me/submissions/1f56f215-6e24-4e0d-b401-8f86f3b86de7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SubProjOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SUEqClosure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_stage1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_stage2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_stage3
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_stage4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_stage5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x) {i2 : K} (h2i : 2 * i2 = 1) {δ : K} (hδ : IsUnit δ)
  (hσδ : σ δ = -δ) [IsReduced K]
  (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
include hσ hJ he hff hef hfix h2i hδ hσδ
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {s : ℕ} {a : Fin s → ι → K} (hae : ∀ j, hf σ J (a j) e = 0)
    (haf : ∀ j, hf σ J (a j) f = 0) (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal →
      m₂.IsMaximal → m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
    {b : ι → K} (hb : ∀ j, hf σ J b (a j) = 0) (hν : IsUnit (hf σ J b b)) :
    Reach σ J e f a b (e + (hf σ J b b * i2) • f) := by
  obtain ⟨b1, r1, c1⟩ : ∃ b', Reach σ J e f a b b' ∧ IsCoprime (hf σ J b' f) (hf σ J b' e) := by
    apply stage1 (hmax := hmax) (hb := hb) (hν := hν) <;> first | exact hδ | exact hσδ | assumption
  have i1 : (∀ j, hf σ J b1 (a j) = 0) ∧ hf σ J b1 b1 = hf σ J b b := by
    apply reach_inv (h := r1) (hb := hb) <;> first | exact hδ | exact hσδ | assumption
  obtain ⟨b2, r2, u2⟩ : ∃ b', Reach σ J e f a b1 b' ∧ IsUnit (hf σ J b' e) := by
    apply stage2 (hcop := c1) <;> first | exact hδ | exact hσδ | assumption
  have i2' : (∀ j, hf σ J b2 (a j) = 0) ∧ hf σ J b2 b2 = hf σ J b1 b1 := by
    apply reach_inv (h := r2) (hb := i1.1) <;> first | exact hδ | exact hσδ | assumption
  obtain ⟨b3, r3, f3, u3⟩ : ∃ b', Reach σ J e f a b2 b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧
      IsUnit (hf σ J b' e) := by
    apply stage3 (hb := i2'.1) (hβ := u2) <;> first | exact hδ | exact hσδ | assumption
  have i3 : (∀ j, hf σ J b3 (a j) = 0) ∧ hf σ J b3 b3 = hf σ J b2 b2 := by
    apply reach_inv (h := r3) (hb := i2'.1) <;> first | exact hδ | exact hσδ | assumption
  have c3 : IsCoprime (hf σ J b3 f) (hf σ J b3 e) :=
    ⟨0, ↑u3.unit⁻¹, by rw [zero_mul, zero_add]; exact u3.val_inv_mul⟩
  obtain ⟨b4, r4, f4, u4⟩ : ∃ b', Reach σ J e f a b3 b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧
      IsUnit (hf σ J b' f) := by
    apply stage4 (hform := f3) (hcop := c3) <;> first | exact hδ | exact hσδ | assumption
  have i4 : (∀ j, hf σ J b4 (a j) = 0) ∧ hf σ J b4 b4 = hf σ J b3 b3 := by
    apply reach_inv (h := r4) (hb := i3.1) <;> first | exact hδ | exact hσδ | assumption
  have r5 : Reach σ J e f a b4 (e + (hf σ J b4 b4 * i2) • f) := by
    apply stage5 (hform := f4) (hα := u4) <;> first | exact hδ | exact hσδ | assumption
  have hν4 : hf σ J b4 b4 = hf σ J b b := by rw [i4.2, i3.2, i2'.2, i1.2]
  rw [hν4] at r5
  have t4 : Reach σ J e f a b3 (e + (hf σ J b b * i2) • f) := by
    apply reach_trans (h1 := r4) (h2 := r5) <;> first | exact hδ | exact hσδ | assumption
  have t3 : Reach σ J e f a b2 (e + (hf σ J b b * i2) • f) := by
    apply reach_trans (h1 := r3) (h2 := t4) <;> first | exact hδ | exact hσδ | assumption
  have t2 : Reach σ J e f a b1 (e + (hf σ J b b * i2) • f) := by
    apply reach_trans (h1 := r2) (h2 := t3) <;> first | exact hδ | exact hσδ | assumption
  apply reach_trans (h1 := r1) (h2 := t2) <;> first | exact hδ | exact hσδ | assumption
end ReciprocityTheory.ChartRestriction.G.SA
