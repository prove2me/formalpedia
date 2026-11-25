-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Good.IR_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:42.975021+00:00
-- url     : https://prove2.me/submissions/953c7b43-1399-4e80-8898-5b8ae7ac8738

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
private lemma act_zero_square_integrability {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : act α (0 : Vsp dim) = 0 := by
  first
  | (ext i; simp [act])
  | simp [act]
  | (unfold act; ext i; simp)
private lemma act_add_square_integrability {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  first
  | (ext i; simp [act, mul_add])
  | (unfold act; ext i; simp [mul_add])
private lemma act_real_smul {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (r : ℝ) (v : Vsp dim) :
    act α (r • v) = r • act α v := by
  first
  | (ext i; simp [act, Complex.real_smul]; ring)
  | (ext i; simp [act, mul_smul_comm])
  | (unfold act; ext i; simp [Complex.real_smul]; ring)
end
end ReciprocityTheory.ChartRestriction.G.I2
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
namespace Good
theorem _root_.solution {X : PT E} {c : ℝ} {I : Submodule ℤ (Vsp X.dim)} (hI : Good X c I)
    (α : 𝓞 E) : ∀ v ∈ IR I, act α v ∈ IR I := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hI.stable α x hx)
  | zero => rw [act_zero_square_integrability]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [act_add_square_integrability]; exact add_mem hx hy
  | smul r x _ hx => rw [act_real_smul]; exact Submodule.smul_mem _ r hx
end Good
end ReciprocityTheory.ChartRestriction.G.I2
