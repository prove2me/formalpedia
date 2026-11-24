-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.eq_zero_of_l2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:58.883829+00:00
-- url     : https://prove2.me/submissions/e0ed5d4c-c27d-43c3-b2c3-94518c75a754

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_jof_Hf_self_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_l2_norm_fundamental_domain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (hP : Ext.PackingCount) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec q 1) (h0 : X.l2 q s = 0) : s = 0 := by
  have hd : Differentiable ℂ s := (show Differentiable ℂ s ∧ _ from hs).1
  set g : Vsp X.dim → ℂ := fun z => s (fun _ => z) with hgdef
  have hgc : Continuous g := (hd.comp (differentiable_pi.mpr fun _ => differentiable_id)).continuous
  have hq' : ∀ γ ∈ X.L, ∀ x, g (x + γ) = ((X.eps γ : ℂ)) ^ q *
      cexp (q * Real.pi * Hf x γ + q * Real.pi * Hf γ γ / 2) * g x := by
    intro γ hγ x
    have := (show Differentiable ℂ s ∧ ∀ γ' : Fin 1 → Vsp X.dim, (∀ j, γ' j ∈ X.L) →
        ∀ w, s (w + γ') = (∏ j, (X.eps (γ' j) : ℂ)) ^ q *
          cexp (q * Real.pi * HC w γ' + q * Real.pi * HC γ' γ' / 2) * s w from hs).2
      (fun _ => γ) (fun _ => hγ) (fun _ => x)
    simpa [HC, Pi.add_def, hgdef] using this
  have hne : ∀ γ ∈ X.L, ∀ x, g (x + γ) = 0 ↔ g x = 0 := by
    intro γ hγ x
    rw [hq' γ hγ x]
    have h1 : (X.eps γ : ℂ) ≠ 0 := by rcases X.eps_pm γ hγ with h | h <;> simp [h]
    simp [h1, Complex.exp_ne_zero]
  have hpx : ∀ x, X.ptN2 q s (fun _ => x) = ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) := by
    intro x
    have hre : (HC (fun _ : Fin 1 => x) (fun _ => x)).re = ‖x‖ ^ 2 := by simp [HC, jof_Hf_self_re]
    simp only [PT.ptN2, hre, hgdef]
  have hl := l2_norm_fundamental_domain X q s
  rw [h0] at hl
  simp only [hpx] at hl
  set D := ZSpan.fundamentalDomain X.b with hD
  have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet X.b
  have hDb : Bornology.IsBounded D := ZSpan.fundamentalDomain_isBounded X.b
  haveI : MeasureTheory.VAddInvariantMeasure (Submodule.span ℤ (Set.range X.b)) (Vsp X.dim)
      MeasureTheory.volume :=
    ⟨fun c s _ => by
      simpa [Submodule.vadd_def, vadd_eq_add] using
        MeasureTheory.measure_preimage_add MeasureTheory.volume (c : Vsp X.dim) s⟩
  have hfd := ZSpan.isAddFundamentalDomain X.b (MeasureTheory.volume : MeasureTheory.Measure (Vsp X.dim))
  have hD0 : MeasureTheory.volume D ≠ 0 := hfd.measure_ne_zero (NeZero.ne _)
  have hDt : MeasureTheory.volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hcont : Continuous fun x : Vsp X.dim => ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) := by
    first
    | fun_prop
    | exact ((continuous_norm.comp hgc).pow 2).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hint : MeasureTheory.IntegrableOn
      (fun x : Vsp X.dim => ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2)) D :=
    (hcont.continuousOn.integrableOn_compact hDb.isCompact_closure).mono_set subset_closure
  rw [MeasureTheory.setAverage_eq, smul_eq_mul] at hl
  have hI : ∫ x in D, ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) = 0 := by
    have hr : MeasureTheory.volume.real D ≠ 0 := by
      rw [MeasureTheory.measureReal_def]
      exact ENNReal.toReal_ne_zero.mpr ⟨hD0, hDt⟩
    rcases mul_eq_zero.mp hl.symm with h | h
    · exact absurd (inv_eq_zero.mp h) hr
    · exact h
  have hae := (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
    (MeasureTheory.ae_of_all _ fun x => by show (0:ℝ) ≤ _; positivity) hint).mp hI
  have h2 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vsp X.dim)), x ∈ D → g x = 0 := by
    rw [← MeasureTheory.ae_restrict_iff' hDm]
    filter_upwards [hae] with x hx
    simpa [Real.exp_ne_zero] using hx
  rw [MeasureTheory.ae_iff] at h2
  have hset : {x | ¬(x ∈ D → g x = 0)} = {x | g x ≠ 0} ∩ D := by
    ext x; simp [and_comm]
  rw [hset] at h2
  open Pointwise in
  have hinv : ∀ γ : Submodule.span ℤ (Set.range X.b), γ +ᵥ {x | g x ≠ 0} = {x | g x ≠ 0} := by
    intro γ
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [Set.mem_setOf_eq]
    have e : (-γ) +ᵥ y = y + -(γ : Vsp X.dim) := by
      first
      | (rw [Submodule.vadd_def, add_comm]; rfl)
      | simp [Submodule.vadd_def, add_comm]
      | (show ((-γ : Submodule.span ℤ (Set.range X.b)) : Vsp X.dim) + y = _; simp [add_comm])
    rw [e]
    exact not_congr (hne _ (neg_mem γ.2) y)
  have ht0 := hfd.measure_zero_of_invariant {x | g x ≠ 0} hinv h2
  have hopen : IsOpen {x | g x ≠ 0} := isOpen_ne_fun hgc continuous_const
  have hempty : {x | g x ≠ 0} = ∅ := (hopen.measure_eq_zero_iff MeasureTheory.volume).mp ht0
  funext v
  show s v = 0
  have hv : v = fun _ => v 0 := funext fun k => by rw [Subsingleton.elim k 0]
  have hz : g (v 0) = 0 := by
    by_contra hc
    have hm : v 0 ∈ ({x | g x ≠ 0} : Set (Vsp X.dim)) := hc
    rw [hempty] at hm
    exact hm
  rw [hv]
  exact hz
end ReciprocityTheory.ChartRestriction.G.I2
