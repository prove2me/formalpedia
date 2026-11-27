-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.unfold_Zn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:27.727339+00:00
-- url     : https://prove2.me/submissions/0688f0f6-7780-421e-a466-ef04799ace8d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CubeIcoMeas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_UnfoldZn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {d : ℕ} (g : (Fin d → ℝ) → ENNReal) :
    ∫⁻ x, g x = ∑' n : Fin d → ℤ, ∫⁻ x in cubeIco (Fin d), g (x + fun i => (n i : ℝ)) := by
  classical
  set b := Pi.basisFun ℝ (Fin d) with hb
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) (Fin d → ℝ) volume :=
    ⟨fun c s _ => by
      show volume ((fun x => (c : Fin d → ℝ) + x) ⁻¹' s) = volume s
      exact measure_preimage_add _ _ _⟩
  have hF := ZSpan.isAddFundamentalDomain b (volume : Measure (Fin d → ℝ))
  have hdom : ZSpan.fundamentalDomain b = cubeIco (Fin d) := by
    ext x; simp [ZSpan.fundamentalDomain, cubeIco, b]
  rw [hF.lintegral_eq_tsum'', hdom]
  have hmem : ∀ n : Fin d → ℤ, (fun i => (n i : ℝ)) ∈ Submodule.span ℤ (Set.range b) := by
    intro n
    rw [Module.Basis.mem_span_iff_repr_mem]
    intro i; simp [b]
  let e : (Fin d → ℤ) → Submodule.span ℤ (Set.range b) := fun n => ⟨_, hmem n⟩
  have he : Function.Bijective e := by
    constructor
    · intro n m h
      funext i
      have := congrFun (congrArg Subtype.val h) i
      have h2 : (n i : ℝ) = m i := by simpa [e] using this
      exact_mod_cast h2
    · rintro ⟨y, hy⟩
      have hy' := hy
      rw [Module.Basis.mem_span_iff_repr_mem] at hy'
      choose n hn using hy'
      refine ⟨n, Subtype.ext ?_⟩
      funext i
      simpa [b, e] using hn i
  rw [← (Equiv.ofBijective e he).tsum_eq]
  congr 1; funext n
  congr 1; funext x
  show g ((fun i => (n i : ℝ)) + x) = _
  rw [add_comm]
end ReciprocityTheory.ChartRestriction.G.I2
