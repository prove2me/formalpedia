-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tens_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:05:19.134216+00:00
-- url     : https://prove2.me/submissions/4177b86f-d9ae-4f5a-b514-dc0acf695902

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain

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
theorem _root_.solution {n q : ℕ} {s : Fin n → (Fin 1 → Vsp X.dim) → ℂ} (hs : ∀ k, s k ∈ X.Sec q 1) :
    tens X s ∈ X.Sec q n := by
  have hd : ∀ k, Differentiable ℂ (s k) := fun k => (show Differentiable ℂ (s k) ∧ _ from hs k).1
  show _ ∧ _
  refine ⟨?_, fun γ hγ v => ?_⟩
  · show Differentiable ℂ (fun v : Fin n → Vsp X.dim => ∏ k, s k (fun _ => v k))
    first
    | exact Differentiable.finset_prod (fun k _ => (hd k).comp (differentiable_pi.mpr fun _ => differentiable_apply k))
    | fun_prop
  · have he : ∀ k, s k (fun _ => (v + γ) k) = ((X.eps (γ k) : ℂ)) ^ q *
        cexp (q * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) * s k (fun _ => v k) := by
      intro k
      have := (show Differentiable ℂ (s k) ∧ ∀ γ' : Fin 1 → Vsp X.dim, (∀ j, γ' j ∈ X.L) →
        ∀ w, s k (w + γ') = (∏ j, (X.eps (γ' j) : ℂ)) ^ q *
          cexp (q * Real.pi * HC w γ' + q * Real.pi * HC γ' γ' / 2) * s k w from hs k).2
        (fun _ => γ k) (fun _ => hγ k) (fun _ => v k)
      simpa [HC, Pi.add_def] using this
    have hsum : ∑ k, ((q : ℂ) * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) =
        q * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2 := by
      simp only [HC, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    show ∏ k, s k (fun _ => (v + γ) k) = (∏ k, (X.eps (γ k) : ℂ)) ^ q *
      cexp (q * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2) * ∏ k, s k (fun _ => v k)
    rw [Finset.prod_congr rfl fun k _ => he k, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow, ← Complex.exp_sum, hsum]
end ReciprocityTheory.ChartRestriction.G.I2
