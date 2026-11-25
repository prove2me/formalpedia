-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.opH_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:52.484038+00:00
-- url     : https://prove2.me/submissions/8fa095eb-ce4a-48d1-bba2-9aa116e1097a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorFormula
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_phi_X
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_deriv_part

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.SP.Mi
variable {n : ℕ}
set_option maxHeartbeats 2000000
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) (f : Pm (Polynomial ℂ) ρ) :
    opH s m b (I p) (J q) (phi b I J f) = (-(cMn s b)) • phi b I J (opE (alMn m b) p q f) := by
  have h := deriv_part s m b I J p q f
  simp only [opH, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, Derivation.coeFn_coe, opE, map_add, map_mul]
  have hs : (∑ a : Fin n, ∑ d : Fin n, (-(if b = true then Complex.I * s else -(Complex.I * s))) •
      (yv b a (I p) * yv b (J q) d * (pderiv (b, a, d)) (phi b I J f))) =
      (-(if b = true then Complex.I * s else -(Complex.I * s))) • ∑ a : Fin n, ∑ d : Fin n,
        yv b a (I p) * yv b (J q) d * (pderiv (b, a, d)) (phi b I J f) := by
    simp only [Finset.smul_sum]
  have h1 : phi b I J (C (alMn m b)) = C (if b = true then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X) := by
    simp only [phi, rename_C, alMn]
  rw [hs, h, ← smul_add, h1, phi_X]
  rfl
end PositivityTheory.Rg.Sw.SP
