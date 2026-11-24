-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:55.653695+00:00
-- url     : https://prove2.me/submissions/22ce199e-71cc-42f1-8035-5fb1b2d936bb

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Mathlib.Algebra.MvPolynomial.Funext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_FFVMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open NumberField IsDedekindDomain Formalism.L2.Pj MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k K : Type} [Field k] [Field K]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (io : k →+* K) {cc : Ty → Ty} {isX : Ty → Prop} {P : MvPolynomial (Letter Ty r n) k}
    (hP : P ∈ harmK r n k cc isX (fun _ => 1)) : P.map io ∈ harmK r n K cc isX (fun _ => 1) := by
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hP ⊢
  intro τ hτ a a'
  have e : lap r n K 1 τ (cc τ) a a' (P.map io) = (lap r n k 1 τ (cc τ) a a' P).map io := by
    simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Derivation.coeFn_coe,
      pderiv_map, map_sum, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    split_ifs <;> simp [pderiv_map]
  rw [e, hP τ hτ a a', map_zero]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
