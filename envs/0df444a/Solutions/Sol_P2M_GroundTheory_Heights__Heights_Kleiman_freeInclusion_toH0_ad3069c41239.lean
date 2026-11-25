-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_freeInclusion_toH0_ad3069c41239
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:51.992886+00:00
-- url     : https://prove2.me/submissions/8adc40ed-87bb-4522-b986-c3f9ee101039

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMapShift_mk_088a57e319ca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)
variable (hb : ∀ j, b j ∈ 𝓜.piece (d j))
include hb
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (j : Fin r) (p : (polyGraded S N).piece (c - d j)) :
    freeIncl 𝓜 b d hb 0 c j (toH0 (polyGraded S N) (c - d j) p) =
      toH0 𝓜 c ⟨(p : Poly S N) • b j, smul_basis_mem 𝓜 b d hb c j p⟩ := by
  obtain ⟨w, hw, hw'⟩ := cohomMapShift_mk (𝓜 := polyGraded S N) (𝓜' := 𝓜)
    (LinearMap.toSpanSingleton (Poly S N) M (b j)) (d j)
    (fun _ _ hp => by
      rw [LinearMap.toSpanSingleton_apply, add_comm]
      exact smul_mem_of_mem_polyGraded 𝓜 hp (hb j)) 0 (show c = c - d j + d j by ring)
    ⟨constCochain (p : Poly S N), constCochain_mem _ _ _ p.2⟩
  refine hw.trans ?_
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun I => (hw' I).trans (locMap_mk _ _ _ _)))
end GroundTheory.Heights₂.Heights.Kleiman
