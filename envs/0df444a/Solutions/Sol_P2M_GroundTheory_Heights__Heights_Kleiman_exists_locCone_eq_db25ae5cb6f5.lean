-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_locCone_eq_db25ae5cb6f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:20:33.925544+00:00
-- url     : https://prove2.me/submissions/e46339bd-6c67-446c-b53c-fbe8e7e042de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_eq_99b34d9786d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tilde_le_span_018999601e2d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_smul_coneSingle_4b1ab4277a3e


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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {y : Ω}
    (hy : y ∈ M.tilde c ⟨I.1, I.2.1, hI⟩) :
    ∃ z ∈ degLoc M.coneGraded c I, locCone M I.1 hI z = coneSingle S x c y := by
  refine Submodule.span_induction (p := fun y _ => ∃ z ∈ degLoc M.coneGraded c I,
    locCone M I.1 hI z = coneSingle S x c y) ?_ ?_ ?_ ?_ (tilde_le_span M c _ hy)
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine ⟨LocalizedModule.mk ⟨coneSingle S x a m, M.coneSingle_mem_coneSub hm⟩ ⟨s, hs⟩,
      Submodule.subset_span ⟨_, ⟨s, hs⟩, a, e, M.coneSingle_mem_conePiece hm, hse, hae, rfl⟩,
      locCone_mk_eq M hI ?_⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI hs
    change s • coneSingle S x c ((aeval x s)⁻¹ • m) = coneSingle S x a m
    rw [smul_coneSingle hse, smul_eq_mul, mul_inv_cancel_left₀ hs0, show c + (e : ℤ) = a by omega]
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨z, hz, hzy⟩ ⟨z', hz', hzy'⟩
    exact ⟨z + z', add_mem hz hz', by rw [map_add, map_add, hzy, hzy']⟩
  · rintro t _ _ ⟨z, hz, hzy⟩
    exact ⟨t • z, Submodule.smul_mem _ t hz, by rw [LinearMap.map_smul_of_tower, hzy, map_smul]⟩
end GroundTheory.Heights₂.Heights.Kleiman
