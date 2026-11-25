-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_locEmb_eq_6cc96fc5108f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:40:01.040308+00:00
-- url     : https://prove2.me/submissions/5d604be9-f9ee-4108-ac51-e48ad86d1437

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_map_C_mem_monos_b5180478af36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_mk_cfee296f451f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_smul__c950eebc53d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwM_val_mk_6383b3b12662


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
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I : StdCell N) (hI : I.1 ⊆ support x) {b c : ℤ} {y : Ω}
    (hy : y ∈ twLocPart η M₀ b c I.1) :
    ∃ w ∈ degLoc (twGraded η M₀) c I, UT.toL (locEmb η M₀ I.1 hI w) = single (b, c) y := by
  refine Submodule.span_induction (p := fun y _ => ∃ w ∈ degLoc (twGraded η M₀) c I,
    UT.toL (locEmb η M₀ I.1 hI w) = single (b, c) y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s₀, a, e, hs₀, hse, hz, hae, rfl⟩
    let m : TwM η M₀ := TwM.mk (single (b, a) z) (isTw_single η M₀ hz)
    let s : monos (S := MvPolynomial (Fin (r + 1)) S) I.1 :=
      ⟨MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s₀, map_C_mem_monos hs₀⟩
    refine ⟨LocalizedModule.mk m s, Submodule.subset_span ⟨m, s, a, e, ?_, hse.map C, hae, rfl⟩, ?_⟩
    · exact single_mem_tDeg (b, a) z
    · have hv := eval_ne_zero_of_subset hI hs₀
      rw [locEmb_mk η M₀ hI m s (xyHom_map_C x η hse) hv, TwM.val_mk, single_mul_single]
      congr 1
      ext
      · simp
      · simp; omega
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, single_zero]; rfl⟩
  · rintro u v _ _ ⟨w, hw, hwu⟩ ⟨w', hw', hwv⟩
    refine ⟨w + w', Submodule.add_mem _ hw hw', ?_⟩
    rw [map_add]
    change UT.toL _ + UT.toL _ = _
    rw [hwu, hwv, single_add]
    rfl
  · rintro r' u _ ⟨w, hw, hwu⟩
    refine ⟨(C r' : MvPolynomial (Fin (r + 1)) S) • w, Submodule.smul_mem _ _ hw, ?_⟩
    rw [locEmb_smul', hwu, yHom_C, single_mul_single, zero_add, Algebra.smul_def]
end GroundTheory.Heights₂.Heights.Kleiman
