-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_fg_96ac575d611f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:36.641946+00:00
-- url     : https://prove2.me/submissions/eadc5f1c-7f58-4cbb-a283-b9fe80da0f8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_mem_span_forms_of_mem_ideal_85d986a9ff48
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_finset_forms_7e62cb2b7e9a

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
open GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
theorem _root_.solution [IsNoetherianRing S] (J' : Ideal (Poly S N))
    (hJ' : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') (I : Chart x) :
    (idealMod J' I).FG := by
  classical
  obtain ⟨H, hHJ, hspan, hH⟩ := exists_finset_forms J' hJ'
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have heq : idealMod J' I = Submodule.span (chartRing S x I)
      ((fun g : Poly S N => aeval x g / aeval x (X i ^ g.totalDegree : Poly S N)) ''
        (↑H : Set (Poly S N))) := by
    apply le_antisymm
    · rw [idealMod, Submodule.span_le]
      rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
      have hs0 := eval_ne_zero_of_mem_monos I hs
      rw [← hspan] at hf
      have hmem := mem_span_forms_of_mem_ideal totalDegree hH hf hfe
      refine Submodule.span_induction (p := fun p _ => aeval x p / aeval x s ∈
        Submodule.span (chartRing S x I) ((fun g : Poly S N =>
          aeval x g / aeval x (X i ^ g.totalDegree : Poly S N)) '' (↑H : Set (Poly S N))))
        ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨g, hg, h', d', hh', hd, rfl⟩
        have hX : aeval x (X i ^ g.totalDegree : Poly S N) ≠ 0 := by
          rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
        let c : chartRing S x I := ⟨aeval x (h' * X i ^ g.totalDegree) / aeval x s,
          h' * X i ^ g.totalDegree, s, e, hs, hd ▸ hh'.mul (isHomogeneous_X_pow i _), hse, rfl⟩
        have hc : aeval x (h' * g) / aeval x s =
            c • (aeval x g / aeval x (X i ^ g.totalDegree : Poly S N)) := by
          rw [chartRing_smul_def]
          change _ = aeval x (h' * X i ^ g.totalDegree) / aeval x s * _
          rw [map_mul, map_mul]
          field_simp
        rw [hc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)
      · simp
      · intro p q _ _ hp hq
        rw [map_add, add_div]
        exact Submodule.add_mem _ hp hq
      · intro r p _ hp
        rw [map_smul, smul_div_assoc]
        exact Submodule.smul_of_tower_mem _ r hp
    · rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨g, X i ^ g.totalDegree, g.totalDegree, hHJ hg,
        pow_mem (X_mem_monos hi) _, hH g hg, isHomogeneous_X_pow i _, rfl⟩
  rw [heq]
  exact Submodule.fg_span (H.finite_toSet.image _)
end GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
