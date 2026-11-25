-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_step_77fe98b2628b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:06.226803+00:00
-- url     : https://prove2.me/submissions/81bcbb71-86d4-4a56-ac47-fee0008db945

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_quotient_79d7d8dcab70

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module IsLocalRing LinearMap Submodule
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
open Classical
variable {B : Type*} [CommRing B]
variable {R : Type*} [CommRing R] [Algebra R B]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
namespace GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
theorem _root_.solution {p q : Submodule B N} (h : p ⋖ q) :
    ∃ m : MaximalSpectrum B, length R q = length R p + length R (B ⧸ m.asIdeal) ∧
      ∀ n : MaximalSpectrum B,
        length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl q) =
          length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl p) +
            if n = m then 1 else 0 := by
  let f : p →ₗ[B] q := inclusion h.le
  have key : IsSimpleModule B (q ⧸ range f) := by
    rwa [range_inclusion, ← covBy_iff_quot_is_simple h.le]
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
  let g : q →ₗ[B] B ⧸ m := e.toLinearMap.comp (range f).mkQ
  have hf : Function.Injective f := inclusion_injective _
  have hg : Function.Surjective g := e.surjective.comp (range f).mkQ_surjective
  have hfg : Function.Exact f g := exact_iff.mpr ((e.ker_comp _).trans (range f).ker_mkQ)
  refine ⟨⟨m, hm⟩, length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R) hf hg hfg,
    fun n => ?_⟩
  rw [← length_localizedModule_quotient n ⟨m, hm⟩]
  exact length_eq_add_of_exact
    ((IsLocalizedModule.map n.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ p)
      (LocalizedModule.mkLinearMap _ q) f).extendScalarsOfIsLocalization n.asIdeal.primeCompl
        (Localization.AtPrime n.asIdeal))
    ((IsLocalizedModule.map n.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ q)
      (LocalizedModule.mkLinearMap _ (B ⧸ m)) g).extendScalarsOfIsLocalization
        n.asIdeal.primeCompl (Localization.AtPrime n.asIdeal))
    (IsLocalizedModule.map_injective _ _ _ f hf) (IsLocalizedModule.map_surjective _ _ _ g hg)
    (LocalizedModule.map_exact _ f g hfg)
end GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
