-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_length_map_8e436c9e22c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:54.542814+00:00
-- url     : https://prove2.me/submissions/ef56d064-3c6d-464e-b91b-73136617041b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_map_iff_702b680ecd84
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_length_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_isLocData_atPrime_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')
namespace GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
theorem _root_.solution (V W : Ideal R) [W.IsPrime] [(W.map (φ : R →+* R')).IsPrime] (hVW : V ≤ W)
    (x : R) :
    Module.length (Localization.AtPrime (W.map (φ : R →+* R')))
        (LocalizedModule (W.map (φ : R →+* R')).primeCompl
          (R' ⧸ (V.map (φ : R →+* R') ⊔ Ideal.span {φ x}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ (V ⊔ Ideal.span {x}))) := by
  set V' := V.map (φ : R →+* R')
  set W' := W.map (φ : R →+* R')
  have hVW' : V' ≤ W' := Ideal.map_mono hVW
  have : (W'.map (Ideal.Quotient.mk V')).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hVW')
  have h' := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.isLocData_atPrime_quot V' W' hVW'
  letI : Algebra R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) :=
    ((algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V')))).comp
      (φ : R →+* R')).toAlgebra
  have hal : ∀ r, algebraMap R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) r =
      algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) (φ r) := fun r => rfl
  have hS : ∀ s : R', s ∈ W'.primeCompl → φ.symm s ∈ W.primeCompl := by
    intro s hs h
    apply hs
    rw [← φ.apply_symm_apply s]
    exact (mem_map_iff φ W _).2 h
  have h : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData R
      (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) W.primeCompl V := by
    refine ⟨fun s hs => ?_, fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
    · rw [hal]
      exact h'.1 _ (fun h => hs ((mem_map_iff φ W s).1 h))
    · obtain ⟨r, s, hs, e⟩ := h'.2.1 y
      refine ⟨φ.symm r, φ.symm s, hS s hs, ?_⟩
      rw [hal, hal, φ.apply_symm_apply, φ.apply_symm_apply]
      exact e
    · rw [hal] at hr
      obtain ⟨s, hs, e⟩ := h'.2.2.1 _ hr
      refine ⟨φ.symm s, hS s hs, ?_⟩
      rw [← mem_map_iff φ V, map_mul, φ.apply_symm_apply]
      exact e
    · rw [hal]
      exact h'.2.2.2 _ ((mem_map_iff φ V v).2 hv)
  exact (h'.length_eq (φ x)).trans (h.length_eq x).symm
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
