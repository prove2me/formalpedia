-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_comap_specHom_2c5b1ebdb7b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:29.544685+00:00
-- url     : https://prove2.me/submissions/7fb010c5-ab5f-4e4b-bc1c-ffc5ba811656

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inl_8fd93a755c4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_form_c00665a83bdb

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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution (e : ℕ) {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)) :
    incIdeal (integralModel I) (e + 1) ≤
      (modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) ⊔
        Ideal.span {chartForm (parY e n v)}).comap (specHom e n v) := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_comap, specHom_rename_inl]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, specHom_form]
    induction i using Fin.cases with
    | zero =>
      exact Ideal.mem_sup_right (Ideal.subset_span (by simp [chartForm, parIdx]))
    | succ i =>
      exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, by simp [secForm, parIdx]⟩))
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
