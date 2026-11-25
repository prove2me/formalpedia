-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.locJacTyp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:48.440351+00:00
-- url     : https://prove2.me/submissions/d651979e-31c1-4895-9095-dc1efe7e086e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (h0 : SdNorm (E := E) ψ v) (hZ : VolZZ σ v) (hU : VolU σ v)
    (hP : VolPP σ v) (hA : Arith (F := F) v) : PI.LocJacTyp.LocJacTyp σ ψ v := by
  intro typed g r T T' TF TF' hfin hσ ht hg hsplit hTF hTF' hdiff hT
  have hS : SplitHyp σ v := ⟨hfin, hσ, hsplit⟩
  rcases h0 with h0 | ⟨m, -, h0⟩
  · have h1 : sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) = 0 := h0 _
    have h2 : sdE (E := E) ψ v Unit = 0 := h0 _
    have h3 : ∏ l : Fin (r + 1), volC (E := E) ψ v (PPTyp σ v g r T T' l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ 0) (by simp [volC, h2])
    simp [volS, h1, h3]
  · obtain ⟨hZH, hZv⟩ := h0 (Fin (r + 1) × Fin (r + 1))
    obtain ⟨hUH, hUv⟩ := h0 (UIdx r)
    obtain ⟨hCH, hCv⟩ := h0 Unit
    have hZv' : (sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) (Obox (E := E) v _)).toReal =
        m ^ ((r + 1) * (r + 1)) := by rw [hZv]; simp [Fintype.card_prod]
    have hCv' : (sdE (E := E) ψ v Unit (Obox (E := E) v Unit)).toReal = m := by rw [hCv]; simp
    have eZ := hZ g r TF TF' m hS hg hTF hTF' hdiff _ hZH hZv'
    have eU := hU g r m hS hg _ hUH hUv
    have eP := hP g r T T' m hS hg hT _ hCH hCv'
    unfold volS volU volC
    rw [eZ, eU]
    simp only [eP]
    exact hA typed g r m ht hg
end PI.UnitaryGroupMassFormula.LocJacTyp
