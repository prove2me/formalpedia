-- Prove2me | solution 1 for PI.LocJacOrd.W.locJacOrd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:26.511796+00:00
-- url     : https://prove2.me/submissions/2946da02-6fda-45af-9357-db89324e7d93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacOrd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocJacOrd.W
theorem _root_.solution (h0 : SdNormO (E := E) ψ v) (hZ : VolZZO (E := E) v) (hU : VolUO (E := E) v)
    (hP : VolPO (E := E) v) (hA : ArithO (F := F) v) : LocJacOrd (E := E) ψ v := by
  intro typed g r hfin ht
  rcases h0 with h0 | ⟨m, -, h0⟩
  · have h1 : sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) = 0 := h0 _
    have h2 : sdE (E := E) ψ v Unit = 0 := h0 _
    have h3 : ∏ l : Fin (r + 1), volC (E := E) ψ v (PPOrd (E := E) v r l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ 0) (by simp [volC, h2])
    simp [volS, h1, h3]
  · obtain ⟨hZH, hZv⟩ := h0 (Fin (r + 1) × Fin (r + 1))
    obtain ⟨hUH, hUv⟩ := h0 (UIdx r)
    obtain ⟨hCH, hCv⟩ := h0 Unit
    have hZv' : (sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) (Obox (E := E) v _)).toReal =
        m ^ ((r + 1) * (r + 1)) := by rw [hZv]; simp [Fintype.card_prod]
    have hCv' : (sdE (E := E) ψ v Unit (Obox (E := E) v Unit)).toReal = m := by rw [hCv]; simp
    have eZ := hZ r m hfin _ hZH hZv'
    have eU := hU r m hfin _ hUH hUv
    have eP := hP r m hfin _ hCH hCv'
    unfold volS volU volC
    rw [eZ, eU]
    simp only [eP]
    exact hA typed g r m ht
end PI.LocJacOrd.W
