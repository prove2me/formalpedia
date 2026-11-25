-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_nefOnFibres_map_relabel_36f78da6ae3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:47.497981+00:00
-- url     : https://prove2.me/submissions/3eace890-4929-46b6-9946-64038ddc55fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_map_34db07ffdc36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiProjPrime_map_relabel_iff_311df4d0de71
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_charOf_map_relabel_ff9c6d4a87db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_geoNum_relabel_270ea30b3b6f

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (P : Ideal (MRing ι)) (a : K' → ℤ) :
    NefOnFibres P (a ∘ ε) ↔ NefOnFibres (P.map (relabelRingEquiv ε h)) a := by
  have hcard : Fintype.card K = Fintype.card K' := Fintype.card_congr ε
  constructor
  · intro H W' hW' hPW' hch hdim
    have hWW' : (W'.comap (relabelRingEquiv ε h)).map (relabelRingEquiv ε h) = W' :=
      Ideal.map_comap_of_surjective _ (relabelRingEquiv ε h).surjective W'
    rw [← hWW'] at hW' hch hdim ⊢
    have := H (W'.comap (relabelRingEquiv ε h))
      ((isMultiProjPrime_map_relabel_iff ε h _).1 hW') (Ideal.map_le_iff_le_comap.1 hPW')
      (by rwa [charOf_map_relabel] at hch)
      (by rw [ringKrullDim_quotient_map] at hdim; rw [hdim, hcard])
    exact this.trans_eq (geoNum_relabel ε h 1 _ fun _ => a)
  · intro H W hW hPW hch hdim
    have := H (W.map (relabelRingEquiv ε h)) ((isMultiProjPrime_map_relabel_iff ε h W).2 hW)
      (Ideal.map_mono hPW) (by rwa [charOf_map_relabel])
      (by rw [ringKrullDim_quotient_map, hdim, hcard])
    exact this.trans_eq (geoNum_relabel ε h 1 W fun _ => a).symm
end GroundTheory.Heights₂.Heights
