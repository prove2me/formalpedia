-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_proof_a2bcc0e883e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:10:59.28354+00:00
-- url     : https://prove2.me/submissions/e30dc167-ea2b-4ed7-abc3-1d31d40585f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeComplexBaseChange
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeComplexBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_map_int_complex_eq_43e09671a890
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_comap_of_minimal_6dbf60797385
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_dim_cancel_one_0972b078a348
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isRadical_map
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_ringKrullDim_of_mem_minimalPrimes_map
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ConeComplexBaseChange
namespace GroundTheory.Heights₂.Heights.Targets
namespace ConeComplexBaseChange
theorem _root_.solution : ConeComplexBaseChange.Statement := by
  intro K _ ι _ P n s W' Wa hV hs hW hWh hWa
  obtain ⟨-, ⟨hPp, -, -⟩, hPh, hdim⟩ := hV
  have hP' : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [hPh] at this
    exact this
  obtain ⟨hQp, -, hQdim⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have hmapP : P.map (MvPolynomial.map (Int.castRingHom ℂ)) =
      (ReciprocityTheory.AnForm.R.extQ P).map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [map_int_complex_eq, ← Ideal.map_map]; rfl
  have : W'.IsPrime := hW.1.1.1
  refine ⟨?_, fun Q hQ => ⟨?_, ?_⟩, ?_⟩
  · rw [hmapP]
    exact ReciprocityTheory.AnForm.R.BaseChangeC.isRadical_map _
  · have hQ' := hQ
    rw [hmapP] at hQ'
    rw [ReciprocityTheory.AnForm.R.BaseChangeC.ringKrullDim_of_mem_minimalPrimes_map _ Q hQ']
    rw [hdim, show n + 2 + Fintype.card K = (n + Fintype.card K + 1) + 1 by omega] at hQdim
    exact dim_cancel_one hQdim
  · intro hsQ
    apply hs
    rw [← comap_of_minimal P hPh Q hQ]
    exact hsQ
  · have hco : Wa.comap (MvPolynomial.map (Int.castRingHom ℂ)) = W' := comap_of_minimal W' hWh Wa hWa
    have hPW : P ⊔ Ideal.span {s} ≤ W' := hW.1.1.2
    refine ⟨⟨hWa.1.1, le_trans (Ideal.map_mono hPW) hWa.1.2⟩, ?_⟩
    rintro Q' ⟨hQ'p, hQ'le⟩ hQ'W
    have h1 : P ⊔ Ideal.span {s} ≤ Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
      Ideal.map_le_iff_le_comap.mp hQ'le
    have h2 : Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W' := hco ▸ Ideal.comap_mono hQ'W
    have h3 : W' ≤ Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
      hW.1.2 ⟨Ideal.comap_isPrime _ _, h1⟩ h2
    exact hWa.2 ⟨hQ'p, Ideal.map_le_iff_le_comap.mpr h3⟩ hQ'W
end ConeComplexBaseChange
end GroundTheory.Heights₂.Heights.Targets
