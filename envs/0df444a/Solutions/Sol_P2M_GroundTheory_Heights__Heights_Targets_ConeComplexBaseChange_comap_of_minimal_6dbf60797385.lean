-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_comap_of_minimal_6dbf60797385
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:00:26.766822+00:00
-- url     : https://prove2.me/submissions/ac8b09ca-8336-48d5-a472-884c87749b7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeComplexBaseChange
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeComplexBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_map_int_complex_eq_43e09671a890
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_comap_of_mem_minimalPrimes_map
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
open GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
theorem _root_.solution (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
  have hP' : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hm
    rw [hP] at this
    exact this
  obtain ⟨hpr, hco, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have : (P.map (MvPolynomial.map (Int.castRingHom ℚ))).IsPrime := hpr
  rw [map_int_complex_eq, ← Ideal.map_map] at hQ
  have h := ReciprocityTheory.AnForm.R.BaseChangeC.comap_of_mem_minimalPrimes_map _ Q hQ
  rw [map_int_complex_eq, ← Ideal.comap_comap, h]
  exact hco
end GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
