-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_restPolynomial_b9129232db91
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:20.610984+00:00
-- url     : https://prove2.me/submissions/9b3f6944-45ff-44ee-95a3-4dcd1595aaed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_prod_eq_zero_f8221cfdebfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_vandermondeOf_eq_zero_e325c8c3d5fa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
variable (f r a : ℕ) (c : SmallBlock)
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (D : Derivation ℚ (RootRing f (r + a)) (RootRing f (r + a)))
    (α β : Fin f → ℚ) (hy : ∀ σ i, D (X (yIndex f r a c σ i)) = C (α σ))
    (hz : ∀ σ i, D (X (zIndex f r a c σ i)) = C (β σ)) :
    D (fibreClass f r a c) = 0 ∧
    D (restPolynomial f r a c) =
      C (((f * (r * a) + 1 : ℕ) : ℚ) * (c.sign * r * ∑ σ, α σ)) *
        (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c) := by
  have hyr : ∀ σ i, D (yRoot f r a c σ i) = C (c.sign * α σ) := by
    intro σ i
    rw [yRoot, C_mul', D.map_smul, hy, smul_eq_C_mul, ← C_mul]
  have hzr : ∀ σ i, D (zRoot f r a c σ i) = C (β σ) := fun σ i => hz σ i
  have hfib : D (fibreClass f r a c) = 0 := by
    unfold fibreClass
    refine derivation_prod_eq_zero D _ _ (fun σ _ => ?_)
    rw [Derivation.leibniz,
      derivation_vandermondeOf_eq_zero D _ (fun i j => by rw [hzr, hzr]),
      derivation_vandermondeOf_eq_zero D _ (fun i j => by rw [hyr, hyr]), smul_zero, smul_zero,
      add_zero]
  refine ⟨hfib, ?_⟩
  have hmu : D (smallBlockMu f r a c) = C (c.sign * r * ∑ σ, α σ) := by
    simp only [smallBlockMu, map_sum, hyr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [show (r : RootRing f (r + a)) = C (r : ℚ) from (map_natCast C r).symm]
    simp_rw [← C_mul, ← map_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring
  rw [restPolynomial, Derivation.leibniz, hfib, smul_zero, zero_add, Derivation.leibniz_pow, hmu]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  simp only [map_mul, map_natCast, map_add, map_one]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.RestTerms.Flag
