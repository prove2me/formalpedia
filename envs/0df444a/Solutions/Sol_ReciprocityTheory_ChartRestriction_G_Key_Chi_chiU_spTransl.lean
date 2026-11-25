-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_spTransl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:18:50.919973+00:00
-- url     : https://prove2.me/submissions/7daba653-df58-413c-9d6d-899220bf5c70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eC_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofRealVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofIntVec_dot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_mulVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_cMat_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_spTransl
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
import Theorems.Thm_ReciprocityTheory_PTheta_ofIntVec_mulVec
import Theorems.Thm_ReciprocityTheory_PTheta_thetaTranslTau_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (hS : S.IsSymm) :
    ChiAtU g (spTransl S) := by
  intro n n'
  have hA : ofRealVec (halfVec n) ⬝ᵥ (S.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n)) =
      ((n ⬝ᵥ (S *ᵥ n) : ℤ) : ℂ) / 4 := by
    rw [ofRealVec_halfVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      ← ofIntVec_mulVec, ofIntVec_dot]
    simp only [smul_eq_mul]
    ring
  have hB : ofRealVec (halfVec n) ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ) / 2) =
      ((n ⬝ᵥ (fun i => S i i) : ℤ) : ℂ) / 4 := by
    simp only [dotProduct, ofRealVec, halfVec, Int.cast_sum, Int.cast_mul]
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨n, n' - S *ᵥ n - (fun i => S i i),
    eC (-(ofRealVec (halfVec n) ⬝ᵥ (S.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n))) / 2 -
      ofRealVec (halfVec n) ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ) / 2)) ^ 2, ?_, ?_⟩
  · rw [← pow_mul, eC_pow, hA, hB]
    convert eC_int (-(n ⬝ᵥ (S *ᵥ n)) - 2 * (n ⬝ᵥ (fun i => S i i))) using 2
    push_cast
    ring
  · intro τ _ z
    have hz : zAct (spTransl S) τ z = z := by simp [zAct, jAut_spTransl]
    have hx : expArg (spTransl S) τ z = 0 := by simp [expArg, cMat_spTransl]
    have hb : halfVec (n' - S *ᵥ n - fun i => S i i) +
        S.map (fun x : ℤ => (x : ℝ)) *ᵥ halfVec n + (fun i => ((S i i : ℤ) : ℝ) / 2) =
        halfVec n' := by
      rw [mulVec_halfVec]
      funext i
      simp only [halfVec, Pi.add_apply, Pi.sub_apply]
      push_cast
      ring
    rw [hz, hx, spAct_spTransl, jAut_spTransl, Matrix.det_one, eC_zero,
      thetaTranslTau_holds (Fin g) (halfVec n) _ z τ S hS, hb]
    ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi
