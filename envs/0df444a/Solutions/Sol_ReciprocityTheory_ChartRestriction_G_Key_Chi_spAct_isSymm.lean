-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:55.358515+00:00
-- url     : https://prove2.me/submissions/ec45f33e-a89b-4326-912d-4af1155075c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sp_keyT

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
theorem _root_.solution {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hj : IsUnit (jAut γ τ).det) : (spAct γ τ).IsSymm := by
  show (nAut γ τ * (jAut γ τ)⁻¹)ᵀ = nAut γ τ * (jAut γ τ)⁻¹
  have hk := sp_keyT hγ τ
  rw [hτ.eq, sub_self, sub_eq_zero] at hk
  have hJt : IsUnit (jAut γ τ)ᵀ.det := by rwa [Matrix.det_transpose]
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  calc ((jAut γ τ)ᵀ)⁻¹ * (nAut γ τ)ᵀ
      = ((jAut γ τ)ᵀ)⁻¹ * (nAut γ τ)ᵀ * (jAut γ τ * (jAut γ τ)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hj, Matrix.mul_one]
    _ = ((jAut γ τ)ᵀ)⁻¹ * ((nAut γ τ)ᵀ * jAut γ τ) * (jAut γ τ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = ((jAut γ τ)ᵀ)⁻¹ * ((jAut γ τ)ᵀ * nAut γ τ) * (jAut γ τ)⁻¹ := by rw [← hk]
    _ = nAut γ τ * (jAut γ τ)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJt, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
