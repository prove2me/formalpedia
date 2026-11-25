-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:01:49.098847+00:00
-- url     : https://prove2.me/submissions/19fb95e4-9055-454d-8226-145c311c67c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_exists_colsFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution : SpGenStatement := by
  intro g M hM
  obtain ⟨A, rfl⟩ : ∃ A : symplecticGroup (Fin g) ℤ,
      (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = M := ⟨⟨M, hM⟩, rfl⟩
  obtain ⟨O, hO, hF⟩ := exists_colsFixed
    ((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (A⁻¹).2 g le_rfl
  have h1 : O * ((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = 1 := by
    ext r c
    rcases c with i | i
    · exact (hF i i.isLt).1 r
    · exact (hF i i.isLt).2 r
  have h2 : ((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) *
      (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = 1 :=
    congrArg Subtype.val (inv_mul_cancel A)
  have hOM : O = (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) := by
    calc O = O * (((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) *
          (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)) := by rw [h2, Matrix.mul_one]
      _ = (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [← hOM]
  exact hO
end ReciprocityTheory.ChartRestriction.G.Key.Chi
