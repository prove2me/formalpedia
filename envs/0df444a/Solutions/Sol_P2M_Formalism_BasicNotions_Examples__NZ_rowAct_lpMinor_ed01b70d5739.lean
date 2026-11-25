-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_rowAct_lpMinor_ed01b70d5739
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:40.361387+00:00
-- url     : https://prove2.me/submissions/3a54b992-212c-420b-8f5a-6612237ba349

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Definitions.Def_Lemmata_GeneralBFactRightBisForm_Imports
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevB
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.GradedWeylDivisibility
variable (R : Type) [CommRing R] {r n : ℕ}
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (h : Matrix (Fin r) (Fin r) R) (hl : ∀ i j, i < j → h i j = 0) (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    rowAct R h (lpMinor R (n := n) s hr hn) =
      C (∏ a : Fin s, h (Fin.castLE hr a) (Fin.castLE hr a)) * lpMinor R s hr hn := by
  classical
  unfold lpMinor
  rw [AlgHom.map_det]
  have hM : (rowAct R (n := n) h).mapMatrix (Matrix.of fun p q : Fin s =>
      (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) =
      (Matrix.of fun p b : Fin s => (C (h (Fin.castLE hr p) (Fin.castLE hr b)) : MvPolynomial (Fin r × Fin n) R)) *
        Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R) := by
    refine Matrix.ext fun p q => ?_
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    show rowAct R h (X (Fin.castLE hr p, Fin.castLE hn q)) = _
    rw [rowAct, aeval_X]
    symm
    refine Finset.sum_of_injOn (Fin.castLE hr) (Fin.castLE_injective hr).injOn (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
      (fun b _ hb => ?_) (fun _ _ => rfl)
    have hbs : ¬ b.val < s := fun hlt => hb ⟨⟨b.val, hlt⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
    have : Fin.castLE hr p < b := by
      rw [Fin.lt_def, Fin.val_castLE]
      have := p.2
      omega
    rw [hl _ _ this, C_0, zero_mul]
  rw [hM, Matrix.det_mul, Matrix.det_of_lowerTriangular, map_prod]
  · rfl
  · intro i j hij
    have hij' : i < j := hij
    rw [Matrix.of_apply, hl _ _ (by rw [Fin.lt_def]; exact hij'), C_0]
end Formalism.BasicNotions.Examples₂.NZ
