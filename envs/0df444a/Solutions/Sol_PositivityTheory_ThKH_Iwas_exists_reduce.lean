-- Prove2me | solution 1 for PositivityTheory.ThKH.Iwas.exists_reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:38.93711+00:00
-- url     : https://prove2.me/submissions/0c15cc2a-3657-42ec-a370-f9e3201c90e7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc
import Theorems.Thm_PositivityTheory_ThKH_Iwas_antiJ_submatrix
import Theorems.Thm_PositivityTheory_ThKH_Iwas_iso_iff_cT
import Theorems.Thm_Formalism_UG_P_fIwasawa_upper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Iwas
open Matrix Formalism.UG Formalism.UG.P GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
namespace PositivityTheory.ThKH.Iwas
theorem _root_.solution (hc : ∀ x, c (c x) = x) (hv : ∀ x, Valued.v (c x) = Valued.v x) {m : ℕ}
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) (hM : Iso c (Wm L (Fin m)) (Wm L (Fin m)) M) :
    ∃ k, Iso c (Wm L (Fin m)) (Wm L (Fin m)) k ∧ (∀ i j, Valued.v (k i j) ≤ 1) ∧
      ∀ i j, (k * M) (Sum.inr i) (Sum.inl j) = 0 := by
  have hW : antiJ L (m + m) = (Wm L (Fin m)).submatrix (ee m).symm (ee m).symm := by
    rw [← antiJ_submatrix]; simp
  have h1 : fIwasawaUn c (M.submatrix (ee m).symm (ee m).symm) := by
    unfold fIwasawaUn
    rw [hW]
    change (cT c M).submatrix (ee m).symm (ee m).symm * _ * _ = _
    rw [submatrix_mul_equiv, submatrix_mul_equiv, (iso_iff_cT hc M).1 hM]
  obtain ⟨k, hk, hT⟩ := fIwasawa_upper c hc hv _ h1
  refine ⟨k.submatrix (ee m) (ee m), (iso_iff_cT hc _).2 ?_, fun i j => hk.2 _ _, fun i j => ?_⟩
  · rw [← antiJ_submatrix]
    change (cT c k).submatrix (ee m) (ee m) * _ * _ = _
    rw [submatrix_mul_equiv, submatrix_mul_equiv, hk.1]
  · have e : k.submatrix (ee m) (ee m) * M = (k * M.submatrix (ee m).symm (ee m).symm).submatrix (ee m) (ee m) := by
      rw [← submatrix_mul_equiv k _ (ee m) (ee m) (ee m)]; simp
    rw [e]
    refine hT ?_
    have := j.2
    change (ee m (Sum.inl j)).val < (ee m (Sum.inr i)).val
    simp only [ee, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
    omega
end PositivityTheory.ThKH.Iwas
