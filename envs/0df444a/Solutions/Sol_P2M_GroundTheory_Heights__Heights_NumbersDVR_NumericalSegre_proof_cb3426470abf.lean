-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegre_proof_cb3426470abf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:06:42.822954+00:00
-- url     : https://prove2.me/submissions/14059e4c-a512-4f0e-9331-e1d7b58a50d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_perm_8e7327d5a04e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_segreSide_succ_5e5340993d17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_zetaDeg_split_66f428df64d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_truncCoord_of_le_bb68e2da1b41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_cons_add_83d8ed79e032

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open NumericalSegreProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace NumericalSegre
theorem _root_.solution (hadd : FieldNumbers.IntNumAdd.Statement.{0})
    (hdim : FlagBundleDim.Statement) (hcut : FlagBundleCut.Statement)
    (hvan : FlagBundlePullbackVanish.Statement) (hbase : FlagBundleLineBase.Statement) :
    NumericalSegre.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hP hdimV N hN E _ _ B w b hflag M a φ hφ Φ _ _ t ht n Y hnY
  have claim : ∀ i : ℕ, 1 ≤ i → ∀ hi : i ≤ N, ∀ (n : ℕ) (Y : List (K → ℤ)),
      n + Y.length + 1 = e + i →
      intNumL F (projIdeal F y w φ (truncCoord t i)) (List.replicate n zetaDeg ++ Y.map liftDeg) =
        segreSide F (pointIdeal F y) (fun j : Fin i => a - b (Fin.castLE hi j)) n Y := by
    intro i hi1
    induction i, hi1 using Nat.le_induction with
    | base =>
      intro hi n Y hnY
      rw [hbase F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht hi n Y (by omega)]
      simp [segreSide, Finset.Nat.antidiagonalTuple_one, rootList, List.finRange_succ]
      rfl
    | succ i hi1 ih =>
      intro hi n
      induction n with
      | zero =>
        intro Y hY
        rw [List.replicate_zero, List.nil_append,
          hvan F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht (i + 1) (by omega) hi Y
            (by omega)]
        unfold segreSide
        rw [if_neg (by omega)]
      | succ m ihm =>
        intro Y hY
        set l := List.replicate m (zetaDeg : Option K → ℤ) ++ Y.map liftDeg with hl
        have hlen : l.length + 1 = e + i := by
          simp [hl]
          omega
        obtain ⟨hPi, hdi⟩ := hdim F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht (i + 1)
          (by omega) hi
        rw [show e + (i + 1) - 1 = l.length + 1 by omega] at hdi
        rw [List.replicate_succ, List.cons_append, ← hl,
          ← zetaDeg_split a (b ⟨i, hi⟩), intNumL_cons_add hadd F _ hPi l hdi]
        have hc := hcut F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht ⟨i, hi⟩ hi1 l hlen
        simp only at hc
        rw [hc, ih (by omega) m Y (by omega)]
        have hperm : (liftDeg (a - b ⟨i, hi⟩) :: l).Perm
            (List.replicate m zetaDeg ++ ((a - b ⟨i, hi⟩) :: Y).map liftDeg) := by
          rw [hl, List.map_cons]
          exact List.perm_middle.symm
        rw [intNumL_perm F _ hperm, ihm _ (by simp; omega), segreSide_succ F _ hi1]
        rfl
  rw [← truncCoord_of_le t (le_refl N), claim N hN (le_refl N) n Y (by omega)]
  rfl
end NumericalSegre
end GroundTheory.Heights₂.Heights.NumbersDVR
