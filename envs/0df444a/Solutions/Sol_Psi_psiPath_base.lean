-- Prove2me | solution 1 for Psi.psiPath_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:15:35.830673+00:00
-- url     : https://prove2.me/submissions/c44ef797-f540-4aec-952c-1363a64233f1

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_cUDraw_fUD_append
import Theorems.Thm_Psi_firstDDidx_repl_true_DD

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l k : ℕ) :
    psiPath ((List.replicate l [true, false]).flatten
              ++ List.replicate (k + 1) true ++ List.replicate (k + 1) false)
      = (List.replicate l false ++ List.replicate k true, [0]) := by
  cases k with
  | zero =>
      set P := (List.replicate l [true, false]).flatten
              ++ List.replicate (0 + 1) true ++ List.replicate (0 + 1) false with hPdef
      have hPeq : P = ((List.replicate l [true, false]).flatten ++ [true]) ++ [false] := by
        rw [hPdef]; simp [List.append_assoc]
      have hcr : cUDraw P = l + 1 := by
        rw [hPeq, show ((List.replicate l [true, false]).flatten ++ [true]) ++ [false]
            = (List.replicate l [true, false]).flatten ++ [true, false] from by
            simp [List.append_assoc], cUDraw_fUD_append]; rfl
      have hlen : P.length = 2 * l + 2 := by
        rw [hPdef]; simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega
      have hcUD : cUD P = l := by rw [cUD, hcr, if_pos (by omega)]; omega
      have hrest : List.drop (2 * l + 1) P = [false] := by
        rw [hPeq, show 2 * l + 1 = ((List.replicate l [true, false]).flatten ++ [true]).length from by
          simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega, List.drop_left]
      rw [psiPath.eq_1, hcUD, hrest]
      split
      · simp
      · next i h => rw [show firstDDidx [false] = none from rfl] at h; exact absurd h (by simp)
  | succ k' =>
      set P := (List.replicate l [true, false]).flatten
              ++ List.replicate (k' + 1 + 1) true ++ List.replicate (k' + 1 + 1) false with hPdef
      set rest := List.replicate (k' + 1) true ++ List.replicate (k' + 1 + 1) false with hrestdef
      have hcr : cUDraw P = l := by
        rw [hPdef, List.append_assoc, cUDraw_fUD_append,
          show List.replicate (k' + 1 + 1) true = true :: true :: List.replicate k' true from by
            rw [List.replicate_succ, List.replicate_succ]]
        rfl
      have hlen : P.length = 2 * l + 2 * (k' + 2) := by
        rw [hPdef]; simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega
      have hcUD : cUD P = l := by rw [cUD, hcr, if_neg (by omega)]
      have hrestP : List.drop (2 * l + 1) P = rest := by
        rw [hPdef, hrestdef,
          show (List.replicate l [true, false]).flatten ++ List.replicate (k' + 1 + 1) true
              ++ List.replicate (k' + 1 + 1) false
            = ((List.replicate l [true, false]).flatten ++ [true])
              ++ (List.replicate (k' + 1) true ++ List.replicate (k' + 1 + 1) false) from by
            rw [show List.replicate (k' + 1 + 1) true = [true] ++ List.replicate (k' + 1) true from by
              rw [List.replicate_succ]; rfl]
            simp [List.append_assoc],
          show 2 * l + 1 = ((List.replicate l [true, false]).flatten ++ [true]).length from by
            simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega, List.drop_left]
      have hfdd : firstDDidx rest = some (k' + 1) := by
        rw [hrestdef, show List.replicate (k' + 1 + 1) false
            = false :: false :: List.replicate k' false from by
          rw [List.replicate_succ, List.replicate_succ]]
        exact firstDDidx_repl_true_DD (k' + 1) _
      have htk : rest.take (k' + 1) = List.replicate (k' + 1) true := by
        rw [hrestdef, List.take_append_of_le_length (by simp)]; simp
      have hdp : rest.drop (k' + 1) = List.replicate (k' + 1 + 1) false := by
        rw [hrestdef, List.drop_append_of_le_length (by simp)]; simp
      have hbc : min ((rest.take (k' + 1)).reverse.takeWhile id).length
                     (((rest.drop (k' + 1)).takeWhile (· = false)).length - 1) = k' + 1 := by
        rw [htk, hdp, List.reverse_replicate]; simp
      have hρrec : rest.take (k' + 1 - (k' + 1)) = [] := by simp
      have hρ'rec : rest.drop (k' + 1 + (k' + 1) + 1) = [] := by
        rw [hrestdef]; apply List.drop_eq_nil_of_le
        simp only [List.length_append, List.length_replicate]; omega
      rw [psiPath.eq_1, hcUD, hrestP]
      split
      · next h => rw [hfdd] at h; exact absurd h (by simp)
      · next i h =>
          rw [hfdd] at h; injection h with hh; subst hh
          simp only [hbc, hρrec, hρ'rec]
          rw [dif_pos (by simp)]
end Psi
