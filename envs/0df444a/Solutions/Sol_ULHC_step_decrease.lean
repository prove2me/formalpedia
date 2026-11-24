-- Prove2me | solution 1 for ULHC.step_decrease
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:43:36.737848+00:00
-- url     : https://prove2.me/submissions/b6c92278-f270-43cd-a5dd-8638403c89fd

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_dval_eq
import Theorems.Thm_ULHC_Mz_lt_of_ncomp
import Theorems.Thm_ULHC_Mz_of_noT3
import Theorems.Thm_ULHC_Mz_of_T3
import Theorems.Thm_ULHC_t3_count
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Good_step
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_findPath_none
import Theorems.Thm_ULHC_findPath_some
import Theorems.Thm_ULHC_findT3_none
import Theorems.Thm_ULHC_round_ca
import Theorems.Thm_ULHC_seq_count
import Theorems.Thm_ULHC_step_deg2
import Theorems.Thm_ULHC_strip_even_gen


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hPC : PathComplete V)
include hs x0 hconn hPC
namespace ULHC
theorem _root_.solution {G : Finset Edge} (hG : Deg2 V G) (h2 : 2 ≤ ncomp V G) :
    ∃ G', step V G = some G' ∧ Mz V G' < Mz V G := by
  rcases ht : findT3 V G with _ | ⟨d, tf⟩
  · have hT := findT3_none hG.1 ht
    rcases hp : findPath V G with _ | ⟨a, L⟩
    · obtain ⟨σ, L, hP⟩ := hPC G hG hT h2
      exact absurd hP (findPath_none hG.1 hp σ L)
    have hstep : step V G = some (applyS G a) := by
      unfold step
      rw [ht, hp]
    refine ⟨_, hstep, ?_⟩
    have hG' := step_deg2 hG hstep
    obtain ⟨hP, hmin⟩ := findPath_some hG.1 hp
    have hMz := Mz_of_noT3 hT
    rw [dval_eq hp] at hMz
    cases L with
    | nil =>
      -- An odd first strip joins two components.
      --
      have hv : ValidSeq V G [a] := ⟨hP.1.1, hP.1.2⟩
      have hc := seq_count [a] G hG hv
      change ncomp V (applyS G a) + 1 = ncomp V G at hc
      exact Mz_lt_of_ncomp hG'.1 (le_of_eq hc)
    | cons b L' =>
      obtain ⟨⟨h1, hpat, hcell, hsep⟩, hch⟩ := hP.1
      have hae : a.n % 2 = 0 := hch.1
      obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
      have hfc : applyS G a = flipCol G a.c a.s (k + 2) := by
        unfold applyS
        rw [hk]
      have hpat' : StripPat G a.c a.s (k + 2) := by rw [← hk]; exact hpat
      rcases strip_even_gen k (by omega) G hG (fun j hj => hcell j (by omega)) hpat' hsep with
        heq | hdrop
      · rw [← hfc] at heq
        by_cases hT' : NoTypeIII V (applyS G a)
        · -- The rest of the path is a path of the new 2-factor.
          --
          obtain ⟨hP', hw⟩ := round_ca hs x0 hconn hG hT ⟨h1, hpat, hcell, hsep⟩ hae
            (by omega) hT' hmin hP rfl
          rcases hp' : findPath V (applyS G a) with _ | ⟨σ', L''⟩
          · exact absurd hP' (findPath_none hG'.1 hp' b L')
          have hle := (findPath_some hG'.1 hp').2 b L' hP'
          rw [Mz_of_noT3 hT', dval_eq hp', heq, hMz]
          omega
        · rw [Mz_of_T3 hT', heq, hMz]
          omega
      · rw [← hfc] at hdrop
        exact Mz_lt_of_ncomp hG'.1 (by omega)
  · have hstep : step V G = some (flip G d) := by
      unfold step
      rw [ht]
    refine ⟨_, hstep, ?_⟩
    exact Mz_lt_of_ncomp (step_deg2 hG hstep).1 (le_of_eq (t3_count hG ht))
end ULHC
