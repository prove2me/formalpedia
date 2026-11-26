-- Prove2me | solution 1 for SemigroupBetti.GenData.lemma14
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:20:00.380289+00:00
-- url     : https://prove2.me/submissions/bde750af-961a-4763-83ed-7a9811ad62e4

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_exists_coord_eq
public import Theorems.Thm_SemigroupBetti_GenData_exc_nu_V2
public import Theorems.Thm_SemigroupBetti_GenData_exc_coprime
public import Theorems.Thm_SemigroupBetti_GenData_sideP_split
public import Theorems.Thm_SemigroupBetti_GenData_W_le_w
public import Theorems.Thm_SemigroupBetti_GenData_alt_coord_eq_zero
public import Theorems.Thm_SemigroupBetti_GenData_exists_alt
public import Theorems.Thm_SemigroupBetti_GenData_isSplit_of_mem_fam
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_no_bridge
public import Theorems.Thm_SemigroupBetti_GenData_nu_add
public import Theorems.Thm_SemigroupBetti_GenData_nu_eq_sum
public import Theorems.Thm_SemigroupBetti_GenData_nu_single
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_one_le_crit
public import Theorems.Thm_SemigroupBetti_GenData_sel_eq_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_of_split
public import Theorems.Thm_SemigroupBetti_GenData_sel_pos
public import Theorems.Thm_SemigroupBetti_GenData_sel_two_bounds
public import Theorems.Thm_SemigroupBetti_GenData_three_le_W
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (hA : G.A = 1) (hB : G.B = G.W - 1) (hP : G.P = G.W - 2) :
    G.crit 2 = G.W - 1 := by
  have hW := G.three_le_W
  -- `c₂ ≤ W - 1`
  have hle : G.crit 2 ≤ G.W - 1 := by
    apply Nat.find_min'
    rw [isCritCand_iff]
    refine ⟨by omega, ![0, 1, 0, G.W - 2], exc_nu_V2 hA hB, fun h => ?_⟩
    have := congrFun h 1
    simp at this
  by_contra hne
  have hc : G.crit 2 ≤ G.W - 2 := by omega
  have hc1 := G.one_le_crit 2
  -- saturation: some `𝓟` degree has selected `23`-vector `(0,0,W-2,y)`
  have hK : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
  obtain ⟨D, hD, hzD⟩ := G.exists_coord_eq (K := {2, 3}) (i := 3) (k := 2) (by decide) (by decide)
    G.famP (fun d hd => G.sideP_split hd)
    (fun d hd => by
      have := G.sel_two_bounds (G.sideP_split hd) hK (by decide)
      rw [hA] at this; exact this)
    hP (v := G.W - 2) (by omega) le_rfl
  have hS23 := G.sideP_split hD
  have hS01 := G.isSplit_of_mem_fam hD
  set z := G.sel D {2, 3} with hz
  have hz0 : z 0 = 0 := G.sel_eq_zero hS23 hK (by decide)
  have hz1 : z 1 = 0 := G.sel_eq_zero hS23 hK (by decide)
  have hz3 : 0 < z 3 := G.sel_pos hS23 hK (by decide)
  have hnuz : G.nu z = D := (G.sel_of_split hS23 hK).1
  -- the alternative `r` at the critical degree avoids `2` and uses `0` or `1`
  obtain ⟨r, hr, hrne⟩ := G.exists_alt 2
  have hr2 := G.alt_coord_eq_zero hr hrne
  have hr01 : 0 < r 0 ∨ 0 < r 1 := by
    by_contra h0
    push Not at h0
    have hr0 : r 0 = 0 := by omega
    have hr1 : r 1 = 0 := by omega
    have hreq : r = Pi.single 3 (r 3) := by
      funext j; fin_cases j <;> simp [hr0, hr1, hr2]
    rw [hreq, G.nu_single] at hr
    have hdvd : G.n 3 ∣ G.crit 2 * G.n 2 := ⟨r 3, by rw [← hr, mul_comm]⟩
    have h3 := (exc_coprime hA hB).dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (by omega) h3
    have := G.W_le_w
    have := G.m_pos
    have hn3 : G.n 3 = G.m + G.w := rfl
    omega
  -- the bridge `b = r + (W-2-c₂) e₂ + y e₃`
  let b := r + Pi.single 2 (G.W - 2 - G.crit 2) + Pi.single 3 (z 3)
  have hb : G.nu b = D := by
    simp only [b]
    rw [G.nu_add, G.nu_add, G.nu_single, G.nu_single, hr, ← hnuz, G.nu_eq_sum z, hz0, hz1, hzD,
      ← Nat.add_mul, Nat.add_sub_cancel' hc, n_two, n_three]
    ring
  have hK01 : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  have hy := G.sel_of_split hS01 hK01
  rcases hr01 with h | h
  · refine G.no_bridge hS23 hnuz hy.1 hb (i := 3) (by decide) hz3 (j := 0) (by decide)
      (G.sel_pos hS01 hK01 (by decide)) ⟨3, ?_, hz3⟩ ⟨0, ?_, G.sel_pos hS01 hK01 (by decide)⟩
    · simp [b]; omega
    · simp [b]; omega
  · refine G.no_bridge hS23 hnuz hy.1 hb (i := 3) (by decide) hz3 (j := 1) (by decide)
      (G.sel_pos hS01 hK01 (by decide)) ⟨3, ?_, hz3⟩ ⟨1, ?_, G.sel_pos hS01 hK01 (by decide)⟩
    · simp [b]; omega
    · simp [b]; omega
end SemigroupBetti.GenData
