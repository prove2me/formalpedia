-- Prove2me | solution 1 for PascalExtremes.padicVal_G_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:16.087609+00:00
-- url     : https://prove2.me/submissions/e65a9879-b718-471b-99b6-79ccb94532b6

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_G_dvd_choose
public import Theorems.Thm_PascalExtremes_G_ne_zero
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {N m p k : ℕ} (hm : 0 < m) (hNm : m < N) (hp : p.Prime)
    (hk : Admissible N m k) :
    padicValNat p (G N m) ≤ padicValNat p (N.choose k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hGne : G N m ≠ 0 := G_ne_zero hm hNm
  have hchooseNe : N.choose k ≠ 0 :=
    Nat.choose_ne_zero_iff.mpr hk.2.1.le
  have hGdvd : G N m ∣ N.choose k :=
    G_dvd_choose (mem_admissibleIndices_iff.mpr hk)
  by_contra hnot
  have hlt :
      padicValNat p (N.choose k) < padicValNat p (G N m) :=
    Nat.lt_of_not_ge hnot
  have hpG : p ^ (padicValNat p (N.choose k) + 1) ∣ G N m :=
    (padicValNat_dvd_iff_le hGne).2 hlt
  have hpChoose : p ^ (padicValNat p (N.choose k) + 1) ∣ N.choose k :=
    hpG.trans hGdvd
  have hle :
      padicValNat p (N.choose k) + 1 ≤ padicValNat p (N.choose k) :=
    (padicValNat_dvd_iff_le hchooseNe).1 hpChoose
  omega
end PascalExtremes
