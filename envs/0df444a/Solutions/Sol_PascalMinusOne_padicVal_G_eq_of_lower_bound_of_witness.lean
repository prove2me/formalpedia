-- Prove2me | solution 1 for PascalMinusOne.padicVal_G_eq_of_lower_bound_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:54.445106+00:00
-- url     : https://prove2.me/submissions/70bf2f4b-bd3c-4406-a0df-1d66ef8d2173

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_G_dvd_choose
import Theorems.Thm_PascalMinusOne_G_ne_zero
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution
    {N m p r : ℕ} (hm : 0 < m) (hNm : m < N) (hp : p.Prime)
    (hlower :
      ∀ k, Admissible N m k → r ≤ padicValNat p (N.choose k))
    (hwitness :
      ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = r) :
    padicValNat p (G N m) = r := by
  letI : Fact p.Prime := ⟨hp⟩
  have hGne : G N m ≠ 0 := G_ne_zero hm hNm
  apply Nat.le_antisymm
  · obtain ⟨k, hkadm, hkval⟩ := hwitness
    have hkMem : k ∈ admissibleIndices N m :=
      mem_admissibleIndices_iff.mpr hkadm
    have hGdvd : G N m ∣ N.choose k :=
      G_dvd_choose hkMem
    by_contra hnot
    have hlt : r < padicValNat p (G N m) :=
      Nat.lt_of_not_ge hnot
    have hpG : p ^ (r + 1) ∣ G N m :=
      (padicValNat_dvd_iff_le hGne).2 hlt
    have hpChoose : p ^ (r + 1) ∣ N.choose k :=
      hpG.trans hGdvd
    have hchooseNe : N.choose k ≠ 0 :=
      Nat.choose_ne_zero_iff.mpr hkadm.2.1.le
    have hle : r + 1 ≤ padicValNat p (N.choose k) :=
      (padicValNat_dvd_iff_le hchooseNe).1 hpChoose
    rw [hkval] at hle
    exact (Nat.not_succ_le_self r) (by
      simpa [Nat.succ_eq_add_one] using hle)
  · rw [← padicValNat_dvd_iff_le hGne]
    rw [G, Finset.dvd_gcd_iff]
    intro k hk
    have hkadm : Admissible N m k :=
      mem_admissibleIndices_iff.mp hk
    have hchooseNe : N.choose k ≠ 0 :=
      Nat.choose_ne_zero_iff.mpr hkadm.2.1.le
    exact (padicValNat_dvd_iff_le hchooseNe).2 (hlower k hkadm)
end PascalMinusOne
