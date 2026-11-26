-- Prove2me | solution 1 for RHHeight1000.gram_zero661_exists
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T10:00:27.602999+00:00
-- url     : https://prove2.me/submissions/f506f920-7345-4e8b-b9e0-9fcff3cd00b6

import Definitions.Def_RHT1000_Support_20261118_S003
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.defProp false
set_option linter.auxLemma false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort146
section
namespace Enclosure
theorem isNear_verify_le (X q eps : ℝ) (cneg qneg : Bool) (cn cd rn rd qn qd en ed : ℕ)
    (hcert : Real.IsNear X cneg cn cd rn rd)
    (hq : q = sfrac qneg qn qd) (heps : eps = sfrac false en ed)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hqd : Nat.ble 1 qd) (hed : Nat.ble 1 ed)
    (hlo : Nat.ble ((((numPos qneg qn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((qd.mul ed).mul rd))).add
              (rn.mul ((cd.mul qd).mul ed)))
            ((((numPos cneg cn).mul ((qd.mul ed).mul rd)).add
              ((numNeg qneg qn).mul ((ed.mul cd).mul rd))).add
              (en.mul ((qd.mul cd).mul rd))))
    (hhi : Nat.ble ((((numPos cneg cn).mul ((qd.mul ed).mul rd)).add
              ((numNeg qneg qn).mul ((ed.mul cd).mul rd))).add
              (rn.mul ((cd.mul qd).mul ed)))
            ((((numPos qneg qn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((qd.mul ed).mul rd))).add
              (en.mul ((qd.mul cd).mul rd)))) :
    |X - q| ≤ eps := by
  subst hq heps
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hqdR : (0:ℝ) < qd := pos_real_of_ble hqd
  have hedR : (0:ℝ) < ed := pos_real_of_ble hed
  have heps : sfrac false en ed = (en : ℝ) / ed := by simp [sfrac]
  rw [Real.IsNear, abs_le] at hcert
  have hloR : sfrac qneg qn qd - (en : ℝ) / ed ≤ sfrac cneg cn cd - (rn : ℝ) / rd := by
    rw [sfrac_eq_parts qneg qn qd, sfrac_eq_parts cneg cn cd,
      div_sub_div _ _ hqdR.ne' hedR.ne', div_sub_div _ _ hcdR.ne' hrdR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos qneg qn * (ed * cd * rd) + numNeg cneg cn * (qd * ed * rd)
                + rn * (cd * qd * ed) : ℕ) : ℝ)
            ≤ ((numPos cneg cn * (qd * ed * rd) + numNeg qneg qn * (ed * cd * rd)
                + en * (qd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hlo
    push_cast at hc ⊢; nlinarith [hc]
  have hhiR : sfrac cneg cn cd + (rn : ℝ) / rd ≤ sfrac qneg qn qd + (en : ℝ) / ed := by
    rw [sfrac_eq_parts qneg qn qd, sfrac_eq_parts cneg cn cd,
      div_add_div _ _ hcdR.ne' hrdR.ne', div_add_div _ _ hqdR.ne' hedR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos cneg cn * (qd * ed * rd) + numNeg qneg qn * (ed * cd * rd)
                + rn * (cd * qd * ed) : ℕ) : ℝ)
            ≤ ((numPos qneg qn * (ed * cd * rd) + numNeg cneg cn * (qd * ed * rd)
                + en * (qd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hhi
    push_cast at hc ⊢; nlinarith [hc]
  rw [heps, abs_le]
  exact ⟨by linarith [hcert.1, hloR], by linarith [hcert.2, hhiR]⟩
theorem isNear_verify_le_center (X q eps : ℝ) (neg : Bool) (cn cd rn rd qn qd en ed : ℕ)
    (hcert : Real.IsNear X neg cn cd rn rd)
    (hq : q = sfrac neg qn qd) (heps : eps = sfrac false en ed)
    (hcd : Nat.ble 1 cd) (hqd : Nat.ble 1 qd) (hrd : Nat.ble 1 rd) (hed : Nat.ble 1 ed)
    (hsame : (qn.mul cd).beq (cn.mul qd)) (hle : Nat.ble (rn.mul ed) (en.mul rd)) :
    |X - q| ≤ eps := by
  subst hq heps
  simp only [Nat.beq_eq, Nat.ble_eq, Nat.mul_eq] at hsame hle
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hqdR : (0:ℝ) < qd := pos_real_of_ble hqd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hedR : (0:ℝ) < ed := pos_real_of_ble hed
  have hqc : (qn : ℝ) / qd = (cn : ℝ) / cd := by
    rw [div_eq_div_iff hqdR.ne' hcdR.ne']; exact_mod_cast hsame
  have hqcenter : sfrac neg qn qd = sfrac neg cn cd := by unfold sfrac; rw [hqc]
  rw [hqcenter]
  have hcert' : |X - sfrac neg cn cd| ≤ (rn : ℝ) / rd := hcert
  refine hcert'.trans ?_
  rw [show sfrac false en ed = (en : ℝ) / ed from by simp [sfrac], div_le_div_iff₀ hrdR hedR]
  exact_mod_cast hle
theorem Real.IsNear.neg_val {x : ℝ} {cn cd rn rd : ℕ}
    (h : Real.IsNear x true cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd)
    (hlt : Nat.blt (rn.mul cd) (cn.mul rd)) : x < 0 := by
  simp only [Nat.blt_eq, Nat.mul_eq] at hlt
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hu := h.upper
  rw [sfrac_true_div, neg_div] at hu
  have hcross : (rn : ℝ) * cd < (cn : ℝ) * rd := by exact_mod_cast hlt
  have hlt' : (rn : ℝ) / rd < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ hrdR hcdR]
    linarith
  linarith
theorem Real.IsNear.pos_val {x : ℝ} {cn cd rn rd : ℕ}
    (h : Real.IsNear x false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd)
    (hlt : Nat.blt (rn.mul cd) (cn.mul rd)) : 0 < x := by
  simp only [Nat.blt_eq, Nat.mul_eq] at hlt
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hl := h.lower
  rw [sfrac_false_div] at hl
  have hcross : (rn : ℝ) * cd < (cn : ℝ) * rd := by exact_mod_cast hlt
  have hlt' : (rn : ℝ) / rd < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ hrdR hcdR]
    linarith
  linarith
theorem norm_gt_of_isNear {x e : ℝ} {nx ne' : Bool} {cnx cdx rnx rdx cne cde rne rde : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (he : Real.IsNear e ne' cne cde rne rde)
    (hcdx : Nat.ble 1 cdx) (hrdx : Nat.ble 1 rdx) (hcde : Nat.ble 1 cde) (hrde : Nat.ble 1 rde)
    (h : Nat.blt ((((numPos ne' cne).mul (rde.mul (cdx.mul rdx))).add
            (rne.mul (cde.mul (cdx.mul rdx)))).add
            (rnx.mul (cde.mul (rde.mul cdx))))
          ((cnx.mul (cde.mul (rde.mul rdx))).add
            ((numNeg ne' cne).mul (rde.mul (cdx.mul rdx))))) :
    ‖x‖ > e := by
  simp only [Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at h
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hcdeR : (0:ℝ) < cde := pos_real_of_ble hcde
  have hrdeR : (0:ℝ) < rde := pos_real_of_ble hrde
  have habs : (cnx : ℝ) / cdx - (rnx : ℝ) / rdx ≤ |x| := by
    have h1 : |sfrac nx cnx cdx| - |x - sfrac nx cnx cdx| ≤ |x| := by
      have := abs_sub_abs_le_abs_sub (sfrac nx cnx cdx) x
      have habs2 : |sfrac nx cnx cdx - x| = |x - sfrac nx cnx cdx| := abs_sub_comm _ _
      linarith [this, habs2 ▸ this]
    rw [abs_sfrac] at h1
    have h2 : |x - sfrac nx cnx cdx| ≤ (rnx : ℝ) / rdx := hx
    linarith
  have hup := he.upper
  have hcR : ((numPos ne' cne * (rde * (cdx * rdx)) + rne * (cde * (cdx * rdx))
        + rnx * (cde * (rde * cdx)) : ℕ) : ℝ)
      < ((cnx * (cde * (rde * rdx)) + numNeg ne' cne * (rde * (cdx * rdx)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcR
  have hkey : sfrac ne' cne cde + (rne : ℝ) / rde < (cnx : ℝ) / cdx - (rnx : ℝ) / rdx := by
    rw [sfrac_eq_parts]
    rw [div_add_div _ _ hcdeR.ne' hrdeR.ne', div_sub_div _ _ hcdxR.ne' hrdxR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcR]
  rw [Real.norm_eq_abs, gt_iff_lt]
  linarith
theorem gt_of_isNear {x e : ℝ} {nx ne' : Bool} {cnx cdx rnx rdx cne cde rne rde : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (he : Real.IsNear e ne' cne cde rne rde)
    (hcdx : Nat.ble 1 cdx) (hrdx : Nat.ble 1 rdx) (hcde : Nat.ble 1 cde) (hrde : Nat.ble 1 rde)
    (h : Nat.blt ((((numPos ne' cne).mul (rde.mul (cdx.mul rdx))).add
            (rne.mul (cde.mul (cdx.mul rdx)))).add
          (((numNeg nx cnx).mul (rdx.mul (cde.mul rde))).add
            (rnx.mul (cdx.mul (cde.mul rde)))))
          (((numPos nx cnx).mul (rdx.mul (cde.mul rde))).add
            ((numNeg ne' cne).mul (rde.mul (cdx.mul rdx))))) :
    x > e := by
  simp only [Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at h
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hcdeR : (0:ℝ) < cde := pos_real_of_ble hcde
  have hrdeR : (0:ℝ) < rde := pos_real_of_ble hrde
  have hlo : sfrac nx cnx cdx - (rnx : ℝ) / rdx ≤ x := by
    have h1 : |x - sfrac nx cnx cdx| ≤ (rnx : ℝ) / rdx := hx
    linarith [(abs_le.mp h1).1]
  have hup : e ≤ sfrac ne' cne cde + (rne : ℝ) / rde := he.upper
  have hcR : ((numPos ne' cne * (rde * (cdx * rdx)) + rne * (cde * (cdx * rdx))
        + (numNeg nx cnx * (rdx * (cde * rde)) + rnx * (cdx * (cde * rde))) : ℕ) : ℝ)
      < ((numPos nx cnx * (rdx * (cde * rde))
        + numNeg ne' cne * (rde * (cdx * rdx)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcR
  have hkey : sfrac ne' cne cde + (rne : ℝ) / rde < sfrac nx cnx cdx - (rnx : ℝ) / rdx := by
    rw [sfrac_eq_parts, sfrac_eq_parts,
      div_add_div _ _ hcdeR.ne' hrdeR.ne', div_sub_div _ _ hcdxR.ne' hrdxR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcR]
  linarith
end Enclosure
end
end CertificatePort146


section CertificatePort147
section
namespace Enclosure
theorem Real.IsNear.of_eq {x y : ℝ} {n : Bool} {cn cd rn rd : ℕ}
    (he : x = y) (h : Real.IsNear y n cn cd rn rd) : Real.IsNear x n cn cd rn rd := by
  rw [he]; exact h
theorem sum_Ico_consec_real (f : ℕ → ℝ) (a m b : ℕ)
    (hab : Nat.ble a m = true) (hmb : Nat.ble m b = true) :
    (∑ i ∈ Finset.Ico a b, f i) = (∑ i ∈ Finset.Ico a m, f i) + (∑ i ∈ Finset.Ico m b, f i) :=
  (Finset.sum_Ico_consecutive f (Nat.le_of_ble_eq_true hab) (Nat.le_of_ble_eq_true hmb)).symm
theorem sum_Ico_width_one_real (f : ℕ → ℝ) (a b : ℕ) (h : Nat.beq b (a.add 1) = true) :
    (∑ i ∈ Finset.Ico a b, f i) = f a := by
  have hb : b = a + 1 := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.sum_Ico_succ_top (Nat.le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]
theorem Real.IsNear.sum_Ico_empty (f : ℕ → ℝ) (a b : ℕ) (h : Nat.beq a b = true) :
    Real.IsNear (∑ i ∈ Finset.Ico a b, f i) false (nat_lit 0) (nat_lit 1) (nat_lit 0)
      (nat_lit 1) := by
  have hb : a = b := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.Ico_self, Finset.sum_empty]
  simp [Real.IsNear, sfrac]
theorem sum_range_eq_Ico_real (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) = (∑ i ∈ Finset.Ico 0 n, f i) := by
  rw [Finset.range_eq_Ico]
end Enclosure
end
end CertificatePort147


section CertificatePort148
section
end
end CertificatePort148


section CertificatePort149
section
namespace BSN
open Enclosure
open _root_.Real
def argRoundOk (u v u' v' Dp D : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) v)
    (Nat.add (Nat.sub (nat_lit 1) v')
    (Nat.add (Nat.sub (nat_lit 1) Dp)
    (Nat.add (Nat.sub (nat_lit 1) D)
    (Nat.add (Nat.sub (u'.mul v) (u.mul v'))
             (Nat.sub (Nat.add (Nat.mul (D.mul Dp) (Nat.sub (u.mul v') (u'.mul v)))
                               (Nat.mul D (v.mul v')))
                      (Nat.mul Dp (v.mul v'))))))))
    (nat_lit 0)
private theorem argRoundOk_parts {u v u' v' Dp D : ℕ} (hs : argRoundOk u v u' v' Dp D = true) :
    1 ≤ v ∧ 1 ≤ v' ∧ 1 ≤ Dp ∧ 1 ≤ D ∧ u' * v ≤ u * v' ∧
      D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v') := by
  simp only [argRoundOk, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, z6⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.le_of_sub_eq_zero z1, Nat.le_of_sub_eq_zero z2, Nat.le_of_sub_eq_zero z3,
    Nat.le_of_sub_eq_zero z4, Nat.le_of_sub_eq_zero z5, Nat.le_of_sub_eq_zero z6⟩
private theorem arg_round_bound {u v u' v' Dp D : ℕ}
    (hv : 1 ≤ v) (hv' : 1 ≤ v') (hDp : 1 ≤ Dp) (hD : 1 ≤ D)
    (hle : u' * v ≤ u * v')
    (hmain : D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v')) :
    |(u : ℝ) / v - (u' : ℝ) / v'| + 1 / Dp ≤ 1 / D := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv'R : (0 : ℝ) < v' := by exact_mod_cast hv'
  have hDpR : (0 : ℝ) < Dp := by exact_mod_cast hDp
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hleR : ((u' : ℝ) * v) ≤ (u : ℝ) * v' := by exact_mod_cast hle
  have hnn : (0 : ℝ) ≤ (u : ℝ) * v' - (u' : ℝ) * v := by linarith
  have hsub : ((u * v' - u' * v : ℕ) : ℝ) = (u : ℝ) * v' - (u' : ℝ) * v := by
    have hle' : (u' * v : ℕ) ≤ (u * v' : ℕ) := hle
    push_cast [Nat.cast_sub hle']
    ring
  have hrw : (u : ℝ) / v - (u' : ℝ) / v' = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    field_simp
  have habs : |(u : ℝ) / v - (u' : ℝ) / v'| = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    rw [hrw]
    exact abs_of_nonneg (div_nonneg hnn (by positivity))
  have hmainR : (D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v') ≤ Dp * (v * v') := by
    have hc : ((D * Dp * (u * v' - u' * v) + D * (v * v') : ℕ) : ℝ)
        ≤ ((Dp * (v * v') : ℕ) : ℝ) := by
      exact_mod_cast hmain
    push_cast [hsub] at hc
    linarith
  rw [← sub_nonneg, habs]
  have key : (1 : ℝ) / D - (((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') + 1 / Dp)
      = ((Dp : ℝ) * (v * v') - ((D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v')))
        / ((D : ℝ) * Dp * (v * v')) := by
    field_simp
  rw [key]
  exact div_nonneg (by linarith) (by positivity)
theorem cos_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.cos ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.cos ((u : ℝ) / v) - Real.cos ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_cos_sub_cos_le _ _
  have h' : |Real.cos ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.cos ((u : ℝ) / v)) (Real.cos ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.cos ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres
theorem sin_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.sin ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.sin ((u : ℝ) / v) - Real.sin ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_sin_sub_sin_le _ _
  have h' : |Real.sin ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.sin ((u : ℝ) / v)) (Real.sin ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.sin ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres
theorem sin_quad0 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ)) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi]
theorem sin_quad1 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 1) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi_div_two]
theorem sin_quad2 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi]
theorem sin_quad3 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 3) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi, sin_add_pi_div_two]
theorem sin_triple_step (θ q qnew : ℝ) (D Rho D' : ℝ)
    (hq1 : |q| ≤ 1)
    (hq : |Real.sin θ - q| ≤ 1 / D)
    (hround : |(3 * q - 4 * q ^ 3) - qnew| ≤ 1 / Rho)
    (hcomb : 15 * (1 / D) + 1 / Rho ≤ 1 / D') :
    |Real.sin (3 * θ) - qnew| ≤ 1 / D' := by
  rw [Real.sin_three_mul]
  have hs1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hfirst : |3 * Real.sin θ - 4 * Real.sin θ ^ 3 - (3 * q - 4 * q ^ 3)| ≤ 15 * (1 / D) := by
    have hfac : 3 * Real.sin θ - 4 * Real.sin θ ^ 3 - (3 * q - 4 * q ^ 3)
        = (Real.sin θ - q) * (3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)) := by ring
    rw [hfac, abs_mul]
    have hsum : |Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2| ≤ 3 := by
      calc |Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2|
          ≤ |Real.sin θ ^ 2| + |Real.sin θ * q| + |q ^ 2| :=
            (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
        _ ≤ 1 + 1 + 1 := by
            gcongr
            · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs1
            · rw [abs_mul]; exact mul_le_one₀ hs1 (abs_nonneg _) hq1
            · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hq1
        _ = 3 := by norm_num
    have hc : |3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)| ≤ 15 :=
      calc |3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)|
          ≤ |(3 : ℝ)| + |4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)| := abs_sub _ _
        _ = 3 + 4 * |Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2| := by
            rw [abs_mul]; norm_num
        _ ≤ 3 + 4 * 3 := by gcongr
        _ = 15 := by norm_num
    calc |Real.sin θ - q| * |3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)|
        ≤ (1 / D) * 15 := by
          apply mul_le_mul hq hc (abs_nonneg _)
          exact le_trans (abs_nonneg _) hq
      _ = 15 * (1 / D) := by ring
  calc |3 * Real.sin θ - 4 * Real.sin θ ^ 3 - qnew|
      ≤ |3 * Real.sin θ - 4 * Real.sin θ ^ 3 - (3 * q - 4 * q ^ 3)|
          + |(3 * q - 4 * q ^ 3) - qnew| := abs_sub_le _ _ _
    _ ≤ 15 * (1 / D) + 1 / Rho := add_le_add hfirst hround
    _ ≤ 1 / D' := hcomb
theorem sin_triple_step_dyadic (nq : Bool) (cq Q : ℕ) (nq' : Bool) (cq' Q' D D' : ℕ) (θ : ℝ)
    (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q') (hD : Nat.ble 1 D) (hD' : Nat.ble 1 D')
    (hq1a : (numPos nq cq).ble ((numNeg nq cq).add Q))
    (hq1b : (numNeg nq cq).ble ((numPos nq cq).add Q))
    (hround1 : (((numPos nq' cq').mul (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')).ble
      ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))))
    (hround2 : ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))).blt
      ((((numPos nq' cq').mul (Q.pow 3)).add (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')))
    (hcomb : (((Nat.mul 15 Q').add D).mul D').ble (D.mul Q'))
    (hstep : Real.IsNear (Real.sin θ) nq cq Q 1 D) :
    Real.IsNear (Real.sin (3 * θ)) nq' cq' Q' 1 D' := by
  set mp := numPos nq cq with hmp_def
  set mn := numNeg nq cq with hmn_def
  set mp' := numPos nq' cq' with hmp'_def
  set mn' := numNeg nq' cq' with hmn'_def
  rw [Real.IsNear, Nat.cast_one, sfrac_eq_parts nq cq Q, ← hmp_def, ← hmn_def] at hstep
  rw [Real.IsNear, Nat.cast_one, sfrac_eq_parts nq' cq' Q', ← hmp'_def, ← hmn'_def]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hq1a hq1b hround1 hround2 hcomb
  have hQr : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hQ'r : (0 : ℝ) < Q' := pos_real_of_ble hQ'
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hD'r : (0 : ℝ) < D' := pos_real_of_ble hD'
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQr
  have hQ'ne : (Q' : ℝ) ≠ 0 := ne_of_gt hQ'r
  set q : ℝ := ((mp : ℝ) - mn) / Q with hq_def
  set qn : ℝ := ((mp' : ℝ) - mn') / Q' with hqn_def
  have hq1 : |q| ≤ 1 := by
    rw [hq_def, abs_div, abs_of_pos hQr, div_le_one hQr, abs_le]
    refine ⟨?_, ?_⟩
    · have : (mn : ℝ) ≤ (mp : ℝ) + Q := by exact_mod_cast hq1b
      linarith
    · have : (mp : ℝ) ≤ (mn : ℝ) + Q := by exact_mod_cast hq1a
      linarith
  have C1z : ((mp' : ℤ) * Q ^ 3 + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q')
      ≤ ((3 * mp * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3) := by
    exact_mod_cast hround1
  have C2z : ((3 * (mp : ℤ) * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3)
      < ((mp' : ℤ) * Q ^ 3 + Q ^ 3 + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q') := by
    exact_mod_cast hround2
  set M : ℤ := 3 * ((mp : ℤ) - mn) * Q ^ 2 - 4 * ((mp : ℤ) - mn) ^ 3 with hM_def
  set s' : ℤ := (mp' : ℤ) - mn' with hs'_def
  have hN0 : (0 : ℤ) ≤ M * Q' - s' * Q ^ 3 := by
    have hexp : M * (Q' : ℤ) - s' * Q ^ 3
        = ((3 * (mp : ℤ) * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3)
          - ((mp' : ℤ) * Q ^ 3 + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q') := by
      rw [hM_def, hs'_def]; ring
    rw [hexp]; linarith [C1z]
  have hN1 : M * (Q' : ℤ) - s' * Q ^ 3 < Q ^ 3 := by
    have hexp : M * (Q' : ℤ) - s' * Q ^ 3 - Q ^ 3
        = ((3 * (mp : ℤ) * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3)
          - ((mp' : ℤ) * Q ^ 3 + Q ^ 3
                + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q') := by
      rw [hM_def, hs'_def]; ring
    linarith [C2z, hexp]
  have hround : |(3 * q - 4 * q ^ 3) - qn| ≤ 1 / (Q' : ℝ) := by
    have hval : 3 * q - 4 * q ^ 3 - qn
        = ((M : ℝ) * Q' - (s' : ℝ) * Q ^ 3) / ((Q : ℝ) ^ 3 * Q') := by
      rw [hq_def, hqn_def, hM_def, hs'_def]
      push_cast
      field_simp
    rw [hval]
    have hden : (0 : ℝ) < (Q : ℝ) ^ 3 * Q' := by positivity
    have hN0r : (0 : ℝ) ≤ (M : ℝ) * Q' - (s' : ℝ) * Q ^ 3 := by exact_mod_cast hN0
    have hN1r : (M : ℝ) * Q' - (s' : ℝ) * Q ^ 3 < Q ^ 3 := by exact_mod_cast hN1
    rw [abs_of_nonneg (div_nonneg hN0r (le_of_lt hden)), div_le_div_iff₀ hden hQ'r, one_mul]
    have hmul : ((M : ℝ) * Q' - (s' : ℝ) * Q ^ 3) * Q' ≤ (Q : ℝ) ^ 3 * Q' :=
      mul_le_mul_of_nonneg_right (le_of_lt hN1r) (le_of_lt hQ'r)
    linarith [hmul]
  have hcombr : 15 * (1 / (D : ℝ)) + 1 / (Q' : ℝ) ≤ 1 / (D' : ℝ) := by
    have hlhs : 15 * (1 / (D : ℝ)) + 1 / (Q' : ℝ) = (15 * (Q' : ℝ) + D) / ((D : ℝ) * Q') := by
      field_simp
    rw [hlhs, div_le_div_iff₀ (mul_pos hDr hQ'r) hD'r, one_mul]
    have key : (15 * (Q' : ℝ) + D) * D' ≤ (D : ℝ) * Q' := by exact_mod_cast hcomb
    linarith [key]
  exact sin_triple_step θ q qn (D : ℝ) (Q' : ℝ) (D' : ℝ) hq1 hstep hround hcombr
theorem sin_triple_step_arg (a dj dj1 : ℕ) (nq : Bool) (cq Q : ℕ) (nq' : Bool) (cq' Q' D D' : ℕ)
    (hdj1 : dj1.beq (Nat.mul 3 dj))
    (hdj : Nat.ble 1 dj)
    (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q') (hD : Nat.ble 1 D) (hD' : Nat.ble 1 D')
    (hq1a : (numPos nq cq).ble ((numNeg nq cq).add Q))
    (hq1b : (numNeg nq cq).ble ((numPos nq cq).add Q))
    (hround1 : (((numPos nq' cq').mul (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')).ble
      ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))))
    (hround2 : ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))).blt
      ((((numPos nq' cq').mul (Q.pow 3)).add (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')))
    (hcomb : (((Nat.mul 15 Q').add D).mul D').ble (D.mul Q'))
    (hstep : Real.IsNear (Real.sin ((a : ℝ) / (dj1 : ℝ))) nq cq Q 1 D) :
    Real.IsNear (Real.sin ((a : ℝ) / (dj : ℝ))) nq' cq' Q' 1 D' := by
  simp only [Nat.beq_eq, Nat.mul_eq] at hdj1
  subst hdj1
  have hdjpos : 0 < dj := pos_of_ble hdj
  have hdjr : (dj : ℝ) ≠ 0 := by exact_mod_cast hdjpos.ne'
  have h3 : (3 : ℝ) * ((a : ℝ) / ((3 * dj : ℕ) : ℝ)) = (a : ℝ) / (dj : ℝ) := by
    push_cast
    field_simp
  rw [Real.IsNear, ← h3, ← Real.IsNear]
  exact sin_triple_step_dyadic nq cq Q nq' cq' Q' D D' ((a : ℝ) / ((3 * dj : ℕ) : ℝ))
    hQ hQ' hD hD' hq1a hq1b hround1 hround2 hcomb hstep
theorem reduce_core_val (F r rc q B inner Dinv : ℝ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hlip : |g r - g rc| ≤ |r - rc|)
    (hB : |r - rc| ≤ B)
    (hinner : |g rc - q| ≤ inner)
    (htot : B + inner ≤ Dinv) :
    |F - ε * q| ≤ Dinv := by
  have h1 : |F - ε * q| ≤ |g r - g rc| + |g rc - q| := by
    rw [hquad]
    calc |ε * g r - ε * q| = |ε| * |g r - q| := by rw [← mul_sub, abs_mul]
      _ = |g r - q| := by rw [hε, one_mul]
      _ ≤ |g r - g rc| + |g rc - q| := abs_sub_le _ _ _
  calc |F - ε * q| ≤ |g r - g rc| + |g rc - q| := h1
    _ ≤ B + inner := add_le_add (hlip.trans hB) hinner
    _ ≤ Dinv := htot
theorem reduce_step_val (F x r rcv Pr val : ℝ) (k E Dp D : ℕ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hr : r = x - (k : ℝ) * (π / 2))
    (hlip : |g r - g rcv| ≤ |r - rcv|)
    (hrc : rcv = x - (k : ℝ) * (Pr / 2))
    (hpi : |Real.pi - Pr| ≤ 1 / (E : ℝ))
    (hinner : |g rcv - val| ≤ 1 / (Dp : ℝ))
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    |F - ε * val| ≤ 1 / (D : ℝ) := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at htot
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have hDpr : (0 : ℝ) < Dp := pos_real_of_ble hDp
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hB : |r - rcv| ≤ (k : ℝ) / (2 * E) := by
    rw [hr, hrc]
    have e : (x - (k : ℝ) * (π / 2)) - (x - (k : ℝ) * (Pr / 2)) = (k : ℝ) * (Pr / 2 - π / 2) := by
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    have hhalf : |Pr / 2 - π / 2| ≤ 1 / (2 * E) := by
      have e2 : Pr / 2 - π / 2 = -(Real.pi - Pr) / 2 := by ring
      rw [e2, abs_div, abs_neg, abs_two]
      calc |Real.pi - Pr| / 2 ≤ (1 / (E : ℝ)) / 2 := by gcongr
        _ = 1 / (2 * E) := by ring
    calc (k : ℝ) * |Pr / 2 - π / 2| ≤ (k : ℝ) * (1 / (2 * E)) := by gcongr
      _ = (k : ℝ) / (2 * E) := by ring
  have htotR : (k : ℝ) / (2 * E) + 1 / (Dp : ℝ) ≤ 1 / (D : ℝ) := by
    have hc : ((k * D * Dp + 2 * E * D : ℕ) : ℝ) ≤ ((2 * E * Dp : ℕ) : ℝ) := by exact_mod_cast htot
    push_cast at hc
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hc, hEr, hDpr, hDr]
  exact reduce_core_val F r rcv val ((k : ℝ) / (2 * E)) (1 / Dp) (1 / D) ε g hε hquad
    hlip hB hinner htotR
theorem reduce_quad_val (F x rcv : ℝ) (g : ℝ → ℝ) (ε : ℝ) (Pc PQ : ℕ) (ineg oneg : Bool)
    (icn Qd k E Dp D : ℕ)
    (hε : |ε| = 1)
    (hquad : F = ε * g (x - (k : ℝ) * (π / 2)))
    (hlip : ∀ a b, |g a - g b| ≤ |a - b|)
    (hsign : sfrac oneg icn Qd = ε * sfrac ineg icn Qd)
    (hrc : rcv = x - (k : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (g rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear F oneg icn Qd 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hpi
  rw [← sfrac_false_div Pc PQ] at hpi
  rw [Real.IsNear, Nat.cast_one] at hinner
  rw [Real.IsNear, Nat.cast_one, hsign]
  exact reduce_step_val F x (x - (k : ℝ) * (π / 2)) rcv (sfrac false Pc PQ)
    (sfrac ineg icn Qd) k E Dp D ε g hε hquad rfl (hlip _ _) hrc hpi hinner hE hDp hD htot
theorem cos_quad0 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ)) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi]
theorem cos_quad1 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 1) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi_div_two]
theorem cos_quad2 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi]
theorem cos_quad3 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 3) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi, cos_add_pi_div_two, neg_neg]
theorem sin_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← sin_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem sin_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq + 1) E Dp D abs_one
    (by rw [one_mul, ← sin_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem sin_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem sin_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 3) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem cos_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← cos_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem cos_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 1) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem cos_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot
theorem cos_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq + 3) E Dp D
    abs_one
    (by rw [one_mul, ← cos_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot
theorem sin_reduce_arg_pos_rat (a b Pc PQ k u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add (k.mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - (k : ℝ) * (sfrac false Pc PQ / 2) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hlink hv
  subst hv
  rw [sfrac_false_div]
  have hQr : (0 : ℝ) < PQ := pos_real_of_ble hQ
  have hbr : (0 : ℝ) < b := pos_real_of_ble hb
  have hlinkR : (2 * a * PQ : ℝ) = (u + k * (b * Pc) : ℝ) := by exact_mod_cast hlink
  push_cast
  field_simp
  ring_nf
  linarith [hlinkR]
theorem sin_reduce_arg_pos_rat_q0 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.mul 4 qq).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq) u v hlink hv hQ hb
theorem sin_reduce_arg_pos_rat_q1 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 1).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 1) u v hlink hv hQ hb
theorem sin_reduce_arg_pos_rat_q2 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 2).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 2) u v hlink hv hQ hb
theorem sin_reduce_arg_pos_rat_q3 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 3).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 3) u v hlink hv hQ hb
end BSN
end
end CertificatePort149


section CertificatePort150
section
namespace Enclosure
def Complex.IsNear (z : ℂ)
    (reNeg : Bool) (reCn reCd reRn reRd : ℕ)
    (imNeg : Bool) (imCn imCd imRn imRd : ℕ) : Prop :=
  Real.IsNear z.re reNeg reCn reCd reRn reRd ∧
  Real.IsNear z.im imNeg imCn imCd imRn imRd
theorem Complex.IsNear.re_isNear {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Real.IsNear z.re reNeg reCn reCd reRn reRd := h.1
theorem Complex.IsNear.im_isNear {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Real.IsNear z.im imNeg imCn imCd imRn imRd := h.2
theorem Complex.IsNear.mk {re im : ℝ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear re reNeg reCn reCd reRn reRd)
    (him : Real.IsNear im imNeg imCn imCd imRn imRd) :
    Complex.IsNear ⟨re, im⟩ reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := ⟨hre, him⟩
theorem Complex.IsNear.neg {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Complex.IsNear (-z) (!reNeg) reCn reCd reRn reRd (!imNeg) imCn imCd imRn imRd := by
  obtain ⟨hre, him⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Complex.neg_re]; exact hre.neg
  · rw [Complex.neg_im]; exact him.neg
theorem Complex.IsNear.add {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re + w.re) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.im + w.im) imN imCn imCd imRn imRd) :
    Complex.IsNear (z + w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.add_re]; exact hre
  · rw [Complex.add_im]; exact him
theorem Complex.IsNear.sub {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re - w.re) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.im - w.im) imN imCn imCd imRn imRd) :
    Complex.IsNear (z - w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.sub_re]; exact hre
  · rw [Complex.sub_im]; exact him
theorem Complex.IsNear.mul {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re * w.re - z.im * w.im) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.re * w.im + z.im * w.re) imN imCn imCd imRn imRd) :
    Complex.IsNear (z * w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re]; exact hre
  · rw [Complex.mul_im]; exact him
def numPosC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) cn 0 neg
def numNegC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 0 cn neg
theorem numPosC_eq (neg : Bool) (cn : ℕ) : numPosC neg cn = numPos neg cn := by
  cases neg <;> rfl
theorem numNegC_eq (neg : Bool) (cn : ℕ) : numNegC neg cn = numNeg neg cn := by
  cases neg <;> rfl
theorem Complex.IsNear.addLitP {z w : ℂ}
    {nxr : Bool} {cnxr cdxr rnxr rdxr : ℕ} {nxi : Bool} {cnxi cdxi rnxi rdxi : ℕ}
    {nyr : Bool} {cnyr cdyr rnyr rdyr : ℕ} {nyi : Bool} {cnyi cdyi rnyi rdyi : ℕ}
    {nRr : Bool} {cnRr cnRr' cdRr' rnRr' rdRr' : ℕ}
    {nRi : Bool} {cnRi cnRi' cdRi' rnRi' rdRi' : ℕ}
    (h1 : Complex.IsNear z nxr cnxr cdxr rnxr rdxr nxi cnxi cdxi rnxi rdxi)
    (h2 : Complex.IsNear w nyr cnyr cdyr rnyr rdyr nyi cnyi cdyi rnyi rdyi)
    (hcdxr : Nat.ble (nat_lit 1) cdxr) (hcdyr : Nat.ble (nat_lit 1) cdyr)
    (hrdxr : Nat.ble (nat_lit 1) rdxr) (hrdyr : Nat.ble (nat_lit 1) rdyr)
    (hnumr : Nat.beq
      (((numPosC nRr cnRr).add ((numNegC nxr cnxr).mul cdyr)).add
        ((numNegC nyr cnyr).mul cdxr))
      (((numNegC nRr cnRr).add ((numPosC nxr cnxr).mul cdyr)).add
        ((numPosC nyr cnyr).mul cdxr)))
    (hcdRr' : Nat.ble (nat_lit 1) cdRr') (hrdRr' : Nat.ble (nat_lit 1) rdRr')
    (hcr : Nat.beq (cnRr.mul cdRr') (cnRr'.mul (cdxr.mul cdyr)))
    (hrr : Nat.ble (((rnxr.mul rdyr).add (rnyr.mul rdxr)).mul rdRr')
      (rnRr'.mul (rdxr.mul rdyr)))
    (hcdxi : Nat.ble (nat_lit 1) cdxi) (hcdyi : Nat.ble (nat_lit 1) cdyi)
    (hrdxi : Nat.ble (nat_lit 1) rdxi) (hrdyi : Nat.ble (nat_lit 1) rdyi)
    (hnumi : Nat.beq
      (((numPosC nRi cnRi).add ((numNegC nxi cnxi).mul cdyi)).add
        ((numNegC nyi cnyi).mul cdxi))
      (((numNegC nRi cnRi).add ((numPosC nxi cnxi).mul cdyi)).add
        ((numPosC nyi cnyi).mul cdxi)))
    (hcdRi' : Nat.ble (nat_lit 1) cdRi') (hrdRi' : Nat.ble (nat_lit 1) rdRi')
    (hci : Nat.beq (cnRi.mul cdRi') (cnRi'.mul (cdxi.mul cdyi)))
    (hri : Nat.ble (((rnxi.mul rdyi).add (rnyi.mul rdxi)).mul rdRi')
      (rnRi'.mul (rdxi.mul rdyi))) :
    Complex.IsNear (z + w) nRr cnRr' cdRr' rnRr' rdRr' nRi cnRi' cdRi' rnRi' rdRi' := by
  simp only [numPosC_eq, numNegC_eq] at hnumr hnumi
  exact Complex.IsNear.add
    (Real.IsNear.addLit h1.1 h2.1 hcdxr hcdyr hrdxr hrdyr hnumr hcdRr' hrdRr' hcr hrr)
    (Real.IsNear.addLit h1.2 h2.2 hcdxi hcdyi hrdxi hrdyi hnumi hcdRi' hrdRi' hci hri)
theorem Complex.IsNear.subLitP {z w : ℂ}
    {nxr : Bool} {cnxr cdxr rnxr rdxr : ℕ} {nxi : Bool} {cnxi cdxi rnxi rdxi : ℕ}
    {nyr : Bool} {cnyr cdyr rnyr rdyr : ℕ} {nyi : Bool} {cnyi cdyi rnyi rdyi : ℕ}
    {nRr : Bool} {cnRr cnRr' cdRr' rnRr' rdRr' : ℕ}
    {nRi : Bool} {cnRi cnRi' cdRi' rnRi' rdRi' : ℕ}
    (h1 : Complex.IsNear z nxr cnxr cdxr rnxr rdxr nxi cnxi cdxi rnxi rdxi)
    (h2 : Complex.IsNear w nyr cnyr cdyr rnyr rdyr nyi cnyi cdyi rnyi rdyi)
    (hcdxr : Nat.ble (nat_lit 1) cdxr) (hcdyr : Nat.ble (nat_lit 1) cdyr)
    (hrdxr : Nat.ble (nat_lit 1) rdxr) (hrdyr : Nat.ble (nat_lit 1) rdyr)
    (hnumr : Nat.beq
      (((numPosC nRr cnRr).add ((numNegC nxr cnxr).mul cdyr)).add
        ((numPosC nyr cnyr).mul cdxr))
      (((numNegC nRr cnRr).add ((numPosC nxr cnxr).mul cdyr)).add
        ((numNegC nyr cnyr).mul cdxr)))
    (hcdRr' : Nat.ble (nat_lit 1) cdRr') (hrdRr' : Nat.ble (nat_lit 1) rdRr')
    (hcr : Nat.beq (cnRr.mul cdRr') (cnRr'.mul (cdxr.mul cdyr)))
    (hrr : Nat.ble (((rnxr.mul rdyr).add (rnyr.mul rdxr)).mul rdRr')
      (rnRr'.mul (rdxr.mul rdyr)))
    (hcdxi : Nat.ble (nat_lit 1) cdxi) (hcdyi : Nat.ble (nat_lit 1) cdyi)
    (hrdxi : Nat.ble (nat_lit 1) rdxi) (hrdyi : Nat.ble (nat_lit 1) rdyi)
    (hnumi : Nat.beq
      (((numPosC nRi cnRi).add ((numNegC nxi cnxi).mul cdyi)).add
        ((numPosC nyi cnyi).mul cdxi))
      (((numNegC nRi cnRi).add ((numPosC nxi cnxi).mul cdyi)).add
        ((numNegC nyi cnyi).mul cdxi)))
    (hcdRi' : Nat.ble (nat_lit 1) cdRi') (hrdRi' : Nat.ble (nat_lit 1) rdRi')
    (hci : Nat.beq (cnRi.mul cdRi') (cnRi'.mul (cdxi.mul cdyi)))
    (hri : Nat.ble (((rnxi.mul rdyi).add (rnyi.mul rdxi)).mul rdRi')
      (rnRi'.mul (rdxi.mul rdyi))) :
    Complex.IsNear (z - w) nRr cnRr' cdRr' rnRr' rdRr' nRi cnRi' cdRi' rnRi' rdRi' := by
  simp only [numPosC_eq, numNegC_eq] at hnumr hnumi
  refine Complex.IsNear.sub
    (Real.IsNear.subLit h1.1 h2.1 hcdxr hcdyr hrdxr hrdyr ?_ hcdRr' hrdRr' hcr hrr)
    (Real.IsNear.subLit h1.2 h2.2 hcdxi hcdyi hrdxi hrdyi ?_ hcdRi' hrdRi' hci hri)
  · cases nyr <;> simpa [numPos, numNeg] using hnumr
  · cases nyi <;> simpa [numPos, numNeg] using hnumi
theorem Complex.IsNear.recentre2 {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {rCn' rCd' rRn' rRd' iCn' iCd' iRn' iRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hrcd : Nat.ble (nat_lit 1) rCd) (hrcd' : Nat.ble (nat_lit 1) rCd') (hrrd : Nat.ble
          (nat_lit 1) rRd)
    (hrrd' : Nat.ble (nat_lit 1) rRd')
    (hrfloor : Nat.ble (rCn'.mul rCd) (rCn.mul rCd'))
    (hrrad : Nat.ble
      (((rRn.mul (rCd.mul rCd')).add (((rCn.mul rCd').sub (rCn'.mul rCd)).mul rRd)).mul rRd')
      (rRn'.mul (rRd.mul (rCd.mul rCd'))))
    (hicd : Nat.ble (nat_lit 1) iCd) (hicd' : Nat.ble (nat_lit 1) iCd') (hird : Nat.ble
          (nat_lit 1) iRd)
    (hird' : Nat.ble (nat_lit 1) iRd')
    (hifloor : Nat.ble (iCn'.mul iCd) (iCn.mul iCd'))
    (hirad : Nat.ble
      (((iRn.mul (iCd.mul iCd')).add (((iCn.mul iCd').sub (iCn'.mul iCd)).mul iRd)).mul iRd')
      (iRn'.mul (iRd.mul (iCd.mul iCd')))) :
    Complex.IsNear z rN rCn' rCd' rRn' rRd' iN iCn' iCd' iRn' iRd' :=
  ⟨h.1.recentre hrcd hrcd' hrrd hrrd' hrfloor hrrad,
   h.2.recentre hicd hicd' hird hird' hifloor hirad⟩
theorem Complex.IsNear.recentreRe {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {rCn' rCd' rRn' rRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hrcd : Nat.ble (nat_lit 1) rCd) (hrcd' : Nat.ble (nat_lit 1) rCd') (hrrd : Nat.ble
          (nat_lit 1) rRd)
    (hrrd' : Nat.ble (nat_lit 1) rRd')
    (hrfloor : Nat.ble (rCn'.mul rCd) (rCn.mul rCd'))
    (hrrad : Nat.ble
      (((rRn.mul (rCd.mul rCd')).add (((rCn.mul rCd').sub (rCn'.mul rCd)).mul rRd)).mul rRd')
      (rRn'.mul (rRd.mul (rCd.mul rCd')))) :
    Complex.IsNear z rN rCn' rCd' rRn' rRd' iN iCn iCd iRn iRd :=
  ⟨h.1.recentre hrcd hrcd' hrrd hrrd' hrfloor hrrad, h.2⟩
theorem Complex.IsNear.recentreIm {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {iCn' iCd' iRn' iRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hicd : Nat.ble (nat_lit 1) iCd) (hicd' : Nat.ble (nat_lit 1) iCd') (hird : Nat.ble
          (nat_lit 1) iRd)
    (hird' : Nat.ble (nat_lit 1) iRd')
    (hifloor : Nat.ble (iCn'.mul iCd) (iCn.mul iCd'))
    (hirad : Nat.ble
      (((iRn.mul (iCd.mul iCd')).add (((iCn.mul iCd').sub (iCn'.mul iCd)).mul iRd)).mul iRd')
      (iRn'.mul (iRd.mul (iCd.mul iCd')))) :
    Complex.IsNear z rN rCn rCd rRn rRd iN iCn' iCd' iRn' iRd' :=
  ⟨h.1, h.2.recentre hicd hicd' hird hird' hifloor hirad⟩
theorem Complex.IsNear.of_parts {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear z.re reNeg reCn reCd reRn reRd)
    (him : Real.IsNear z.im imNeg imCn imCd imRn imRd) :
    Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := ⟨hre, him⟩
theorem Complex.IsNear.of_eq {z w : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (he : z = w) (h : Complex.IsNear w reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := by
  rw [he]; exact h
theorem Complex.inv_re_eq_mul (z : ℂ) : (z⁻¹).re = z.re * (Complex.normSq z)⁻¹ := by
  rw [Complex.inv_re, div_eq_mul_inv]
theorem Complex.inv_im_eq_mul (z : ℂ) : (z⁻¹).im = -z.im * (Complex.normSq z)⁻¹ := by
  rw [Complex.inv_im, div_eq_mul_inv, neg_mul]
theorem Complex.normSq_eq_mul_add_mul (z : ℂ) :
    Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z
theorem Complex.arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  have h1 : -(Real.pi / 2) < z.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz)
  have h2 : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [← Complex.tan_arg z, Real.arctan_tan h1 h2]
theorem clog_re_eq (p r q N M : ℕ) (hq : Nat.ble (nat_lit 1) q = true)
    (hN : Nat.beq N ((p.mul p).add (r.mul r)) = true) (hM : Nat.beq M (q.mul q) = true) :
    (Complex.log ⟨sfrac false p q, sfrac false r q⟩).re
      = sfrac false (nat_lit 1) (nat_lit 2) * Real.log (sfrac false N M) := by
  obtain rfl := Nat.eq_of_beq_eq_true hN
  obtain rfl := Nat.eq_of_beq_eq_true hM
  have hqR : (0 : ℝ) < q := pos_real_of_ble hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  have hnorm : Complex.normSq ⟨sfrac false p q, sfrac false r q⟩
      = sfrac false ((p.mul p).add (r.mul r)) (q.mul q) := by
    rw [Complex.normSq_mk]
    simp only [sfrac_false_div, Nat.mul_eq, Nat.add_eq]
    push_cast
    field_simp
  rw [Complex.log_re, Complex.norm_def, hnorm, sfrac_false_div, sfrac_false_div,
    Real.log_sqrt (by positivity)]
  push_cast
  ring
theorem clog_im_eq (p r q : ℕ) (hp : Nat.ble (nat_lit 1) p
      = true) (hq : Nat.ble (nat_lit 1) q = true) :
    (Complex.log ⟨sfrac false p q, sfrac false r q⟩).im = Real.arctan ((r : ℝ) / p) := by
  have hpR : (0 : ℝ) < p := pos_real_of_ble hp
  have hqR : (0 : ℝ) < q := pos_real_of_ble hq
  have hproj_re : (⟨sfrac false p q, sfrac false r q⟩ : ℂ).re = sfrac false p q := rfl
  have hproj_im : (⟨sfrac false p q, sfrac false r q⟩ : ℂ).im = sfrac false r q := rfl
  have hre : (0 : ℝ) < (⟨sfrac false p q, sfrac false r q⟩ : ℂ).re := by
    rw [hproj_re, sfrac_false_div]
    exact div_pos hpR hqR
  rw [Complex.log_im, Complex.arg_eq_arctan_of_re_pos hre, hproj_re, hproj_im,
    sfrac_false_div, sfrac_false_div, div_div_div_cancel_right₀ hqR.ne']
end Enclosure
end
end CertificatePort150


section CertificatePort151
section
open MeasureTheory Real Filter Topology
open scoped Nat
private theorem abs_eq_neg_one_pow_mul {m : ℕ} {y : ℝ} (h : 0 ≤ (-1 : ℝ) ^ m * y) :
    |y| = (-1 : ℝ) ^ m * y := by
  rw [← abs_of_nonneg h, abs_mul, abs_neg_one_pow, one_mul]
private theorem hasSum_one_div_nat_pow_bernoulli (m : ℕ) (hm0 : m ≠ 0) :
    HasSum (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 * m))
      ((-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! * (bernoulli (2 * m) : ℝ)) := by
  have h2 : (2 : ℝ) ^ (2 * m - 1) * 2 = 2 ^ (2 * m) := by rw [← pow_succ]; congr 1; lia
  rw [show (-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! * (bernoulli (2 * m) : ℝ)
        = (-1 : ℝ) ^ (m + 1) * 2 ^ (2 * m - 1) * π ^ (2 * m) * (bernoulli (2 * m) : ℝ)
            / (2 * m)! from by rw [mul_pow, ← h2]; ring]
  exact hasSum_zeta_nat hm0
theorem bernoulliFun_sub_self_eq_tsum_cos (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)
      = (-1 : ℝ) ^ (m + 1) * (2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m))
          * ∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m) := by
  have hm0 : m ≠ 0 := by lia
  set B : ℝ := bernoulliFun (2 * m) (Int.fract x)
  set b : ℝ := (bernoulli (2 * m) : ℝ)
  set Cval : ℝ := (-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! with hCval
  have hfracmem : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hcos : ∀ n : ℕ, cos (2 * π * n * Int.fract x) = cos (2 * π * n * x) := by
    intro n
    have heq : (2 : ℝ) * π * n * x
        = 2 * π * n * Int.fract x + ((n : ℤ) * ⌊x⌋ : ℤ) * (2 * π) := by
      have := Int.floor_add_fract x
      push_cast
      linear_combination (-(2 * π * (n : ℝ))) * this
    rw [heq, Real.cos_add_int_mul_two_pi]
  have hsx : HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 * m) * cos (2 * π * n * x)) (Cval * B) := by
    have h := hasSum_one_div_nat_pow_mul_cos hm0 hfracmem
    rw [show (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * m))).eval (Int.fract x)
          = B from rfl] at h
    simpa only [hcos] using h
  have hs0 : HasSum (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 * m)) (Cval * b) :=
    hasSum_one_div_nat_pow_bernoulli m hm0
  have hdiff := hsx.sub hs0
  have key : (∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m)) = Cval * B - Cval * b := by
    rw [← hdiff.tsum_eq]; exact tsum_congr fun n ↦ by ring
  rw [key, hCval]
  set a : ℝ := (-1 : ℝ) ^ (m + 1) with ha
  have ha2 : a * a = 1 := by rw [ha, ← pow_add]; exact Even.neg_one_pow ⟨m + 1, by ring⟩
  have hpi : ((2 * π) ^ (2 * m) : ℝ) ≠ 0 := by positivity
  have hfac : ((2 * m)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hEF : a * (2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m))
      * (a * (2 * π) ^ (2 * m) / 2 / (2 * m)!) = 1 := by
    field_simp; linear_combination ha2
  linear_combination (-(B - b)) * hEF
theorem centered_kernel_mul_sign_nonneg (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    0 ≤ (-1 : ℝ) ^ m * (bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)) := by
  have hA : (0 : ℝ) ≤ 2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m) := by positivity
  have hS : (∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m)) ≤ 0 :=
    tsum_nonpos fun n ↦
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (Real.cos_le_one _)) (by positivity)
  have hs3 : (-1 : ℝ) ^ m * (-1) ^ (m + 1) = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨m, by ring⟩
  rw [bernoulliFun_sub_self_eq_tsum_cos m hm x, ← mul_assoc, ← mul_assoc, hs3]
  linarith [mul_nonneg hA (neg_nonneg.mpr hS)]
private theorem integrableOn_Ioi_of_bound_mul_rpow {f : ℝ → ℝ} (hf : Continuous f)
    (hbound : ∀ x, |f x| ≤ 1) {q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ f x * x ^ q) (Set.Ioi N) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt hq hN)
    ((hf.continuousOn.mul (fun x hx ↦
      (Real.continuousAt_rpow_const x q
        (Or.inl (hN.trans (Set.mem_Ioi.mp hx)).ne')).continuousWithinAt)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hN.trans (Set.mem_Ioi.mp hx)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (hbound x)
private theorem integrableOn_Ioi_sin_mul_rpow {ω q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ sin (ω * x) * x ^ q) (Set.Ioi N) :=
  integrableOn_Ioi_of_bound_mul_rpow (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    (fun _ ↦ abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) hq hN
private theorem integrableOn_Ioi_cos_mul_rpow {ω q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ cos (ω * x) * x ^ q) (Set.Ioi N) :=
  integrableOn_Ioi_of_bound_mul_rpow (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    (fun _ ↦ abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) hq hN
private theorem integral_Ioi_sin_mul_rpow_nonneg {p : ℝ} (hp : 1 < p) {N k : ℕ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) :
    0 ≤ ∫ x in Set.Ioi (N : ℝ), sin (2 * π * k * x) * x ^ (-p) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  set ω : ℝ := 2 * π * (k : ℝ) with hω
  have hω0 : 0 < ω := by rw [hω]; positivity
  set T : ℝ := 1 / (2 * (k : ℝ)) with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  have hωT : ω * T = π := by rw [hω, hT]; field_simp
  set A : ℕ → ℝ := fun j ↦ (N : ℝ) + j * T with hA
  have hAsucc : ∀ j, A (j + 1) = A j + T := fun j ↦ by simp only [hA]; push_cast; ring
  have hApos : ∀ j, 0 < A j := fun j ↦ by simp only [hA]; positivity
  have hAle : ∀ j, A j ≤ A (j + 1) := fun j ↦ by rw [hAsucc]; linarith
  set g : ℝ → ℝ := fun x ↦ sin (ω * x) * x ^ (-p) with hg
  set c : ℕ → ℝ := fun j ↦ ∫ u in (0 : ℝ)..T, sin (ω * u) * (A j + u) ^ (-p) with hc
  have hsincont : Continuous fun x : ℝ ↦ sin (ω * x) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hrpow : ContinuousOn (fun x : ℝ ↦ x ^ (-p)) (Set.Ioi (0 : ℝ)) := fun x hx ↦
    (Real.continuousAt_rpow_const x (-p) (Or.inl (Set.mem_Ioi.mp hx).ne')).continuousWithinAt
  have hgint : ∀ j, IntervalIntegrable g volume (A j) (A (j + 1)) := fun j ↦
    (hsincont.continuousOn.mul (hrpow.mono fun x hx ↦ by
      rw [Set.uIcc_of_le (hAle j)] at hx
      exact lt_of_lt_of_le (hApos j) hx.1)).intervalIntegrable
  have hcint : ∀ j, IntervalIntegrable
      (fun u ↦ sin (ω * u) * (A j + u) ^ (-p)) volume 0 T := fun j ↦ by
    refine (hsincont.continuousOn.mul (ContinuousOn.rpow_const
      (continuous_const.add continuous_id).continuousOn fun u hu ↦ Or.inl ?_)).intervalIntegrable
    rw [Set.uIcc_of_le hT0.le] at hu
    exact (by linarith [hApos j, hu.1] : (0 : ℝ) < A j + u).ne'
  have hsinu : ∀ u ∈ Set.Icc (0 : ℝ) T, 0 ≤ sin (ω * u) := fun u hu ↦
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hω0.le hu.1)
      (by linarith [mul_le_mul_of_nonneg_left hu.2 hω0.le, hωT])
  have hcanti : Antitone c := antitone_nat_of_succ_le fun j ↦ by
    simp only [hc]
    refine intervalIntegral.integral_mono_on hT0.le (hcint (j + 1)) (hcint j) fun u hu ↦ ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
      (by linarith [hApos j, hu.1]) (by linarith [hAsucc j, hT0]) (by linarith)) (hsinu u hu)
  have hpiece : ∀ j, (∫ x in A j..A (j + 1), g x) = (-1 : ℝ) ^ j * c j := fun j ↦ by
    rw [show (∫ x in A j..A (j + 1), g x) = ∫ u in (0 : ℝ)..T, g (A j + u) from by
      rw [intervalIntegral.integral_comp_add_left g (A j), add_zero, ← hAsucc j]]
    simp only [hc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    have key : sin (ω * (A j + u)) = (-1 : ℝ) ^ j * sin (ω * u) := by
      rw [show ω * (A j + u) = ω * u + ((j + 2 * k * N : ℕ) : ℝ) * π by
            simp only [hA, hω, hT]; field_simp; push_cast; ring,
        Real.sin_add_nat_mul_pi,
        show ((-1 : ℝ)) ^ (j + 2 * k * N) = (-1 : ℝ) ^ j by
          rw [pow_add, show 2 * k * N = 2 * (k * N) by ring, pow_mul]; norm_num]
    simp only [hg, key]
    ring
  have hA0 : A 0 = (N : ℝ) := by simp [hA]
  have hpartial : ∀ n, ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * c i = ∫ x in (N : ℝ)..A n, g x :=
    fun n ↦ by
      rw [← hA0, ← intervalIntegral.sum_integral_adjacent_intervals
        (f := g) fun k (_ : k < n) ↦ hgint k]
      exact Finset.sum_congr rfl fun i _ ↦ (hpiece i).symm
  have hgintegrable : IntegrableOn g (Set.Ioi (N : ℝ)) := by
    rw [hg]; exact integrableOn_Ioi_sin_mul_rpow (by linarith) hN0
  have hAtop : Tendsto A atTop atTop :=
    (tendsto_atTop_add_const_left atTop (N : ℝ)
      (tendsto_natCast_atTop_atTop.atTop_mul_const hT0)).congr fun _ ↦ rfl
  have htend_sum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * c i) atTop
      (𝓝 (∫ x in Set.Ioi (N : ℝ), g x)) :=
    (intervalIntegral_tendsto_integral_Ioi (N : ℝ) hgintegrable hAtop).congr
      fun n ↦ (hpartial n).symm
  simpa using Antitone.alternating_series_le_tendsto htend_sum hcanti 0
theorem integral_Ioi_cos_mul_rpow_nonneg {a : ℝ} (ha : 1 < a) {N k : ℕ} (hN : 1 ≤ N) :
    0 ≤ ∫ x in Set.Ioi (N : ℝ), cos (2 * π * k * x) * x ^ (-a) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine setIntegral_nonneg measurableSet_Ioi fun x hx ↦ ?_
    simpa using Real.rpow_nonneg (hN0.trans hx).le (-a)
  set ω : ℝ := 2 * π * (k : ℝ) with hω
  have hω0 : 0 < ω := by rw [hω]; positivity
  have hJ : 0 ≤ ∫ x in Set.Ioi (N : ℝ), sin (ω * x) * x ^ (-(a + 1)) := by
    rw [hω]; exact integral_Ioi_sin_mul_rpow_nonneg (p := a + 1) (by linarith) hN hk
  have hcoscont : Continuous fun x : ℝ ↦ cos (ω * x) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcosint : IntegrableOn (fun x ↦ cos (ω * x) * x ^ (-a)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cos_mul_rpow (by linarith) hN0
  have hsinint : IntegrableOn (fun x ↦ sin (ω * x) * x ^ (-(a + 1))) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_sin_mul_rpow (by linarith) hN0
  have hsinN : sin (ω * N) = 0 := by
    rw [show ω * (N : ℝ) = ((2 * k * N : ℕ) : ℝ) * π by rw [hω]; push_cast; ring]
    exact Real.sin_nat_mul_pi _
  have hrel : ∀ᶠ R in atTop, (∫ x in (N : ℝ)..R, cos (ω * x) * x ^ (-a))
      = R ^ (-a) * sin (ω * R) / ω
        + a / ω * ∫ x in (N : ℝ)..R, sin (ω * x) * x ^ (-(a + 1)) := by
    filter_upwards [eventually_ge_atTop (N : ℝ)] with R hR
    have hne : ∀ x ∈ Set.uIcc (N : ℝ) R, x ≠ 0 := fun x hx ↦ by
      rw [Set.uIcc_of_le hR] at hx; exact (lt_of_lt_of_le hN0 hx.1).ne'
    have hu : ∀ x ∈ Set.uIcc (N : ℝ) R, HasDerivAt (fun x ↦ x ^ (-a)) (-a * x ^ (-(a + 1))) x :=
      fun x hx ↦ by
        have hd := hasDerivAt_rpow_const (x := x) (p := -a) (Or.inl (hne x hx))
        rwa [show -a - 1 = -(a + 1) by ring] at hd
    have hv : ∀ x ∈ Set.uIcc (N : ℝ) R,
        HasDerivAt (fun x ↦ sin (ω * x) / ω) (cos (ω * x)) x := fun x _ ↦ by
      have h2 : HasDerivAt (fun t ↦ sin (ω * t)) (cos (ω * x) * ω) x :=
        (Real.hasDerivAt_sin (ω * x)).comp x (by simpa using (hasDerivAt_id x).const_mul ω)
      have h3 := h2.div_const ω
      rwa [mul_div_assoc, div_self hω0.ne', mul_one] at h3
    have hu'int : IntervalIntegrable (fun x ↦ -a * x ^ (-(a + 1))) volume (N : ℝ) R :=
      (continuousOn_const.mul fun x hx ↦
        (Real.continuousAt_rpow_const x (-(a + 1))
          (Or.inl (hne x hx))).continuousWithinAt).intervalIntegrable
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'int
      (hcoscont.intervalIntegrable _ _)
    rw [intervalIntegral.integral_congr fun x _ ↦ mul_comm (x ^ (-a)) (cos (ω * x))] at hibp
    rw [hibp, show (∫ x in (N : ℝ)..R, -a * x ^ (-(a + 1)) * (sin (ω * x) / ω))
          = -(a / ω) * ∫ x in (N : ℝ)..R, sin (ω * x) * x ^ (-(a + 1)) by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun x _ ↦ by ring, hsinN]
    ring
  have hbdry : Tendsto (fun R : ℝ ↦ R ^ (-a) * sin (ω * R) / ω) atTop (𝓝 0) := by
    have hb0 : Tendsto (fun R : ℝ ↦ R ^ (-a) / ω) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < a by linarith)).div_const ω
    refine squeeze_zero_norm' ?_ hb0
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRa : (0 : ℝ) ≤ R ^ (-a) := Real.rpow_nonneg hR.le _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hω0, abs_mul, abs_of_nonneg hRa,
      div_le_div_iff_of_pos_right hω0]
    simpa using mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨Real.neg_one_le_sin (ω * R), Real.sin_le_one (ω * R)⟩) hRa
  have heq := tendsto_nhds_unique
    ((intervalIntegral_tendsto_integral_Ioi (N : ℝ) hcosint tendsto_id).congr' hrel)
    (hbdry.add ((intervalIntegral_tendsto_integral_Ioi (N : ℝ) hsinint
      tendsto_id).const_mul (a / ω)))
  rw [heq, zero_add]
  exact mul_nonneg (div_nonneg (by linarith) hω0.le) hJ
theorem zetaRemainder_eq_integral_bernoulliFun_fract_sub (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M + 1 : ℝ) < s.re) :
    zetaRemainder s M N
      = -((ascPochhammer ℂ (2 * M + 2)).eval s / ((2 * M + 2)! : ℂ))
          * ∫ x in Set.Ioi (N : ℝ),
              ((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
                * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ)) := by
  rw [zetaRemainder, Complex.eulerMaclaurinRemainderIoi_cpow_eq s (2 * M + 2) N]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set p : ℕ := 2 * M + 2 with hp
  set w : ℂ := -s - (p : ℂ) with hw
  have hwre : w.re < -1 := by
    rw [hw, Complex.sub_re, Complex.neg_re, Complex.natCast_re, hp]; push_cast; linarith
  have hxint : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ w) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hwre hN0
  have hBint : IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) := Complex.integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN hwre
  have hsubint : IntegrableOn
      (fun x : ℝ ↦ ((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) :=
    (hBint.sub (hxint.const_mul ((bernoulli p : ℝ) : ℂ))).congr
      (.of_forall fun x ↦ by simp only [Pi.sub_apply]; push_cast; ring)
  have hsplit : (∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      = (∫ x in Set.Ioi (N : ℝ),
            ((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w)
        + ((bernoulli p : ℝ) : ℂ) * ∫ x in Set.Ioi (N : ℝ), (x : ℂ) ^ w := by
    rw [show (∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
          = ∫ x in Set.Ioi (N : ℝ),
              (((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w
                + ((bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w) from
        setIntegral_congr_fun measurableSet_Ioi (fun x _ ↦ by push_cast; ring),
      integral_add hsubint (hxint.const_mul ((bernoulli p : ℝ) : ℂ)), integral_const_mul]
  rw [hsplit, integral_Ioi_cpow_of_lt hwre hN0]
  have hwone : w + 1 = -s - ((2 * M + 1 : ℕ) : ℂ) := by rw [hw, hp]; push_cast; ring
  have hPp : (ascPochhammer ℂ p).eval s
      = (ascPochhammer ℂ (2 * M + 1)).eval s * (s + ((2 * M + 1 : ℕ) : ℂ)) := by
    rw [show p = (2 * M + 1) + 1 from by lia, ascPochhammer_succ_eval]
  have hpne : (p ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
  have hden : -s - ((2 * M + 1 : ℕ) : ℂ) ≠ 0 := fun h ↦ by
    have hre : (-s - ((2 * M + 1 : ℕ) : ℂ)).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re] at hre
    push_cast at hre; linarith
  rw [hwone, hPp]
  push_cast at hden hpne ⊢
  field_simp
  ring
theorem integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le (m : ℕ) (hm : 1 ≤ m) {a : ℝ}
    (ha : 1 < a) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in Set.Ioi (N : ℝ),
        |bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)| * x ^ (-a)
      ≤ |(bernoulli (2 * m) : ℝ)| * ∫ x in Set.Ioi (N : ℝ), x ^ (-a) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  have hxa_neg : -a < -1 := by linarith
  set b : ℝ := (bernoulli (2 * m) : ℝ)
  set Am : ℝ := 2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m) with hAm
  have hAm0 : 0 < Am := by rw [hAm]; positivity
  set W : ℝ := ∫ x in Set.Ioi (N : ℝ), x ^ (-a) with hW
  have hweight_int : IntegrableOn (fun x : ℝ ↦ x ^ (-a)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hxa_neg hN0
  have hcos_int : ∀ k : ℕ,
      IntegrableOn (fun x ↦ cos (2 * π * (k : ℝ) * x) * x ^ (-a)) (Set.Ioi (N : ℝ)) := fun _ ↦
    integrableOn_Ioi_cos_mul_rpow hxa_neg hN0
  set f : ℕ → ℝ → ℝ :=
    fun k x ↦ Am / (k : ℝ) ^ (2 * m) * (1 - cos (2 * π * (k : ℝ) * x)) * x ^ (-a) with hf
  have hf_int : ∀ k, IntegrableOn (f k) (Set.Ioi (N : ℝ)) := fun k ↦
    ((hweight_int.sub (hcos_int k)).const_mul (Am / (k : ℝ) ^ (2 * m))).congr <| by
      filter_upwards with x
      simp only [hf, Pi.sub_apply]; ring
  have hf_nonneg : ∀ k, ∀ x ∈ Set.Ioi (N : ℝ), 0 ≤ f k x := fun k x hx ↦ by
    simp only [hf]
    exact mul_nonneg (mul_nonneg (div_nonneg hAm0.le (by positivity))
        (by linarith [Real.cos_le_one (2 * π * (k : ℝ) * x)]))
      (Real.rpow_nonneg (lt_trans hN0 hx).le _)
  have hbound : ∀ k, (∫ x in Set.Ioi (N : ℝ), f k x) ≤ Am / (k : ℝ) ^ (2 * m) * W := fun k ↦ by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x _ ↦
      show f k x = Am / (k : ℝ) ^ (2 * m) * (x ^ (-a) - cos (2 * π * (k : ℝ) * x) * x ^ (-a))
        by simp only [hf]; ring, integral_const_mul, integral_sub hweight_int (hcos_int k)]
    exact mul_le_mul_of_nonneg_left
      (by linarith [integral_Ioi_cos_mul_rpow_nonneg (a := a) (N := N) (k := k) ha hN])
      (div_nonneg hAm0.le (by positivity))
  have hsummable_bound : Summable (fun k : ℕ ↦ Am / (k : ℝ) ^ (2 * m) * W) :=
    ((((Real.summable_one_div_nat_pow (p := 2 * m)).mpr (by lia)).mul_left Am).congr
      fun k ↦ by ring).mul_right W
  have hsummable_int : Summable (fun k : ℕ ↦ ∫ x in Set.Ioi (N : ℝ), f k x) :=
    Summable.of_nonneg_of_le
      (fun k ↦ setIntegral_nonneg measurableSet_Ioi (hf_nonneg k)) hbound hsummable_bound
  have habs : ∀ x : ℝ, |bernoulliFun (2 * m) (Int.fract x) - b|
      = Am * ∑' k : ℕ, (1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m) := fun x ↦ by
    rw [abs_eq_neg_one_pow_mul (centered_kernel_mul_sign_nonneg m hm x),
      bernoulliFun_sub_self_eq_tsum_cos m hm x,
      show ∑' k : ℕ, (1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m)
          = -∑' k : ℕ, (cos (2 * π * (k : ℝ) * x) - 1) / (k : ℝ) ^ (2 * m) from by
        rw [← tsum_neg]; exact tsum_congr fun k ↦ by ring]
    have hsq : (-1 : ℝ) ^ m * (-1) ^ (m + 1) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨m, by ring⟩
    linear_combination
      (Am * ∑' k : ℕ, (cos (2 * π * (k : ℝ) * x) - 1) / (k : ℝ) ^ (2 * m)) * hsq
  calc ∫ x in Set.Ioi (N : ℝ),
        |bernoulliFun (2 * m) (Int.fract x) - b| * x ^ (-a)
      = ∫ x in Set.Ioi (N : ℝ), ∑' k : ℕ, f k x :=
        setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ by
          rw [tsum_congr fun k ↦ show f k x
                = Am * ((1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m)) * x ^ (-a) by
              simp only [hf]; ring, tsum_mul_right, tsum_mul_left, ← habs x]
    _ = ∑' k : ℕ, ∫ x in Set.Ioi (N : ℝ), f k x :=
        (integral_tsum_of_summable_integral_norm hf_int (hsummable_int.congr fun k ↦
          setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
            (Real.norm_of_nonneg (hf_nonneg k x hx)).symm)).symm
    _ ≤ ∑' k : ℕ, Am / (k : ℝ) ^ (2 * m) * W :=
        hsummable_int.tsum_mono hsummable_bound hbound
    _ = |b| * W := by
        have hAmζ : (∑' k : ℕ, Am / (k : ℝ) ^ (2 * m)) = (-1 : ℝ) ^ (m + 1) * b := by
          have hpi : ((2 * π) ^ (2 * m) : ℝ) ≠ 0 := by positivity
          have hfac : ((2 * m)! : ℝ) ≠ 0 := by positivity
          rw [tsum_congr fun k : ℕ ↦ div_eq_mul_one_div Am ((k : ℝ) ^ (2 * m)), tsum_mul_left,
            (hasSum_one_div_nat_pow_bernoulli m (by lia)).tsum_eq, hAm]
          field_simp
          ring
        have hnn : 0 ≤ (-1 : ℝ) ^ (m + 1) * b :=
          hAmζ ▸ tsum_nonneg fun k ↦ div_nonneg hAm0.le (by positivity)
        rw [tsum_mul_right, hAmζ, ← abs_eq_neg_one_pow_mul hnn]
noncomputable abbrev zetaRemainderBound (s : ℂ) (M N : ℕ) : ℝ :=
  ‖s + ((2 * M + 1 : ℕ) : ℂ)‖ / (s.re + ((2 * M + 1 : ℕ) : ℝ))
    * ‖((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s
        * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))‖
theorem norm_zetaRemainder_le (s : ℂ) (M N : ℕ) (hN : 1 ≤ N) (hs : -(2 * M + 1 : ℝ) < s.re) :
    ‖zetaRemainder s M N‖ ≤ zetaRemainderBound s M N := by
  simp only [zetaRemainderBound]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := s.re + ((2 * M + 2 : ℕ) : ℝ) with ha_def
  have ha : 1 < a := by rw [ha_def]; push_cast; linarith
  set W : ℝ := ∫ x in Set.Ioi (N : ℝ), x ^ (-a) with hW
  have hwre : (-s - ((2 * M + 2 : ℕ) : ℂ)).re = -a := by
    rw [ha_def]; simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; push_cast; ring
  have hre1 : (-s - ((2 * M + 1 : ℕ) : ℂ)).re = -(s.re + ((2 * M + 1 : ℕ) : ℝ)) := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
  have hrel : -a + 1 = -(s.re + ((2 * M + 1 : ℕ) : ℝ)) := by rw [ha_def]; push_cast; ring
  have hP : ‖(ascPochhammer ℂ (2 * M + 2)).eval s‖
      = ‖(ascPochhammer ℂ (2 * M + 1)).eval s‖ * ‖s + ((2 * M + 1 : ℕ) : ℂ)‖ := by
    rw [show 2 * M + 2 = (2 * M + 1) + 1 from by lia, ascPochhammer_succ_eval, norm_mul]
  have ht : ‖((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))‖
      = |(bernoulli (2 * M + 2) : ℝ)| / ((2 * M + 2)! : ℝ)
          * ‖(ascPochhammer ℂ (2 * M + 1)).eval s‖
          * (N : ℝ) ^ (-(s.re + ((2 * M + 1 : ℕ) : ℝ))) := by
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * M + 2)! : ℝ)),
      ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0, hre1]
  have hWval : W = -(N : ℝ) ^ (-a + 1) / (-a + 1) := by
    rw [hW]; exact integral_Ioi_rpow_of_lt (by linarith : -a < -1) hN0
  have hInorm : ‖∫ x in Set.Ioi (N : ℝ),
        ((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
          * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ))‖
      ≤ |(bernoulli (2 * M + 2) : ℝ)| * W := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
      show ‖((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
            * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ))‖
          = |bernoulliFun (2 * M + 2) (Int.fract x) - (bernoulli (2 * M + 2) : ℝ)| * x ^ (-a) by
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans hN0 hx), hwre]]
    have h3 := integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le (M + 1) (by lia) ha hN
    rwa [show 2 * (M + 1) = 2 * M + 2 from by ring] at h3
  rw [zetaRemainder_eq_integral_bernoulliFun_fract_sub s M N hN hs, norm_mul, norm_neg, norm_div,
    Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left hInorm (by positivity)).trans (le_of_eq ?_)
  rw [hP, ht, hWval, hrel]
  have hFacne : ((2 * M + 2)! : ℝ) ≠ 0 := by positivity
  have hDne : s.re + ((2 * M + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (by push_cast; linarith : (0 : ℝ) < s.re + ((2 * M + 1 : ℕ) : ℝ))
  field_simp
end
end CertificatePort151


section CertificatePort152
section
open scoped Nat
namespace Enclosure
theorem natCast_cpow_eq (n : ℕ) (hn : 0 < n) (σ t : ℝ) :
    ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      ⟨Real.exp (σ * Real.log n) * Real.cos (t * Real.log n),
       Real.exp (σ * Real.log n) * Real.sin (t * Real.log n)⟩ := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
  have hstd : ((Real.log n : ℝ) : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)
            = ((Real.log n * σ : ℝ) : ℂ) + ((Real.log n * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [Complex.cpow_def_of_ne_zero hn0, hlog, hstd]
  apply Complex.ext
  · rw [Complex.exp_re]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    congr 1 <;> congr 1 <;> ring
  · rw [Complex.exp_im]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    congr 1 <;> congr 1 <;> ring
def natAbsSubLe (XP XN Xd YP YN Yd δn δd : ℕ) : Bool :=
  Nat.ble (((XP.mul Yd).add (YN.mul Xd)).mul δd)
      ((δn.mul (Xd.mul Yd)).add (((XN.mul Yd).add (YP.mul Xd)).mul δd)) &&
    Nat.ble (((YP.mul Xd).add (XN.mul Yd)).mul δd)
      ((δn.mul (Xd.mul Yd)).add (((YN.mul Xd).add (XP.mul Yd)).mul δd))
theorem abs_sub_le_of_natAbsSubLe {XP XN Xd YP YN Yd δn δd : ℕ}
    (hXd : 0 < Xd) (hYd : 0 < Yd) (hδd : 0 < δd)
    (h : natAbsSubLe XP XN Xd YP YN Yd δn δd = true) :
    |((XP : ℝ) - XN) / Xd - ((YP : ℝ) - YN) / Yd| ≤ (δn : ℝ) / δd := by
  simp only [natAbsSubLe, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hX : (0 : ℝ) < Xd := by exact_mod_cast hXd
  have hY : (0 : ℝ) < Yd := by exact_mod_cast hYd
  have hδ : (0 : ℝ) < δd := by exact_mod_cast hδd
  have h1' : ((XP : ℝ) * Yd + YN * Xd) * δd ≤ δn * (Xd * Yd) + (XN * Yd + YP * Xd) * δd := by
    exact_mod_cast h1
  have h2' : ((YP : ℝ) * Xd + XN * Yd) * δd ≤ δn * (Xd * Yd) + (YN * Xd + XP * Yd) * δd := by
    exact_mod_cast h2
  have e : ((XP : ℝ) - XN) / Xd - ((YP : ℝ) - YN) / Yd
      = ((XP : ℝ) * Yd + YN * Xd - (XN * Yd + YP * Xd)) / (Xd * Yd) := by
    field_simp
    ring
  have hXY : (0 : ℝ) < Xd * Yd := mul_pos hX hY
  rw [e, abs_div, abs_of_pos hXY, div_le_div_iff₀ hXY hδ]
  rcases abs_cases ((XP : ℝ) * Yd + YN * Xd - (XN * Yd + YP * Xd)) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;> nlinarith
end Enclosure
namespace BSN
open Enclosure
open Complex
noncomputable abbrev hardyZErrorBoundStrong (M N : ℕ) (t : ℝ) : ℝ :=
  riemannSiegelThetaStirlingErrorBound M (thetaShift M)
      * ‖zetaApproximant (1 / 2 + Complex.I * t) M N‖
    + zetaRemainderBound (1 / 2 + Complex.I * t) M N
theorem hardyZErrorBoundEM_le_strong (M N : ℕ) (t : ℝ) (hN : Nat.ble 1 N = true) :
    hardyZErrorBoundEM M N t ≤ hardyZErrorBoundStrong M N t := by
  have hN' : 1 ≤ N := Nat.le_of_ble_eq_true hN
  have hs : -(2 * M + 1 : ℝ) < (1 / 2 + Complex.I * (t : ℂ)).re := by
    have hre : (1 / 2 + Complex.I * (t : ℂ)).re = 1 / 2 := by simp
    rw [hre]
    have : (0 : ℝ) ≤ 2 * M + 1 := by positivity
    linarith
  exact add_le_add le_rfl (norm_zetaRemainder_le _ M N hN' hs)
theorem gt_trans_le (x s b : ℝ) (hle : b ≤ s) (h : x > s) : x > b := lt_of_le_of_lt hle h
theorem re_exp_mul (θ : ℝ) (ζ : ℂ) :
    (Complex.exp (Complex.I * (θ : ℂ)) * ζ).re = Real.cos θ * ζ.re - Real.sin θ * ζ.im := by
  rw [mul_comm Complex.I, Complex.exp_mul_I, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_im]
theorem zetaApproximant_eq_folded (s : ℂ) (M N : ℕ) (hN : 0 < N) :
    zetaApproximant s M N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2
            + ∑ k ∈ Finset.Icc 1 M,
                ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                  * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h1s : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0, Complex.cpow_one]
  have hks : ∀ k : ℕ, (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))
      = (N : ℂ) ^ (-s) * ((N : ℂ) ^ (2 * k - 1))⁻¹ := fun k => by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0]
    congr 1
    rw [Complex.cpow_neg, Complex.cpow_natCast]
  have hsum : (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
      = (N : ℂ) ^ (-s) * ∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
            * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hks k]
    ring
  rw [zetaApproximant, h1s, hsum]
  ring
theorem s_crit_mk (t : ℝ) (tneg : Bool) (tn td : ℕ) (ht : t = sfrac tneg tn td) :
    (1 / 2 + Complex.I * (t : ℂ)) = ⟨sfrac false (nat_lit 1) (nat_lit 2), sfrac tneg tn td⟩ := by
  subst ht
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sfrac_false_div]
theorem s_add_nat_mk (t : ℝ) (tneg : Bool) (tn td n : ℕ) (ht : t = sfrac tneg tn td) :
    (1 / 2 + Complex.I * (t : ℂ)) + (n : ℂ)
      = ⟨sfrac false (Nat.add 1 (Nat.mul 2 n)) (nat_lit 2), sfrac tneg tn td⟩ := by
  simp only [Nat.mul_eq, Nat.add_eq]
  subst ht
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sfrac_false_div]
  ring
theorem w_shift_mk (t : ℝ) (tneg : Bool) (tn td j : ℕ) (ht : t = sfrac tneg tn td)
    (htd : Nat.ble 1 td = true) :
    1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)
      = ⟨sfrac false ((Nat.add 1 (Nat.mul 4 j)).mul td) (Nat.mul 4 td),
         sfrac tneg (Nat.mul 2 tn) (Nat.mul 4 td)⟩ := by
  simp only [Nat.mul_eq, Nat.add_eq]
  subst ht
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, sfrac_false_div]
    field_simp
  · cases tneg <;> simp [Complex.add_im, Complex.mul_im, sfrac] <;> field_simp <;> ring
theorem ascPochhammer_one_eval (s : ℂ) : (ascPochhammer ℂ (nat_lit 1)).eval s = s := by
  rw [ascPochhammer_one, Polynomial.eval_X]
theorem ascPochhammer_succ_eval_c (n b : ℕ) (s : ℂ) (hb : Nat.beq b (n.add 1) = true) :
    (ascPochhammer ℂ b).eval s = (ascPochhammer ℂ n).eval s * (s + n) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact ascPochhammer_succ_eval n s
theorem complex_zero_mk : (0 : ℂ)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  apply Complex.ext <;> simp [sfrac]
theorem cpow_neg_s_mk (t : ℝ) (tn td n : ℕ) (ht : t = sfrac false tn td)
    (hn : Nat.ble 1 n = true) :
    (n : ℂ) ^ (-(1 / 2 + Complex.I * (t : ℂ)))
      = ⟨(Real.sqrt (n : ℝ))⁻¹
            * Real.cos (sfrac false tn td * Real.log (sfrac false n (nat_lit 1))),
         (Real.sqrt (n : ℝ))⁻¹
            * -Real.sin (sfrac false tn td * Real.log (sfrac false n (nat_lit 1)))⟩ := by
  have hn' : 0 < n := pos_of_ble hn
  have hnR : (0 : ℝ) < n := pos_real_of_ble hn
  have hexp : -(1 / 2 + Complex.I * (t : ℂ))
      = ((-(1/2) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hexp, natCast_cpow_eq n hn' (-(1/2)) (-t)]
  have hmag : Real.exp (-(1 / 2 * Real.log n)) = (Real.sqrt (n : ℝ))⁻¹ := by
    have h1 : ((1 : ℝ) / (n : ℝ)) = Real.exp (-Real.log n) := by
      rw [one_div, Real.exp_neg, Real.exp_log hnR]
    have h2 : Real.exp (-(1 / 2 * Real.log n)) = Real.sqrt (1 / (n : ℝ)) := by
      rw [h1, ← Real.exp_half]
      congr 1
      ring
    rw [h2, one_div, Real.sqrt_inv]
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  apply Complex.ext <;>
    simp only [hlogsfrac, neg_mul, Real.cos_neg, Real.sin_neg, hmag]
theorem head_sum_base (s : ℂ) :
    (∑ n ∈ Finset.Ico (1 : ℕ) 1, (n : ℂ) ^ (-s))
        = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [Finset.Ico_self, Finset.sum_empty]
  exact complex_zero_mk
theorem head_sum_succ (s : ℂ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true)
    (ha : Nat.ble 1 a = true) :
    (∑ n ∈ Finset.Ico 1 b, (n : ℂ) ^ (-s))
      = (∑ n ∈ Finset.Ico 1 a, (n : ℂ) ^ (-s)) + (a : ℂ) ^ (-s) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Ico_succ_top (Nat.le_of_ble_eq_true ha) _
noncomputable def headSumC (s : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)
theorem head_sum_c_base (s : ℂ) : headSumC s (nat_lit 1)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ :=
  head_sum_base s
theorem head_sum_c_succ (s : ℂ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true)
    (ha : Nat.ble 1 a = true) : headSumC s b = headSumC s a + (a : ℂ) ^ (-s) :=
  head_sum_succ s a b hb ha
theorem head_sum_c_two (s : ℂ) :
    headSumC s (nat_lit 2)
      = ⟨sfrac false (nat_lit 1) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [head_sum_c_succ s (nat_lit 1) (nat_lit 2) (by rfl) (by rfl), head_sum_c_base, Nat.cast_one,
    Complex.one_cpow]
  apply Complex.ext <;> simp [sfrac]
theorem head_sum_c_eq (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) = headSumC s N := rfl
theorem bern_sum_base (s : ℂ) (N : ℕ) :
    (∑ k ∈ Finset.Icc (1 : ℕ) (nat_lit 0),
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹)
      = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [hIcc, Finset.sum_empty]
  exact complex_zero_mk
theorem bern_sum_succ (s : ℂ) (N m b e : ℕ) (hb : Nat.beq b (m.add 1) = true)
    (he : Nat.beq (e.add 1) (Nat.mul 2 b) = true) :
    (∑ k ∈ Finset.Icc 1 b,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹)
      = (∑ k ∈ Finset.Icc 1 m,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
            * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹)
        + ((bernoulli (2 * b) : ℝ) / ((2 * b)! : ℝ) : ℂ)
            * (ascPochhammer ℂ e).eval s * ((N : ℂ) ^ e)⁻¹ := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  have he' : e = 2 * (m + 1) - 1 := by
    have h : e + 1 = 2 * (m + 1) := Nat.eq_of_beq_eq_true he
    omega
  subst he'
  exact Finset.sum_Icc_succ_top (by omega) _
theorem half_c_mk : (1 / 2 : ℂ)
    = ⟨sfrac false (nat_lit 1) (nat_lit 2), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  apply Complex.ext
  · simp [sfrac]
  · simp [sfrac]
theorem N_div_s_sub_one_mk (t : ℝ) (tn td N : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) :
    (N : ℂ) / ((1 / 2 + Complex.I * (t : ℂ)) - 1)
      = ⟨sfrac true ((Nat.mul 2 N).mul (td.mul td)) ((td.mul td).add (Nat.mul 4 (tn.mul tn))),
         sfrac true ((Nat.mul 4 N).mul (tn.mul td)) ((td.mul td).add (Nat.mul 4 (tn.mul tn)))⟩ := by
  simp only [Nat.mul_eq, Nat.add_eq]
  subst ht
  have h1 : (0 : ℝ) < tn := pos_real_of_ble htn
  have h2 : (0 : ℝ) < td := pos_real_of_ble htd
  have hw : ((1 / 2 + Complex.I * ((sfrac false tn td : ℝ) : ℂ)) - 1)
      = ⟨-(1/2), (tn : ℝ) / td⟩ := by
    apply Complex.ext
    · simp [sfrac_false_div]
      norm_num
    · simp [sfrac_false_div]
  rw [hw]
  have hns : Complex.normSq ⟨-(1/2), (tn : ℝ) / td⟩ = 1/4 + (tn : ℝ)^2 / (td : ℝ)^2 := by
    rw [Complex.normSq_mk]
    ring
  apply Complex.ext
  · rw [Complex.div_re, hns]
    simp [sfrac]
    field_simp
    ring
  · rw [Complex.div_im, hns]
    simp [sfrac]
    field_simp
theorem natCast_pow_inv_mk (N m P : ℕ) (hP : Nat.pow N m = P)
    (_hN : Nat.ble 1 N = true) :
    ((N : ℂ) ^ m)⁻¹ = ⟨sfrac false (nat_lit 1) P, sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  obtain rfl := hP
  simp only [Nat.pow_eq]
  have h : ((N : ℂ) ^ m)⁻¹ = (((N ^ m : ℕ) : ℝ) : ℂ)⁻¹ := by push_cast; ring
  rw [h, ← Complex.ofReal_inv]
  apply Complex.ext
  · rw [Complex.ofReal_re, sfrac_false_div, Nat.cast_one, one_div]
  · rw [Complex.ofReal_im]
    simp [sfrac]
def factNat (n : ℕ) : ℕ := n.rec 1 (fun k acc => Nat.mul (Nat.succ k) acc)
theorem factNat_eq (n : ℕ) : factNat n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h : factNat (k + 1) = (k + 1) * factNat k := rfl
    rw [h, ih, Nat.factorial_succ]
theorem bern_coeff_mk (k bn bd F : ℕ) (bneg : Bool)
    (hB : (bernoulli (2 * k) : ℝ) = sfrac bneg bn bd)
    (hF : factNat (Nat.mul 2 k) = F) (hbd : Nat.ble 1 bd = true) :
    ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
      = ⟨sfrac bneg bn (bd.mul F), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  obtain rfl := hF
  simp only [factNat_eq, Nat.mul_eq]
  have hbdR : (0 : ℝ) < bd := pos_real_of_ble hbd
  have hFR : (0 : ℝ) < ((2 * k)! : ℝ) := by exact_mod_cast (2 * k).factorial_pos
  rw [← Complex.ofReal_div]
  apply Complex.ext
  · rw [Complex.ofReal_re, hB]
    simp only [sfrac]
    cases bneg <;> (simp; field_simp)
  · rw [Complex.ofReal_im]
    simp [sfrac]
theorem zetaApproximant_eq_folded' (s : ℂ) (M N : ℕ) (hN : Nat.ble 1 N = true) :
    zetaApproximant s M N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2
            + ∑ k ∈ Finset.Icc 1 M,
                ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                  * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹) :=
  zetaApproximant_eq_folded s M N (pos_of_ble hN)
theorem w_sub_half_zero_mk (t : ℝ) (tneg : Bool) (tn td : ℕ) (ht : t = sfrac tneg tn td)
    (htd : Nat.ble 1 td = true) :
    (1 / 4 + Complex.I * ((t : ℂ) / 2) + ((nat_lit 0 : ℕ) : ℂ)) - 1 / 2
      = ⟨sfrac true td (Nat.mul 4 td), sfrac tneg (Nat.mul 2 tn) (Nat.mul 4 td)⟩ := by
  rw [w_shift_mk t tneg tn td (nat_lit 0) ht htd]
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  apply Complex.ext
  · simp only [Nat.mul_eq, mul_zero, Nat.add_eq, add_zero, one_mul, sfrac_false_div, Nat.cast_mul,
      Nat.cast_ofNat, one_div, sub_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self',
      sfrac_true_div]
    all_goals (field_simp; try ring)
  · simp
theorem w_sub_half_mk (t : ℝ) (tneg : Bool) (tn td N : ℕ) (ht : t = sfrac tneg tn td)
    (htd : Nat.ble 1 td = true) (hN : Nat.ble 1 N = true) :
    (1 / 4 + Complex.I * ((t : ℂ) / 2) + (N : ℂ)) - 1 / 2
      = ⟨sfrac false (((Nat.mul 4 N).sub 1).mul td) (Nat.mul 4 td),
         sfrac tneg (Nat.mul 2 tn) (Nat.mul 4 td)⟩ := by
  have hN' : 0 < N := pos_of_ble hN
  rw [w_shift_mk t tneg tn td N ht htd]
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  apply Complex.ext
  · simp only [sfrac_false_div, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, one_div,
      sub_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self']
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * N)]
    push_cast
    field_simp
    ring
  · simp
theorem log_two_pi_eq : Real.log (2 * Real.pi)
    = Real.log (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi) := by
  norm_num [sfrac]
theorem t_half_eq (t : ℝ) (tneg : Bool) (tn td : ℕ) (ht : t = sfrac tneg tn td) :
    t / 2 = sfrac tneg tn (2 * td) := by
  subst ht
  cases tneg <;> simp [sfrac] <;> ring
theorem stirling_coeff_mk (k bn bd : ℕ) (bneg : Bool)
    (hB : (bernoulli (2 * k) : ℝ) = sfrac bneg bn bd)
    (hk : Nat.ble 1 k = true) (hbd : Nat.ble 1 bd = true) :
    (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1))
      = ⟨sfrac bneg bn (bd.mul ((Nat.mul 2 k).mul ((Nat.mul 2 k).sub 1))),
         sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  simp only [Nat.mul_eq, Nat.sub_eq]
  have hk' : 0 < k := pos_of_ble hk
  have hbdR : (0 : ℝ) < bd := pos_real_of_ble hbd
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.le_of_ble_eq_true hk
  have hd : (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) = (((2 * k * (2 * k - 1) : ℕ) : ℝ) : ℂ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    ring
  have hn : (bernoulli (2 * k) : ℂ) = ((bernoulli (2 * k) : ℝ) : ℂ) := by
    push_cast
    ring
  have hdR : (0 : ℝ) < ((2 * k * (2 * k - 1) : ℕ) : ℝ) := by
    have h1 : 0 < 2 * k * (2 * k - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast h1
  rw [hn, hd, ← Complex.ofReal_div]
  apply Complex.ext
  · rw [Complex.ofReal_re, hB]
    simp only [sfrac]
    cases bneg <;> (simp; field_simp)
  · rw [Complex.ofReal_im]
    simp [sfrac]
theorem zpow_one_sub_two_mul (w : ℂ) (k e : ℕ) (hk : Nat.ble 1 k = true)
    (he : Nat.beq (e.add 1) (Nat.mul 2 k) = true) :
    w ^ (1 - 2 * (k : ℤ)) = (w ^ e)⁻¹ := by
  have hk' : 0 < k := pos_of_ble hk
  have he' : e = 2 * k - 1 := by
    have h := Nat.eq_of_beq_eq_true he
    simp only [Nat.add_eq, Nat.mul_eq] at h
    omega
  subst he'
  have h : (1 - 2 * (k : ℤ)) = -(((2 * k - 1 : ℕ) : ℤ)) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    ring
  rw [h, zpow_neg, zpow_natCast]
theorem pow_succ_c (w : ℂ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    w ^ b = w ^ m * w := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact pow_succ w m
theorem pow_one_c (w : ℂ) : w ^ (nat_lit 1) = w := pow_one w
theorem stirling_sum_base (w : ℂ) :
    (∑ k ∈ Finset.Icc (1 : ℕ) (nat_lit 0),
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)))
      = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [hIcc, Finset.sum_empty]
  exact complex_zero_mk
theorem stirling_sum_succ (w : ℂ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    (∑ k ∈ Finset.Icc (1 : ℕ) b,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)))
      = (∑ k ∈ Finset.Icc (1 : ℕ) m,
          (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)))
        + (bernoulli (2 * b) : ℂ) / (2 * (b : ℂ) * (2 * (b : ℂ) - 1)) * w ^ (1 - 2 * (b : ℤ)) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Icc_succ_top (by omega) _
theorem log_sum_base (t : ℝ) :
    (∑ j ∈ Finset.range 0, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
      = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [Finset.range_zero, Finset.sum_empty]
  exact complex_zero_mk
theorem log_sum_succ (t : ℝ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    (∑ j ∈ Finset.range b, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
      = (∑ j ∈ Finset.range m, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
        + Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (m : ℂ)) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_range_succ _ m
noncomputable def logSumC (t : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ))
theorem log_sum_c_base (t : ℝ) : logSumC t (nat_lit 0)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ :=
  log_sum_base t
theorem log_sum_c_succ (t : ℝ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    logSumC t b = logSumC t m + Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (m : ℂ)) :=
  log_sum_succ t m b hb
theorem log_sum_c_eq (t : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
      = logSumC t N := rfl
theorem logGammaStirling_unfold (M : ℕ) (w : ℂ) :
    Complex.Stirling.logGammaStirling M w
      = (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ)
        + ∑ k ∈ Finset.Icc 1 M,
            (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)) :=
  rfl
theorem riemannSiegelThetaApproximant_named (M N : ℕ) (t : ℝ) :
    riemannSiegelThetaApproximant M N t
      = ((Complex.Stirling.logGammaStirling M (1 / 4 + Complex.I * (t / 2) + N)
            - ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * (t / 2) + j)).im
          - t / 2 * Real.log Real.pi) :=
  rfl
theorem riemannSiegelThetaApproximant_two_zero {t : ℝ} (ht : 0 < t) :
    riemannSiegelThetaApproximant 2 0 t
      = t / 4 * Real.log (1 / 16 + t ^ 2 / 4) - 1 / 4 * (Real.pi / 2 - Real.arctan (1 / (2 * t)))
        - t / 2 - t / 2 * Real.log Real.pi
        - (t / 2) / (12 * (1 / 16 + t ^ 2 / 4))
        + (3 * (1 / 16) * (t / 2) - (t / 2) ^ 3) / (360 * (1 / 16 + t ^ 2 / 4) ^ 3) := by
  set w : ℂ := 1 / 4 + Complex.I * (t / 2) with hw
  have hre : w.re = 1 / 4 := by simp [hw]
  have him : w.im = t / 2 := by simp [hw]
  have hnsq : Complex.normSq w = 1 / 16 + t ^ 2 / 4 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hnsq_pos : 0 < 1 / 16 + t ^ 2 / 4 := by positivity
  have harg : Complex.arg w = Real.pi / 2 - Real.arctan (1 / (2 * t)) := by
    rw [Complex.arg_eq_arctan (by rw [hre]; norm_num), hre, him]
    have h2t : 0 < 2 * t := by positivity
    rw [show t / 2 / (1 / 4) = 2 * t by ring, one_div, Real.arctan_inv_of_pos h2t]
    ring
  have hlog : Real.log ‖w‖ = 1 / 2 * Real.log (1 / 16 + t ^ 2 / 4) := by
    rw [Complex.norm_def, hnsq, Real.log_sqrt hnsq_pos.le]; ring
  have hw3im : (w ^ 3).im = 3 * (1 / 16) * (t / 2) - (t / 2) ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_im, Complex.mul_re, hre, him]; ring
  have hw3nsq : Complex.normSq (w ^ 3) = (1 / 16 + t ^ 2 / 4) ^ 3 := by
    rw [map_pow, hnsq]
  simp only [riemannSiegelThetaApproximant, Nat.cast_zero, add_zero, Finset.range_zero,
    Finset.sum_empty, sub_zero, Complex.Stirling.logGammaStirling_two]
  rw [← hw]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.inv_im, Complex.log_re,
    Complex.log_im, Complex.sub_re, hre, him, harg, hlog, hw3im, hw3nsq, hnsq,
    Complex.ofReal_im, Complex.ofReal_re]
  norm_num
  field_simp
  ring
theorem riemannSiegelThetaApproximant_two_zero_mk (t : ℝ) (tn td S Q V T4 T2 Rn Rd : ℕ)
    (ht : t = sfrac false tn td) (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true)
    (hS : Nat.beq S ((td.mul td).add ((Nat.mul 4 tn).mul tn)) = true)
    (hQ : Nat.beq Q ((Nat.mul 16 td).mul td) = true) (hV : Nat.beq V (Nat.mul 2 tn) = true)
    (hT4 : Nat.beq T4 (Nat.mul 4 td) = true) (hT2 : Nat.beq T2 (Nat.mul 2 td) = true)
    (hRn : Nat.beq (Rn.add ((Nat.mul 48 tn).mul (td.pow 5)))
      (((Nat.mul 30 tn).mul td).mul (S.pow 2) |>.add ((Nat.mul 64 (tn.pow 3)).mul (td.pow 3)))
      = true)
    (hRd : Nat.beq Rd (Nat.mul 45 (S.pow 3)) = true) :
    riemannSiegelThetaApproximant 2 0 t
      = sfrac false tn T4 * Real.log (sfrac false S Q)
        - sfrac false 1 4 * (sfrac false 1 2 * Real.pi - Real.arctan ((td : ℝ) / (V : ℝ)))
        - sfrac false tn T2 - sfrac false tn T2 * Real.log Real.pi + sfrac true Rn Rd := by
  simp only [Nat.beq_eq, Nat.mul_eq, Nat.add_eq, Nat.pow_eq] at hS hQ hV hT4 hT2 hRn hRd
  subst hS hQ hV hT4 hT2 hRd ht
  have hn : (0 : ℝ) < tn := pos_real_of_ble htn
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have hRn' : (Rn : ℝ) = 30 * tn * td * ((td : ℝ) * td + 4 * tn * tn) ^ 2
      + 64 * (tn : ℝ) ^ 3 * td ^ 3 - 48 * tn * (td : ℝ) ^ 5 := by
    have := congrArg (fun n : ℕ ↦ (n : ℝ)) hRn
    push_cast at this
    linarith
  rw [riemannSiegelThetaApproximant_two_zero (by rw [sfrac_false_div]; positivity)]
  simp only [sfrac, if_false, if_true, one_mul, neg_one_mul, Bool.false_eq_true]
  have hlog : (1 / 16 + ((tn : ℝ) / td) ^ 2 / 4)
      = (((td * td + 4 * tn * tn : ℕ) : ℝ) / ((16 * td * td : ℕ) : ℝ)) := by
    push_cast; field_simp; ring
  have hatan : 1 / (2 * ((tn : ℝ) / td)) = (td : ℝ) / ((2 * tn : ℕ) : ℝ) := by
    push_cast; field_simp
  rw [hlog, hatan, hRn']
  push_cast
  field_simp
  ring
theorem theta_err_eq (M N A B : ℕ)
    (hA : Nat.mul (factNat (Nat.succ (Nat.mul 2 M))) (Nat.pow 4 (Nat.mul 2 M)) = A)
    (hB : Nat.mul (Nat.mul 2 M) (Nat.pow (Nat.succ (Nat.mul 4 N)) (Nat.mul 2 M)) = B)
    (hM : Nat.ble 1 M = true) :
    riemannSiegelThetaStirlingErrorBound M N
      = sfrac false A B * ((2 * Real.pi) ^ (Nat.mul 2 M))⁻¹ := by
  obtain rfl := hA
  obtain rfl := hB
  simp only [factNat_eq, Nat.succ_eq_add_one, Nat.mul_eq, Nat.pow_eq]
  have hM' : 0 < M := pos_of_ble hM
  have hMR : (0 : ℝ) < 2 * M := by
    have : (0 : ℕ) < 2 * M := by omega
    exact_mod_cast this
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (2 * M) := by positivity
  have h4N : (0 : ℝ) < (4 * (N : ℝ) + 1) ^ (2 * M) := by positivity
  have hz : ((1 / 4 + N : ℝ)) ^ (-(2 * M : ℤ)) = ((1 / 4 + (N : ℝ)) ^ (2 * M))⁻¹ := by
    rw [show (-(2 * M : ℤ)) = -((2 * M : ℕ) : ℤ) from by push_cast; ring, zpow_neg,
      zpow_natCast]
  have hbase : (1 / 4 + (N : ℝ)) = (4 * (N : ℝ) + 1) / 4 := by ring
  rw [riemannSiegelThetaStirlingErrorBound, hz, hbase, div_pow, sfrac_false_div]
  push_cast
  field_simp
theorem theta_err_eq' (t : ℝ) (tn td M N A B : ℕ) (ht : t = sfrac false tn td)
    (hA : Nat.mul (Nat.mul (factNat (Nat.succ (Nat.mul 2 M))) (Nat.pow 2 (Nat.succ (Nat.mul 2 M))))
      (Nat.pow (Nat.mul 16 (Nat.mul td td)) M) = A)
    (hB : Nat.mul (Nat.mul 2 M) (Nat.pow (Nat.add
      (Nat.mul (Nat.mul (Nat.succ (Nat.mul 4 N)) (Nat.succ (Nat.mul 4 N))) (Nat.mul td td))
      (Nat.mul 4 (Nat.mul tn tn))) M) = B)
    (hM : Nat.ble 1 M = true) (htd : Nat.ble 1 td = true) :
    riemannSiegelThetaStirlingErrorBound' M N t
      = sfrac false A B * ((2 * Real.pi) ^ (Nat.mul 2 M))⁻¹ := by
  obtain rfl := hA
  obtain rfl := hB
  subst ht
  simp only [factNat_eq, Nat.succ_eq_add_one, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have hMR : (0 : ℝ) < 2 * M := by linarith [pos_real_of_ble hM]
  have hz : ((1 / 4 + N : ℝ) ^ 2 + (sfrac false tn td / 2) ^ 2) ^ (-(M : ℤ))
      = ((((4 * N + 1) * (4 * N + 1) * (td * td) + 4 * (tn * tn) : ℝ) / (16 * (td * td)))
            ^ M)⁻¹ := by
    rw [zpow_neg, zpow_natCast, sfrac_false_div]
    congr 2
    field_simp
    ring
  rw [riemannSiegelThetaStirlingErrorBound', hz, div_pow, sfrac_false_div]
  push_cast
  field_simp
theorem norm_eq_sqrt_mul_add (z : ℂ) : ‖z‖ = Real.sqrt (z.re * z.re + z.im * z.im) := by
  rw [Complex.norm_def, Complex.normSq_apply]
theorem two_pi_eq : (2 : ℝ) * Real.pi = sfrac false (nat_lit 2) (nat_lit 1) * Real.pi := by
  norm_num [sfrac]
theorem natCast_mul_pi_eq (n : ℕ) : (n : ℝ) * Real.pi = sfrac false n (nat_lit 1) * Real.pi := by
  norm_num [sfrac]
theorem pow_succ_r (x : ℝ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    x ^ b = x ^ m * x := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact pow_succ x m
theorem pow_one_r (x : ℝ) : x ^ (nat_lit 1) = x := pow_one x
theorem zrb_shape_eq (x c t : ℝ) (m : ℕ) :
    x / ((1 / 2 + Complex.I * (t : ℂ)).re + ((m : ℕ) : ℝ)) * c
      = x * sfrac false (nat_lit 2) (Nat.add 1 (Nat.mul 2 m)) * c := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hre : (1 / 2 + Complex.I * (t : ℂ)).re + ((m : ℕ) : ℝ) = ((1 + 2 * m : ℕ) : ℝ) / 2 := by
    simp
    ring
  rw [hre, sfrac_false_div]
  have h0 : ((1 + 2 * m : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℕ) < 1 + 2 * m := by omega
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  field_simp
  ring
theorem cpow_neg_s_sub_mk (t : ℝ) (tn td n m P : ℕ) (ht : t = sfrac false tn td)
    (hn : Nat.ble 1 n = true) (hP : Nat.pow n (Nat.add 1 (Nat.mul 2 m)) = P) :
    (n : ℂ) ^ (-(1 / 2 + Complex.I * (t : ℂ)) - ((m : ℕ) : ℂ))
      = ⟨(Real.sqrt (P : ℝ))⁻¹
            * Real.cos (sfrac false tn td * Real.log (sfrac false n (nat_lit 1))),
         (Real.sqrt (P : ℝ))⁻¹
            * -Real.sin (sfrac false tn td * Real.log (sfrac false n (nat_lit 1)))⟩ := by
  obtain rfl := hP
  simp only [Nat.mul_eq, Nat.add_eq, Nat.pow_eq]
  have hn' : 0 < n := pos_of_ble hn
  have hnR : (0 : ℝ) < n := pos_real_of_ble hn
  have hexp : -(1 / 2 + Complex.I * (t : ℂ)) - ((m : ℕ) : ℂ)
      = ((-(1 / 2) - m : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, natCast_cpow_eq n hn' (-(1 / 2) - m) (-t)]
  have hmag : Real.exp ((-(1 / 2) - m) * Real.log n)
      = (Real.sqrt ((n ^ (1 + 2 * m) : ℕ) : ℝ))⁻¹ := by
    have h1 : (((nat_lit 1 : ℕ) : ℝ) / ((n ^ (1 + 2 * m) : ℕ) : ℝ))
        = Real.exp (-(((1 + 2 * m : ℕ) : ℝ) * Real.log n)) := by
      rw [Nat.cast_one, one_div, Real.exp_neg]
      congr 1
      rw [← Real.log_pow, Real.exp_log (by positivity), Nat.cast_pow]
    have h2 : Real.exp ((-(1 / 2) - m) * Real.log n)
        = Real.sqrt (((nat_lit 1 : ℕ) : ℝ) / ((n ^ (1 + 2 * m) : ℕ) : ℝ)) := by
      rw [h1, ← Real.exp_half]
      congr 1
      push_cast
      ring
    rw [h2, Nat.cast_one, one_div, Real.sqrt_inv]
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  apply Complex.ext <;>
    simp only [hlogsfrac, neg_mul, Real.cos_neg, Real.sin_neg, hmag]
theorem main_sum_rs_term_mk (θ t : ℝ) (tn td n : ℕ) (ht : t = sfrac false tn td) :
    Real.cos (θ - t * Real.log n) / Real.sqrt n
      = (Real.sqrt (n : ℝ))⁻¹
          * Real.cos (θ - sfrac false tn td * Real.log (sfrac false n (nat_lit 1))) := by
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  rw [hlogsfrac, div_eq_inv_mul]
noncomputable def mainSumRS (θ t : ℝ) (ν : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ν, Real.cos (θ - t * Real.log n) / Real.sqrt n
theorem main_sum_rs_base (θ t : ℝ) :
    mainSumRS θ t (nat_lit 0) = sfrac false (nat_lit 0) (nat_lit 1) := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [mainSumRS, hIcc, Finset.sum_empty]
  simp [sfrac]
theorem main_sum_rs_succ (θ t : ℝ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true) :
    mainSumRS θ t b
      = mainSumRS θ t a + Real.cos (θ - t * Real.log b) / Real.sqrt b := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Icc_succ_top (Nat.le_add_left 1 a) _
theorem main_sum_rs_one (θ t : ℝ) : mainSumRS θ t (nat_lit 1) = Real.cos θ := by
  rw [main_sum_rs_succ θ t (nat_lit 0) (nat_lit 1) (by rfl), main_sum_rs_base]
  simp [sfrac]
theorem main_sum_of_phase_eq (θ t : ℝ) (ν : ℕ) :
    Zeta.RiemannSiegel.mainSumOfPhase θ t ν = mainSumRS θ t ν + mainSumRS θ t ν :=
  two_mul (mainSumRS θ t ν)
noncomputable def quadSignPos : ℝ := 1
noncomputable def quadSignNeg : ℝ := -1
theorem abs_quadSignPos : |quadSignPos| = 1 := by simp [quadSignPos]
theorem abs_quadSignNeg : |quadSignNeg| = 1 := by simp [quadSignNeg]
theorem sfrac_eq_quadSignPos_mul (n : Bool) (c q : ℕ) :
    sfrac n c q = quadSignPos * sfrac n c q := by
  simp [quadSignPos]
theorem sfrac_not_eq_quadSignNeg_mul (n : Bool) (c q : ℕ) :
    sfrac (!n) c q = quadSignNeg * sfrac n c q := by
  rw [sfrac_not, quadSignNeg, neg_one_mul]
private theorem exists_eq_four_mul_add_of_mod (k j : ℕ) (hk : Nat.beq (k % 4) j = true) :
    ∃ q : ℕ, k = 4 * q + j :=
  ⟨k / 4, by have := Nat.eq_of_beq_eq_true hk; have := Nat.div_add_mod k 4; omega⟩
theorem cos_quad_nat0 (k : ℕ) (hk : Nat.beq (k % 4) 0 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignPos * Real.cos r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 0 hk
  rw [quadSignPos, one_mul, ← cos_quad0 r q]; push_cast; ring_nf
theorem cos_quad_nat1 (k : ℕ) (hk : Nat.beq (k % 4) 1 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignNeg * Real.sin r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 1 hk
  rw [quadSignNeg, neg_one_mul, ← cos_quad1 r q]; push_cast; ring_nf
theorem cos_quad_nat2 (k : ℕ) (hk : Nat.beq (k % 4) 2 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignNeg * Real.cos r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 2 hk
  rw [quadSignNeg, neg_one_mul, ← cos_quad2 r q]; push_cast; ring_nf
theorem cos_quad_nat3 (k : ℕ) (hk : Nat.beq (k % 4) 3 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignPos * Real.sin r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 3 hk
  rw [quadSignPos, one_mul, ← cos_quad3 r q]; push_cast; ring_nf
theorem mainSumTerm_bound (θ : ℝ) (g : ℝ → ℝ) (ε : ℝ) (b tn td k B DI M : ℕ)
    (nθ : Bool) (cθ rθ cL rL cA rA : ℕ) (nφ : Bool) (u Pc rπ : ℕ) (nI : Bool) (cI : ℕ) (nC : Bool)
    (hε : |ε| = 1) (hquad : ∀ r : ℝ, Real.cos (r + (k : ℝ) * (Real.pi / 2)) = ε * g r)
    (hsign : sfrac nC cI B = ε * sfrac nI cI B)
    (htd : td ≠ 0) (hB : B ≠ 0) (hM : M ≠ 0) (hDI' : (2 : ℝ) * DI = B)
    (hθ : Real.IsNear θ nθ cθ B rθ B)
    (hL : Real.IsNear (Real.log (sfrac false b (nat_lit 1))) false cL B rL B)
    (hA : Real.IsNear (Real.sqrt (b : ℝ))⁻¹ false cA B rA B)
    (hpi : Real.IsNear Real.pi false Pc M rπ M)
    (hI : Real.IsNear (g ((u : ℝ) / (B : ℝ))) nI cI B 1 DI)
    (hφ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL))
      (td.mul B) (numPosC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B)))
      (numNegC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true) :
    |(Real.sqrt (b : ℝ))⁻¹ * Real.cos (θ - sfrac false tn td * Real.log (sfrac false b 1))
        - sfrac false cA B * sfrac nC cI B|
      ≤ (rA : ℝ) / B + sfrac false cA B
          * (((rθ : ℝ) + 3) / B + sfrac false tn td * ((rL : ℝ) / B) + (k : ℝ) * rπ / (2 * M)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hφ' := abs_sub_le_of_natAbsSubLe
    (Nat.pos_of_ne_zero (by simp [Nat.mul_eq, htd, hB]))
    (Nat.pos_of_ne_zero (by simp [Nat.mul_eq, hM, hB])) (Nat.pos_of_ne_zero hB) hφ
  simp only [Nat.mul_eq, Nat.add_eq, numPosC_eq, numNegC_eq] at hφ'
  have eφ : ((((numPos nθ (td * cθ) : ℕ) : ℝ)
      - ((numNeg nθ (td * cθ) + tn * cL : ℕ) : ℝ)) / ((td * B : ℕ) : ℝ))
      = sfrac nθ cθ B - sfrac false tn td * sfrac false cL B := by
    rw [sfrac_eq_parts, sfrac_false_div, sfrac_false_div]
    cases nθ <;> simp [numPos, numNeg] <;> field_simp
    all_goals ring
  set σ : ℝ := if nφ then -1 else 1 with hσdef
  set r : ℝ := (u : ℝ) / B
  set Pr : ℝ := sfrac false Pc M
  have eY : (((numPos nφ (2 * M * u + k * Pc * B) : ℕ) : ℝ)
      - ((numNeg nφ (2 * M * u + k * Pc * B) : ℕ) : ℝ)) / ((2 * M * B : ℕ) : ℝ)
      = σ * (r + (k : ℝ) * (Pr / 2)) := by
    rw [← sfrac_eq_parts, sfrac, show Pr = (Pc : ℝ) / M from sfrac_false_div Pc M, hσdef]
    simp only [r]
    push_cast
    field_simp
  rw [eφ, eY] at hφ'
  have hσ : |σ| = 1 := by rw [hσdef]; split <;> simp
  have hpi' : |Pr - Real.pi| ≤ (rπ : ℝ) / M := by
    have := hpi; rw [Real.IsNear, abs_sub_comm] at this; exact this
  set ψ : ℝ := σ * (r + (k : ℝ) * (Real.pi / 2))
  have hψ : |σ * (r + (k : ℝ) * (Pr / 2)) - ψ| ≤ (k : ℝ) * rπ / (2 * M) := by
    have e : σ * (r + (k : ℝ) * (Pr / 2)) - ψ = σ * ((k : ℝ) * ((Pr - Real.pi) / 2)) := by ring
    rw [e, abs_mul, hσ, one_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_div, abs_two]
    calc (k : ℝ) * (|Pr - Real.pi| / 2) ≤ (k : ℝ) * (((rπ : ℝ) / M) / 2) := by gcongr
      _ = (k : ℝ) * rπ / (2 * M) := by field_simp
  have hcosψ : Real.cos ψ = ε * g r := by
    have : Real.cos ψ = Real.cos (r + (k : ℝ) * (Real.pi / 2)) := by
      simp only [ψ, σ]; split
      · rw [neg_one_mul, Real.cos_neg]
      · rw [one_mul]
    rw [this, hquad]
  simp only [Real.IsNear] at hθ hL hA hI
  rw [Nat.cast_one] at hI
  have hT : 0 ≤ sfrac false tn td := by rw [sfrac_false_div]; positivity
  have hAc : 0 ≤ sfrac false cA B := by rw [sfrac_false_div]; positivity
  set L := Real.log (sfrac false b 1)
  set A := (Real.sqrt (b : ℝ))⁻¹
  set T := sfrac false tn td with hTdef
  have hphase : |θ - T * L - ψ|
      ≤ (rθ : ℝ) / B + T * ((rL : ℝ) / B) + 1 / (B : ℝ) + (k : ℝ) * rπ / (2 * M) := by
    have : θ - T * L - ψ = (θ - sfrac nθ cθ B) - T * (L - sfrac false cL B)
        + (sfrac nθ cθ B - T * sfrac false cL B - σ * (r + (k : ℝ) * (Pr / 2)))
        + (σ * (r + (k : ℝ) * (Pr / 2)) - ψ) := by ring
    rw [this]
    calc _ ≤ |θ - sfrac nθ cθ B| + |T * (L - sfrac false cL B)|
          + |sfrac nθ cθ B - T * sfrac false cL B - σ * (r + (k : ℝ) * (Pr / 2))|
          + |σ * (r + (k : ℝ) * (Pr / 2)) - ψ| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_sub _ _
      _ ≤ _ := by
            rw [abs_mul, abs_of_nonneg hT]
            gcongr
            simpa using hφ'
  set ρ : ℝ := ((rθ : ℝ) + 3) / B + T * ((rL : ℝ) / B) + (k : ℝ) * rπ / (2 * M)
  have hcos : |Real.cos (θ - T * L) - sfrac nC cI B| ≤ ρ := by
    rw [hsign]
    calc _ ≤ |Real.cos (θ - T * L) - Real.cos ψ| + |Real.cos ψ - ε * sfrac nI cI B| :=
          abs_sub_le _ _ _
      _ ≤ ((rθ : ℝ) / B + T * ((rL : ℝ) / B) + 1 / (B : ℝ) + (k : ℝ) * rπ / (2 * M))
          + 1 / (DI : ℝ) := by
            gcongr
            · exact (Real.abs_cos_sub_cos_le _ _).trans hphase
            · rw [hcosψ, ← mul_sub, abs_mul, hε, one_mul]; exact hI
      _ = ρ := by
            have hDIr : (DI : ℝ) = B / 2 := by linarith
            rw [hDIr]; simp only [ρ]; field_simp; ring
  have hterm : |A * Real.cos (θ - T * L) - sfrac false cA B * sfrac nC cI B|
      ≤ (rA : ℝ) / B + sfrac false cA B * ρ := by
    have : A * Real.cos (θ - T * L) - sfrac false cA B * sfrac nC cI B
        = (A - sfrac false cA B) * Real.cos (θ - T * L)
          + sfrac false cA B * (Real.cos (θ - T * L) - sfrac nC cI B) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hAc]
    gcongr
    calc |A - sfrac false cA B| * |Real.cos (θ - T * L)| ≤ |A - sfrac false cA B| * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ ≤ _ := by rw [mul_one]; exact hA
  exact hterm
theorem mainSumRS_step (θ t : ℝ) (g : ℝ → ℝ) (ε : ℝ) (a b tn td k B DI M : ℕ)
    (nθ : Bool) (cθ rθ cL rL cA rA : ℕ) (nS : Bool) (cS rS : ℕ) (nφ : Bool) (u Pc rπ : ℕ)
    (nI : Bool) (cI : ℕ) (nC nR : Bool) (cR rR : ℕ)
    (hε : |ε| = 1) (hquad : ∀ r : ℝ, Real.cos (r + (k : ℝ) * (Real.pi / 2)) = ε * g r)
    (hsign : sfrac nC cI B = ε * sfrac nI cI B)
    (ht : t = sfrac false tn td) (hb : Nat.beq b (a.add 1) = true)
    (hS : Real.IsNear (mainSumRS θ t a) nS cS B rS B)
    (hθ : Real.IsNear θ nθ cθ B rθ B)
    (hL : Real.IsNear (Real.log (sfrac false b (nat_lit 1))) false cL B rL B)
    (hA : Real.IsNear (Real.sqrt (b : ℝ))⁻¹ false cA B rA B)
    (hpi : Real.IsNear Real.pi false Pc M rπ M)
    (hI : Real.IsNear (g ((u : ℝ) / (B : ℝ))) nI cI B 1 DI)
    (hpos : Nat.ble (nat_lit 1) (((td.mul B).mul M).mul DI) = true)
    (hDI : Nat.beq (Nat.mul 2 DI) B = true)
    (hφ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL))
      (td.mul B) (numPosC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B)))
      (numNegC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true)
    (hR : natAbsSubLe (((numPosC nS cS).mul B).add (cA.mul (numPosC nC cI)))
      (((numNegC nS cS).mul B).add (cA.mul (numNegC nC cI))) (B.mul B)
      (numPosC nR cR) (numNegC nR cR) B (nat_lit 1) B = true)
    (hrad : Nat.ble (((((rS.add rA).add 1).mul B).mul td).mul (Nat.mul 2 M) |>.add
        (cA.mul (((Nat.mul 2 M).mul ((td.mul (rθ.add 3)).add (tn.mul rL))).add
          ((k.mul rπ).mul (td.mul B)))))
      (((rR.mul B).mul td).mul (Nat.mul 2 M)) = true) :
    Real.IsNear (mainSumRS θ t b) nR cR B rR B := by
  rw [main_sum_rs_succ θ t a b hb, main_sum_rs_term_mk θ t tn td b ht]
  simp only [Nat.ble_eq, Nat.mul_eq] at hpos
  have hp : td ≠ 0 ∧ B ≠ 0 ∧ M ≠ 0 ∧ DI ≠ 0 := by
    simpa [Nat.one_le_iff_ne_zero, Nat.mul_ne_zero_iff, and_assoc] using hpos
  obtain ⟨htd, hB, hM, hDI0⟩ := hp
  have hDI' : (2 : ℝ) * DI = B := by
    have := Nat.eq_of_beq_eq_true hDI; simp only [Nat.mul_eq] at this; exact_mod_cast this
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have htdr : (0 : ℝ) < td := by exact_mod_cast Nat.pos_of_ne_zero htd
  have hterm := mainSumTerm_bound θ g ε b tn td k B DI M nθ cθ rθ cL rL cA rA nφ u Pc rπ nI cI nC
    hε hquad hsign htd hB hM hDI' hθ hL hA hpi hI hφ
  simp only [Real.IsNear] at hS ⊢
  set T := sfrac false tn td with hTdef
  set L := Real.log (sfrac false b 1)
  set A := (Real.sqrt (b : ℝ))⁻¹
  set ρ : ℝ := ((rθ : ℝ) + 3) / B + T * ((rL : ℝ) / B) + (k : ℝ) * rπ / (2 * M)
  have hR' := abs_sub_le_of_natAbsSubLe
    (Nat.pos_of_ne_zero (by simp [Nat.mul_eq, hB])) (Nat.pos_of_ne_zero hB)
    (Nat.pos_of_ne_zero hB) hR
  simp only [Nat.mul_eq, Nat.add_eq, numPosC_eq, numNegC_eq] at hR'
  have eR' : ((((numPos nS cS * B + cA * numPos nC cI : ℕ) : ℝ)
      - ((numNeg nS cS * B + cA * numNeg nC cI : ℕ) : ℝ)) / ((B * B : ℕ) : ℝ))
      = sfrac nS cS B + sfrac false cA B * sfrac nC cI B := by
    rw [sfrac_eq_parts nS, sfrac_eq_parts nC, sfrac_false_div]
    push_cast
    field_simp
    ring
  rw [eR', ← sfrac_eq_parts] at hR'
  have hsum : |mainSumRS θ t a + A * Real.cos (θ - T * L) - sfrac nR cR B|
      ≤ (rS : ℝ) / B + ((rA : ℝ) / B + sfrac false cA B * ρ) + 1 / B := by
    have : mainSumRS θ t a + A * Real.cos (θ - T * L) - sfrac nR cR B
        = (mainSumRS θ t a - sfrac nS cS B)
          + (A * Real.cos (θ - T * L) - sfrac false cA B * sfrac nC cI B)
          + (sfrac nS cS B + sfrac false cA B * sfrac nC cI B - sfrac nR cR B) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    gcongr
    · refine (abs_add_le _ _).trans ?_
      gcongr
    · simpa using hR'
  refine hsum.trans ?_
  simp only [Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at hrad
  have hrad' : (((rS + rA + 1) * B * td * (2 * M) + cA * (2 * M * (td * (rθ + 3) + tn * rL)
      + k * rπ * (td * B)) : ℕ) : ℝ) ≤ ((rR * B * td * (2 * M) : ℕ) : ℝ) := by exact_mod_cast hrad
  push_cast at hrad'
  have hden : (0 : ℝ) < (B : ℝ) * B * td * (2 * M) := by positivity
  have key : (rS : ℝ) / B + ((rA : ℝ) / B + sfrac false cA B * ρ) + 1 / B
      = (((rS : ℝ) + rA + 1) * B * td * (2 * M) + cA * (2 * M * (td * ((rθ : ℝ) + 3) + tn * rL)
          + k * rπ * (td * B))) / ((B : ℝ) * B * td * (2 * M)) := by
    simp only [ρ, hTdef, sfrac_false_div]
    field_simp
    ring
  have keyR : (rR : ℝ) / B = (rR : ℝ) * B * td * (2 * M) / ((B : ℝ) * B * td * (2 * M)) := by
    field_simp
  rw [key, keyR]
  exact div_le_div_of_nonneg_right hrad' hden.le
def natFloorLe (XP XN : ℕ) (nR : Bool) (cR B : ℕ) : Bool :=
  Nat.ble (((numPosC nR cR).mul B).add XN) (XP.add ((numNegC nR cR).mul B)) &&
    Nat.ble (XP.add ((numNegC nR cR).mul B)) ((((numPosC nR cR).mul B).add XN).add B)
theorem abs_sub_le_of_natFloorLe {XP XN cR B : ℕ} {nR : Bool} (hB : 0 < B)
    (h : natFloorLe XP XN nR cR B = true) :
    |((XP : ℝ) - XN) / ((B * B : ℕ) : ℝ) - sfrac nR cR B| ≤ 1 / (B : ℝ) := by
  simp only [natFloorLe, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq, numPosC_eq,
    numNegC_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have h1' : ((numPos nR cR : ℝ) * B + XN) ≤ XP + (numNeg nR cR : ℝ) * B := by exact_mod_cast h1
  have h2' : ((XP : ℝ) + (numNeg nR cR : ℝ) * B) ≤ (numPos nR cR : ℝ) * B + XN + B := by
    exact_mod_cast h2
  rw [sfrac_eq_parts, abs_le]
  push_cast
  constructor
  · rw [show ((XP : ℝ) - XN) / (B * B) - (numPos nR cR - numNeg nR cR) / B
        = (XP - XN - (numPos nR cR - numNeg nR cR) * B) / (B * B) by field_simp]
    have : (0 : ℝ) ≤ (XP - XN - (numPos nR cR - numNeg nR cR) * B) / (B * B) := by
      apply div_nonneg _ (by positivity); linarith
    linarith [show (0 : ℝ) ≤ 1 / B by positivity]
  · rw [show ((XP : ℝ) - XN) / (B * B) - (numPos nR cR - numNeg nR cR) / B
        = (XP - XN - (numPos nR cR - numNeg nR cR) * B) / (B * B) by field_simp,
      div_le_div_iff₀ (by positivity) hBr]
    nlinarith
theorem mainSumRS_step2 (θ t : ℝ) (g₁ g₂ : ℝ → ℝ) (ε₁ ε₂ : ℝ) (a b₁ b₂ tn td k₁ k₂ B DI M : ℕ)
    (nθ : Bool) (cθ rθ cL₁ rL₁ cA₁ rA₁ cL₂ rL₂ cA₂ rA₂ : ℕ) (nS : Bool) (cS rS : ℕ)
    (nφ₁ : Bool) (u₁ : ℕ) (nφ₂ : Bool) (u₂ Pc rπ : ℕ)
    (nI₁ : Bool) (cI₁ : ℕ) (nC₁ nI₂ : Bool) (cI₂ : ℕ) (nC₂ nR : Bool) (cR rR : ℕ)
    (hε₁ : |ε₁| = 1) (hquad₁ : ∀ r : ℝ, Real.cos (r + (k₁ : ℝ) * (Real.pi / 2)) = ε₁ * g₁ r)
    (hsign₁ : sfrac nC₁ cI₁ B = ε₁ * sfrac nI₁ cI₁ B)
    (hε₂ : |ε₂| = 1) (hquad₂ : ∀ r : ℝ, Real.cos (r + (k₂ : ℝ) * (Real.pi / 2)) = ε₂ * g₂ r)
    (hsign₂ : sfrac nC₂ cI₂ B = ε₂ * sfrac nI₂ cI₂ B)
    (ht : t = sfrac false tn td) (hb₁ : Nat.beq b₁ (a.add 1) = true)
    (hb₂ : Nat.beq b₂ (b₁.add 1) = true)
    (hS : Real.IsNear (mainSumRS θ t a) nS cS B rS B)
    (hθ : Real.IsNear θ nθ cθ B rθ B)
    (hL₁ : Real.IsNear (Real.log (sfrac false b₁ (nat_lit 1))) false cL₁ B rL₁ B)
    (hA₁ : Real.IsNear (Real.sqrt (b₁ : ℝ))⁻¹ false cA₁ B rA₁ B)
    (hL₂ : Real.IsNear (Real.log (sfrac false b₂ (nat_lit 1))) false cL₂ B rL₂ B)
    (hA₂ : Real.IsNear (Real.sqrt (b₂ : ℝ))⁻¹ false cA₂ B rA₂ B)
    (hpi : Real.IsNear Real.pi false Pc M rπ M)
    (hI₁ : Real.IsNear (g₁ ((u₁ : ℝ) / (B : ℝ))) nI₁ cI₁ B 1 DI)
    (hI₂ : Real.IsNear (g₂ ((u₂ : ℝ) / (B : ℝ))) nI₂ cI₂ B 1 DI)
    (hpos : Nat.ble (nat_lit 1) (((td.mul B).mul M).mul DI) = true)
    (hDI : Nat.beq (Nat.mul 2 DI) B = true)
    (hφ₁ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL₁))
      (td.mul B) (numPosC nφ₁ (((Nat.mul 2 M).mul u₁).add ((k₁.mul Pc).mul B)))
      (numNegC nφ₁ (((Nat.mul 2 M).mul u₁).add ((k₁.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true)
    (hφ₂ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL₂))
      (td.mul B) (numPosC nφ₂ (((Nat.mul 2 M).mul u₂).add ((k₂.mul Pc).mul B)))
      (numNegC nφ₂ (((Nat.mul 2 M).mul u₂).add ((k₂.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true)
    (hR : natFloorLe ((((numPosC nS cS).mul B).add (cA₁.mul (numPosC nC₁ cI₁))).add
        (cA₂.mul (numPosC nC₂ cI₂)))
      ((((numNegC nS cS).mul B).add (cA₁.mul (numNegC nC₁ cI₁))).add (cA₂.mul (numNegC nC₂ cI₂)))
      nR cR B = true)
    (hrad : Nat.ble (((((((rS.add rA₁).add rA₂).add 1).mul B).mul td).mul (Nat.mul 2 M) |>.add
        (cA₁.mul (((Nat.mul 2 M).mul ((td.mul (rθ.add 3)).add (tn.mul rL₁))).add
          ((k₁.mul rπ).mul (td.mul B))))) |>.add
        (cA₂.mul (((Nat.mul 2 M).mul ((td.mul (rθ.add 3)).add (tn.mul rL₂))).add
          ((k₂.mul rπ).mul (td.mul B)))))
      (((rR.mul B).mul td).mul (Nat.mul 2 M)) = true) :
    Real.IsNear (mainSumRS θ t b₂) nR cR B rR B := by
  rw [main_sum_rs_succ θ t b₁ b₂ hb₂, main_sum_rs_succ θ t a b₁ hb₁,
    main_sum_rs_term_mk θ t tn td b₁ ht, main_sum_rs_term_mk θ t tn td b₂ ht]
  simp only [Nat.ble_eq, Nat.mul_eq] at hpos
  have hp : td ≠ 0 ∧ B ≠ 0 ∧ M ≠ 0 ∧ DI ≠ 0 := by
    simpa [Nat.one_le_iff_ne_zero, Nat.mul_ne_zero_iff, and_assoc] using hpos
  obtain ⟨htd, hB, hM, hDI0⟩ := hp
  have hDI' : (2 : ℝ) * DI = B := by
    have := Nat.eq_of_beq_eq_true hDI; simp only [Nat.mul_eq] at this; exact_mod_cast this
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have htdr : (0 : ℝ) < td := by exact_mod_cast Nat.pos_of_ne_zero htd
  have hT₁ := mainSumTerm_bound θ g₁ ε₁ b₁ tn td k₁ B DI M nθ cθ rθ cL₁ rL₁ cA₁ rA₁ nφ₁ u₁ Pc rπ
    nI₁ cI₁ nC₁ hε₁ hquad₁ hsign₁ htd hB hM hDI' hθ hL₁ hA₁ hpi hI₁ hφ₁
  have hT₂ := mainSumTerm_bound θ g₂ ε₂ b₂ tn td k₂ B DI M nθ cθ rθ cL₂ rL₂ cA₂ rA₂ nφ₂ u₂ Pc rπ
    nI₂ cI₂ nC₂ hε₂ hquad₂ hsign₂ htd hB hM hDI' hθ hL₂ hA₂ hpi hI₂ hφ₂
  have hR' := abs_sub_le_of_natFloorLe (Nat.pos_of_ne_zero hB) hR
  simp only [Nat.mul_eq, Nat.add_eq, numPosC_eq, numNegC_eq] at hR'
  have eX : ((((numPos nS cS * B + cA₁ * numPos nC₁ cI₁ + cA₂ * numPos nC₂ cI₂ : ℕ) : ℝ)
      - ((numNeg nS cS * B + cA₁ * numNeg nC₁ cI₁ + cA₂ * numNeg nC₂ cI₂ : ℕ) : ℝ))
      / ((B * B : ℕ) : ℝ))
      = sfrac nS cS B + sfrac false cA₁ B * sfrac nC₁ cI₁ B
        + sfrac false cA₂ B * sfrac nC₂ cI₂ B := by
    rw [sfrac_eq_parts nS, sfrac_eq_parts nC₁, sfrac_eq_parts nC₂, sfrac_false_div,
      sfrac_false_div]
    push_cast
    field_simp
    ring
  rw [eX] at hR'
  simp only [Real.IsNear] at hS ⊢
  set T := sfrac false tn td with hTdef
  set X₁ := (Real.sqrt (b₁ : ℝ))⁻¹ * Real.cos (θ - T * Real.log (sfrac false b₁ 1))
  set X₂ := (Real.sqrt (b₂ : ℝ))⁻¹ * Real.cos (θ - T * Real.log (sfrac false b₂ 1))
  have hsum : |mainSumRS θ t a + X₁ + X₂ - sfrac nR cR B|
      ≤ (rS : ℝ) / B
        + ((rA₁ : ℝ) / B + sfrac false cA₁ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₁ : ℝ) / B) + (k₁ : ℝ) * rπ / (2 * M)))
        + ((rA₂ : ℝ) / B + sfrac false cA₂ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₂ : ℝ) / B) + (k₂ : ℝ) * rπ / (2 * M)))
        + 1 / B := by
    have : mainSumRS θ t a + X₁ + X₂ - sfrac nR cR B
        = (mainSumRS θ t a - sfrac nS cS B)
          + (X₁ - sfrac false cA₁ B * sfrac nC₁ cI₁ B)
          + (X₂ - sfrac false cA₂ B * sfrac nC₂ cI₂ B)
          + (sfrac nS cS B + sfrac false cA₁ B * sfrac nC₁ cI₁ B
              + sfrac false cA₂ B * sfrac nC₂ cI₂ B - sfrac nR cR B) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    gcongr
    · refine (abs_add_le _ _).trans ?_
      gcongr
      refine (abs_add_le _ _).trans ?_
      gcongr
  refine hsum.trans ?_
  simp only [Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at hrad
  have hrad' : (((rS + rA₁ + rA₂ + 1) * B * td * (2 * M)
      + cA₁ * (2 * M * (td * (rθ + 3) + tn * rL₁) + k₁ * rπ * (td * B))
      + cA₂ * (2 * M * (td * (rθ + 3) + tn * rL₂) + k₂ * rπ * (td * B)) : ℕ) : ℝ)
      ≤ ((rR * B * td * (2 * M) : ℕ) : ℝ) := by exact_mod_cast hrad
  push_cast at hrad'
  have hden : (0 : ℝ) < (B : ℝ) * B * td * (2 * M) := by positivity
  have key : (rS : ℝ) / B
        + ((rA₁ : ℝ) / B + sfrac false cA₁ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₁ : ℝ) / B) + (k₁ : ℝ) * rπ / (2 * M)))
        + ((rA₂ : ℝ) / B + sfrac false cA₂ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₂ : ℝ) / B) + (k₂ : ℝ) * rπ / (2 * M)))
        + 1 / B
      = (((rS : ℝ) + rA₁ + rA₂ + 1) * B * td * (2 * M)
          + cA₁ * (2 * M * (td * ((rθ : ℝ) + 3) + tn * rL₁) + k₁ * rπ * (td * B))
          + cA₂ * (2 * M * (td * ((rθ : ℝ) + 3) + tn * rL₂) + k₂ * rπ * (td * B)))
        / ((B : ℝ) * B * td * (2 * M)) := by
    simp only [hTdef, sfrac_false_div]
    field_simp
    ring
  have keyR : (rR : ℝ) / B = (rR : ℝ) * B * td * (2 * M) / ((B : ℝ) * B * td * (2 * M)) := by
    field_simp
  rw [key, keyR]
  exact div_le_div_of_nonneg_right hrad' hden.le
theorem neg_one_pow_even_mk (n : ℕ) (h : Nat.beq (n % 2) (nat_lit 0) = true) :
    (-1 : ℝ) ^ n = sfrac false (nat_lit 1) (nat_lit 1) := by
  rw [(Nat.even_iff.2 (Nat.eq_of_beq_eq_true h)).neg_one_pow]
  norm_num [sfrac]
theorem neg_one_pow_odd_mk (n : ℕ) (h : Nat.beq (n % 2) (nat_lit 1) = true) :
    (-1 : ℝ) ^ n = sfrac true (nat_lit 1) (nat_lit 1) := by
  rw [(Nat.odd_iff.2 (Nat.eq_of_beq_eq_true h)).neg_one_pow]
  norm_num [sfrac]
theorem t_div_two_pi_mk (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td) :
    t / (2 * Real.pi)
      = sfrac false tn td * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi)⁻¹ := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  subst ht
  rw [h2, div_eq_mul_inv]
theorem sfrac_div_two_pi_nonneg (tn td : ℕ) : 0 ≤ sfrac false tn td / (2 * Real.pi) := by
  rw [sfrac_false_div]
  positivity
theorem rpow_neg_quarter_mk (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 / 4) : ℝ) = (Real.sqrt (Real.sqrt x))⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx, Real.rpow_neg hx]
  norm_num
theorem correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
            * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  rw [h2] at h
  rw [h2, h16, eq_inv_mul_iff_mul_eq₀ h, Zeta.RiemannSiegel.cos_mul_correction p]
  ring_nf
theorem cos_two_pi_p_ne_zero_mk (t : ℝ) (tn td ν : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true)
    (hν : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν) :
    Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
        * (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))) ≠ 0 := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have hν1 : sfrac false ν (nat_lit 1) = (ν : ℝ) := by norm_num [sfrac]
  have htnR : (0 : ℝ) < tn := pos_real_of_ble htn
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  set q : ℚ := (tn : ℚ) / (td : ℚ) with hqdef
  have hq : 0 < q := by
    rw [hqdef]
    exact div_pos (by exact_mod_cast htnR) (by exact_mod_cast htdR)
  have hqt : ((q : ℚ) : ℝ) = t := by
    rw [ht, hqdef, sfrac_false_div]; push_cast; ring
  rw [h2, hν1, ← hν, ← hqt]
  exact Zeta.RiemannSiegel.cos_two_pi_fract_sqrt_ne_zero q hq
theorem thirtyTwoPi_le_dec {t : ℝ} (tn td : ℕ) (ht : t = sfrac false tn td)
    (htd : Nat.ble 1 td = true)
    (h : Nat.ble (Nat.mul 504 td) (Nat.mul 5 tn) = true) : 32 * Real.pi ≤ t := by
  subst ht
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have h' : (504 : ℝ) * td ≤ 5 * tn := by
    simp only [Nat.mul_eq] at h; exact_mod_cast Nat.le_of_ble_eq_true h
  have hpi : Real.pi * td ≤ 3.15 * td := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le hd.le
  rw [sfrac_false_div, le_div_iff₀ hd]
  linarith
theorem floor_sqrt_eq_dec {t : ℝ} (tn td ν : ℕ) (ht : t = sfrac false tn td)
    (htd : Nat.ble 1 td = true)
    (hlo : Nat.ble (Nat.mul (Nat.mul 628318530717958647694 (Nat.mul ν ν)) td)
      (Nat.mul 100000000000000000000 tn) = true)
    (hhi : Nat.blt (Nat.mul 100000000000000000000 tn)
      (Nat.mul (Nat.mul 628318530717958647692 (Nat.mul (ν + 1) (ν + 1))) td) = true) :
    ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν := by
  subst ht
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlo' : (628318530717958647694 : ℝ) * (ν * ν) * td ≤ 100000000000000000000 * tn := by
    simp only [Nat.mul_eq] at hlo; exact_mod_cast Nat.le_of_ble_eq_true hlo
  have hhi' : (100000000000000000000 : ℝ) * tn
      < 628318530717958647692 * ((ν + 1) * (ν + 1)) * td := by
    simp only [Nat.mul_eq, Nat.blt_eq] at hhi; exact_mod_cast hhi
  have hsq : (0 : ℝ) ≤ (ν : ℝ) * ν := by positivity
  have hsq' : (0 : ℝ) ≤ ((ν : ℝ) + 1) * ((ν : ℝ) + 1) := by positivity
  have hpiu : (2 * Real.pi) * ((ν : ℝ) * ν) ≤ 6.28318530717958647694 * ((ν : ℝ) * ν) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_d20]) hsq
  have hpil : (6.28318530717958647692 : ℝ) * (((ν : ℝ) + 1) * ((ν : ℝ) + 1))
      ≤ (2 * Real.pi) * (((ν : ℝ) + 1) * ((ν : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_d20]) hsq'
  rw [sfrac_false_div, Nat.floor_eq_iff (Real.sqrt_nonneg _)]
  refine ⟨?_, ?_⟩
  · rw [Real.le_sqrt (Nat.cast_nonneg ν) (by positivity), le_div_iff₀ h2pi, sq]
    rw [le_div_iff₀ hd] at *
    nlinarith [hlo', hpiu, hd]
  · rw [Real.sqrt_lt' (by positivity), div_lt_iff₀ h2pi, div_lt_iff₀ hd, sq]
    nlinarith [hhi', hpil, hd]
theorem sfrac_div_two_pi_pos (tn td : ℕ) (htn : Nat.ble 1 tn = true)
    (htd : Nat.ble 1 td = true) : 0 < sfrac false tn td / (2 * Real.pi) := by
  have h1 : (0 : ℝ) < tn := pos_real_of_ble htn
  have h2 : (0 : ℝ) < td := pos_real_of_ble htd
  rw [sfrac_false_div]
  exact div_pos (div_pos h1 h2) (by positivity)
theorem t_div_two_pi_nonneg (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td) :
    0 ≤ t / (2 * Real.pi) := by
  subst ht; exact sfrac_div_two_pi_nonneg tn td
theorem sqrt_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num
theorem rpow_neg_three_quarter_mk (x : ℝ) (hx : 0 < x) :
    x ^ (-(3 / 4) : ℝ)
      = (Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x))⁻¹ := by
  rw [sqrt_sqrt_eq_rpow hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_neg hx.le]
  norm_num
theorem rpow_neg_five_quarter_mk (x : ℝ) (hx : 0 < x) :
    x ^ (-(5 / 4) : ℝ) = (Real.sqrt (Real.sqrt x) * x)⁻¹ := by
  rw [sqrt_sqrt_eq_rpow hx.le, ← Real.rpow_add_one hx.ne', ← Real.rpow_neg hx.le]
  norm_num
theorem rpow_neg_fifteen_quarter_mk (x : ℝ) (hx : 0 < x) :
    x ^ (-(15 / 4) : ℝ)
      = (Real.sqrt (Real.sqrt x) * x * (Real.sqrt (Real.sqrt x) * x)
          * (Real.sqrt (Real.sqrt x) * x))⁻¹ := by
  rw [sqrt_sqrt_eq_rpow hx.le, ← Real.rpow_add_one hx.ne', ← Real.rpow_add hx,
    ← Real.rpow_add hx, ← Real.rpow_neg hx.le]
  norm_num
theorem hardyZApproximantRS₀_eq (t : ℝ) (ν : ℕ)
    (hν : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν) :
    hardyZApproximantRS₀ t
      = Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ν
        - (-1) ^ ν * (t / (2 * Real.pi)) ^ (-(1 / 4) : ℝ)
            * Zeta.RiemannSiegel.correction
                (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1)) := by
  have hs : sfrac false ν (nat_lit 1) = (ν : ℝ) := by norm_num [sfrac]
  rw [hs]
  subst hν
  rfl
theorem hardyZErrorBoundRS₀_mk (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) :
    hardyZErrorBoundRS₀ t
      = sfrac false (nat_lit 25) (nat_lit 4)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))⁻¹
        + sfrac false (nat_lit 1) (nat_lit 32)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))))⁻¹
        + sfrac false (nat_lit 13) (nat_lit 10)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi)))
              * Real.sqrt (Real.sqrt (t / (2 * Real.pi)))
              * Real.sqrt (Real.sqrt (t / (2 * Real.pi))))⁻¹ := by
  subst ht
  have hT : 0 < sfrac false tn td / (2 * Real.pi) := sfrac_div_two_pi_pos tn td htn htd
  have h25 : sfrac false (nat_lit 25) (nat_lit 4) = (25 / 4 : ℝ) := by norm_num [sfrac]
  have h32 : sfrac false (nat_lit 1) (nat_lit 32) = (1 / 32 : ℝ) := by norm_num [sfrac]
  have h13 : sfrac false (nat_lit 13) (nat_lit 10) = (13 / 10 : ℝ) := by norm_num [sfrac]
  rw [h25, h32, h13, ← rpow_neg_five_quarter_mk _ hT, ← rpow_neg_fifteen_quarter_mk _ hT,
    ← rpow_neg_three_quarter_mk _ hT]
theorem hardyZApproximantRS_eq (t : ℝ) (ν : ℕ)
    (hν : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν) :
    hardyZApproximantRS t
      = Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ν
        - (-1) ^ ν * (t / (2 * Real.pi)) ^ (-(1 / 4) : ℝ)
            * (Zeta.RiemannSiegel.correction
                  (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))
                + Zeta.RiemannSiegel.correctionLinear
                    (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))
                  * (Real.sqrt (t / (2 * Real.pi)))⁻¹) := by
  have hs : sfrac false ν (nat_lit 1) = (ν : ℝ) := by norm_num [sfrac]
  rw [hs]
  subst hν
  rfl
theorem hardyZErrorBoundRS_mk (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) :
    hardyZErrorBoundRS t
      = sfrac false (nat_lit 25) (nat_lit 4)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))⁻¹
        + sfrac false (nat_lit 1) (nat_lit 32)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))))⁻¹ := by
  subst ht
  have hT : 0 < sfrac false tn td / (2 * Real.pi) := sfrac_div_two_pi_pos tn td htn htd
  have h25 : sfrac false (nat_lit 25) (nat_lit 4) = (25 / 4 : ℝ) := by norm_num [sfrac]
  have h32 : sfrac false (nat_lit 1) (nat_lit 32) = (1 / 32 : ℝ) := by norm_num [sfrac]
  rw [h25, h32, ← rpow_neg_five_quarter_mk _ hT, ← rpow_neg_fifteen_quarter_mk _ hT]
theorem hardyZErrorBoundRS_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    hardyZErrorBoundRS t ≤ hardyZErrorBoundRS s := by
  have hT : 0 < s / (2 * Real.pi) := div_pos hs (by positivity)
  have hle : s / (2 * Real.pi) ≤ t / (2 * Real.pi) := by gcongr
  have h5 := Real.rpow_le_rpow_of_nonpos hT hle (by norm_num : -(5 / 4 : ℝ) ≤ 0)
  have h15 := Real.rpow_le_rpow_of_nonpos hT hle (by norm_num : -(15 / 4 : ℝ) ≤ 0)
  simp only [hardyZErrorBoundRS]
  linarith
theorem hardyZErrorBoundRS₀_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    hardyZErrorBoundRS₀ t ≤ hardyZErrorBoundRS₀ s := by
  have hT : 0 < s / (2 * Real.pi) := div_pos hs (by positivity)
  have hle : s / (2 * Real.pi) ≤ t / (2 * Real.pi) := by gcongr
  have h3 := Real.rpow_le_rpow_of_nonpos hT hle (by norm_num : -(3 / 4 : ℝ) ≤ 0)
  have h := hardyZErrorBoundRS_anti hs hst
  simp only [hardyZErrorBoundRS₀]
  linarith
theorem norm_gt_hardyZErrorBoundRS_of_le (x s t : ℝ) (sn sd tn td : ℕ)
    (hs : s = sfrac false sn sd) (ht : t = sfrac false tn td) (hsn : Nat.ble 1 sn = true)
    (hsd : Nat.ble 1 sd = true) (htd : Nat.ble 1 td = true)
    (hst : Nat.ble (sn.mul td) (tn.mul sd) = true) (h : ‖x‖ > hardyZErrorBoundRS s) :
    ‖x‖ > hardyZErrorBoundRS t := by
  have hs0 : 0 < s := by
    rw [hs, sfrac_false_div]; exact div_pos (pos_real_of_ble hsn) (pos_real_of_ble hsd)
  exact lt_of_le_of_lt (hardyZErrorBoundRS_anti hs0 (dec_le_dec sn sd tn td hs ht hsd htd hst)) h
theorem norm_gt_hardyZErrorBoundRS₀_of_le (x s t : ℝ) (sn sd tn td : ℕ)
    (hs : s = sfrac false sn sd) (ht : t = sfrac false tn td) (hsn : Nat.ble 1 sn = true)
    (hsd : Nat.ble 1 sd = true) (htd : Nat.ble 1 td = true)
    (hst : Nat.ble (sn.mul td) (tn.mul sd) = true) (h : ‖x‖ > hardyZErrorBoundRS₀ s) :
    ‖x‖ > hardyZErrorBoundRS₀ t := by
  have hs0 : 0 < s := by
    rw [hs, sfrac_false_div]; exact div_pos (pos_real_of_ble hsn) (pos_real_of_ble hsd)
  exact lt_of_le_of_lt (hardyZErrorBoundRS₀_anti hs0 (dec_le_dec sn sd tn td hs ht hsd htd hst)) h
theorem deriv_correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    iteratedDeriv 1 Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * (-(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                    * (sfrac false (nat_lit 2) (nat_lit 1) * p
                          - sfrac false (nat_lit 1) (nat_lit 1))
                * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))))
            - -(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * Zeta.RiemannSiegel.correction p) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  have h1 : sfrac false (nat_lit 1) (nat_lit 1) = (1 : ℝ) := by norm_num [sfrac]
  have hsq : p * p = p ^ 2 := by ring
  rw [h2] at h
  rw [h2, h16, h1, hsq, eq_inv_mul_iff_mul_eq₀ h]
  linear_combination Zeta.RiemannSiegel.cos_mul_iteratedDeriv_one p
theorem iteratedDeriv_two_correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    iteratedDeriv 2 Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * (-((sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
                * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
                * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))))
            - sfrac false (nat_lit 4) (nat_lit 1) * Real.pi
                * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16)))
            - sfrac false (nat_lit 2) (nat_lit 1)
                * -(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * iteratedDeriv 1 Zeta.RiemannSiegel.correction p
            - -(sfrac false (nat_lit 4) (nat_lit 1) * (Real.pi * Real.pi)
                  * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * Zeta.RiemannSiegel.correction p) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h4 : sfrac false (nat_lit 4) (nat_lit 1) = (4 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  have h1 : sfrac false (nat_lit 1) (nat_lit 1) = (1 : ℝ) := by norm_num [sfrac]
  have hsq : p * p = p ^ 2 := by ring
  simp only [h2] at h
  simp only [h2, h4, h16, h1, hsq]
  rw [eq_inv_mul_iff_mul_eq₀ h]
  linear_combination Zeta.RiemannSiegel.cos_mul_iteratedDeriv_two p
theorem iteratedDeriv_three_correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    iteratedDeriv 3 Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * ((sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
              * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
              * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
              * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16)))
            - sfrac false (nat_lit 3) (nat_lit 1)
                * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
                * (sfrac false (nat_lit 4) (nat_lit 1) * Real.pi)
                    * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                      * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16)))
            - sfrac false (nat_lit 3) (nat_lit 1)
                * -(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * iteratedDeriv 2 Zeta.RiemannSiegel.correction p
            - sfrac false (nat_lit 3) (nat_lit 1)
                * -(sfrac false (nat_lit 4) (nat_lit 1) * (Real.pi * Real.pi)
                  * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * iteratedDeriv 1 Zeta.RiemannSiegel.correction p
            - sfrac false (nat_lit 8) (nat_lit 1) * (Real.pi * Real.pi * Real.pi)
                * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p)
                * Zeta.RiemannSiegel.correction p) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h3 : sfrac false (nat_lit 3) (nat_lit 1) = (3 : ℝ) := by norm_num [sfrac]
  have h4 : sfrac false (nat_lit 4) (nat_lit 1) = (4 : ℝ) := by norm_num [sfrac]
  have h8 : sfrac false (nat_lit 8) (nat_lit 1) = (8 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  have h1 : sfrac false (nat_lit 1) (nat_lit 1) = (1 : ℝ) := by norm_num [sfrac]
  have hsq : p * p = p ^ 2 := by ring
  simp only [h2] at h
  simp only [h2, h3, h4, h8, h16, h1, hsq]
  rw [eq_inv_mul_iff_mul_eq₀ h]
  linear_combination Zeta.RiemannSiegel.cos_mul_iteratedDeriv_three p
theorem correctionLinear_mk (p : ℝ) :
    Zeta.RiemannSiegel.correctionLinear p
      = -(iteratedDeriv 3 Zeta.RiemannSiegel.correction p
          * (sfrac false (nat_lit 96) (nat_lit 1) * (Real.pi * Real.pi))⁻¹) := by
  have h96 : sfrac false (nat_lit 96) (nat_lit 1) = (96 : ℝ) := by norm_num [sfrac]
  rw [h96, Zeta.RiemannSiegel.correctionLinear_eq, div_eq_mul_inv]
  ring
theorem inv_eq_neg_inv_neg (x : ℝ) : x⁻¹ = -(-x)⁻¹ := by
  rw [inv_neg, neg_neg]
theorem mul_neg_of_neg_pos_r (x y : ℝ) (hx : x < 0) (hy : 0 < y) : x * y < 0 :=
  mul_neg_of_neg_of_pos hx hy
theorem mul_neg_of_pos_neg_r (x y : ℝ) (hx : 0 < x) (hy : y < 0) : x * y < 0 :=
  mul_neg_of_pos_of_neg hx hy
end BSN
end
end CertificatePort152


section CertificatePort153
section
namespace BSN
open Enclosure
theorem log_nat_of_cert (S Dd n : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (hs : Nat.beq S n) (hd : Nat.beq Dd 1)
    (h : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) neg cn cd rn rd) :
    Real.IsNear (Real.log ((n : ℕ) : ℝ)) neg cn cd rn rd := by
  have hs' : S = n := Nat.eq_of_beq_eq_true hs
  have hd' : Dd = 1 := Nat.eq_of_beq_eq_true hd
  rw [hs', hd'] at h
  rwa [Nat.cast_one, div_one] at h
theorem log_reduce_eq (N M k : ℕ) (hN : 0 < N) (hM : 0 < M) :
    Real.log ((N : ℝ) / M) = Real.log ((N : ℝ) / (M * 2 ^ k)) + (k : ℝ) * Real.log 2 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have e : (N : ℝ) / (M * 2 ^ k) = ((N : ℝ) / M) / 2 ^ k := by rw [div_div]
  have key : Real.log ((N : ℝ) / (M * 2 ^ k)) = Real.log ((N : ℝ) / M) - (k : ℝ) * Real.log 2 := by
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow]
  rw [key]; ring
theorem log_rat_reduce_isNear (a b k S Dd pr Qr p2 Q2 D E : ℕ) (ha : Nat.ble 1 a)
    (hb : Nat.ble 1 b)
    (hS : S.beq (Nat.mul 2 a)) (hDd : Dd.beq (Nat.mul b (Nat.pow 2 (Nat.succ k))))
    (hr : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false pr Qr 1 D)
    (h2 : Real.IsNear (Real.log 2) false p2 Q2 1 E)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hQr : Nat.ble 1 Qr) (hQ2 : Nat.ble 1 Q2) :
    Real.IsNear (Real.log ((a : ℝ) / b)) false ((pr.mul Q2).add ((k.mul p2).mul Qr)) (Qr.mul Q2)
      (E.add (k.mul D)) (D.mul E) := by
  obtain rfl := Nat.eq_of_beq_eq_true hS
  obtain rfl := Nat.eq_of_beq_eq_true hDd
  simp only [Nat.mul_eq, Nat.add_eq, Nat.pow_eq] at hr ⊢
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hr h2
  have hDR : (0:ℝ) < D := pos_real_of_ble hD
  have hER : (0:ℝ) < E := pos_real_of_ble hE
  have hQrR : (0:ℝ) < Qr := pos_real_of_ble hQr
  have hQ2R : (0:ℝ) < Q2 := pos_real_of_ble hQ2
  have harg : ((↑(2 * a) : ℝ) / ((b * 2 ^ (k + 1) : ℕ) : ℝ)) = (↑a : ℝ) / ((b : ℝ) * 2 ^ k) := by
    push_cast; ring
  rw [harg] at hr
  have hlogn : Real.log ((↑a : ℝ) / b)
      = Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) + ↑k * Real.log 2 :=
    log_reduce_eq a b k (pos_of_ble ha) (pos_of_ble hb)
  have hcentre : ((pr * Q2 + k * p2 * Qr : ℕ) : ℝ) / ((Qr * Q2 : ℕ) : ℝ)
              = (pr : ℝ) / Qr + ↑k * ((p2 : ℝ) / Q2) := by
    push_cast; field_simp [hQrR.ne', hQ2R.ne']
  have hrad : ((E + k * D : ℕ) : ℝ) / ((D * E : ℕ) : ℝ) = 1 / ↑D + ↑k * (1 / ↑E) := by
    push_cast; field_simp [hDR.ne', hER.ne']
  rw [Real.IsNear, sfrac_false_div, hlogn, hcentre, hrad]
  calc |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) + ↑k * Real.log 2
          - ((pr : ℝ) / Qr + ↑k * ((p2 : ℝ) / Q2))|
      = |(Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr)
          + ↑k * (Real.log 2 - (p2 : ℝ) / Q2)| := by ring_nf
    _ ≤ |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr|
          + |↑k * (Real.log 2 - (p2 : ℝ) / Q2)| := abs_add_le _ _
    _ = |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr|
          + ↑k * |Real.log 2 - (p2 : ℝ) / Q2| := by rw [abs_mul, Nat.abs_cast]
    _ ≤ 1 / ↑D + ↑k * (1 / ↑E) := by gcongr
theorem log_two_eq (p2 Q2 E : ℕ)
    (h : Real.IsNear (Real.log (((4 : ℕ) : ℝ) / ((2 : ℕ) : ℝ))) false p2 Q2 1 E) :
    Real.IsNear (Real.log 2) false p2 Q2 1 E := by
  have e : (((4 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 2 := by norm_num
  rwa [e] at h
theorem logfrac_isNear (S Dd g a b p Q D : ℕ) (hg : Nat.ble 1 g)
    (hs : Nat.beq (S.mul g) (Nat.mul 2 a))
    (hd : Nat.beq (Dd.mul g) (Nat.mul 2 b))
    (h : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false p Q 1 D) :
    Real.IsNear (Real.log ((a : ℝ) / b)) false p Q 1 D := by
  have hs' : S * g = 2 * a := Nat.eq_of_beq_eq_true hs
  have hd' : Dd * g = 2 * b := Nat.eq_of_beq_eq_true hd
  have hgR : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_ble hg).ne'
  have h1 : (S : ℝ) * g = 2 * a := by exact_mod_cast hs'
  have h2 : (Dd : ℝ) * g = 2 * b := by exact_mod_cast hd'
  have e : ((S : ℝ) / (Dd : ℝ)) = (a : ℝ) / b := by
    calc (S : ℝ) / (Dd : ℝ)
        = (S : ℝ) * g / ((Dd : ℝ) * g) := (mul_div_mul_right _ _ hgR).symm
      _ = 2 * (a : ℝ) / (2 * (b : ℝ)) := by rw [h1, h2]
      _ = (a : ℝ) / b := mul_div_mul_left _ _ two_ne_zero
  rwa [e] at h
end BSN
end
end CertificatePort153


section CertificatePort156
section
namespace BSN
open Finset in
theorem exp_sub_sum_nonneg (x : ℝ) (N : ℕ) (hx : 0 ≤ x) :
    0 ≤ Real.exp x - ∑ k ∈ range N, x ^ k / k.factorial := by
  have hsum : Summable (fun n => x ^ n / n.factorial) := Real.summable_pow_div_factorial x
  have hexp : Real.exp x = ∑' n, x ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, sub_nonneg]
  exact hsum.sum_le_tsum _ (fun i _ => by positivity)
open Finset in
theorem exp_sub_sum_le (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (hxN : x < N + 1) :
    Real.exp x - ∑ k ∈ range N, x ^ k / k.factorial ≤
      x ^ N / N.factorial * ((N + 1) / (N + 1 - x)) := by
  have hsum : Summable (fun n => x ^ n / n.factorial) := Real.summable_pow_div_factorial x
  have hexp : Real.exp x = ∑' n, x ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hr : (0:ℝ) ≤ x / (N + 1) := by positivity
  have hr1 : x / (N + 1) < 1 := by rw [div_lt_one (by positivity)]; exact hxN
  have htail : Real.exp x - ∑ k ∈ range N, x ^ k / k.factorial
      = ∑' j, x ^ (j + N) / ((j + N).factorial : ℝ) := by
    rw [hexp, ← hsum.sum_add_tsum_nat_add N]; ring
  rw [htail]
  have htsum : Summable (fun j => x ^ (j + N) / ((j + N).factorial : ℝ)) :=
    (summable_nat_add_iff N).2 hsum
  have hgeo : Summable (fun j => x ^ N / N.factorial * (x / (N + 1)) ^ j) :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hterm : ∀ j, x ^ (j + N) / ((j + N).factorial : ℝ)
      ≤ x ^ N / N.factorial * (x / (N + 1)) ^ j := by
    intro j
    have hfac : ((N.factorial : ℝ) * (N + 1) ^ j) ≤ ((j + N).factorial : ℝ) := by
      have := Nat.factorial_mul_pow_le_factorial (m := N) (n := j)
      rw [add_comm j N]
      exact_mod_cast this
    have hnum : (0:ℝ) ≤ x ^ N * x ^ j := by positivity
    calc x ^ (j + N) / ((j + N).factorial : ℝ)
        = (x ^ N * x ^ j) / ((j + N).factorial : ℝ) := by rw [pow_add]; ring_nf
      _ ≤ (x ^ N * x ^ j) / (N.factorial * (N + 1) ^ j) :=
          div_le_div_of_nonneg_left hnum (by positivity) hfac
      _ = x ^ N / N.factorial * (x / (N + 1)) ^ j := by rw [div_pow]; ring
  calc ∑' j, x ^ (j + N) / ((j + N).factorial : ℝ)
      ≤ ∑' j, x ^ N / N.factorial * (x / (N + 1)) ^ j := htsum.tsum_le_tsum hterm hgeo
    _ = x ^ N / N.factorial * ∑' j, (x / (N + 1)) ^ j := tsum_mul_left
    _ = x ^ N / N.factorial * (1 - x / (N + 1))⁻¹ := by rw [tsum_geometric_of_lt_one hr hr1]
    _ = x ^ N / N.factorial * ((N + 1) / (N + 1 - x)) := by
        have h2 : (N:ℝ) + 1 ≠ 0 := by positivity
        rw [show (1:ℝ) - x / (N + 1) = (N + 1 - x) / (N + 1) by field_simp, inv_div]
open Finset in
theorem alt_series_tail_bound (x : ℝ) (E : ℕ) (f : ℕ → ℝ) (N : ℕ) (hx : 0 ≤ x)
    (hsummable : Summable f) (hxE : x < E + 1)
    (hnorm : ∀ j, ‖f (j + N)‖ = x ^ (E + 2 * j) / (E + 2 * j).factorial) :
    |∑' j, f (j + N)| ≤ x ^ E / E.factorial * (1 - (x / (E + 1)) ^ 2)⁻¹ := by
  have hb : x / (E + 1) < 1 := by rw [div_lt_one (by positivity)]; exact hxE
  have hr : (0:ℝ) ≤ (x / (E + 1)) ^ 2 := by positivity
  have hr1 : (x / (E + 1)) ^ 2 < 1 := pow_lt_one₀ (by positivity) hb (by norm_num)
  have htsumnorm : Summable (fun j => ‖f (j + N)‖) :=
    ((summable_nat_add_iff N).2 hsummable).norm
  have hgeo : Summable (fun j => x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j) :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hterm : ∀ j, ‖f (j + N)‖ ≤ x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j := by
    intro j
    rw [hnorm]
    have hfac : (E.factorial : ℝ) * (E + 1) ^ (2 * j) ≤ ((E + 2 * j).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_pow_le_factorial (m := E) (n := 2 * j)
    have hnum : (0:ℝ) ≤ x ^ E * x ^ (2 * j) := by positivity
    calc x ^ (E + 2 * j) / ((E + 2 * j).factorial : ℝ)
        = (x ^ E * x ^ (2 * j)) / ((E + 2 * j).factorial : ℝ) := by rw [pow_add]
      _ ≤ (x ^ E * x ^ (2 * j)) / (E.factorial * (E + 1) ^ (2 * j)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hfac
      _ = x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j := by rw [← pow_mul, div_pow]; ring
  calc |∑' j, f (j + N)|
      = ‖∑' j, f (j + N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, ‖f (j + N)‖ := norm_tsum_le_tsum_norm htsumnorm
    _ ≤ ∑' j, x ^ E / E.factorial * ((x / (E + 1)) ^ 2) ^ j := htsumnorm.tsum_le_tsum hterm hgeo
    _ = x ^ E / E.factorial * ∑' j, ((x / (E + 1)) ^ 2) ^ j := tsum_mul_left
    _ = x ^ E / E.factorial * (1 - (x / (E + 1)) ^ 2)⁻¹ := by rw [tsum_geometric_of_lt_one hr hr1]
open Finset in
theorem sin_sub_sum_le (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (hxN : x < 2 * N + 2) :
    |Real.sin x - ∑ k ∈ range N, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1).factorial| ≤
      x ^ (2 * N + 1) / (2 * N + 1).factorial * (1 - (x / (2 * N + 2)) ^ 2)⁻¹ := by
  set f : ℕ → ℝ := fun n => (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1).factorial with hf
  have hsummable : Summable f := (Real.hasSum_sin x).summable
  have hsin : Real.sin x = ∑' n, f n := Real.sin_eq_tsum x
  have htail : Real.sin x - ∑ k ∈ range N, f k = ∑' j, f (j + N) := by
    rw [hsin, ← hsummable.sum_add_tsum_nat_add N]; ring
  rw [htail]
  have hnorm : ∀ j, ‖f (j + N)‖ = x ^ (2 * N + 1 + 2 * j) / (2 * N + 1 + 2 * j).factorial := by
    intro j
    have he : 2 * (j + N) + 1 = 2 * N + 1 + 2 * j := by ring
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hx, Nat.abs_cast, he]
  refine (alt_series_tail_bound x (2 * N + 1) f N hx hsummable (by push_cast; linarith)
    hnorm).trans_eq ?_
  push_cast; ring
open Finset in
theorem cos_sub_sum_le (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (hxN : x < 2 * N + 1) :
    |Real.cos x - ∑ k ∈ range N, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial| ≤
      x ^ (2 * N) / (2 * N).factorial * (1 - (x / (2 * N + 1)) ^ 2)⁻¹ := by
  set f : ℕ → ℝ := fun n => (-1) ^ n * x ^ (2 * n) / (2 * n).factorial with hf
  have hsummable : Summable f := (Real.hasSum_cos x).summable
  have hcos : Real.cos x = ∑' n, f n := Real.cos_eq_tsum x
  have htail : Real.cos x - ∑ k ∈ range N, f k = ∑' j, f (j + N) := by
    rw [hcos, ← hsummable.sum_add_tsum_nat_add N]; ring
  rw [htail]
  have hnorm : ∀ j, ‖f (j + N)‖ = x ^ (2 * N + 2 * j) / (2 * N + 2 * j).factorial := by
    intro j
    have he : 2 * (j + N) = 2 * N + 2 * j := by ring
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hx, Nat.abs_cast, he]
  refine (alt_series_tail_bound x (2 * N) f N hx hsummable (by push_cast; linarith)
    hnorm).trans_eq ?_
  push_cast; ring
open Finset in
theorem abs_pow_sub_pow_le {a b M : ℝ} {n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ M) (hbM : b ≤ M) :
    |b ^ n - a ^ n| ≤ n * M ^ (n - 1) * |b - a| := by
  rw [← Commute.geom_sum₂_mul (Commute.all b a) n, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc |∑ i ∈ range n, b ^ i * a ^ (n - 1 - i)|
      ≤ ∑ i ∈ range n, |b ^ i * a ^ (n - 1 - i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ range n, b ^ i * a ^ (n - 1 - i) :=
        Finset.sum_congr rfl fun i _ => abs_of_nonneg (by positivity)
    _ ≤ ∑ _i ∈ range n, M ^ (n - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hile : i ≤ n - 1 := by simp only [Finset.mem_range] at hi; omega
        have hM : 0 ≤ M := ha.trans haM
        have hpow : b ^ i * a ^ (n - 1 - i) ≤ M ^ i * M ^ (n - 1 - i) :=
          mul_le_mul (pow_le_pow_left₀ hb hbM i) (pow_le_pow_left₀ ha haM _)
            (by positivity) (by positivity)
        rwa [← pow_add, Nat.add_sub_cancel' hile] at hpow
    _ = n * M ^ (n - 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
theorem geo_factor_le (x D : ℝ) (hD : 0 < D) (hx : 2 * x ^ 2 ≤ D ^ 2) :
    (1 - (x / D) ^ 2)⁻¹ ≤ 2 := by
  have h2 : (x / D) ^ 2 ≤ 1 / 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  rw [← one_div]
  calc 1 / (1 - (x / D) ^ 2) ≤ 1 / (1 / 2) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ = 2 := by norm_num
theorem factorial_add_four (m : ℕ) :
    (m + 4).factorial = m.factorial * ((m + 1) * (m + 2) * (m + 3) * (m + 4)) := by
  have e : m + 4 = m + 1 + 1 + 1 + 1 := rfl
  rw [e, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  ring
open Finset in
theorem sum_range_two_mul {α} [AddCommMonoid α] (f : ℕ → α) (M : ℕ) :
    ∑ i ∈ range (2 * M), f i = ∑ j ∈ range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    abel
theorem sub_grid_round (F Ne De No Do : ℝ) (m : ℤ) (Q D : ℕ)
    (hFV : |F - (Ne / De - No / Do)| ≤ 1 / (2 * D))
    (hr1 : (m : ℝ) * (De * Do) ≤ (Ne * Do - No * De) * Q)
    (hr2 : (Ne * Do - No * De) * Q < ((m : ℝ) + 1) * (De * Do))
    (hDe : 0 < De) (hDo : 0 < Do) (hDr : 0 < (D : ℝ)) (hQr : 0 < (Q : ℝ))
    (hQ : 2 * D ≤ Q) :
    |F - (m : ℝ) / Q| ≤ 1 / D := by
  have hd : (0 : ℝ) < De * Do := mul_pos hDe hDo
  have hV : Ne / De - No / Do = (Ne * Do - No * De) / (De * Do) := by field_simp
  have e1 : (m : ℝ) / Q ≤ (Ne * Do - No * De) / (De * Do) := by
    rw [div_le_div_iff₀ hQr hd]; exact hr1
  have e2 : (Ne * Do - No * De) / (De * Do) < (m : ℝ) / Q + 1 / Q := by
    rw [← add_div, div_lt_div_iff₀ hd hQr]; exact hr2
  have hround' : |(Ne / De - No / Do) - (m : ℝ) / Q| ≤ 1 / (2 * D) := by
    rw [hV, abs_of_nonneg (sub_nonneg.mpr e1)]
    calc (Ne * Do - No * De) / (De * Do) - (m : ℝ) / Q
        ≤ 1 / Q := by linarith [e2]
      _ ≤ 1 / (2 * D) := by
          rw [div_le_div_iff₀ hQr (mul_pos two_pos hDr), one_mul, one_mul]; exact_mod_cast hQ
  calc |F - (m : ℝ) / Q|
      ≤ |F - (Ne / De - No / Do)| + |(Ne / De - No / Do) - (m : ℝ) / Q| := abs_sub_le _ _ _
    _ ≤ 1 / (2 * D) + 1 / (2 * D) := add_le_add hFV hround'
    _ = 1 / D := by rw [← add_div, one_add_one_eq_two, ← div_div, div_self two_ne_zero]
end BSN
end
end CertificatePort156


section CertificatePort157
section
namespace BSN
open Enclosure
open Finset
def expNatP (u : ℕ) : ℕ → ℕ := fun _ => u
def expNatQ (v : ℕ) : ℕ → ℕ := fun j => Nat.mul v (Nat.succ j)
theorem exp_neg_recip_bound (Q D0 Q' D p p' : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hp : Nat.ble 1 p) (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q')
    (hD : Nat.ble 1 D) (hD0 : Nat.ble 1 D0) (hQp : Q.ble p)
    (hr1 : (p'.mul p).ble (Q'.mul Q)) (hr2 : (Q'.mul Q).blt ((p'.succ).mul p))
    (hcomb : (D.mul (Q'.add D0)).ble (D0.mul Q'))
    (hpos : Real.IsNear (Real.exp x) false p Q 1 D0) :
    Real.IsNear (Real.exp (-x)) false p' Q' 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hpos ⊢
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hQp hr1 hr2 hcomb
  have hpR : (0 : ℝ) < p := pos_real_of_ble hp
  have hQR : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hQ'R : (0 : ℝ) < Q' := pos_real_of_ble hQ'
  have hDR : (0 : ℝ) < D := pos_real_of_ble hD
  have hD0R : (0 : ℝ) < D0 := pos_real_of_ble hD0
  set a : ℝ := Real.exp x with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact Real.one_le_exp hx
  have ha0 : 0 < a := by linarith
  have hane : a ≠ 0 := ne_of_gt ha0
  set b : ℝ := (p : ℝ) / Q with hbdef
  have hb1 : 1 ≤ b := by rw [hbdef, le_div_iff₀ hQR, one_mul]; exact_mod_cast hQp
  have hb0 : 0 < b := by linarith
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hexpneg : Real.exp (-x) = 1 / a := by rw [Real.exp_neg, one_div, ha]
  rw [hexpneg]
  have hab : |1 / a - 1 / b| ≤ 1 / D0 := by
    have heq : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
    rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < a * b),
      div_le_iff₀ (by positivity : (0 : ℝ) < a * b)]
    calc |b - a| = |a - b| := abs_sub_comm b a
      _ ≤ 1 / D0 := hpos
      _ ≤ 1 / D0 * (a * b) := le_mul_of_one_le_right (by positivity) (by nlinarith)
  have hterm2 : |1 / b - (p' : ℝ) / Q'| ≤ 1 / Q' := by
    have h1b : 1 / b = (Q : ℝ) / p := by rw [hbdef, one_div_div]
    rw [h1b]
    have e1 : (p' : ℝ) / Q' ≤ (Q : ℝ) / p := by
      rw [div_le_div_iff₀ hQ'R hpR, mul_comm (Q : ℝ)]; exact_mod_cast hr1
    have e2 : (Q : ℝ) / p < (p' : ℝ) / Q' + 1 / Q' := by
      rw [← add_div, div_lt_div_iff₀ hpR hQ'R, mul_comm (Q : ℝ)]; exact_mod_cast hr2
    rw [abs_of_nonneg (by linarith)]; linarith
  calc |1 / a - (p' : ℝ) / Q'|
      ≤ |1 / a - 1 / b| + |1 / b - (p' : ℝ) / Q'| := abs_sub_le _ _ _
    _ ≤ 1 / D0 + 1 / Q' := add_le_add hab hterm2
    _ ≤ 1 / D := by
        have hc : (D : ℝ) * (Q' + D0) ≤ D0 * Q' := by exact_mod_cast hcomb
        rw [div_add_div _ _ (ne_of_gt hD0R) (ne_of_gt hQ'R), one_mul, mul_one,
          div_le_div_iff₀ (by positivity) hDR, one_mul]
        nlinarith
theorem exp_neg_bound (u v Q D0 Q' D p p' : ℕ)
    (hp : Nat.ble 1 p) (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q')
    (hD : Nat.ble 1 D) (hD0 : Nat.ble 1 D0) (hQp : Q.ble p)
    (hr1 : (p'.mul p).ble (Q'.mul Q)) (hr2 : (Q'.mul Q).blt ((p'.succ).mul p))
    (hcomb : (D.mul (Q'.add D0)).ble (D0.mul Q'))
    (hpos : Real.IsNear (Real.exp ((u : ℝ) / v)) false p Q 1 D0) :
    Real.IsNear (Real.exp ((-(u : ℝ)) / v)) false p' Q' 1 D := by
  rw [neg_div]
  exact exp_neg_recip_bound Q D0 Q' D p p' ((u : ℝ) / v) (by positivity)
    hp hQ hQ' hD hD0 hQp hr1 hr2 hcomb hpos
theorem exp_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ j ∈ Finset.Ico 0 (i + 1), ((u : ℚ) / ((v * (j + 1) : ℕ) : ℚ))
      = ((u : ℚ) / v) ^ (i + 1) / ((i + 1).factorial : ℚ) := by
  rw [← Finset.range_eq_Ico]
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range]
  have hfac : ∏ j ∈ Finset.range (i + 1), ((j : ℚ) + 1) = ((i + 1).factorial : ℚ) := by
    rw [← Finset.prod_range_add_one_eq_factorial (i + 1)]; push_cast; ring
  rw [hfac, div_pow]
  have hvne : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hfne : ((i + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
theorem exp_value (u v N T Q P : ℕ) (hv : v ≠ 0) (hN : 1 ≤ N)
    (h : (T, Q, P) = binarySplit (fun _ => u) (fun j => v * (j + 1)) 0 (N - 1)) :
    (((Q + T : ℕ) : ℚ) / (Q : ℚ))
      = ∑ i ∈ Finset.range N, ((u : ℚ) / v) ^ i / (i.factorial : ℚ) := by
  have hqne : ∀ i, (fun j => v * (j + 1)) i ≠ 0 := by intro i; simp [hv]
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := fun _ => u) (q := fun j => v * (j + 1))
      (m := 0) (n := N - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := fun _ => u) (q := fun j => v * (j + 1))
    (m := 0) (n := N - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => by simpa using exp_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : N = N - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  rw [hspec]
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  push_cast
  field_simp
  ring
open Real in
theorem exp_dyadic_bound (u v N Nm Qd D T P Q p : ℕ)
    (hu : u.blt ((N.succ).mul v)) (hQd : Nat.ble 1 Qd) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hN : Nat.ble 1 N) (hNm : (Nm.succ).beq N)
    (hsplit : binarySplit (expNatP u) (expNatQ v) 0 Nm = (T, Qd, P))
    (htail : (((u.pow N).mul (N.succ)).mul v).mul (Nat.mul 2 D) |>.ble
      (((v.mul N).mul Qd).mul (((N.succ).mul v).sub u)))
    (hr1 : (p.mul Qd).ble ((Qd.add T).mul Q)) (hr2 : ((Qd.add T).mul Q).blt ((p.succ).mul Qd))
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.exp ((u : ℝ) / v)) false p Q 1 D := by
  have hNm' : Nm = N - 1 := by
    have h : Nm + 1 = N := Nat.eq_of_beq_eq_true hNm
    omega
  subst hNm'
  have hQdeq : Qd = v ^ (N - 1) * (N - 1).factorial := by
    have h := (binarySplit_PQ (p := expNatP u) (q := expNatQ v) (m := 0) (n := N - 1)).2
    rw [hsplit] at h
    have hQdraw : Qd = ∏ j ∈ Finset.Ico 0 (N - 1), expNatQ v j := h
    rw [hQdraw, ← Finset.range_eq_Ico]
    simp only [expNatQ, Nat.mul_eq, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    rw [Finset.prod_range_add_one_eq_factorial]
  have hbridge : v * N * Qd = v ^ N * N.factorial := by
    rw [hQdeq]
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by have := Nat.le_of_ble_eq_true hN; omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ, Nat.factorial_succ]; ring
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
    Nat.sub_eq] at hu htail hr1 hr2 hQ
  rw [hbridge] at htail
  have hDN : 0 < D := pos_of_ble hD
  have hqs' : (0 : ℝ) < Qd := pos_real_of_ble hQd
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hvne : v ≠ 0 := (pos_of_ble hv).ne'
  have hvR : (v : ℝ) ≠ 0 := ne_of_gt hvr
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hx0 : 0 ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < (N : ℝ) + 1 := by rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hsum : ∑ k ∈ Finset.range N, ((u : ℝ) / v) ^ k / (k.factorial : ℝ)
      = ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) := by
    have hq := exp_value u v N T Qd P hvne (Nat.le_of_ble_eq_true hN) hsplit.symm
    have hr := congrArg (fun r : ℚ => (r : ℝ)) hq
    push_cast at hr ⊢
    rw [← hr]
  have hexp : |Real.exp ((u : ℝ) / v) - ((Qd + T : ℕ) : ℝ) / (Qd : ℝ)|
      ≤ ((u : ℝ) / v) ^ N / N.factorial * (((N : ℝ) + 1) / ((N : ℝ) + 1 - (u : ℝ) / v)) := by
    rw [← hsum, abs_of_nonneg (exp_sub_sum_nonneg _ N hx0)]
    exact exp_sub_sum_le _ N hx0 hxlt
  have htail' : ((u : ℝ) / v) ^ N / N.factorial * (((N : ℝ) + 1) / ((N : ℝ) + 1 - (u : ℝ) / v))
      ≤ 1 / (2 * D) := by
    have hpos : (0 : ℝ) < (N : ℝ) + 1 - (u : ℝ) / v := by linarith
    have hsubpos : 0 < (N + 1) * v - u := by
      have h := hu; simp only [Nat.succ_eq_add_one] at h; omega
    have hfacne : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos N).ne'
    have hvpowne : (v : ℝ) ^ N ≠ 0 := pow_ne_zero N hvR
    have hc1 : ((N : ℝ) + 1 - (u : ℝ) / v) = (((N + 1) * v - u : ℕ) : ℝ) / v := by
      rw [Nat.cast_sub hu.le]; push_cast; field_simp
    have key : ((u : ℝ) / v) ^ N / N.factorial * (((N : ℝ) + 1) / ((N : ℝ) + 1 - (u : ℝ) / v))
        = ((u : ℝ) ^ N * ((N : ℝ) + 1) * v) /
          ((v : ℝ) ^ N * N.factorial * (((N + 1) * v - u : ℕ) : ℝ)) := by
      rw [hc1, div_pow]
      field_simp
    have hden : (0 : ℝ) < (v : ℝ) ^ N * N.factorial * (((N + 1) * v - u : ℕ) : ℝ) :=
      mul_pos (mul_pos (pow_pos hvr N) (by exact_mod_cast Nat.factorial_pos N))
        (by exact_mod_cast hsubpos)
    rw [key, div_le_div_iff₀ hden (mul_pos two_pos hDr), one_mul]
    exact_mod_cast htail
  have e1 : (p : ℝ) / Q ≤ ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) := by
    rw [div_le_div_iff₀ hQr hqs']; exact_mod_cast hr1
  have e2 : ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) < (p : ℝ) / Q + 1 / Q := by
    rw [← add_div, div_lt_div_iff₀ hqs' hQr]; exact_mod_cast hr2
  have hround' : |((Qd + T : ℕ) : ℝ) / (Qd : ℝ) - (p : ℝ) / Q| ≤ 1 / (2 * D) := by
    rw [abs_of_nonneg (sub_nonneg.mpr e1)]
    calc ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) - (p : ℝ) / Q
        ≤ 1 / Q := by linarith [e2]
      _ ≤ 1 / (2 * D) := by
          rw [div_le_div_iff₀ hQr (mul_pos two_pos hDr), one_mul, one_mul]; exact_mod_cast hQ
  calc |Real.exp ((u : ℝ) / v) - (p : ℝ) / Q|
      ≤ |Real.exp ((u : ℝ) / v) - ((Qd + T : ℕ) : ℝ) / (Qd : ℝ)|
          + |((Qd + T : ℕ) : ℝ) / (Qd : ℝ) - (p : ℝ) / Q| := abs_sub_le _ _ _
    _ ≤ 1 / (2 * D) + 1 / (2 * D) := add_le_add (hexp.trans htail') hround'
    _ = 1 / D := by rw [← add_div, one_add_one_eq_two, ← div_div, div_self two_ne_zero]
theorem exp_int_of_rat (u : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (h : Real.IsNear (Real.exp ((u : ℝ) / ((1 : ℕ) : ℝ))) neg cn cd rn rd) :
    Real.IsNear (Real.exp ((u : ℕ) : ℝ)) neg cn cd rn rd := by
  rwa [Nat.cast_one, div_one] at h
end BSN
end
end CertificatePort157


section CertificatePort159
section
namespace BSN
open Enclosure
open Finset
theorem prod_even_denom (j : ℕ) :
    ∏ k ∈ range j, ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5))
        = (4 * j + 1).factorial := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : 4 * (n + 1) + 1 = (4 * n + 1) + 4 := by ring
    rw [prod_range_succ, ih, e, factorial_add_four]
theorem prod_odd_denom (j : ℕ) :
    (∏ k ∈ range j, ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7))) * 6 =
      (4 * j + 3).factorial := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have e : 4 * (n + 1) + 3 = (4 * n + 3) + 4 := by ring
    rw [prod_range_succ, e, factorial_add_four, ← ih]
    ring
theorem sinEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((sinEvenP u k : ℚ) / (sinEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [sinEvenP, sinEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial := by
    have keyN : ∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5)))
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, prod_even_denom]
    exact_mod_cast keyN
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem sinEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (sinEvenP u) (sinEvenQ v) 0 (M - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 1) / ((v : ℚ) ^ (4 * j + 1) * (4 * j + 1).factorial) := by
  have hqne : ∀ i, sinEvenQ v i ≠ 0 := by
    intro i; simp only [sinEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => sinEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 1) / ((v : ℚ) ^ (4 * (i + 1) + 1) * (4 * (i + 1) + 1).factorial)
        = (u : ℚ) / v *
          ((u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial)) := by
    intro i _
    rw [pow_succ' (u : ℚ), pow_succ' (v : ℚ)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
  field_simp
  ring
theorem sinOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((sinOddP u k : ℚ) / (sinOddQ v k))
      = 6 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [sinOddP, sinOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial / 6 := by
    have keyN : (∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)))) * 6
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_odd_denom]
    have keyQ : (∏ k ∈ Finset.range (i + 1),
        ((v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)) : ℕ) : ℚ)) * 6
        = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (6 : ℚ) ≠ 0)]
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem sinOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (sinOddP u) (sinOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 3 * (Q + T) / (6 * v ^ 3 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 3) / ((v : ℚ) ^ (4 * j + 3) * (4 * j + 3).factorial) := by
  have hqne : ∀ i, sinOddQ v i ≠ 0 := by
    intro i; simp only [sinOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := sinOddP u) (q := sinOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := sinOddP u) (q := sinOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => sinOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 3) / ((v : ℚ) ^ (4 * (i + 1) + 3) * (4 * (i + 1) + 3).factorial)
        = (u : ℚ) ^ 3 / (6 * v ^ 3) *
          (6 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial)) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 3, pow_add (v : ℚ) (4 * (i + 1)) 3]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_succ, Nat.factorial_zero]
  push_cast
  field_simp
  ring
theorem sin_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : (((numPos neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  have hMpos0 : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hbridge : v * (Qe * sinEvenQ v (M - 1))
      = v ^ (2 * (2 * M) + 1) * (2 * (2 * M) + 1).factorial := by
    have hQeprod : Qe = ∏ k ∈ Finset.range (M - 1), sinEvenQ v k := by
      have h := (binarySplit_PQ (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1)).2
      rw [heven, ← Finset.range_eq_Ico] at h; exact h
    rw [hQeprod, ← Finset.prod_range_succ, show M - 1 + 1 = M from by omega]
    simp only [sinEvenQ, Nat.pow_eq, Nat.mul_eq, Nat.add_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, prod_even_denom,
      show 2 * (2 * M) + 1 = 4 * M + 1 from by ring, pow_succ]
    ring
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQeN : 0 < Qe := pos_of_ble hQe
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := sinEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := sinOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : (u : ℚ) * (Qe + Te) / (v * Qe) - (u : ℚ) ^ 3 * (Qo + To) / (6 * v ^ 3 * Qo)
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℚ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) + 1 = 4 * j + 1 := by ring
    have e2 : 2 * (2 * j + 1) + 1 = 4 * j + 3 := by ring
    rw [e1, e2, s1, s2, div_pow, div_pow]
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hu hu2 htail hQ hr1 hr2
  set De := v * Qe with hDe_def
  set Do := 6 * v ^ 3 * Qo with hDo_def
  set Ne := u * (Qe + Te) with hNe_def
  set No := u ^ 3 * (Qo + To) with hNo_def
  have hDeR : (De : ℝ) = (v : ℝ) * Qe := by rw [hDe_def]; push_cast; ring
  have hDoR : (Do : ℝ) = 6 * (v : ℝ) ^ 3 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((De : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * De) * Q := by
    have h : (mp : ℤ) * ((De : ℤ) * Do) + (No : ℤ) * De * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((De : ℤ) * Do) = (mp : ℤ) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q < (m + 1) * ((De : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do)
        < (mp + 1) * ((De : ℤ) * Do) + (No : ℤ) * De * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((De : ℤ) * Do)
        = (mp + 1) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hDe0 : (0 : ℝ) < De := by rw [hDeR]; positivity
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / De - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℝ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDe_def, hNo_def, hDo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((2 * M : ℕ) : ℝ) + 2 := by
    rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hsin := sin_sub_sum_le ((u : ℝ) / v) (2 * M) hxnn hxlt
  rw [← hvalR] at hsin
  have hsin' : |Real.sin ((u : ℝ) / v) - ((Ne : ℝ) / De - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine hsin.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * (2 * M) + 1) / (2 * (2 * M) + 1).factorial * 2
        ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * (2 * M) + 1) * 2 * (2 * D)
          = 2 * (u : ℝ) ^ (2 * (2 * M) + 1) * (2 * D) := by ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ (2 * (2 * M) + 1) * (2 * D)
          ≤ (v : ℝ) * (Qe : ℝ) * (sinEvenQ v (M - 1) : ℝ) := by exact_mod_cast htail
      have hbR : (v : ℝ) * (Qe : ℝ) * (sinEvenQ v (M - 1) : ℝ)
          = (v : ℝ) ^ (2 * (2 * M) + 1) * ((2 * (2 * M) + 1).factorial : ℝ) := by
        have hb : v * Qe * sinEvenQ v (M - 1)
            = v ^ (2 * (2 * M) + 1) * (2 * (2 * M) + 1).factorial := by
          rw [Nat.mul_assoc]; exact hbridge
        exact_mod_cast hb
      exact le_of_le_of_eq htR hbR
    refine le_trans ?_ hA2
    gcongr
    exact geo_factor_le _ _ (by positivity) (by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact_mod_cast hu2)
  have hr1' : (m : ℝ) * ((De : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * De) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * De) * Q < ((m : ℝ) + 1) * ((De : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.sin ((u : ℝ) / v)) (Ne : ℝ) (De : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hsin' hr1' hr2' hDe0 hDo0 hDr hQr hQ
theorem sin_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : ((cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      (((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q)).blt
      ((((cn.succ)).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) false cn Q 1 D := by
  refine sin_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega
theorem sin_dyadic_bound_t (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : (((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))).blt
      ((((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) true cn Q 1 D := by
  refine sin_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po true cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
      Nat.zero_mul, Nat.zero_add] at hr1 ⊢
    omega
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.blt_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.one_mul] at hr2 ⊢
    omega
theorem sin_neg_of_bound (u v : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (hpos : Real.IsNear (Real.sin ((u : ℝ) / v)) neg cn cd rn rd) :
    Real.IsNear (Real.sin ((-(u : ℝ)) / v)) (!neg) cn cd rn rd := by
  rw [Real.IsNear, sfrac_not, neg_div, Real.sin_neg]
  have he : -Real.sin ((u : ℝ) / v) - -sfrac neg cn cd
      = -(Real.sin ((u : ℝ) / v) - sfrac neg cn cd) := by ring
  rw [he, abs_neg]
  exact hpos
end BSN
end
end CertificatePort159


section CertificatePort161
section
namespace BSN
open Enclosure
open Finset
theorem prod_cosEven_denom (j : ℕ) :
    ∏ k ∈ range j, ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)) = (4 * j).factorial := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : 4 * (n + 1) = (4 * n) + 4 := by ring
    rw [prod_range_succ, ih, e, factorial_add_four]
theorem prod_cosOdd_denom (j : ℕ) :
    (∏ k ∈ range j, ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6))) * 2 =
      (4 * j + 2).factorial := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have e : 4 * (n + 1) + 2 = (4 * n + 2) + 4 := by ring
    rw [prod_range_succ, e, factorial_add_four, ← ih]
    ring
theorem cosEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((cosEvenP u k : ℚ) / (cosEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1)).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [cosEvenP, cosEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1)).factorial := by
    have keyN : ∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)))
        = v ^ (4 * (i + 1)) * (4 * (i + 1)).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
        prod_cosEven_denom]
    exact_mod_cast keyN
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1)).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem cosEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (cosEvenP u) (cosEvenQ v) 0 (M - 1)) :
    (((Q + T : ℕ) : ℚ) / Q)
      = ∑ j ∈ Finset.range M, (u : ℚ) ^ (4 * j) / ((v : ℚ) ^ (4 * j) * (4 * j).factorial) := by
  have hqne : ∀ i, cosEvenQ v i ≠ 0 := by
    intro i; simp only [cosEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => cosEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ', hspec]
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  push_cast
  field_simp
  ring
theorem cosOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((cosOddP u k : ℚ) / (cosOddQ v k))
      = 2 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [cosOddP, cosOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial / 2 := by
    have keyN : (∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)))) * 2
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_cosOdd_denom]
    have keyQ : (∏ k ∈ Finset.range (i + 1),
        ((v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)) : ℕ) : ℚ)) * 2
        = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)]
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]
theorem cosOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (cosOddP u) (cosOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 2 * (Q + T) / (2 * v ^ 2 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 2) / ((v : ℚ) ^ (4 * j + 2) * (4 * j + 2).factorial) := by
  have hqne : ∀ i, cosOddQ v i ≠ 0 := by
    intro i; simp only [cosOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := cosOddP u) (q := cosOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := cosOddP u) (q := cosOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => cosOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 2) / ((v : ℚ) ^ (4 * (i + 1) + 2) * (4 * (i + 1) + 2).factorial)
        = (u : ℚ) ^ 2 / (2 * v ^ 2) *
          (2 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial)) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 2, pow_add (v : ℚ) (4 * (i + 1)) 2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_two]
  push_cast
  field_simp
  ring
theorem cos_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : (((numPos neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)).ble
      ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  have hMpos0 : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hbridge : Qe * cosEvenQ v (M - 1) = v ^ (2 * (2 * M)) * (2 * (2 * M)).factorial := by
    have hQeprod : Qe = ∏ k ∈ Finset.range (M - 1), cosEvenQ v k := by
      have h := (binarySplit_PQ (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1)).2
      rw [heven, ← Finset.range_eq_Ico] at h; exact h
    rw [hQeprod, ← Finset.prod_range_succ, show M - 1 + 1 = M from by omega]
    simp only [cosEvenQ, Nat.pow_eq, Nat.mul_eq, Nat.add_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
      prod_cosEven_denom, show 4 * M = 2 * (2 * M) from by ring]
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := cosEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := cosOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : ((Qe + Te : ℕ) : ℚ) / Qe - (u : ℚ) ^ 2 * (Qo + To) / (2 * v ^ 2 * Qo)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℚ) / v) ^ (2 * i) / (2 * i).factorial := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) = 4 * j := by ring
    have e2 : 2 * (2 * j + 1) = 4 * j + 2 := by ring
    rw [e1, e2, s1, s2, div_pow, div_pow]
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hu hu2 htail hQ hr1 hr2
  push_cast at hcombine
  set Do := 2 * v ^ 2 * Qo with hDo_def
  set Ne := Qe + Te with hNe_def
  set No := u ^ 2 * (Qo + To) with hNo_def
  have hDoR : (Do : ℝ) = 2 * (v : ℝ) ^ 2 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((Qe : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q := by
    have h : (mp : ℤ) * ((Qe : ℤ) * Do) + (No : ℤ) * Qe * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((Qe : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((Qe : ℤ) * Do) = (mp : ℤ) * ((Qe : ℤ) * Do) - (mn : ℤ) * ((Qe : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * Qe * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q < (m + 1) * ((Qe : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((Qe : ℤ) * Do)
        < (mp + 1) * ((Qe : ℤ) * Do) + (No : ℤ) * Qe * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((Qe : ℤ) * Do)
        = (mp + 1) * ((Qe : ℤ) * Do) - (mn : ℤ) * ((Qe : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * Qe * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQe0 : (0 : ℝ) < Qe := pos_real_of_ble hQe
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / Qe - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℝ) / v) ^ (2 * i) / (2 * i).factorial := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDo_def, hNo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((2 * M : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hcos := cos_sub_sum_le ((u : ℝ) / v) (2 * M) hxnn hxlt
  rw [← hvalR] at hcos
  have hcos' : |Real.cos ((u : ℝ) / v) - ((Ne : ℝ) / Qe - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine hcos.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * (2 * M)) / (2 * (2 * M)).factorial * 2 ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * (2 * M)) * 2 * (2 * D)
          = 2 * (u : ℝ) ^ (2 * (2 * M)) * (2 * D) := by ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ (2 * (2 * M)) * (2 * D) ≤ (Qe : ℝ) * (cosEvenQ v (M - 1) : ℝ) := by
        exact_mod_cast htail
      have hbR : (Qe : ℝ) * (cosEvenQ v (M - 1) : ℝ)
          = (v : ℝ) ^ (2 * (2 * M)) * ((2 * (2 * M)).factorial : ℝ) := by exact_mod_cast hbridge
      exact le_of_le_of_eq htR hbR
    refine le_trans ?_ hA2
    gcongr
    exact geo_factor_le _ _ (by positivity) (by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact_mod_cast hu2)
  have hr1' : (m : ℝ) * ((Qe : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * Qe) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * Qe) * Q < ((m : ℝ) + 1) * ((Qe : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.cos ((u : ℝ) / v)) (Ne : ℝ) (Qe : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hcos' hr1' hr2' hQe0 hDo0 hDr hQr hQ
theorem cos_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : ((cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)).ble
      (((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q)).blt
      (((cn.succ).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) false cn Q 1 D := by
  refine cos_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega
theorem cos_dyadic_bound_t (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q).ble
      ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        (cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        (cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))).blt
      ((Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) true cn Q 1 D := by
  refine cos_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po true cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
      Nat.zero_mul, Nat.zero_add] at hr1 ⊢
    omega
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.blt_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.one_mul] at hr2 ⊢
    omega
theorem cos_neg_of_bound (u v : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (h : Real.IsNear (Real.cos ((u : ℝ) / v)) neg cn cd rn rd) :
    Real.IsNear (Real.cos ((-(u : ℝ)) / v)) neg cn cd rn rd := by
  rw [Real.IsNear, neg_div, Real.cos_neg]; exact h
end BSN
end
end CertificatePort161


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort163
section
namespace BSN
open Enclosure
open Finset
private theorem prod_2k3 (i : ℕ) :
    ∏ k ∈ range i, (2 * k + 3) = (∏ k ∈ range i, (2 * k + 1)) * (2 * i + 1) := by
  induction i with
  | zero => simp
  | succ n ih => rw [prod_range_succ, ih, prod_range_succ]; ring
theorem artanh_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ j ∈ Finset.Ico 0 (i + 1), ((artanhP u j : ℚ) / (artanhQ v j))
      = ((u : ℚ) / v) ^ (2 * (i + 1)) / ((2 * (i + 1) + 1 : ℕ) : ℚ) := by
  rw [← Finset.range_eq_Ico]
  simp only [artanhP, artanhQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ k ∈ Finset.range (i + 1), ((u ^ 2 * (2 * k + 1) : ℕ) : ℚ))
      = (u : ℚ) ^ (2 * (i + 1)) * ∏ k ∈ Finset.range (i + 1), ((2 * k + 1 : ℕ) : ℚ) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hden : (∏ k ∈ Finset.range (i + 1), ((v ^ 2 * (2 * k + 3) : ℕ) : ℚ))
      = (v : ℚ) ^ (2 * (i + 1)) *
        ((∏ k ∈ Finset.range (i + 1), ((2 * k + 1 : ℕ) : ℚ)) * (2 * (i + 1) + 1)) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
    congr 1
    exact_mod_cast prod_2k3 (i + 1)
  rw [hnum, hden, div_pow]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hp1 : (∏ k ∈ Finset.range (i + 1), ((2 * k + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp
theorem artanh_value (u v N T Q P : ℕ) (hv : v ≠ 0) (hN : 1 ≤ N)
    (h : (T, Q, P) = binarySplit (artanhP u) (artanhQ v) 0 (N - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ i ∈ Finset.range N, ((u : ℚ) / v) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ) := by
  have hqne : ∀ i, artanhQ v i ≠ 0 := by
    intro i; simp only [artanhQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 2 hv) (by omega)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := artanhP u) (q := artanhQ v)
      (m := 0) (n := N - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := artanhP u) (q := artanhQ v)
    (m := 0) (n := N - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => artanh_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : N = N - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (N - 1),
      ((u : ℚ) / v) ^ (2 * (i + 1) + 1) / ((2 * (i + 1) + 1 : ℕ) : ℚ)
        = ((u : ℚ) / v) * (((u : ℚ) / v) ^ (2 * (i + 1)) / ((2 * (i + 1) + 1 : ℕ) : ℚ)) := by
    intro i _
    rw [pow_succ']
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.cast_one, div_one]
  field_simp
  ring
theorem log_dyadic_bound (u v N Nm Qd Qdy D T P p S Dd : ℕ)
    (huv : u.blt v) (hg : (Nat.mul 2 (u.pow 2)).ble (v.pow 2)) (hQd : Nat.ble 1 Qd)
    (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hN : Nat.ble 1 N) (hNm : (Nm.succ).beq N)
    (hS : S.beq (v.add u)) (hDd : Dd.beq (v.sub u))
    (hsplit : binarySplit (artanhP u) (artanhQ v) 0 Nm = (T, Qd, P))
    (htail : ((Nat.mul 4 (u.pow ((Nat.mul 2 N).succ))).mul (Nat.mul 2 D)).ble
      (v.pow ((Nat.mul 2 N).succ)))
    (hr1 : (p.mul (v.mul Qd)).ble ((Nat.mul 2 (u.mul (Qd.add T))).mul Qdy))
    (hr2 : ((Nat.mul 2 (u.mul (Qd.add T))).mul Qdy).blt ((p.succ).mul (v.mul Qd)))
    (hQ : (Nat.mul 2 D).ble Qdy) :
    Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false p Qdy 1 D := by
  have hNm' : Nm = N - 1 := by
    have h : Nm + 1 = N := Nat.eq_of_beq_eq_true hNm
    omega
  subst hNm'
  obtain rfl : S = v + u := Nat.eq_of_beq_eq_true hS
  obtain rfl : Dd = v - u := Nat.eq_of_beq_eq_true hDd
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one]
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at huv hg hQd hD hv hN htail hr1 hr2 hQ
  have hQdy0 : 0 < Qdy := by omega
  have hQdyr : (0 : ℝ) < Qdy := by exact_mod_cast hQdy0
  have hvne : v ≠ 0 := by omega
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  have hQd0 : (0 : ℝ) < Qd := by exact_mod_cast (by omega : 0 < Qd)
  have hden0 : (0 : ℝ) < (v : ℝ) * Qd := mul_pos hv0 hQd0
  have hsumR : (u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd)
      = ∑ i ∈ Finset.range N, ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    have hq := artanh_value u v N T Qd P hvne hN hsplit.symm
    have hr := congrArg (fun r : ℚ => (r : ℝ)) hq
    push_cast at hr
    rw [hr]
  have hlog' : |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ))
        - 2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd))| ≤ 1 / (2 * D) := by
    have hx : |(u : ℝ) / v| < 1 := by
      rw [abs_of_nonneg (by positivity), div_lt_one hv0]; exact_mod_cast huv
    have hm := Real.sum_range_sub_log_div_le hx N
    have harg : ((1 : ℝ) + (u : ℝ) / v) / (1 - (u : ℝ) / v)
        = ((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ) := by
      rw [Nat.cast_sub huv.le]; push_cast; field_simp
    rw [harg] at hm
    rw [hsumR]
    have habs : |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ)) -
          2 * ∑ i ∈ Finset.range N, ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)|
        = 2 * |1 / 2 * Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ)) -
          ∑ i ∈ Finset.range N, ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)| := by
      rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← abs_mul]; congr 1; ring
    rw [habs]
    refine (mul_le_mul_of_nonneg_left hm (by norm_num)).trans ?_
    have hdm : ((u : ℝ) / v) ^ (2 * N + 1) / (1 - ((u : ℝ) / v) ^ 2)
        = ((u : ℝ) / v) ^ (2 * N + 1) * (1 - ((u : ℝ) / v) ^ 2)⁻¹ := div_eq_mul_inv _ _
    rw [abs_of_nonneg (by positivity), hdm]
    have hgf := geo_factor_le u v hv0 (by exact_mod_cast hg)
    have hA2 : (4 : ℝ) * ((u : ℝ) / v) ^ (2 * N + 1) ≤ 1 / (2 * D) := by
      rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (mul_pos two_pos hDr), one_mul]
      exact_mod_cast htail
    calc 2 * (((u : ℝ) / v) ^ (2 * N + 1) * (1 - ((u : ℝ) / v) ^ 2)⁻¹)
        ≤ 2 * (((u : ℝ) / v) ^ (2 * N + 1) * 2) := by gcongr
      _ = 4 * ((u : ℝ) / v) ^ (2 * N + 1) := by ring
      _ ≤ 1 / (2 * D) := hA2
  have h2val : 2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd))
      = ((2 * (u * (Qd + T)) : ℕ) : ℝ) / ((v * Qd : ℕ) : ℝ) := by push_cast; ring
  have e1 : (p : ℝ) / Qdy ≤ ((2 * (u * (Qd + T)) : ℕ) : ℝ) / ((v * Qd : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hQdyr (by exact_mod_cast hden0)]; exact_mod_cast hr1
  have e2 : ((2 * (u * (Qd + T)) : ℕ) : ℝ) / ((v * Qd : ℕ) : ℝ) < (p : ℝ) / Qdy + 1 / Qdy := by
    rw [← add_div, div_lt_div_iff₀ (by exact_mod_cast hden0) hQdyr]; exact_mod_cast hr2
  have hround' : |2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd)) - (p : ℝ) / Qdy|
      ≤ 1 / (2 * D) := by
    rw [h2val, abs_of_nonneg (sub_nonneg.mpr e1)]
    calc ((2 * (u * (Qd + T)) : ℕ) : ℝ) / ((v * Qd : ℕ) : ℝ) - (p : ℝ) / Qdy
        ≤ 1 / Qdy := by linarith [e2]
      _ ≤ 1 / (2 * D) := by
          rw [div_le_div_iff₀ hQdyr (mul_pos two_pos hDr), one_mul, one_mul]; exact_mod_cast hQ
  calc |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ)) - (p : ℝ) / Qdy|
      ≤ |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ))
            - 2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd))|
          + |2 * ((u : ℝ) * ((Qd : ℝ) + T) / ((v : ℝ) * Qd)) - (p : ℝ) / Qdy| := abs_sub_le _ _ _
    _ ≤ 1 / (2 * D) + 1 / (2 * D) := add_le_add hlog' hround'
    _ = 1 / D := by rw [← add_div, one_add_one_eq_two, ← div_div, div_self two_ne_zero]
theorem isNear_log_inv (P Q : ℝ) (cn cd rn rd : ℕ) (hPQ : P = Q⁻¹)
    (h : Real.IsNear (Real.log Q) false cn cd rn rd) :
    Real.IsNear (Real.log P) true cn cd rn rd := by
  have hlog : Real.log P = -Real.log Q := by rw [hPQ, Real.log_inv]
  rw [hlog]; exact h.neg
theorem sfrac_recip (a b : ℕ) : sfrac false a b = ((b : ℝ) / a)⁻¹ := by
  rw [sfrac_false_div, inv_div]
theorem isNear_log_sfrac (pn pd cn cd rn rd : ℕ) (neg : Bool)
    (h : Real.IsNear (Real.log ((pn : ℝ) / pd)) neg cn cd rn rd) :
    Real.IsNear (Real.log (sfrac false pn pd)) neg cn cd rn rd := by rwa [sfrac_false_div]
theorem isNear_log_arg (P : ℝ) (pn pd cn cd rn rd : ℕ) (neg : Bool) (hP : P = sfrac false pn pd)
    (h : Real.IsNear (Real.log (sfrac false pn pd)) neg cn cd rn rd) :
    Real.IsNear (Real.log P) neg cn cd rn rd := by rw [hP]; exact h
theorem isNear_log_image {x : ℝ} {n1 n2 nR : Bool}
    {cn cd ρn ρd L1 K1 L2 K2 c1 d1 r1 e1 c2 d2 r2 e2 cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cn cd ρn ρd)
    (hcd : Nat.ble 1 cd) (hρd : Nat.ble 1 ρd) (hK1 : Nat.ble 1 K1) (hK2 : Nat.ble 1 K2)
    (hL1 : Nat.ble 1 L1)
    (hpos : Nat.blt (ρn.mul cd) (cn.mul ρd))
    (hE1 : Nat.beq (L1.mul (cd.mul ρd)) (((cn.mul ρd).sub (ρn.mul cd)).mul K1))
    (hE2 : Nat.beq (L2.mul (cd.mul ρd)) (((cn.mul ρd).add (ρn.mul cd)).mul K2))
    (h1 : Real.IsNear (Real.log (sfrac false L1 K1)) n1 c1 d1 r1 e1)
    (h2 : Real.IsNear (Real.log (sfrac false L2 K2)) n2 c2 d2 r2 e2)
    (hd1 : Nat.ble 1 d1) (he1 : Nat.ble 1 e1) (hd2 : Nat.ble 1 d2) (he2 : Nat.ble 1 e2)
    (hcdR : Nat.ble 1 cdR) (hrdR : Nat.ble 1 rdR)
    (hL : Nat.ble ((((numPos nR cnR).mul ((rdR.mul d1).mul e1)).add
              ((numNeg n1 c1).mul ((cdR.mul rdR).mul e1))).add
              (r1.mul ((cdR.mul rdR).mul d1)))
            ((((numPos n1 c1).mul ((cdR.mul rdR).mul e1)).add
              ((numNeg nR cnR).mul ((rdR.mul d1).mul e1))).add
              (rnR.mul ((cdR.mul d1).mul e1))))
    (hH : Nat.ble ((((numPos n2 c2).mul ((cdR.mul rdR).mul e2)).add
              ((numNeg nR cnR).mul ((rdR.mul d2).mul e2))).add
              (r2.mul ((cdR.mul rdR).mul d2)))
            ((((numPos nR cnR).mul ((rdR.mul d2).mul e2)).add
              ((numNeg n2 c2).mul ((cdR.mul rdR).mul e2))).add
              (rnR.mul ((cdR.mul d2).mul e2)))) :
    Real.IsNear (Real.log x) nR cnR cdR rnR rdR := by
  refine Real.IsNear.of_interval h1 h2 ?_ ?_ hd1 he1 hd2 he2 hcdR hrdR hL hH
  case _ =>
    simp only [Nat.blt_eq, Nat.mul_eq, Nat.sub_eq] at hpos hE1
    have hcdR' : (0:ℝ) < cd := pos_real_of_ble hcd
    have hρdR' : (0:ℝ) < ρd := pos_real_of_ble hρd
    have hK1R : (0:ℝ) < K1 := pos_real_of_ble hK1
    have hL1R : (0:ℝ) < L1 := pos_real_of_ble hL1
    have hfrac : sfrac false L1 K1 = (cn : ℝ) / cd - (ρn : ℝ) / ρd := by
      rw [sfrac_false_div, div_sub_div _ _ hcdR'.ne' hρdR'.ne',
        div_eq_div_iff hK1R.ne' (by positivity)]
      have hE1R : (L1 : ℝ) * (cd * ρd) = ((cn * ρd - ρn * cd : ℕ) : ℝ) * K1 := by
        exact_mod_cast Nat.eq_of_beq_eq_true hE1
      rw [Nat.cast_sub hpos.le] at hE1R
      push_cast at hE1R ⊢
      linarith [hE1R]
    have hle : sfrac false L1 K1 ≤ x := by
      rw [hfrac]
      have h := hx.lower; rwa [sfrac_false_div] at h
    have hL1pos : (0:ℝ) < sfrac false L1 K1 := by
      rw [sfrac_false_div]; positivity
    exact Real.log_le_log hL1pos hle
  case _ =>
    simp only [Nat.blt_eq, Nat.mul_eq, Nat.sub_eq,
      Nat.add_eq] at hpos hE1 hE2
    have hcdR' : (0:ℝ) < cd := pos_real_of_ble hcd
    have hρdR' : (0:ℝ) < ρd := pos_real_of_ble hρd
    have hK1R : (0:ℝ) < K1 := pos_real_of_ble hK1
    have hK2R : (0:ℝ) < K2 := pos_real_of_ble hK2
    have hL1R : (0:ℝ) < L1 := pos_real_of_ble hL1
    have hfrac1 : sfrac false L1 K1 = (cn : ℝ) / cd - (ρn : ℝ) / ρd := by
      rw [sfrac_false_div, div_sub_div _ _ hcdR'.ne' hρdR'.ne',
        div_eq_div_iff hK1R.ne' (by positivity)]
      have hE1R : (L1 : ℝ) * (cd * ρd) = ((cn * ρd - ρn * cd : ℕ) : ℝ) * K1 := by
        exact_mod_cast Nat.eq_of_beq_eq_true hE1
      rw [Nat.cast_sub hpos.le] at hE1R
      push_cast at hE1R ⊢
      linarith [hE1R]
    have hfrac2 : sfrac false L2 K2 = (cn : ℝ) / cd + (ρn : ℝ) / ρd := by
      rw [sfrac_false_div, div_add_div _ _ hcdR'.ne' hρdR'.ne',
        div_eq_div_iff hK2R.ne' (by positivity)]
      have hE2R : (L2 : ℝ) * (cd * ρd) = ((cn * ρd + ρn * cd : ℕ) : ℝ) * K2 := by
        exact_mod_cast Nat.eq_of_beq_eq_true hE2
      push_cast at hE2R ⊢
      linarith [hE2R]
    have hxpos : (0:ℝ) < x := by
      have hlo : sfrac false L1 K1 ≤ x := by
        rw [hfrac1]
        have h := hx.lower; rwa [sfrac_false_div] at h
      have hL1pos : (0:ℝ) < sfrac false L1 K1 := by
        rw [sfrac_false_div]; positivity
      linarith
    have hle : x ≤ sfrac false L2 K2 := by
      rw [hfrac2]
      have h := hx.upper; rwa [sfrac_false_div] at h
    exact Real.log_le_log hxpos hle
private theorem ble_of_le {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq.mpr h
theorem isNear_log_image_fff {x : ℝ}
    {cn cd ρn ρd L1 K1 L2 K2 c1 d1 r1 e1 c2 d2 r2 e2 cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cn cd ρn ρd)
    (hcd : Nat.ble 1 cd) (hρd : Nat.ble 1 ρd) (hK1 : Nat.ble 1 K1) (hK2 : Nat.ble 1 K2)
    (hL1 : Nat.ble 1 L1)
    (hpos : Nat.blt (ρn.mul cd) (cn.mul ρd))
    (hE1 : Nat.beq (L1.mul (cd.mul ρd)) (((cn.mul ρd).sub (ρn.mul cd)).mul K1))
    (hE2 : Nat.beq (L2.mul (cd.mul ρd)) (((cn.mul ρd).add (ρn.mul cd)).mul K2))
    (h1 : Real.IsNear (Real.log (sfrac false L1 K1)) false c1 d1 r1 e1)
    (h2 : Real.IsNear (Real.log (sfrac false L2 K2)) false c2 d2 r2 e2)
    (hd1 : Nat.ble 1 d1) (he1 : Nat.ble 1 e1) (hd2 : Nat.ble 1 d2) (he2 : Nat.ble 1 e2)
    (hcdR : Nat.ble 1 cdR) (hrdR : Nat.ble 1 rdR)
    (hL : Nat.ble ((cnR.mul ((rdR.mul d1).mul e1)).add (r1.mul ((cdR.mul rdR).mul d1)))
            ((c1.mul ((cdR.mul rdR).mul e1)).add (rnR.mul ((cdR.mul d1).mul e1))))
    (hH : Nat.ble ((c2.mul ((cdR.mul rdR).mul e2)).add (r2.mul ((cdR.mul rdR).mul d2)))
            ((cnR.mul ((rdR.mul d2).mul e2)).add (rnR.mul ((cdR.mul d2).mul e2)))) :
    Real.IsNear (Real.log x) false cnR cdR rnR rdR :=
  isNear_log_image hx hcd hρd hK1 hK2 hL1 hpos hE1 hE2 h1 h2 hd1 he1 hd2 he2 hcdR hrdR
    (ble_of_le (by
      have h := Nat.le_of_ble_eq_true hL
      simp only [Nat.mul_eq, Nat.add_eq] at h
      simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]; omega))
    (ble_of_le (by
      have h := Nat.le_of_ble_eq_true hH
      simp only [Nat.mul_eq, Nat.add_eq] at h
      simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]; omega))
theorem isNear_log_image_ttt {x : ℝ}
    {cn cd ρn ρd L1 K1 L2 K2 c1 d1 r1 e1 c2 d2 r2 e2 cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cn cd ρn ρd)
    (hcd : Nat.ble 1 cd) (hρd : Nat.ble 1 ρd) (hK1 : Nat.ble 1 K1) (hK2 : Nat.ble 1 K2)
    (hL1 : Nat.ble 1 L1)
    (hpos : Nat.blt (ρn.mul cd) (cn.mul ρd))
    (hE1 : Nat.beq (L1.mul (cd.mul ρd)) (((cn.mul ρd).sub (ρn.mul cd)).mul K1))
    (hE2 : Nat.beq (L2.mul (cd.mul ρd)) (((cn.mul ρd).add (ρn.mul cd)).mul K2))
    (h1 : Real.IsNear (Real.log (sfrac false L1 K1)) true c1 d1 r1 e1)
    (h2 : Real.IsNear (Real.log (sfrac false L2 K2)) true c2 d2 r2 e2)
    (hd1 : Nat.ble 1 d1) (he1 : Nat.ble 1 e1) (hd2 : Nat.ble 1 d2) (he2 : Nat.ble 1 e2)
    (hcdR : Nat.ble 1 cdR) (hrdR : Nat.ble 1 rdR)
    (hL : Nat.ble ((c1.mul ((cdR.mul rdR).mul e1)).add (r1.mul ((cdR.mul rdR).mul d1)))
            ((cnR.mul ((rdR.mul d1).mul e1)).add (rnR.mul ((cdR.mul d1).mul e1))))
    (hH : Nat.ble ((cnR.mul ((rdR.mul d2).mul e2)).add (r2.mul ((cdR.mul rdR).mul d2)))
            ((c2.mul ((cdR.mul rdR).mul e2)).add (rnR.mul ((cdR.mul d2).mul e2)))) :
    Real.IsNear (Real.log x) true cnR cdR rnR rdR :=
  isNear_log_image hx hcd hρd hK1 hK2 hL1 hpos hE1 hE2 h1 h2 hd1 he1 hd2 he2 hcdR hrdR
    (ble_of_le (by
      have h := Nat.le_of_ble_eq_true hL
      simp only [Nat.mul_eq, Nat.add_eq] at h
      simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]; omega))
    (ble_of_le (by
      have h := Nat.le_of_ble_eq_true hH
      simp only [Nat.mul_eq, Nat.add_eq] at h
      simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]; omega))
theorem isNear_log_image_tff {x : ℝ}
    {cn cd ρn ρd L1 K1 L2 K2 c1 d1 r1 e1 c2 d2 r2 e2 cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cn cd ρn ρd)
    (hcd : Nat.ble 1 cd) (hρd : Nat.ble 1 ρd) (hK1 : Nat.ble 1 K1) (hK2 : Nat.ble 1 K2)
    (hL1 : Nat.ble 1 L1)
    (hpos : Nat.blt (ρn.mul cd) (cn.mul ρd))
    (hE1 : Nat.beq (L1.mul (cd.mul ρd)) (((cn.mul ρd).sub (ρn.mul cd)).mul K1))
    (hE2 : Nat.beq (L2.mul (cd.mul ρd)) (((cn.mul ρd).add (ρn.mul cd)).mul K2))
    (h1 : Real.IsNear (Real.log (sfrac false L1 K1)) true c1 d1 r1 e1)
    (h2 : Real.IsNear (Real.log (sfrac false L2 K2)) false c2 d2 r2 e2)
    (hd1 : Nat.ble 1 d1) (he1 : Nat.ble 1 e1) (hd2 : Nat.ble 1 d2) (he2 : Nat.ble 1 e2)
    (hcdR : Nat.ble 1 cdR) (hrdR : Nat.ble 1 rdR)
    (hL : Nat.ble (((cnR.mul ((rdR.mul d1).mul e1)).add (c1.mul ((cdR.mul rdR).mul e1))).add
            (r1.mul ((cdR.mul rdR).mul d1)))
            (rnR.mul ((cdR.mul d1).mul e1)))
    (hH : Nat.ble ((c2.mul ((cdR.mul rdR).mul e2)).add (r2.mul ((cdR.mul rdR).mul d2)))
            ((cnR.mul ((rdR.mul d2).mul e2)).add (rnR.mul ((cdR.mul d2).mul e2)))) :
    Real.IsNear (Real.log x) false cnR cdR rnR rdR :=
  isNear_log_image hx hcd hρd hK1 hK2 hL1 hpos hE1 hE2 h1 h2 hd1 he1 hd2 he2 hcdR hrdR
    (ble_of_le (by
      have h := Nat.le_of_ble_eq_true hL
      simp only [Nat.mul_eq, Nat.add_eq] at h
      simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]; omega))
    (ble_of_le (by
      have h := Nat.le_of_ble_eq_true hH
      simp only [Nat.mul_eq, Nat.add_eq] at h
      simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]; omega))
theorem isNear_log_image_tft {x : ℝ}
    {cn cd ρn ρd L1 K1 L2 K2 c1 d1 r1 e1 c2 d2 r2 e2 cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cn cd ρn ρd)
    (hcd : Nat.ble 1 cd) (hρd : Nat.ble 1 ρd) (hK1 : Nat.ble 1 K1) (hK2 : Nat.ble 1 K2)
    (hL1 : Nat.ble 1 L1)
    (hpos : Nat.blt (ρn.mul cd) (cn.mul ρd))
    (hE1 : Nat.beq (L1.mul (cd.mul ρd)) (((cn.mul ρd).sub (ρn.mul cd)).mul K1))
    (hE2 : Nat.beq (L2.mul (cd.mul ρd)) (((cn.mul ρd).add (ρn.mul cd)).mul K2))
    (h1 : Real.IsNear (Real.log (sfrac false L1 K1)) true c1 d1 r1 e1)
    (h2 : Real.IsNear (Real.log (sfrac false L2 K2)) false c2 d2 r2 e2)
    (hd1 : Nat.ble 1 d1) (he1 : Nat.ble 1 e1) (hd2 : Nat.ble 1 d2) (he2 : Nat.ble 1 e2)
    (hcdR : Nat.ble 1 cdR) (hrdR : Nat.ble 1 rdR)
    (hL : Nat.ble ((c1.mul ((cdR.mul rdR).mul e1)).add (r1.mul ((cdR.mul rdR).mul d1)))
            ((cnR.mul ((rdR.mul d1).mul e1)).add (rnR.mul ((cdR.mul d1).mul e1))))
    (hH : Nat.ble (((c2.mul ((cdR.mul rdR).mul e2)).add (cnR.mul ((rdR.mul d2).mul e2))).add
            (r2.mul ((cdR.mul rdR).mul d2)))
            (rnR.mul ((cdR.mul d2).mul e2))) :
    Real.IsNear (Real.log x) true cnR cdR rnR rdR :=
  isNear_log_image hx hcd hρd hK1 hK2 hL1 hpos hE1 hE2 h1 h2 hd1 he1 hd2 he2 hcdR hrdR
    (ble_of_le (by
      have h := Nat.le_of_ble_eq_true hL
      simp only [Nat.mul_eq, Nat.add_eq] at h
      simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]; omega))
    (ble_of_le (by
      have h := Nat.le_of_ble_eq_true hH
      simp only [Nat.mul_eq, Nat.add_eq] at h
      simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]; omega))
theorem log_verify_gen (P X EPS : ℝ) (cneg xneg : Bool) (cn cd rn rd xn xd en ed : ℕ)
    (hcert : Real.IsNear (Real.log P) cneg cn cd rn rd)
    (hX : X = sfrac xneg xn xd) (hEPS : EPS = sfrac false en ed)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hxd : Nat.ble 1 xd) (hed : Nat.ble 1 ed)
    (hlo : Nat.blt ((((numPos xneg xn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((xd.mul ed).mul rd))).add
              (rn.mul ((cd.mul xd).mul ed)))
            ((((numPos cneg cn).mul ((xd.mul ed).mul rd)).add
              ((numNeg xneg xn).mul ((ed.mul cd).mul rd))).add
              (en.mul ((xd.mul cd).mul rd))))
    (hhi : Nat.blt ((((numPos cneg cn).mul ((xd.mul ed).mul rd)).add
              ((numNeg xneg xn).mul ((ed.mul cd).mul rd))).add
              (rn.mul ((cd.mul xd).mul ed)))
            ((((numPos xneg xn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((xd.mul ed).mul rd))).add
              (en.mul ((xd.mul cd).mul rd)))) :
    |Real.log P - X| < EPS := by
  subst hX hEPS
  simp only [Nat.blt_eq, Nat.add_eq, Nat.mul_eq] at hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hxdR : (0:ℝ) < xd := pos_real_of_ble hxd
  have hedR : (0:ℝ) < ed := pos_real_of_ble hed
  have heps : sfrac false en ed = (en : ℝ) / ed := by simp [sfrac]
  rw [Real.IsNear, abs_le] at hcert
  have hloR : sfrac xneg xn xd - (en : ℝ) / ed < sfrac cneg cn cd - (rn : ℝ) / rd := by
    rw [sfrac_eq_parts xneg xn xd, sfrac_eq_parts cneg cn cd,
      div_sub_div _ _ hxdR.ne' hedR.ne', div_sub_div _ _ hcdR.ne' hrdR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos xneg xn * (ed * cd * rd) + numNeg cneg cn * (xd * ed * rd)
                + rn * (cd * xd * ed) : ℕ) : ℝ)
            < ((numPos cneg cn * (xd * ed * rd) + numNeg xneg xn * (ed * cd * rd)
                + en * (xd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hlo
    push_cast at hc ⊢; nlinarith [hc]
  have hhiR : sfrac cneg cn cd + (rn : ℝ) / rd < sfrac xneg xn xd + (en : ℝ) / ed := by
    rw [sfrac_eq_parts xneg xn xd, sfrac_eq_parts cneg cn cd,
      div_add_div _ _ hcdR.ne' hrdR.ne', div_add_div _ _ hxdR.ne' hedR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos cneg cn * (xd * ed * rd) + numNeg xneg xn * (ed * cd * rd)
                + rn * (cd * xd * ed) : ℕ) : ℝ)
            < ((numPos xneg xn * (ed * cd * rd) + numNeg cneg cn * (xd * ed * rd)
                + en * (xd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hhi
    push_cast at hc ⊢; nlinarith [hc]
  rw [heps, abs_lt]
  exact ⟨by linarith [hcert.1, hloR], by linarith [hcert.2, hhiR]⟩
end BSN
end
end CertificatePort163


section CertificatePort165
section
namespace BSN
open Enclosure
theorem log2_combine (p₁ p₂ p₃ Q D E P : ℕ)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hDE : (Nat.mul 15 E).ble D)
    (hP : P.beq (((Nat.mul 7 p₁).add (Nat.mul 5 p₂)).add (Nat.mul 3 p₃)))
    (h₁ : Real.IsNear (Real.log (((32 : ℕ) : ℝ) / ((30 : ℕ) : ℝ))) false p₁ Q 1 D)
    (h₂ : Real.IsNear (Real.log (((50 : ℕ) : ℝ) / ((48 : ℕ) : ℝ))) false p₂ Q 1 D)
    (h₃ : Real.IsNear (Real.log (((162 : ℕ) : ℝ) / ((160 : ℕ) : ℝ))) false p₃ Q 1 D) :
    Real.IsNear (Real.log 2) false P Q 1 E := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at h₁ h₂ h₃ ⊢
  simp only [Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hDE hP
  subst hP
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have e₁ : (((32 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = 16 / 15 := by norm_num
  have e₂ : (((50 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = 25 / 24 := by norm_num
  have e₃ : (((162 : ℕ) : ℝ) / ((160 : ℕ) : ℝ)) = 81 / 80 := by norm_num
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [e₃] at h₃
  have hdecomp : Real.log 2 = 7 * Real.log (16 / 15) + 5 * Real.log (25 / 24)
      + 3 * Real.log (81 / 80) := by
    have h2 : (2 : ℝ) = (16 / 15) ^ 7 * ((25 / 24) ^ 5 * (81 / 80) ^ 3) := by norm_num
    rw [h2, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have key : Real.log 2 - ((7 * p₁ + 5 * p₂ + 3 * p₃ : ℕ) : ℝ) / Q
      = 7 * (Real.log (16 / 15) - (p₁ : ℝ) / Q) + 5 * (Real.log (25 / 24) - (p₂ : ℝ) / Q)
        + 3 * (Real.log (81 / 80) - (p₃ : ℝ) / Q) := by
    rw [hdecomp]; push_cast; ring
  rw [key]
  calc |7 * (Real.log (16 / 15) - (p₁ : ℝ) / Q) + 5 * (Real.log (25 / 24) - (p₂ : ℝ) / Q)
          + 3 * (Real.log (81 / 80) - (p₃ : ℝ) / Q)|
      ≤ |7 * (Real.log (16 / 15) - (p₁ : ℝ) / Q)|
          + |5 * (Real.log (25 / 24) - (p₂ : ℝ) / Q)|
          + |3 * (Real.log (81 / 80) - (p₃ : ℝ) / Q)| := abs_add_three _ _ _
    _ = 7 * |Real.log (16 / 15) - (p₁ : ℝ) / Q| + 5 * |Real.log (25 / 24) - (p₂ : ℝ) / Q|
          + 3 * |Real.log (81 / 80) - (p₃ : ℝ) / Q| := by
        rw [abs_mul, abs_mul, abs_mul]; norm_num
    _ ≤ 7 * (1 / D) + 5 * (1 / D) + 3 * (1 / D) := by gcongr
    _ = 15 / D := by ring
    _ ≤ 1 / E := by rw [div_le_div_iff₀ hDr hEr, one_mul]; exact_mod_cast hDE
end BSN
end
end CertificatePort165
theorem BSN.log2_near_15._proof_1 : Enclosure.Real.IsNear
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 32)) (@Nat.cast Real Real.instNatCast (nat_lit 30))))
  Bool.false (nat_lit 2325245277969667) (nat_lit 36028797018963968) (nat_lit 1) (nat_lit 15000000000000000) :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 31) (nat_lit 6) (nat_lit 5) (nat_lit 8520036043165426395)
  (nat_lit 36028797018963968) (nat_lit 15000000000000000) (nat_lit 2957113937425449) (nat_lit 945)
  (nat_lit 2325245277969667) (nat_lit 32) (nat_lit 30) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base5 (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 31)) (nat_lit 0) (nat_lit 5)
    (nat_lit 2957113937425449) (nat_lit 8520036043165426395) (nat_lit 945) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.log2_near_15._proof_2 : Enclosure.Real.IsNear
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 50)) (@Nat.cast Real Real.instNatCast (nat_lit 48))))
  Bool.false (nat_lit 1470767354479531) (nat_lit 36028797018963968) (nat_lit 1) (nat_lit 15000000000000000) :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 49) (nat_lit 5) (nat_lit 4) (nat_lit 31405119388272945)
  (nat_lit 36028797018963968) (nat_lit 15000000000000000) (nat_lit 4361095339944) (nat_lit 105)
  (nat_lit 1470767354479531) (nat_lit 50) (nat_lit 48) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base4 (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 49)) (nat_lit 0) (nat_lit 4)
    (nat_lit 4361095339944) (nat_lit 31405119388272945) (nat_lit 105) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.log2_near_15._proof_3 : Enclosure.Real.IsNear
  (Real.log
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 162)) (@Nat.cast Real Real.instNatCast (nat_lit 160))))
  Bool.false (nat_lit 447568451492036) (nat_lit 36028797018963968) (nat_lit 1) (nat_lit 15000000000000000) :=
BSN.log_dyadic_bound (nat_lit 1) (nat_lit 161) (nat_lit 4) (nat_lit 3) (nat_lit 1828708802020905)
  (nat_lit 36028797018963968) (nat_lit 15000000000000000) (nat_lit 23516982791) (nat_lit 15) (nat_lit 447568451492036)
  (nat_lit 162) (nat_lit 160) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base3 (BSN.artanhP (nat_lit 1)) (BSN.artanhQ (nat_lit 161)) (nat_lit 0) (nat_lit 3)
    (nat_lit 23516982791) (nat_lit 1828708802020905) (nat_lit 15) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.log2_near_15 : Enclosure.Real.IsNear
  (Real.log
    (@OfNat.ofNat Real (nat_lit 2)
      (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  Bool.false (nat_lit 24973259072661432) (nat_lit 36028797018963968)
  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
  (@OfNat.ofNat Nat (nat_lit 1000000000000000) (instOfNatNat (nat_lit 1000000000000000))) :=
BSN.log2_combine (nat_lit 2325245277969667) (nat_lit 1470767354479531) (nat_lit 447568451492036)
  (nat_lit 36028797018963968) (nat_lit 15000000000000000) (nat_lit 1000000000000000) (nat_lit 24973259072661432)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  BSN.log2_near_15._proof_1 BSN.log2_near_15._proof_2 BSN.log2_near_15._proof_3


section CertificatePort167
section
namespace BSN
open Enclosure
theorem sqrt_enclosure (N M a b Q : ℕ)
    (hM : Nat.ble 1 M) (hQ : Nat.ble 1 Q) (hab : Nat.ble a b)
    (hlo : ((a.pow 2).mul M).ble (N.mul (Q.pow 2)))
    (hhi : (N.mul (Q.pow 2)).ble ((b.pow 2).mul M)) :
    Real.IsNear (Real.sqrt ((N : ℝ) / M)) false (a.add b) (Nat.mul 2 Q) (b.sub
          a) (Nat.mul 2 Q) := by
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  simp only [Nat.ble_eq, Nat.mul_eq, Nat.pow_eq] at hab hlo hhi
  have hMr : (0 : ℝ) < M := pos_real_of_ble hM
  have hQr : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hQ2 : (0 : ℝ) < (Q : ℝ) ^ 2 := pow_pos hQr 2
  have hlo' : ((a : ℝ) / Q) ^ 2 ≤ (N : ℝ) / M := by
    rw [div_pow, div_le_div_iff₀ hQ2 hMr]; exact_mod_cast hlo
  have hhi' : (N : ℝ) / M ≤ ((b : ℝ) / Q) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hMr hQ2]; exact_mod_cast hhi
  have h1 : (a : ℝ) / Q ≤ Real.sqrt ((N : ℝ) / M) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (a : ℝ) / Q)]
    exact Real.sqrt_le_sqrt hlo'
  have h2 : Real.sqrt ((N : ℝ) / M) ≤ (b : ℝ) / Q := by
    calc Real.sqrt ((N : ℝ) / M)
        ≤ Real.sqrt (((b : ℝ) / Q) ^ 2) := Real.sqrt_le_sqrt hhi'
      _ = (b : ℝ) / Q := Real.sqrt_sq (by positivity)
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab
  have hc1 : ((a : ℝ) + b) / (2 * Q) - ((b : ℝ) - a) / (2 * Q) = (a : ℝ) / Q := by field_simp; ring
  have hc2 : ((a : ℝ) + b) / (2 * Q) + ((b : ℝ) - a) / (2 * Q) = (b : ℝ) / Q := by field_simp; ring
  rw [Real.IsNear, sfrac_false_div, abs_le]
  push_cast [hcast]
  exact ⟨by linarith [h1, hc1], by linarith [h2, hc2]⟩
end BSN
end
end CertificatePort167


section CertificatePort169
section
namespace BSN
open Enclosure
open Finset
private theorem prod_arctanEven (j : ℕ) :
    ∏ k ∈ range j, (4 * k + 5) = (∏ k ∈ range j, (4 * k + 1)) * (4 * j + 1) := by
  induction j with
  | zero => simp
  | succ n ih => rw [prod_range_succ, ih, prod_range_succ]; ring
private theorem prod_arctanOdd (j : ℕ) :
    (∏ k ∈ range j, (4 * k + 7)) * 3 = (∏ k ∈ range j, (4 * k + 3)) * (4 * j + 3) := by
  induction j with
  | zero => rfl
  | succ n ih => rw [prod_range_succ, prod_range_succ, ← ih]; ring
theorem arctan_sub_sum_le (x : ℝ) (M : ℕ) (hx : 0 ≤ x) (hx1 : x < 1) :
    |Real.arctan x - ∑ k ∈ range (2 * M), (-1) ^ k * x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)| ≤
      x ^ (4 * M + 1) / (4 * (M : ℝ) + 1) := by
  set f : ℕ → ℝ := fun n => x ^ (2 * n + 1) / (2 * (n : ℝ) + 1) with hf
  have hx2 : x ^ 2 < 1 := pow_lt_one₀ hx hx1 two_ne_zero
  have hanti : Antitone f := by
    intro a b hab
    simp only [hf]
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact div_le_div₀ (by positivity) (pow_le_pow_of_le_one hx hx1.le (by omega))
      (by positivity) (by linarith)
  have hsum : Summable f := by
    have hg : Summable (fun n : ℕ => x * (x ^ 2) ^ n) :=
      (summable_geometric_of_lt_one (sq_nonneg x) hx2).mul_left x
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hg
    simp only [hf]
    rw [show x * (x ^ 2) ^ n = x ^ (2 * n + 1) by rw [← pow_mul, ← pow_succ']]
    exact div_le_self (by positivity) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have harc : Real.arctan x = ∑' i, (-1) ^ i * f i := by
    rw [← (Real.hasSum_arctan (x := x)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hx]; exact hx1)).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hf]
    rw [mul_div_assoc]
    push_cast
    ring
  have hbound := alternating_series_error_bound f hanti hsum (2 * M)
  rw [← harc] at hbound
  have hsumeq : (∑ i ∈ range (2 * M), (-1) ^ i * f i)
      = ∑ k ∈ range (2 * M), (-1) ^ k * x ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf]
    rw [mul_div_assoc]
  have hfeq : f (2 * M) = x ^ (4 * M + 1) / (4 * (M : ℝ) + 1) := by
    simp only [hf]
    rw [show 2 * (2 * M) + 1 = 4 * M + 1 by ring]
    push_cast
    ring
  rw [hsumeq, hfeq] at hbound
  exact hbound
theorem arctan_recip (u v : ℕ) (hu : Nat.ble 1 u = true) (hv : Nat.ble 1 v = true) :
    Real.arctan ((u : ℝ) / v)
        = sfrac false (nat_lit 1) (nat_lit 2) * Real.pi - Real.arctan ((v : ℝ) / u) := by
  have huR : (0 : ℝ) < u := pos_real_of_ble hu
  have hvR : (0 : ℝ) < v := pos_real_of_ble hv
  have hinv : (u : ℝ) / v = ((v : ℝ) / u)⁻¹ := (inv_div _ _).symm
  rw [hinv, Real.arctan_inv_of_pos (div_pos hvR huR), sfrac_false_div]
  push_cast
  ring
theorem arctan_diag (u v : ℕ) (hu : Nat.ble 1 u = true) (huv : Nat.beq u v = true) :
    Real.arctan ((u : ℝ) / v) = sfrac false (nat_lit 1) (nat_lit 4) * Real.pi := by
  obtain rfl := Nat.eq_of_beq_eq_true huv
  have huR : (0 : ℝ) < u := pos_real_of_ble hu
  rw [div_self huR.ne', Real.arctan_one, sfrac_false_div]
  push_cast
  ring
theorem arctanEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((arctanEvenP u k : ℚ) / (arctanEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 1 : ℕ) : ℚ)) := by
  rw [← Finset.range_eq_Ico]
  simp only [arctanEvenP, arctanEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ k ∈ Finset.range (i + 1), ((u ^ 4 * (4 * k + 1) : ℕ) : ℚ))
      = (u : ℚ) ^ (4 * (i + 1)) * ∏ k ∈ Finset.range (i + 1), ((4 * k + 1 : ℕ) : ℚ) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hden : (∏ k ∈ Finset.range (i + 1), ((v ^ 4 * (4 * k + 5) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), ((4 * k + 1 : ℕ) : ℚ))
        * (4 * (i + 1) + 1)) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
    congr 1
    exact_mod_cast prod_arctanEven (i + 1)
  rw [hnum, hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hp1 : (∏ k ∈ Finset.range (i + 1), ((4 * k + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp
theorem arctanEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (arctanEvenP u) (arctanEvenQ v) 0 (M - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 1) / ((v : ℚ) ^ (4 * j + 1) * ((4 * j + 1 : ℕ) : ℚ)) := by
  have hqne : ∀ i, arctanEvenQ v i ≠ 0 := by
    intro i; simp only [arctanEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb :=
        binarySplit_nonzero (p := arctanEvenP u) (q := arctanEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := arctanEvenP u) (q := arctanEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => arctanEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 1) / ((v : ℚ) ^ (4 * (i + 1) + 1) * ((4 * (i + 1) + 1 : ℕ) : ℚ))
        = (u : ℚ) / v *
          ((u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 1 : ℕ) : ℚ))) := by
    intro i _
    rw [pow_succ' (u : ℚ), pow_succ' (v : ℚ)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.cast_one, mul_one]
  field_simp
  ring
theorem arctanOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((arctanOddP u k : ℚ) / (arctanOddQ v k))
      = 3 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 3 : ℕ) : ℚ)) := by
  rw [← Finset.range_eq_Ico]
  simp only [arctanOddP, arctanOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ k ∈ Finset.range (i + 1), ((u ^ 4 * (4 * k + 3) : ℕ) : ℚ))
      = (u : ℚ) ^ (4 * (i + 1)) * ∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hden : (∏ k ∈ Finset.range (i + 1), ((v ^ 4 * (4 * k + 7) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ))
        * (4 * (i + 1) + 3)) / 3 := by
    have keyN : (∏ k ∈ Finset.range (i + 1), (v ^ 4 * (4 * k + 7))) * 3
        = v ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), (4 * k + 3)) * (4 * (i + 1) + 3)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_arctanOdd]
    have keyQ : (∏ k ∈ Finset.range (i + 1), ((v ^ 4 * (4 * k + 7) : ℕ) : ℚ)) * 3
        = (v : ℚ) ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ))
          * (4 * (i + 1) + 3)) := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)]
  rw [hnum, hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hp1 : (∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp
theorem arctanOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (arctanOddP u) (arctanOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 3 * (Q + T) / (3 * v ^ 3 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 3) / ((v : ℚ) ^ (4 * j + 3) * ((4 * j + 3 : ℕ) : ℚ)) := by
  have hqne : ∀ i, arctanOddQ v i ≠ 0 := by
    intro i; simp only [arctanOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb :=
        binarySplit_nonzero (p := arctanOddP u) (q := arctanOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := arctanOddP u) (q := arctanOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => arctanOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 3) / ((v : ℚ) ^ (4 * (i + 1) + 3) * ((4 * (i + 1) + 3 : ℕ) : ℚ))
        = (u : ℚ) ^ 3 / (3 * v ^ 3) *
          (3 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 3 : ℕ) : ℚ))) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 3, pow_add (v : ℚ) (4 * (i + 1)) 3]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add]
  push_cast
  field_simp
  ring
theorem arctan_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (huv : u.blt v) (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hM : Nat.ble 1 M) (hMm : (Mm.succ).beq M)
    (heven : binarySplit (arctanEvenP u) (arctanEvenQ v) 0 Mm = (Te, Qe, Pe))
    (hodd : binarySplit (arctanOddP u) (arctanOddQ v) 0 Mm = (To, Qo, Po))
    (htail : ((u.pow ((Nat.mul 4 M).succ)).mul (Nat.mul 2 D)).ble
      ((v.pow ((Nat.mul 4 M).succ)).mul ((Nat.mul 4 M).succ)))
    (hr1 : (((numPos neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.arctan ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQeN : 0 < Qe := pos_of_ble hQe
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := arctanEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := arctanOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : (u : ℚ) * (Qe + Te) / (v * Qe) - (u : ℚ) ^ 3 * (Qo + To) / (3 * v ^ 3 * Qo)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℚ) / v) ^ (2 * i + 1) / (2 * (i : ℚ) + 1) := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) + 1 = 4 * j + 1 := by ring
    have e2 : 2 * (2 * j + 1) + 1 = 4 * j + 3 := by ring
    rw [e1, e2, s1, s2]
    push_cast
    rw [div_pow, div_pow]
    have d1 : (2 : ℚ) * (2 * (j : ℚ)) + 1 = 4 * (j : ℚ) + 1 := by ring
    have d2 : (2 : ℚ) * (2 * (j : ℚ) + 1) + 1 = 4 * (j : ℚ) + 3 := by ring
    rw [d1, d2]
    field_simp
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at huv htail hQ hr1 hr2
  set De := v * Qe with hDe_def
  set Do := 3 * v ^ 3 * Qo with hDo_def
  set Ne := u * (Qe + Te) with hNe_def
  set No := u ^ 3 * (Qo + To) with hNo_def
  have hDeR : (De : ℝ) = (v : ℝ) * Qe := by rw [hDe_def]; push_cast; ring
  have hDoR : (Do : ℝ) = 3 * (v : ℝ) ^ 3 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((De : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * De) * Q := by
    have h : (mp : ℤ) * ((De : ℤ) * Do) + (No : ℤ) * De * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((De : ℤ) * Do) = (mp : ℤ) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q < (m + 1) * ((De : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do)
        < (mp + 1) * ((De : ℤ) * Do) + (No : ℤ) * De * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((De : ℤ) * Do)
        = (mp + 1) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hDe0 : (0 : ℝ) < De := by rw [hDeR]; positivity
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / De - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDe_def, hNo_def, hDo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 1 := by rw [div_lt_one hvr]; exact_mod_cast huv
  have harem := arctan_sub_sum_le ((u : ℝ) / v) M hxnn hxlt
  rw [← hvalR] at harem
  have hatail : |Real.arctan ((u : ℝ) / v) - ((Ne : ℝ) / De - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine harem.trans ?_
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have e : (4 * (M : ℝ) + 1) = ((4 * M + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    exact_mod_cast htail
  have hr1' : (m : ℝ) * ((De : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * De) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * De) * Q < ((m : ℝ) + 1) * ((De : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.arctan ((u : ℝ) / v)) (Ne : ℝ) (De : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hatail hr1' hr2' hDe0 hDo0 hDr hQr hQ
theorem arctan_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (huv : u.blt v) (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hM : Nat.ble 1 M) (hMm : (Mm.succ).beq M)
    (heven : binarySplit (arctanEvenP u) (arctanEvenQ v) 0 Mm = (Te, Qe, Pe))
    (hodd : binarySplit (arctanOddP u) (arctanOddQ v) 0 Mm = (To, Qo, Po))
    (htail : ((u.pow ((Nat.mul 4 M).succ)).mul (Nat.mul 2 D)).ble
      ((v.pow ((Nat.mul 4 M).succ)).mul ((Nat.mul 4 M).succ)))
    (hr1 : ((cn.mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      (((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q)).blt
      (((cn.succ).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.arctan ((u : ℝ) / v)) false cn Q 1 D := by
  refine arctan_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn huv hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega
theorem arctan_dyadic_bound_t (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (huv : u.blt v) (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hM : Nat.ble 1 M) (hMm : (Mm.succ).beq M)
    (heven : binarySplit (arctanEvenP u) (arctanEvenQ v) 0 Mm = (Te, Qe, Pe))
    (hodd : binarySplit (arctanOddP u) (arctanOddQ v) 0 Mm = (To, Qo, Po))
    (htail : ((u.pow ((Nat.mul 4 M).succ)).mul (Nat.mul 2 D)).ble
      ((v.pow ((Nat.mul 4 M).succ)).mul ((Nat.mul 4 M).succ)))
    (hr1 : ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))).blt
      (((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.arctan ((u : ℝ) / v)) true cn Q 1 D := by
  refine arctan_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po true cn huv hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
      Nat.zero_mul, Nat.zero_add] at hr1 ⊢
    omega
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.blt_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.one_mul] at hr2 ⊢
    omega
end BSN
end
end CertificatePort169


section CertificatePort170
section
namespace BSN
open Enclosure
theorem pi_combine (c₁ c₂ Q D E P : ℕ)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hDE : (Nat.mul 20 E).ble D)
    (hP : (P.add (Nat.mul 4 c₂)).beq (Nat.mul 16 c₁))
    (h₁ : Real.IsNear (Real.arctan (((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))) false c₁ Q 1 D)
    (h₂ : Real.IsNear (Real.arctan (((1 : ℕ) : ℝ) / ((239 : ℕ) : ℝ))) false c₂ Q 1 D) :
    Real.IsNear Real.pi false P Q 1 E := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at h₁ h₂ ⊢
  simp only [Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hDE hP
  have harg5 : ((1 : ℝ) / ((5 : ℕ) : ℝ)) = 5⁻¹ := by norm_num
  have harg239 : ((1 : ℝ) / ((239 : ℕ) : ℝ)) = 239⁻¹ := by norm_num
  rw [harg5] at h₁
  rw [harg239] at h₂
  have hmachin : Real.pi = 16 * Real.arctan 5⁻¹ - 4 * Real.arctan 239⁻¹ := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    linarith
  have hPr : (P : ℝ) = 16 * c₁ - 4 * c₂ := by
    have h : (P : ℝ) + 4 * c₂ = 16 * c₁ := by exact_mod_cast hP
    linarith
  have key : Real.pi - (P : ℝ) / Q
      = 16 * (Real.arctan 5⁻¹ - (c₁ : ℝ) / Q)
        - 4 * (Real.arctan 239⁻¹ - (c₂ : ℝ) / Q) := by
    rw [hmachin, hPr]; ring
  rw [key]
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  calc |16 * (Real.arctan 5⁻¹ - (c₁ : ℝ) / Q)
          - 4 * (Real.arctan 239⁻¹ - (c₂ : ℝ) / Q)|
      ≤ |16 * (Real.arctan 5⁻¹ - (c₁ : ℝ) / Q)|
          + |4 * (Real.arctan 239⁻¹ - (c₂ : ℝ) / Q)| := by
        exact abs_sub _ _
    _ = 16 * |Real.arctan 5⁻¹ - (c₁ : ℝ) / Q|
          + 4 * |Real.arctan 239⁻¹ - (c₂ : ℝ) / Q| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ 16 * (1 / D) + 4 * (1 / D) := by gcongr
    _ = 20 / D := by ring
    _ ≤ 1 / E := by rw [div_le_div_iff₀ hDr hEr, one_mul]; exact_mod_cast hDE
end BSN
end
end CertificatePort170
theorem BSN.pi_near_15._proof_1 : Enclosure.Real.IsNear
  (Real.arctan
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 1)) (@Nat.cast Real Real.instNatCast (nat_lit 5))))
  Bool.false (nat_lit 14223849116552214) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 20000000000000000) :=
BSN.arctan_dyadic_bound_f (nat_lit 1) (nat_lit 5) (nat_lit 6) (nat_lit 5) (nat_lit 72057594037927936)
  (nat_lit 20000000000000000) (nat_lit 6379115169797445) (nat_lit 19917011260986328125) (nat_lit 9945)
  (nat_lit 33040696220578335) (nat_lit 48135280609130859375) (nat_lit 65835) (nat_lit 14223849116552214)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base5 (BSN.arctanEvenP (nat_lit 1)) (BSN.arctanEvenQ (nat_lit 5)) (nat_lit 0) (nat_lit 5)
    (nat_lit 6379115169797445) (nat_lit 19917011260986328125) (nat_lit 9945) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@BSN.binarySplit_of_base5 (BSN.arctanOddP (nat_lit 1)) (BSN.arctanOddQ (nat_lit 5)) (nat_lit 0) (nat_lit 5)
    (nat_lit 33040696220578335) (nat_lit 48135280609130859375) (nat_lit 65835) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.pi_near_15._proof_2 : Enclosure.Real.IsNear
  (Real.arctan
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
      (@Nat.cast Real Real.instNatCast (nat_lit 1)) (@Nat.cast Real Real.instNatCast (nat_lit 239))))
  Bool.false (nat_lit 301494449981336) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 20000000000000000) :=
BSN.arctan_dyadic_bound_f (nat_lit 1) (nat_lit 239) (nat_lit 2) (nat_lit 1) (nat_lit 72057594037927936)
  (nat_lit 20000000000000000) (nat_lit 1) (nat_lit 16314043205) (nat_lit 1) (nat_lit 3) (nat_lit 22839660487)
  (nat_lit 3) (nat_lit 301494449981336) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@BSN.binarySplit_of_base (BSN.arctanEvenP (nat_lit 1)) (BSN.arctanEvenQ (nat_lit 239)) (nat_lit 0) (nat_lit 1)
    (nat_lit 1) (nat_lit 16314043205) (nat_lit 1) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@BSN.binarySplit_of_base (BSN.arctanOddP (nat_lit 1)) (BSN.arctanOddQ (nat_lit 239)) (nat_lit 0) (nat_lit 1)
    (nat_lit 3) (nat_lit 22839660487) (nat_lit 3) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
    (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
theorem BSN.pi_near_15 : Enclosure.Real.IsNear Real.pi Bool.false (nat_lit 226375608064910080)
  (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) :=
BSN.pi_combine (nat_lit 14223849116552214) (nat_lit 301494449981336) (nat_lit 72057594037927936)
  (nat_lit 20000000000000000) (nat_lit 1000000000000000) (nat_lit 226375608064910080) (@Eq.refl Bool Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) BSN.pi_near_15._proof_1
  BSN.pi_near_15._proof_2


section CertificatePort173
section
namespace BSN
open Enclosure
theorem abs_exp_sub_exp_le_mul (r rc M : ℝ) (hr : Real.exp r ≤ M) (hrc : Real.exp rc ≤ M) :
    |Real.exp r - Real.exp rc| ≤ M * |r - rc| := by
  rcases le_total rc r with h | h
  · have hge : Real.exp rc ≤ Real.exp r := Real.exp_le_exp.mpr h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith : (0 : ℝ) ≤ r - rc)]
    have key : Real.exp r - Real.exp rc ≤ Real.exp r * (r - rc) := by
      have h1 := Real.add_one_le_exp (rc - r)
      have h2 : Real.exp r * (rc - r + 1) ≤ Real.exp r * Real.exp (rc - r) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos r))
      rw [← Real.exp_add] at h2
      have e : r + (rc - r) = rc := by ring
      rw [e] at h2
      nlinarith [Real.exp_pos r]
    calc Real.exp r - Real.exp rc ≤ Real.exp r * (r - rc) := key
      _ ≤ M * (r - rc) := mul_le_mul_of_nonneg_right hr (by linarith)
  · have hge : Real.exp r ≤ Real.exp rc := Real.exp_le_exp.mpr h
    rw [abs_sub_comm (Real.exp r) (Real.exp rc), abs_sub_comm r rc,
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith : (0 : ℝ) ≤ rc - r)]
    have key : Real.exp rc - Real.exp r ≤ Real.exp rc * (rc - r) := by
      have h1 := Real.add_one_le_exp (r - rc)
      have h2 : Real.exp rc * (r - rc + 1) ≤ Real.exp rc * Real.exp (r - rc) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos rc))
      rw [← Real.exp_add] at h2
      have e : rc + (r - rc) = r := by ring
      rw [e] at h2
      nlinarith [Real.exp_pos rc]
    calc Real.exp rc - Real.exp r ≤ Real.exp rc * (rc - r) := key
      _ ≤ M * (rc - r) := mul_le_mul_of_nonneg_right hrc (by linarith)
theorem exp_reduce_core (x r rc val M B inner Dinv : ℝ) (k : ℕ) (hM : 0 ≤ M)
    (hk : Real.exp x = (2 : ℝ) ^ k * Real.exp r)
    (hlip : |Real.exp r - Real.exp rc| ≤ M * |r - rc|)
    (hB : |r - rc| ≤ B)
    (hinner : |Real.exp rc - val| ≤ inner)
    (htot : (2 : ℝ) ^ k * (M * B + inner) ≤ Dinv) :
    |Real.exp x - (2 : ℝ) ^ k * val| ≤ Dinv := by
  have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h1 : |Real.exp x - (2 : ℝ) ^ k * val| = (2 : ℝ) ^ k * |Real.exp r - val| := by
    rw [hk, ← mul_sub, abs_mul, abs_of_pos hpk]
  rw [h1]
  have h2 : |Real.exp r - val| ≤ M * B + inner :=
    calc |Real.exp r - val|
        ≤ |Real.exp r - Real.exp rc| + |Real.exp rc - val| := abs_sub_le _ _ _
      _ ≤ M * B + inner := add_le_add (hlip.trans (mul_le_mul_of_nonneg_left hB hM)) hinner
  calc (2 : ℝ) ^ k * |Real.exp r - val|
      ≤ (2 : ℝ) ^ k * (M * B + inner) := mul_le_mul_of_nonneg_left h2 (le_of_lt hpk)
    _ ≤ Dinv := htot
theorem exp_scale (X k : ℕ) :
    Real.exp X = (2 : ℝ) ^ k * Real.exp ((X : ℝ) - k * Real.log 2) := by
  have h2 : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← h2, ← Real.exp_add]
  congr 1
  ring
theorem exp_reduce_arg_pos (X Lp LQ k u : ℕ)
    (hlink : (X.mul LQ).beq (u.add (k.mul Lp))) (hLQ : Nat.ble 1 LQ) :
    (u : ℝ) / (LQ : ℝ) = (X : ℝ) - (k : ℝ) * ((Lp : ℝ) / (LQ : ℝ)) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hlink
  have hLQr : (0 : ℝ) < LQ := pos_real_of_ble hLQ
  have key : (X : ℝ) * LQ = (u : ℝ) + k * Lp := by exact_mod_cast hlink
  field_simp
  linarith [key]
theorem exp_reduce_step (X k E Lp LQ Dp D u vp vQ Pf : ℕ)
    (hPf : Pf.beq ((Nat.pow 2 k).mul vp))
    (hL : Real.IsNear (Real.log 2) false Lp LQ 1 E)
    (hlink : (X.mul LQ).beq (u.add (k.mul Lp)))
    (hinner : Real.IsNear (Real.exp ((u : ℝ) / (LQ : ℝ))) false vp vQ 1 Dp)
    (hLQ : Nat.ble 1 LQ) (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (hle1 : ((u.mul E).add (k.mul LQ)).ble (LQ.mul E))
    (htot : (((Nat.pow 2 k).mul (((Nat.mul 3 k).mul Dp).add E)).mul D).ble (E.mul Dp)) :
    Real.IsNear (Real.exp ((X : ℕ) : ℝ)) false Pf vQ 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hL hinner ⊢
  have hLQbt := hLQ
  simp only [Nat.beq_eq, Nat.mul_eq, Nat.pow_eq] at hPf
  set val : ℝ := (vp : ℝ) / vQ with hvaldef
  have hPfval : (Pf : ℝ) / (vQ : ℝ) = (2 : ℝ) ^ k * val := by
    rw [hvaldef, hPf]; push_cast; ring
  rw [hPfval]
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq] at hle1 htot
  have hLQr : (0 : ℝ) < LQ := pos_real_of_ble hLQ
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have hDpr : (0 : ℝ) < Dp := pos_real_of_ble hDp
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  set L : ℝ := (Lp : ℝ) / LQ with hLdef
  set rc : ℝ := (u : ℝ) / LQ with hrcdef
  set r : ℝ := (X : ℝ) - k * Real.log 2 with hrdef
  have hrc : rc = (X : ℝ) - k * L := by
    rw [hrcdef, hLdef]; exact exp_reduce_arg_pos X Lp LQ k u hlink hLQbt
  have hknn : (0 : ℝ) ≤ (k : ℝ) / E := by positivity
  have hB : |r - rc| ≤ (k : ℝ) / E := by
    have e : r - rc = -((k : ℝ) * (Real.log 2 - L)) := by rw [hrdef, hrc]; ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    calc (k : ℝ) * |Real.log 2 - L| ≤ (k : ℝ) * (1 / E) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = (k : ℝ) / E := by ring
  have hrcB1 : rc + (k : ℝ) / E ≤ 1 := by
    rw [hrcdef, div_add_div _ _ (ne_of_gt hLQr) (ne_of_gt hEr), div_le_one (by positivity)]
    have hle1R : ((u * E + k * LQ : ℕ) : ℝ) ≤ ((LQ * E : ℕ) : ℝ) := by exact_mod_cast hle1
    push_cast at hle1R ⊢
    nlinarith [hle1R]
  have hrc1 : rc ≤ 1 := by linarith [hrcB1, hknn]
  have hr1 : r ≤ 1 := by
    have h1 : r - rc ≤ |r - rc| := le_abs_self _
    linarith [hB, hrcB1]
  have hexp3 : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  have hr3 : Real.exp r ≤ 3 := le_trans (Real.exp_le_exp.mpr hr1) hexp3
  have hrc3 : Real.exp rc ≤ 3 := le_trans (Real.exp_le_exp.mpr hrc1) hexp3
  have hlip := abs_exp_sub_exp_le_mul r rc 3 hr3 hrc3
  have htotR : (2 : ℝ) ^ k * (3 * ((k : ℝ) / E) + 1 / Dp) ≤ 1 / D := by
    have hc : (2 : ℝ) ^ k * (3 * k * Dp + E) * D ≤ E * Dp := by exact_mod_cast htot
    have e : (2 : ℝ) ^ k * (3 * ((k : ℝ) / E) + 1 / Dp)
        = (2 : ℝ) ^ k * (3 * k * Dp + E) / (E * Dp) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) hDr, one_mul]
    nlinarith [hc]
  exact exp_reduce_core X r rc val 3 ((k : ℝ) / E) (1 / Dp) (1 / D) k (by norm_num)
    (exp_scale X k) hlip hB hinner htotR
end BSN
end
end CertificatePort173
section Reduced182
section
namespace Zeta.Certificates.Gram
open Zeta.Certificates Real Set
abbrev gp1 : GramPoint where
  idx := 655
  fst := 1009.14258
  snd := 1009.14261
  fst_le_snd := by norm_num
  fstCutoff := 0
  fstBernoulli := 2
  sndCutoff := 0
  sndBernoulli := 2
end Zeta.Certificates.Gram
end
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace BSN
theorem sqrt_natCast_div_one (n : ℕ) :
    Real.sqrt (n : ℝ) = Real.sqrt ((n : ℝ) / ((nat_lit 1 : ℕ) : ℝ)) := by
  rw [show ((nat_lit 1 : ℕ) : ℝ) = 1 from Nat.cast_one, div_one]
end BSN
namespace Zeta.Certificates.Gram
open Zeta.Certificates Real Set
abbrev z1_1 : ZIntervalRS where
  fst := 1009.14400
  snd := 1010.37800
  fst_le_snd := by norm_num
end Zeta.Certificates.Gram
end Reduced182

namespace RHHeight1000.GramZero661
noncomputable def p3 :=
@Mathlib.Meta.NormNum.isNat_pow.{0} Nat Nat.instSemiring
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))))
  (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5 10 5 100000

noncomputable def p4 :=
p3
  (@Eq.refl.{1} (Nat → Nat → Nat)
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))))
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Nat Nat.instAddMonoidWithOne
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 10
    (@Eq.refl.{1} Nat (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10))))
  (Mathlib.Meta.NormNum.IsNat.raw_refl 5)
  (@Mathlib.Meta.NormNum.IsNatPowT.run 10 5 100000
    (@Mathlib.Meta.NormNum.IsNatPowT.trans 10 2 100
      (@Eq.{1} Nat (Nat.pow 10 1) 10) 5 100000
      (@Mathlib.Meta.NormNum.IsNatPowT.bit0 10 1 10)
      (@Mathlib.Meta.NormNum.IsNatPowT.bit1 10 2 100)))

noncomputable def p9 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  NNRat.instCharZero
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)
  99999

noncomputable def p10 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)
  100000

noncomputable def p11 :=
p10
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    100000 100000 (Mathlib.Meta.NormNum.IsNat.raw_refl 100000))

noncomputable def p259 :=
@Mathlib.Meta.NormNum.isRat_le_true.{0} Real
  (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField)) Real.linearOrder
  Real.instIsStrictOrderedRing
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
    true 5)
  (Int.ofNat 1016561) (Int.ofNat 1017793) 1000

noncomputable def p260 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 101656100
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5))
  1016561 1000

noncomputable def p261 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101656100 101656100 1016561
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5)
  100000 1000 (Mathlib.Meta.NormNum.IsNat.raw_refl 101656100)

noncomputable def p262 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101656100)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p263 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
    (@instHMul.{0} NNRat
      (@Distrib.toMul.{0} NNRat
        (@instDistribOfSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101656100)
  (@Inv.inv.{0} NNRat
    (@InvOneClass.toInv.{0} NNRat
      (@DivInvOneMonoid.toInvOneClass.{0} NNRat
        (@DivisionMonoid.toDivInvOneMonoid.{0} NNRat
          (@GroupWithZero.toDivisionMonoid.{0} NNRat
            (@DivisionSemiring.toGroupWithZero.{0} NNRat
              (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    (@Nat.cast.{0} NNRat
      (@AddMonoidWithOne.toNatCast.{0} NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
            (@Semiring.toNonAssocSemiring.{0} NNRat
              (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
      100000))

noncomputable def p264 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101656100)
  101656100

noncomputable def p265 :=
p264
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    101656100 101656100 (Mathlib.Meta.NormNum.IsNat.raw_refl 101656100))

noncomputable def p266 :=
@p263 101656100 1 1016561 1 100000 1000
  100
  (@Eq.refl.{1} (NNRat → NNRat → NNRat)
    (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
      (@instHMul.{0} NNRat
        (@Distrib.toMul.{0} NNRat
          (@instDistribOfSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))))
  p265 (@p9 1 p11)

noncomputable def p267 :=
@p259 1000
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat.{0} Real
    (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    1016561 1000
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101656100
      5 1016561 1000
      (p260
        (p261 p4
          (@p262 1016561 1000
            (p266 (@Eq.refl.{1} Nat (Nat.mul 101656100 1))
              (@Eq.refl.{1} Nat 100000)))))))

noncomputable def p268 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 101779300
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5))
  1017793 1000

noncomputable def p269 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101779300 101779300 1017793
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 5)
  100000 1000 (Mathlib.Meta.NormNum.IsNat.raw_refl 101779300)

noncomputable def p270 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101779300)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100000)

noncomputable def p271 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
    (@instHMul.{0} NNRat
      (@Distrib.toMul.{0} NNRat
        (@instDistribOfSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101779300)
  (@Inv.inv.{0} NNRat
    (@InvOneClass.toInv.{0} NNRat
      (@DivInvOneMonoid.toInvOneClass.{0} NNRat
        (@DivisionMonoid.toDivInvOneMonoid.{0} NNRat
          (@GroupWithZero.toDivisionMonoid.{0} NNRat
            (@DivisionSemiring.toGroupWithZero.{0} NNRat
              (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    (@Nat.cast.{0} NNRat
      (@AddMonoidWithOne.toNatCast.{0} NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
            (@Semiring.toNonAssocSemiring.{0} NNRat
              (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
      100000))

noncomputable def p272 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    101779300)
  101779300

noncomputable def p273 :=
p272
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    101779300 101779300 (Mathlib.Meta.NormNum.IsNat.raw_refl 101779300))

noncomputable def p274 :=
@p271 101779300 1 1017793 1 100000 1000
  100
  (@Eq.refl.{1} (NNRat → NNRat → NNRat)
    (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
      (@instHMul.{0} NNRat
        (@Distrib.toMul.{0} NNRat
          (@instDistribOfSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))))
  p273 (@p9 1 p11)

noncomputable def p275 :=
p267
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat.{0} Real
    (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    1017793 1000
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101779300
      5 1017793 1000
      (p268
        (p269 p4
          (@p270 1017793 1000
            (p274 (@Eq.refl.{1} Nat (Nat.mul 101779300 1))
              (@Eq.refl.{1} Nat 100000)))))))

theorem d42 : @LE.le.{0} Real
  (@Preorder.toLE.{0} Real
    (@PartialOrder.toPreorder.{0} Real
      (@SemilatticeInf.toPartialOrder.{0} Real
        (@Lattice.toSemilatticeInf.{0} Real
          (@DistribLattice.toLattice.{0} Real (@instDistribLatticeOfLinearOrder.{0} Real Real.linearOrder))))))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
    true 5) :=
p275 (Eq.refl true)

noncomputable def d43 :=
@NonemptyInterval.mk.{0} Real Real.instLE
  (@Prod.mk.{0, 0} Real Real
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  d42

noncomputable def p497 :=
nat_lit 26986075409044028275299783

noncomputable def p499 :=
nat_lit 26986075409044045455168967

noncomputable def p501 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) Real.pi 2 1
  0 1 226375608064910080 72057594037927936

noncomputable def p507 :=
nat_lit 53972150818088056550599566

noncomputable def p520 :=
nat_lit 53972150818088090910337934

noncomputable def p593 :=
nat_lit 8589934592000000000000000

noncomputable def p596 :=
nat_lit 17179869184000000000000000

noncomputable def p598 :=
nat_lit 18396140817044028275299783

noncomputable def p599 :=
nat_lit 35576010001044028275299783

noncomputable def p605 :=
nat_lit
  583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def p606 :=
nat_lit
  5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def p607 :=
nat_lit
  2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def p612 :=
@BSN.binarySplit_of_base9 (BSN.artanhP p598) (BSN.artanhQ p599) 0
  9 p605 p606 p607 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p617 :=
nat_lit 18396140817044045455168967

noncomputable def p618 :=
nat_lit 35576010001044045455168967

noncomputable def p624 :=
nat_lit
  583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def p625 :=
nat_lit
  5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def p626 :=
nat_lit
  2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def p631 :=
@BSN.binarySplit_of_base9 (BSN.artanhP p617) (BSN.artanhQ p618) 0
  9 p624 p625 p626 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p803 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 2) Real.pi 1 2
  0 1 226375608064910080 72057594037927936

noncomputable def p976 :=
nat_lit 309485009821345068724781056

noncomputable def p982 :=
nat_lit 154742504910672534362390528

noncomputable def p1059 :=
nat_lit 691463075802508163054686763366652189853178875

noncomputable def p1061 :=
nat_lit 2787593149816327892691964784081045188247552

noncomputable def p1062 :=
nat_lit 2184744797947834540264818678394244808492865883128339

noncomputable def p1063 :=
nat_lit 9223372036854775808000000000000000000000000000000000000000000000

noncomputable def p1068 :=
nat_lit 781950621441006189802102638025

noncomputable def p1070 :=
nat_lit 19807040628566084398385987584

noncomputable def p1071 :=
nat_lit 26986075409044041160201671

noncomputable def p1072 :=
nat_lit 1073741824000000000000000000000000000000

noncomputable def p2042 :=
@Enclosure.Real.IsNear.recentre' (Real.log Real.pi) false 78665238759 68719476736 2
  68719476736 78665238759 68719476736 1 34359738368

noncomputable def p2043 :=
@BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1
  1000000000000000 p497 p593 p499 p593
  157330477519 137438953472

noncomputable def p2044 :=
@p2043 1 52800000000 157330477519 137438953472 1
  52800000000 78665238759 68719476736 2 68719476736 BSN.pi_near_15

noncomputable def p2045 :=
BSN.logfrac_isNear p507 p596 1 p497
  p593 157330477519 137438953472 52800000000
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p2046 :=
nat_lit
  28112249726568391589047516573961016100230695266595138796645898844068455765826150661746425623361233424082198271039924780088271379132689863069221204238560183629201607644021685675098964741933636681146646085450281554642234567670273398510595608388401361582887942310446147737587363843978980100496524524149645324535726971841246491625617094543039703127568346472270082785977497346976624911418331836820278316086423086221698714772627386990029610668989360984838503376478261856551986321583831120245376241683570873990542024084976461912564043669928266913234808138444564697009788556422071443556665104485951316241205417724454884855648838586880998728494388445042826471386528295148565814403457608975325084421742121394650813826944853845535730717079638892361862488354697476516361002681016858732631075345788689669322864575479543781416716836529222919811305834432880382494042916396369004063385142542944123203596085267144355012182693848192467538993321594614691095850768794488026694041566360767047538370072844536145465625

noncomputable def p2047 :=
nat_lit
  3004852088952768845920618744553278527204692828375153584392003179441110915259710236217584603096118328104680832169483210561589325374912009409850222660711266215775790384571551429890480172556385640686680474032161112410464266713994866393778433661006945913182018947418487320399615641795552072647902100183574245260251043675061202707045470229404510257054669582810821424393350840091252955407241565764109916492793914631945586814885644558726210255466565212322672666804789077217737419201108469876131774340314495933866107672625386841546065679278379967588836860231971112056212051701786409418893940900332221197280978896706663592437230896317804020812894593837818667147274729545133224953997584838639067106369936658157631771313490070272044892491227518160759585764692109951245393652651596149425400941367486350589239615552351659509511773702708987671624772355194695219991156759969388230106513516518404759588330543927959707500174897764780405058368784771513978993918218553854643944162112070721962901566067768789252375

noncomputable def p2048 :=
nat_lit
  9407440773224172681608700800935793010623091823451060729311335758097884212674519651449525711559811298259706715802174741819386929788979265886490710442570602643258333481940675986925031166385219002468759325425871585023540930321333085653246210767457816937546151967387697762867366118158349272438706119700156825534863826747864802135549084951496534996548721807020772886548043755609972182010967717941572151546388230735108166873457723560431535436103604158287676565659967228712317028040615680390038739538457534455011980724218179173567216927517217433242876173265519116175068208539039413233240521992767665208397431498233209472829716964273590741575120542767682365189084066271996528146206849186493650578605643960924800580523089630169611245121301536400385494384892405066700887668265289347023652942104761440574085006181174048868346007483392864104239217621438509276641851575397778814711237716004915415172882101120782235589971491833178320649134371141612801731087615746635195857438501796739603490909375

noncomputable def p2049 :=
BSN.log_dyadic_bound p598 p599 20 19 p2046
  137438953472 52800000000 p2047 p2048 157330477519
  p507

noncomputable def p2050 :=
p2049 p596 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2051 :=
nat_lit
  1650304246484168217822250182153121331528997195645019090501845025211358811991300272013840033653941454605528374539027499491830801323036315192028455074639283191170947847934211591621904664405572663089205635245616304066484890368301004968418777530432615600724329191377693102551381108985567302017523413605606252081189558178457495658341856826359713554530205476390639506094074087616532907216516745870115563785087886264394307092243534322734607832361293776836022706605203930519204454144456486606258340798134197185010577832970498613095940

noncomputable def p2052 :=
nat_lit
  5152330118349893532259284459583441780070716451433832193251783468388459752855557028796565709036724336156942418379726226536905679903318407859561502395299762704250796677090820257953400678050280204651252244620975294524887177620491285879357122587745210671568814207213541227476164641822276200714342956225642487758614688645347237103590014901463894467904735606994415858329142192847700339914366789219396665272142432155239596089419432340959870316544123271571567481985497208253366969047308607720961663960687437176962547335096733341405875

noncomputable def p2053 :=
@BSN.binarySplit_rec (BSN.artanhP p598) (BSN.artanhQ p599) 0 19
  9 p605 p606 p607 p2051
  p2052

noncomputable def p2054 :=
nat_lit
  4689023516057975750882481307719643750220885092944758800108430431904660080873916826509933801555745586016295889243450194487593450330365959443500829841449240072253514364015516073125797605721974605933992092683371351636968293202725646728829735271589466369799474280105732552195876824582748140145170610365699210256726576095533214614582552020302258805649890312180713120860798546024198346613187419404047036399015423078840528663362027526034732270609631732327097780371703942801984829125820150075562715414744105544599149690602223375

noncomputable def p2055 :=
@BSN.binarySplit_of_base10 (BSN.artanhP p598) (BSN.artanhQ p599) 9
  19 p2051 p2052 p2054 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2056 :=
@p2053 p2054 p2047 p2046 p2048
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (p612 (Eq.refl true))
  (p2055 (Eq.refl true))

noncomputable def p2057 :=
p2044 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (BSN.isNear_log_sfrac p497 p593 157330477519 137438953472
    1 52800000000 false
    (p2045
      (p2050 p2056 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))))

noncomputable def p2058 :=
BSN.logfrac_isNear p520 p596 1 p499
  p593 157330477519 137438953472 52800000000
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p2059 :=
nat_lit
  28112249726568907460877008869448272292468917300661539822477485878707621656431906701706028048427306405265710875708483116966759122895385544819830156795244674632541754443830707273941294995089033428356490509282885064723300802697449921482133275722309366483149434048383907108566415254354824568783131399250272268358636149329667001700939403651929971686504139771582648399892312746886479683987028568936035758161816431633261845913657154371769303950313408559248382929642419083165632911770392995359037468429404240879124068294464716235537436856506956042298285974223689290858683659401065292151897123451222064736785585235431221018049649439372563886315701595281098304271750270872968926297946531264926919670251846171449719442723791463222179752851839175213475316233298067645959528625158496875321419100946334304561169749638234378999637386874925356928373561848382418558332943231405031307075642747796504407594783753774170078472723429650004559240716727362113831551503740797630206625579385418783397570072844536145465625

noncomputable def p2060 :=
nat_lit
  3004852088952827258288190099535631124168114566284207337970056940674351348135361224185106093952970606535695727260345158671755721791400581520330370588532138341756984687453720988491484964511734575418260368734151156841153407162414876752839676953376108288208692242085462695739689384148522826788437087822586887497413203836902051755317535914550644620893279412055445950685345590921102798162921389184656775637861449676147100406454604972151425938388347444151335265623299723631195888111839512355504135172676829460307444689905847047303792776880640602849950094546379376735308619361158700081330061247667415156371627619475851554930068955581234134465848503479162906009209317293239008407944225919387784154374053414813625507104264554954609847197828864338540915550432814784915042683957287234778459934928332697833954180309734050028617392891921873102879555622224078778988254742261073027159089045085149064194991842552848313525138533726320734385011066819633493617444930793199670070398927329942668181566067768789252375

noncomputable def p2061 :=
nat_lit
  9407440773224506529176568857500651144538144565583026311565562241310742360945416609514739181585737663471595495472140923899131384509152239269388817553807034752862166542219692542995804337854598506316907415511184151817482264628622313716122996615543595005129428372116317285987632920507038000124579601150058617461875221973393380924109746168913932623510245472899670149930298259253405611312385676949967940212803800193139782709063837214988572438699173613449788059279786984431338912400273520515747622264511830981712117559767214914416220668489073254135684909167805776893455817185649108869135643881492499080235371375755823857514528492866785157313469780272824393257511939999548644659051837740928586042457828897318497978608139105011180034468394090072098785278119541968136350138141050633792133675665148198849246063996402023436753126022992248443806354116118325467465605265682353640993215005430174748643823987912828900106265897437245293863251493678193606984591788436589065317713701796739603490909375

noncomputable def p2062 :=
BSN.log_dyadic_bound p617 p618 20 19 p2059
  137438953472 52800000000 p2060 p2061 157330477519
  p520

noncomputable def p2063 :=
p2062 p596 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2064 :=
nat_lit
  1650304246484186128867412009819936921388816382751059767398765963755054639143923280158463792274483934740808212048371112906012182601621439247531069913513471136635784296749206584374845702060914503185916659704677926883175747496222698056892855060493354316541478831970074562683336551319267659608462235098980265652009441455370751724704524513554342583620897885263553334180978513935770805125483840465477000513658156278877670969700254471772119915442457072107986597523037886201653555968555346252061549002338545853955944872970498613095940

noncomputable def p2065 :=
nat_lit
  5152330118349943294083290826333022836515130231880860857229852424792252966205183210564070921277131217017959881448620086856031605750985523307433966862109560199766311319504051971946882353836907885876413790862889025679217468377882647644001856146294756122160735102559483971725097723515850591948361445324156615678507861810147027267790641269577049548177011742962163431212264373375521134511279512589447459019773575741927403916906557972820580265943522084084022386657926042196108793299178038229778174716946695417822707335096733341405875

noncomputable def p2066 :=
@BSN.binarySplit_rec (BSN.artanhP p617) (BSN.artanhQ p618) 0 19
  9 p624 p625 p626 p2064
  p2065

noncomputable def p2067 :=
nat_lit
  4689023516058063331002037623096125898133308444773588797722766772904363690199315694532086370200779945238404485037762684681429232564768733597303320724776544828197370162862907869440203675059543116106911694517934138224118662287888938886567296584007491538635662441271265825338604930262978467213691414451034808350275615113776798941418038592666013479792392343454221503297949561017056822910103690417386551812819050918757336666943236793837515011879059159358023173937333580503397118438375315395136644803699507784599149690602223375

noncomputable def p2068 :=
@BSN.binarySplit_of_base10 (BSN.artanhP p617) (BSN.artanhQ p618) 9
  19 p2064 p2065 p2067 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2069 :=
@p2066 p2067 p2060 p2059 p2061
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (p631 (Eq.refl true))
  (p2068 (Eq.refl true))

noncomputable def p2070 :=
p2057
  (BSN.isNear_log_sfrac p499 p593 157330477519 137438953472
    1 52800000000 false
    (p2058
      (p2063 p2069 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))))
  (Eq.refl true) (Eq.refl true)

theorem d91 : Enclosure.Real.IsNear (Real.log Real.pi) false 78665238759 68719476736 1
  34359738368 :=
p2042
  (p2070 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p2071 :=
BSN.logfrac_isNear 4 2 1 2 1 5954088943 8589934592
  3300000000 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p2072 :=
BSN.log_dyadic_bound 1 3 11 10 47940881637414340575
  8589934592 3300000000 1904248773309375360 654729075 5954088943
  4

noncomputable def p2073 :=
p2072 2 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2074 :=
@BSN.binarySplit_of_base10 (BSN.artanhP 1) (BSN.artanhQ 3) 0 10
  1904248773309375360 47940881637414340575 654729075 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

theorem d92 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 2 1)) false 5954088943
  8589934592 1 3300000000 :=
BSN.isNear_log_sfrac 2 1 5954088943 8589934592 1 3300000000
  false
  (p2071
    (p2073 (p2074 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))

noncomputable def p2075 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 2 1)) false
  5954088943 8589934592 1 3300000000 95265423088

theorem d93 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 2 1)) false 95265423088
  137438953472 42 137438953472 :=
@p2075 137438953472 42 137438953472 d92
  (Eq.refl true)

noncomputable def p2076 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 2)))
  false 759250125 1073741824 1 8589934592

noncomputable def p2077 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 2))) false
  12148002000 17179869184 2 17179869184

noncomputable def p2078 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 2)) 24296003999
  17179869184 1 17179869184 6074000999 6074001001

noncomputable def p2079 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 2))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 2) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 24296003999 17179869184

noncomputable def p2080 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 2) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 24296003999 17179869184

noncomputable def p2081 :=
@p2080 1 17179869184 24296003999 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 2 1 12148001999 12148002000 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2082 :=
@p2078 8589934592
  (@p2079 1 17179869184 (BSN.sqrt_natCast_div_one 2)
    (p2081 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d94 : p2076 :=
@p2077 759250125 1073741824 1 8589934592
  p2082 (Eq.refl true)

noncomputable def p2083 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 2)))
  false 97184016000 137438953472 16 137438953472

noncomputable def p2084 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 2))) false
  759250125 1073741824 1 8589934592

theorem d95 : p2083 :=
@p2084 97184016000 137438953472 16 137438953472
  d94 (Eq.refl true)

noncomputable def p2085 :=
BSN.logfrac_isNear 3 1 2 3 1 9437007701 8589934592
  3300000000 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p2086 :=
nat_lit 27198567041618030006108160000

noncomputable def p2087 :=
nat_lit 2682112944407711588577636525

noncomputable def p2088 :=
BSN.log_dyadic_bound 1 2 17 16 p2086 8589934592
  3300000000 p2087 191898783962510625 9437007701 3

noncomputable def p2089 :=
p2088 1 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2090 :=
@BSN.binarySplit_of_base16 (BSN.artanhP 1) (BSN.artanhQ 2) 0 16
  p2087 p2086 191898783962510625 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

theorem d96 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 3 1)) false 9437007701
  8589934592 1 3300000000 :=
BSN.isNear_log_sfrac 3 1 9437007701 8589934592 1 3300000000
  false
  (p2085
    (p2089 (p2090 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))

noncomputable def p2091 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 3 1)) false
  9437007701 8589934592 1 3300000000 150992123216

theorem d97 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 3 1)) false 150992123216
  137438953472 42 137438953472 :=
@p2091 137438953472 42 137438953472 d96
  (Eq.refl true)

noncomputable def p2092 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 3)))
  false 4959401049 8589934592 1 8589934592

noncomputable def p2093 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 3))) false
  9918802098 17179869184 2 17179869184

noncomputable def p2094 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 3)) 29756406295
  17179869184 1 17179869184 4959401048 4959401050

noncomputable def p2095 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 3))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 3) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 29756406295 17179869184

noncomputable def p2096 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 3) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 29756406295 17179869184

noncomputable def p2097 :=
@p2096 1 17179869184 29756406295 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 3 1 14878203147 14878203148 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2098 :=
@p2094 8589934592
  (@p2095 1 17179869184 (BSN.sqrt_natCast_div_one 3)
    (p2097 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d98 : p2092 :=
@p2093 4959401049 8589934592 1 8589934592
  p2098 (Eq.refl true)

noncomputable def p2099 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 3)))
  false 79350416784 137438953472 16 137438953472

noncomputable def p2100 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 3))) false
  4959401049 8589934592 1 8589934592

theorem d99 : p2099 :=
@p2100 79350416784 137438953472 16 137438953472
  d98 (Eq.refl true)

noncomputable def p2101 :=
nat_lit 1181671153346359170692730265957638242378174781758650

noncomputable def p2102 :=
nat_lit 5986310706507378352962293074805895248510699696029696

noncomputable def p2103 :=
Enclosure.Real.IsNear
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 1) (@Nat.cast.{0} Real Real.instNatCast 5)))
  false p2101 p2102

noncomputable def p2104 :=
nat_lit 2000000000000000000000000000000000000000000000000000

noncomputable def p2105 :=
nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625

noncomputable def p2106 :=
nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125

noncomputable def p2107 :=
nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875

noncomputable def p2108 :=
nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375

noncomputable def p2109 :=
BSN.arctan_dyadic_bound_f 1 5 18 17 p2102
  p2104 p2105 p2106 200200021673987500790625
  p2107 p2108

noncomputable def p2110 :=
nat_lit 2442358029135994033939875

noncomputable def p2111 :=
nat_lit 37260822860694382775919147000

noncomputable def p2112 :=
nat_lit 116336546489037573337554931640625

noncomputable def p2113 :=
nat_lit 57493278893883548332405996866302358825

noncomputable def p2114 :=
nat_lit 40230676762013536063022911548614501953125

noncomputable def p2115 :=
@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8
  p2111 p2112 151412625 p2113 p2114

noncomputable def p2116 :=
@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8
  p2111 p2112 151412625 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2117 :=
@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17
  p2113 p2114 1322214852783825 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2118 :=
@p2115 1322214852783825 p2105 p2106
  200200021673987500790625 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (p2116 (Eq.refl true)) (p2117 (Eq.refl true))

noncomputable def p2119 :=
nat_lit 236310350532676991248348623960

noncomputable def p2120 :=
nat_lit 344268321641720831394195556640625

noncomputable def p2121 :=
nat_lit 81801971833623620377505564448994707675

noncomputable def p2122 :=
nat_lit 56886557708273976459167897701263427734375

noncomputable def p2123 :=
@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8
  p2119 p2120 1267389585 p2121 p2122

noncomputable def p2124 :=
@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8
  p2119 p2120 1267389585 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2125 :=
@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17
  p2121 p2122 1927077560082675 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2126 :=
@p2123 1927077560082675 p2107 p2108
  p2110 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (p2124 (Eq.refl true))
  (p2125 (Eq.refl true))

noncomputable def p2127 :=
p2109 p2110 p2101 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true) p2118
  p2126

theorem d100 : p2103 1 p2104 :=
p2127 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2128 :=
nat_lit 25047178968060507272880539293402373975644382030403

noncomputable def p2129 :=
Enclosure.Real.IsNear
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 1) (@Nat.cast.{0} Real Real.instNatCast 239)))
  false p2128 p2102

noncomputable def p2130 :=
nat_lit 4733915408010924740926662591654183582145509

noncomputable def p2131 :=
nat_lit 77229300481955664312677298336960122659119574530232845

noncomputable def p2132 :=
nat_lit 24516194103503660983641551147684725335332607

noncomputable def p2133 :=
nat_lit 186647183216068817672719845704257068688983305564016735

noncomputable def p2134 :=
BSN.arctan_dyadic_bound_f 1 239 6 5 p2102
  p2104 p2130 p2131 9945 p2132
  p2133

noncomputable def p2135 :=
@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5
  p2130 p2131 9945 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2136 :=
@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5
  p2132 p2133 65835 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2137 :=
p2134 65835 p2128 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (p2135 (Eq.refl true)) (p2136 (Eq.refl true))

theorem d101 : p2129 1 p2104 :=
p2137 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2138 :=
nat_lit 18806549737669504701992162098148602382148218980016788

noncomputable def p2139 :=
nat_lit 100000000000000000000000000000000000000000000000000

noncomputable def p2140 :=
BSN.pi_combine p2101 p2128 p2102 p2104
  p2139 p2138 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) d100

theorem d102 : Enclosure.Real.IsNear Real.pi false p2138 p2102 1
  p2139 :=
p2140 d101

noncomputable def p2141 :=
@Enclosure.Real.IsNear.recentre' Real.pi false p2138 p2102 1
  p2139 7244019458077122842 2305843009213693952 1
  2305843009213693952 d102

theorem d103 : Enclosure.Real.IsNear Real.pi false 7244019458077122842 2305843009213693952 1
  2305843009213693952 :=
p2141 (Eq.refl true)

noncomputable def p2142 :=
BSN.logfrac_isNear 8 2 1 4 1 11908177887
  8589934592 3300000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2143 :=
nat_lit 144233304897774462163270126069392063072882592678070068359375

noncomputable def p2144 :=
nat_lit 22391542823158599862738064683496659373458950479911949400000

noncomputable def p2145 :=
nat_lit 555274919675630397422200570030852103853441196875

noncomputable def p2146 :=
BSN.log_dyadic_bound 3 5 23 22 p2143 8589934592
  3300000000 p2144 p2145 11908177887 8

noncomputable def p2147 :=
p2146 2 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2148 :=
nat_lit 117048680082474133384580175

noncomputable def p2149 :=
nat_lit 753960950911045074462890625

noncomputable def p2150 :=
nat_lit 95161842341078937820186139933625

noncomputable def p2151 :=
nat_lit 191300762623701989650726318359375

noncomputable def p2152 :=
@BSN.binarySplit_rec (BSN.artanhP 3) (BSN.artanhQ 5) 0 22 11
  p2148 p2149 431467934736729065175 p2150
  p2151

noncomputable def p2153 :=
nat_lit 1286943652057122751813246125

noncomputable def p2154 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11
  p2148 p2149 431467934736729065175 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2155 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 11 22
  p2150 p2151 p2153 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2156 :=
@p2152 p2153 p2144 p2143 p2145
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (p2154 (Eq.refl true))
  (p2155 (Eq.refl true))

theorem d104 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 4 1)) false 11908177887
  8589934592 1 3300000000 :=
BSN.isNear_log_sfrac 4 1 11908177887 8589934592 1 3300000000
  false
  (p2142
    (p2147 p2156 (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true)))

noncomputable def p2157 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 4 1)) false
  11908177887 8589934592 1 3300000000 190530846192

theorem d105 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 4 1)) false 190530846192
  137438953472 42 137438953472 :=
@p2157 137438953472 42 137438953472 d104
  (Eq.refl true)

noncomputable def p2158 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 4)))
  false 8589934591 17179869184 1 17179869184

noncomputable def p2159 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 4))) false
  8589934591 17179869184 1 17179869184

noncomputable def p2160 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 4)) 34359738369
  17179869184 1 17179869184 4294967295 4294967296

noncomputable def p2161 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 4))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 4) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 34359738369 17179869184

noncomputable def p2162 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 4) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 34359738369 17179869184

noncomputable def p2163 :=
@p2162 1 17179869184 34359738369 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 4 1 17179869184 17179869185 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2164 :=
@p2160 8589934592
  (@p2161 1 17179869184 (BSN.sqrt_natCast_div_one 4)
    (p2163 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d106 : p2158 :=
@p2159 8589934591 17179869184 1 17179869184
  p2164 (Eq.refl true)

noncomputable def p2165 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 4)))
  false 68719476728 137438953472 8 137438953472

theorem d107 : p2165 :=
@p2159 68719476728 137438953472 8 137438953472
  d106 (Eq.refl true)

noncomputable def p2166 :=
BSN.logfrac_isNear 5 1 2 5 1 13824966397
  8589934592 3300000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2167 :=
nat_lit 137609265977726008982980500513428322865970815241775935080267546171875

noncomputable def p2168 :=
nat_lit 28495911347251394938167391982887742139989968211716434922214938612500

noncomputable def p2169 :=
nat_lit 142725851083899285619764626920825276013559341383680000000

noncomputable def p2170 :=
BSN.log_dyadic_bound 2 3 30 29 p2167 8589934592
  3300000000 p2168 p2169 13824966397 5

noncomputable def p2171 :=
p2170 1 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2172 :=
nat_lit 29325128709309236875766211300

noncomputable def p2173 :=
nat_lit 141613827518379161815574079375

noncomputable def p2174 :=
nat_lit 694826083705780165806270091825942581900

noncomputable def p2175 :=
nat_lit 971721959565470920192309454027826454125

noncomputable def p2176 :=
@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 29 14
  p2172 p2173 57299708096576225280000 p2174
  p2175

noncomputable def p2177 :=
nat_lit 2490865238673483697116105670656000

noncomputable def p2178 :=
@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14
  p2172 p2173 57299708096576225280000 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2179 :=
@BSN.binarySplit_of_base15 (BSN.artanhP 2) (BSN.artanhQ 3) 14 29
  p2174 p2175 p2177 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2180 :=
@p2176 p2177 p2168 p2167 p2169
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (p2178 (Eq.refl true))
  (p2179 (Eq.refl true))

theorem d108 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 5 1)) false 13824966397
  8589934592 1 3300000000 :=
BSN.isNear_log_sfrac 5 1 13824966397 8589934592 1 3300000000
  false
  (p2166
    (p2171 p2180 (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true)))

noncomputable def p2181 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 5 1)) false
  13824966397 8589934592 1 3300000000 221199462352

theorem d109 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 5 1)) false 221199462352
  137438953472 42 137438953472 :=
@p2181 137438953472 42 137438953472 d108
  (Eq.refl true)

noncomputable def p2182 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 5)))
  false 1920767767 4294967296 1 8589934592

noncomputable def p2183 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 5))) false
  7683071068 17179869184 2 17179869184

noncomputable def p2184 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 5)) 38415355339
  17179869184 1 17179869184 3841535533 3841535535

noncomputable def p2185 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 5))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 5) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 38415355339 17179869184

noncomputable def p2186 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 5) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 38415355339 17179869184

noncomputable def p2187 :=
@p2186 1 17179869184 38415355339 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 5 1 19207677669 19207677670 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2188 :=
@p2184 8589934592
  (@p2185 1 17179869184 (BSN.sqrt_natCast_div_one 5)
    (p2187 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d110 : p2182 :=
@p2183 1920767767 4294967296 1 8589934592
  p2188 (Eq.refl true)

noncomputable def p2189 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 5)))
  false 61464568544 137438953472 16 137438953472

noncomputable def p2190 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 5))) false
  1920767767 4294967296 1 8589934592

theorem d111 : p2189 :=
@p2190 61464568544 137438953472 16 137438953472
  d110 (Eq.refl true)

noncomputable def p2191 :=
nat_lit 554522696895959841336459264

noncomputable def p2192 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 6) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false p2191 p976

noncomputable def p2193 :=
nat_lit 3300000000000000000000000

noncomputable def p2194 :=
BSN.log_rat_reduce_isNear 6 1 2 12 8 3482918757
  8589934592 24973259072661432 36028797018963968 3300000000
  1000000000000000

noncomputable def p2195 :=
BSN.log_dyadic_bound 2 10 7 6 135135000000000000 8589934592
  3300000000 1846318458961920 42577920 3482918757 12

noncomputable def p2196 :=
p2195 8 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2197 :=
@BSN.binarySplit_of_base6 (BSN.artanhP 2) (BSN.artanhQ 10) 0 6
  1846318458961920 135135000000000000 42577920 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2198 :=
p2194 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p2196 (p2197 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

theorem d112 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 6 1)) false
  4034683638717687 2251799813685248 5000033 16500000000000000 :=
BSN.isNear_log_sfrac 6 1 4034683638717687 2251799813685248 5000033
  16500000000000000 false
  (@p2192 1000006600000000 p2193 4034683638717687
    2251799813685248 5000033 16500000000000000
    (p2198 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p2199 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 6 1)) false
  4034683638717687 2251799813685248 5000033 16500000000000000
  246257546308

theorem d113 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 6 1)) false 246257546308
  137438953472 43 137438953472 :=
@p2199 137438953472 43 137438953472 d112
  (Eq.refl true)

noncomputable def p2200 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 6)))
  false 7013652225 17179869184 1 17179869184

noncomputable def p2201 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 6))) false
  7013652225 17179869184 1 17179869184

noncomputable def p2202 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 6)) 42081913349
  17179869184 1 17179869184 3506826112 3506826113

noncomputable def p2203 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 6))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 6) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 42081913349 17179869184

noncomputable def p2204 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 6) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 42081913349 17179869184

noncomputable def p2205 :=
@p2204 1 17179869184 42081913349 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 6 1 21040956674 21040956675 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2206 :=
@p2202 8589934592
  (@p2203 1 17179869184 (BSN.sqrt_natCast_div_one 6)
    (p2205 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d114 : p2200 :=
@p2201 7013652225 17179869184 1 17179869184
  p2206 (Eq.refl true)

noncomputable def p2207 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 6)))
  false 56109217800 137438953472 8 137438953472

theorem d115 : p2207 :=
@p2201 56109217800 137438953472 8 137438953472
  d114 (Eq.refl true)

noncomputable def p2208 :=
nat_lit 602230021555239699653591040

noncomputable def p2209 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 7) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false p2208 p976

noncomputable def p2210 :=
BSN.log_rat_reduce_isNear 7 1 2 14 8 4807063014
  8589934592 24973259072661432 36028797018963968 3300000000
  1000000000000000

noncomputable def p2211 :=
nat_lit 1583401270004025114067425

noncomputable def p2212 :=
BSN.log_dyadic_bound 3 11 9 8 p2211 8589934592
  3300000000 41108703763709649648240 87256779635025 4807063014 14

noncomputable def p2213 :=
p2212 8 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2214 :=
@BSN.binarySplit_of_base8 (BSN.artanhP 3) (BSN.artanhQ 11) 0 8
  41108703763709649648240 p2211 87256779635025 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2215 :=
p2210 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p2213 (p2214 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

theorem d116 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 7 1)) false
  4381800110824695 2251799813685248 5000033 16500000000000000 :=
BSN.isNear_log_sfrac 7 1 4381800110824695 2251799813685248 5000033
  16500000000000000 false
  (@p2209 1000006600000000 p2193 4381800110824695
    2251799813685248 5000033 16500000000000000
    (p2215 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p2216 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 7 1)) false
  4381800110824695 2251799813685248 5000033 16500000000000000
  267443854420

theorem d117 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 7 1)) false 267443854420
  137438953472 43 137438953472 :=
@p2216 137438953472 43 137438953472 d116
  (Eq.refl true)

noncomputable def p2217 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 7)))
  false 6493380203 17179869184 1 17179869184

noncomputable def p2218 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 7))) false
  6493380203 17179869184 1 17179869184

noncomputable def p2219 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 7)) 45453661417
  17179869184 1 17179869184 3246690101 3246690102

noncomputable def p2220 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 7))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 7) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 45453661417 17179869184

noncomputable def p2221 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 7) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 45453661417 17179869184

noncomputable def p2222 :=
@p2221 1 17179869184 45453661417 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 7 1 22726830708 22726830709 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2223 :=
@p2219 8589934592
  (@p2220 1 17179869184 (BSN.sqrt_natCast_div_one 7)
    (p2222 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d118 : p2217 :=
@p2218 6493380203 17179869184 1 17179869184
  p2223 (Eq.refl true)

noncomputable def p2224 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 7)))
  false 51947041624 137438953472 8 137438953472

theorem d119 : p2224 :=
@p2218 51947041624 137438953472 8 137438953472
  d118 (Eq.refl true)

noncomputable def p2225 :=
nat_lit 643555985949696828723167232

noncomputable def p2226 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 8) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false p2225 p976

noncomputable def p2227 :=
BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8589934592
  24973259072661432 36028797018963968 3300000000 1000000000000000

noncomputable def p2228 :=
BSN.log_dyadic_bound 0 16 1 0 1 8589934592
  3300000000 0 1 0 16

noncomputable def p2229 :=
p2228 16 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2230 :=
p2229
  (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0
    (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2231 :=
p2227 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) p2230 BSN.log2_near_15 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

theorem d120 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 8 1)) false
  9364972152248037 4503599627370496 10000099 33000000000000000 :=
BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 10000099
  33000000000000000 false
  (@p2226 1000009900000000 p2193 9364972152248037
    4503599627370496 10000099 33000000000000000
    (p2231 (Eq.refl true)) (Eq.refl true))

noncomputable def p2232 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 8 1)) false
  9364972152248037 4503599627370496 10000099 33000000000000000
  285796269294

theorem d121 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 8 1)) false 285796269294
  137438953472 43 137438953472 :=
@p2232 137438953472 43 137438953472 d120
  (Eq.refl true)

noncomputable def p2233 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 8)))
  false 759250125 2147483648 1 8589934592

noncomputable def p2234 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 8))) false
  6074001000 17179869184 2 17179869184

noncomputable def p2235 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 8)) 48592007999
  17179869184 1 17179869184 3037000499 3037000501

noncomputable def p2236 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 8))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 8) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 48592007999 17179869184

noncomputable def p2237 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 8) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 48592007999 17179869184

noncomputable def p2238 :=
@p2237 1 17179869184 48592007999 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 8 1 24296003999 24296004000 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2239 :=
@p2235 8589934592
  (@p2236 1 17179869184 (BSN.sqrt_natCast_div_one 8)
    (p2238 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d122 : p2233 :=
@p2234 759250125 2147483648 1 8589934592
  p2239 (Eq.refl true)

noncomputable def p2240 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 8)))
  false 48592008000 137438953472 16 137438953472

noncomputable def p2241 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 8))) false
  759250125 2147483648 1 8589934592

theorem d123 : p2240 :=
@p2241 48592008000 137438953472 16 137438953472
  d122 (Eq.refl true)

noncomputable def p2242 :=
nat_lit 680008069884511480266620928

noncomputable def p2243 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 9) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false p2242 p976

noncomputable def p2244 :=
BSN.log_rat_reduce_isNear 9 1 3 18 16 1011748572
  8589934592 24973259072661432 36028797018963968 3300000000
  1000000000000000

noncomputable def p2245 :=
BSN.log_dyadic_bound 1 17 4 3 2534444745 8589934592
  3300000000 2929319 15 1011748572 18

noncomputable def p2246 :=
p2245 16 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2247 :=
@BSN.binarySplit_of_base3 (BSN.artanhP 1) (BSN.artanhQ 17) 0 3 2929319
  2534444745 15 (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2248 :=
p2244 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p2246 (p2247 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

theorem d124 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 9 1)) false
  9895419787564773 4503599627370496 10000099 33000000000000000 :=
BSN.isNear_log_sfrac 9 1 9895419787564773 4503599627370496 10000099
  33000000000000000 false
  (@p2243 1000009900000000 p2193 9895419787564773
    4503599627370496 10000099 33000000000000000
    (p2248 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p2249 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 9 1)) false
  9895419787564773 4503599627370496 10000099 33000000000000000
  301984246446

theorem d125 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 9 1)) false 301984246446
  137438953472 43 137438953472 :=
@p2249 137438953472 43 137438953472 d124
  (Eq.refl true)

noncomputable def p2250 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 9)))
  false 5726623061 17179869184 1 17179869184

noncomputable def p2251 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 9))) false
  5726623061 17179869184 1 17179869184

noncomputable def p2252 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 9)) 51539607553
  17179869184 1 17179869184 2863311530 2863311531

noncomputable def p2253 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 9))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 9) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 51539607553 17179869184

noncomputable def p2254 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 9) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 51539607553 17179869184

noncomputable def p2255 :=
@p2254 1 17179869184 51539607553 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 9 1 25769803776 25769803777 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2256 :=
@p2252 8589934592
  (@p2253 1 17179869184 (BSN.sqrt_natCast_div_one 9)
    (p2255 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d126 : p2250 :=
@p2251 5726623061 17179869184 1 17179869184
  p2256 (Eq.refl true)

noncomputable def p2257 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 9)))
  false 45812984488 137438953472 8 137438953472

theorem d127 : p2257 :=
@p2251 45812984488 137438953472 8 137438953472
  d126 (Eq.refl true)

noncomputable def p2258 :=
nat_lit 712615570104769214689574912

noncomputable def p2259 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 10) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false p2258 p976

noncomputable def p2260 :=
BSN.log_rat_reduce_isNear 10 1 3 20 16 1916788510
  8589934592 24973259072661432 36028797018963968 3300000000
  1000000000000000

noncomputable def p2261 :=
BSN.log_dyadic_bound 2 18 5 4 10413862744320 8589934592
  3300000000 43175675904 26880 1916788510 20

noncomputable def p2262 :=
p2261 16 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2263 :=
@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 18) 0 4
  43175675904 10413862744320 26880 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2264 :=
p2260 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p2262 (p2263 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

theorem d128 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 10 1)) false
  10369921366578917 4503599627370496 10000099 33000000000000000 :=
BSN.isNear_log_sfrac 10 1 10369921366578917 4503599627370496 10000099
  33000000000000000 false
  (@p2259 1000009900000000 p2193 10369921366578917
    4503599627370496 10000099 33000000000000000
    (p2264 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p2265 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 10 1)) false
  10369921366578917 4503599627370496 10000099 33000000000000000
  316464885454

theorem d129 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 10 1)) false 316464885454
  137438953472 43 137438953472 :=
@p2265 137438953472 43 137438953472 d128
  (Eq.refl true)

noncomputable def p2266 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 10)))
  false 5432751653 17179869184 1 17179869184

noncomputable def p2267 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 10))) false
  5432751653 17179869184 1 17179869184

noncomputable def p2268 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 10)) 54327516525
  17179869184 1 17179869184 2716375826 2716375827

noncomputable def p2269 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 10))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 10) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 54327516525 17179869184

noncomputable def p2270 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 10) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 54327516525 17179869184

noncomputable def p2271 :=
@p2270 1 17179869184 54327516525 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 10 1 27163758262 27163758263 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2272 :=
@p2268 8589934592
  (@p2269 1 17179869184 (BSN.sqrt_natCast_div_one 10)
    (p2271 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d130 : p2266 :=
@p2267 5432751653 17179869184 1 17179869184
  p2272 (Eq.refl true)

noncomputable def p2273 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 10)))
  false 43462013224 137438953472 8 137438953472

theorem d131 : p2273 :=
@p2267 43462013224 137438953472 8 137438953472
  d130 (Eq.refl true)

noncomputable def p2274 :=
nat_lit 742112642020618540985352192

noncomputable def p2275 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 11) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false p2274 p976

noncomputable def p2276 :=
BSN.log_rat_reduce_isNear 11 1 3 22 16 2735496720
  8589934592 24973259072661432 36028797018963968 3300000000
  1000000000000000

noncomputable def p2277 :=
BSN.log_dyadic_bound 3 19 7 6 299096311588005666735
  8589934592 3300000000 2523420310347603792 5524329195 2735496720
  22

noncomputable def p2278 :=
p2277 16 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2279 :=
@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 19) 0 6
  2523420310347603792 299096311588005666735 5524329195 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2280 :=
p2276 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p2278 (p2279 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

theorem d132 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 11 1)) false
  10799160256583397 4503599627370496 10000099 33000000000000000 :=
BSN.isNear_log_sfrac 11 1 10799160256583397 4503599627370496 10000099
  33000000000000000 false
  (@p2275 1000009900000000 p2193 10799160256583397
    4503599627370496 10000099 33000000000000000
    (p2280 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p2281 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 11 1)) false
  10799160256583397 4503599627370496 10000099 33000000000000000
  329564216814

theorem d133 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 11 1)) false 329564216814
  137438953472 43 137438953472 :=
@p2281 137438953472 43 137438953472 d132
  (Eq.refl true)

noncomputable def p2282 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 11)))
  false 5179925457 17179869184 1 17179869184

noncomputable def p2283 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 11))) false
  5179925457 17179869184 1 17179869184

noncomputable def p2284 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 11)) 56979180031
  17179869184 1 17179869184 2589962728 2589962729

noncomputable def p2285 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 11))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 11) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 56979180031 17179869184

noncomputable def p2286 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 11) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 56979180031 17179869184

noncomputable def p2287 :=
@p2286 1 17179869184 56979180031 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 11 1 28489590015 28489590016 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2288 :=
@p2284 8589934592
  (@p2285 1 17179869184 (BSN.sqrt_natCast_div_one 11)
    (p2287 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d134 : p2282 :=
@p2283 5179925457 17179869184 1 17179869184
  p2288 (Eq.refl true)

noncomputable def p2289 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 11)))
  false 41439403656 137438953472 8 137438953472

theorem d135 : p2289 :=
@p2283 41439403656 137438953472 8 137438953472
  d134 (Eq.refl true)

noncomputable def p2290 :=
nat_lit 769041358879192117577515008

noncomputable def p2291 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 12) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false p2290 p976

noncomputable def p2292 :=
BSN.log_rat_reduce_isNear 12 1 3 24 16 3482918757
  8589934592 24973259072661432 36028797018963968 3300000000
  1000000000000000

noncomputable def p2293 :=
BSN.log_dyadic_bound 4 20 7 6 553512960000000000000
  8589934592 3300000000 7562520407908024320 174399160320 3482918757
  24

noncomputable def p2294 :=
p2293 16 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p2295 :=
@BSN.binarySplit_of_base6 (BSN.artanhP 4) (BSN.artanhQ 20) 0 6
  7562520407908024320 553512960000000000000 174399160320 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p2296 :=
p2292 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p2294 (p2295 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

theorem d136 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 12 1)) false
  11191024661518053 4503599627370496 10000099 33000000000000000 :=
BSN.isNear_log_sfrac 12 1 11191024661518053 4503599627370496 10000099
  33000000000000000 false
  (@p2291 1000009900000000 p2193 11191024661518053
    4503599627370496 10000099 33000000000000000
    (p2296 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p2297 :=
@Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac false 12 1)) false
  11191024661518053 4503599627370496 10000099 33000000000000000
  341522969406

theorem d137 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac false 12 1)) false 341522969406
  137438953472 43 137438953472 :=
@p2297 137438953472 43 137438953472 d136
  (Eq.refl true)

noncomputable def p2298 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 12)))
  false 4959401049 17179869184 1 17179869184

noncomputable def p2299 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 12))) false
  4959401049 17179869184 1 17179869184

noncomputable def p2300 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 12)) 59512812589
  17179869184 1 17179869184 2479700524 2479700525

noncomputable def p2301 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 12))
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 12) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 59512812589 17179869184

noncomputable def p2302 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 12) (@Nat.cast.{0} Real Real.instNatCast 1)))
  false 59512812589 17179869184

noncomputable def p2303 :=
@p2302 1 17179869184 59512812589 17179869184 1
  17179869184
  (BSN.sqrt_enclosure 12 1 29756406294 29756406295 8589934592
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

noncomputable def p2304 :=
@p2300 8589934592
  (@p2301 1 17179869184 (BSN.sqrt_natCast_div_one 12)
    (p2303 (Eq.refl true)))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d138 : p2298 :=
@p2299 4959401049 17179869184 1 17179869184
  p2304 (Eq.refl true)

noncomputable def p2305 :=
Enclosure.Real.IsNear (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast 12)))
  false 39675208392 137438953472 8 137438953472

theorem d139 : p2305 :=
@p2299 39675208392 137438953472 8 137438953472
  d138 (Eq.refl true)

theorem d140 : Enclosure.Real.IsNear Real.pi false 226375608064910080 72057594037927936 1
  1000000000000000 :=
BSN.pi_near_15

noncomputable def p2306 :=
Enclosure.Real.IsNear
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  false 884279719003555 140737488355328 1

theorem d141 : p2306 500000000000000 :=
@p501 1 1000000000000000 884279719003555 140737488355328
  1 500000000000000 (Enclosure.Real.IsNear.const false 2 1)
  d140 (Eq.refl true)

noncomputable def p2307 :=
Enclosure.Real.IsNear
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 2734261103 17179869184

noncomputable def p2308 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 2734261103 17179869184

noncomputable def p2309 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  884279719003555 140737488355328 1 500000000000000

noncomputable def p2310 :=
@p2308 1 17179869184 2734261103 17179869184 1
  17179869184
  (@p2309 1367130551 1367130552 8589934592 d141
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))

theorem d142 : p2307 1 17179869184 :=
p2310 (Eq.refl true)

noncomputable def p2314 :=
Enclosure.Real.IsNear
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  false 884279719003555 70368744177664 1

noncomputable def p2315 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 4 1) Real.pi 4 1
  0 1 226375608064910080 72057594037927936

noncomputable def p2316 :=
nat_lit 79228162514264337593543950336

noncomputable def p2317 :=
Enclosure.Real.IsNear (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) false
  p1068 p2316 p1071

noncomputable def p2318 :=
nat_lit 4294967296000000000000000000000000000000

noncomputable def p2319 :=
@Enclosure.Real.IsNear.mulLit_ff Real.pi Real.pi 226375608064910080 72057594037927936 1
  1000000000000000 226375608064910080 72057594037927936 1
  1000000000000000 p1068

noncomputable def p2320 :=
Enclosure.Real.IsNear
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  false p1068 p1070

noncomputable def p2321 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 4 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) 4 1
  0 1

noncomputable def p2323 :=
Enclosure.Real.IsNear
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  false

noncomputable def p2324 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 8 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi)
  8 1

noncomputable def p2325 :=
nat_lit 22300745198530623141535718272648361505980416

noncomputable def p2326 :=
nat_lit 73786976294838206464000000000000000000000000000000000000000000000

noncomputable def p2327 :=
@p2324 0 1 p1059 p2325 p1062
  p2326 p1059 p1061 p1062
  p1063 (Enclosure.Real.IsNear.const false 8 1)

noncomputable def p2328 :=
@Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)
  Real.pi p1068 p2316 p1071

noncomputable def p2332 :=
nat_lit 2345851864323018569406307914075

noncomputable def p2333 :=
nat_lit 2475880078570760549798248448

noncomputable def p2334 :=
nat_lit 80958226227132123480605013

noncomputable def p2335 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 96 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  p2332 p2333 p2334

noncomputable def p2336 :=
nat_lit 134217728000000000000000000000000000000

noncomputable def p2337 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 96 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) 96 1
  0 1

noncomputable def p2422 :=
nat_lit 26400000000000000000000000

noncomputable def p2445 :=
nat_lit 1237940039285380274899124224

noncomputable def p2457 :=
nat_lit
  21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600

noncomputable def p2460 :=
nat_lit
  1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600

noncomputable def p2466 :=
nat_lit 5133330660362904937396483134791632965849700352038159351603073932373040875403608499582161387520

noncomputable def p2469 :=
nat_lit 230999879716330722182841741065623483463236515841717170822138326956786839393162382481197262438400

noncomputable def p2477 :=
nat_lit 46199975943266144436568348213124696692647303168343434164427665391357367878632476496239452487680

noncomputable def p2480 :=
nat_lit 846999558959879314670419717240619439365200558086296293014507198841551744441595402431056628940800

noncomputable def p2495 :=
nat_lit
  339138446815163308389697698331910581583522074180100618498856275084237003166987365461580524413565563726638823827085526321999363494300225850968685904012192644028292543256010576039453443227648000

noncomputable def p2498 :=
nat_lit
  51888182362719986183623747844782318982278877349555394630325010087888261484549066915621820235275531250175740045544085527265902614627934555198208943313865474536328759118169618134036376813830144000

noncomputable def p2504 :=
nat_lit
  282877490902138091004622673603363019119652456796264491099280832830873987773707601701812303598028785564314492868916806270538811366318583631052800

noncomputable def p2507 :=
nat_lit
  9900712181574833185161793576117705669187835987869257188474829149080589572079766059563430625931007494751007250412088219468858397821150427086848000

noncomputable def p2563 :=
@Enclosure.Real.IsNear.of_eq
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (Enclosure.sfrac false 1 1) false 1

noncomputable def p2602 :=
nat_lit 2417851639229258349412352

noncomputable def p2604 :=
nat_lit 14757395258967641292800000000000000

noncomputable def p2613 :=
nat_lit
  1723989524678609869184368353634558086375647288945605880257499904391989104065417411410730399287089189440146844853530817917959165259045966673531664948206962296697359276441600

noncomputable def p2616 :=
nat_lit
  156883046745753498095777520180744785860183903294050135103432491299671008469952984438376466335125116239053362881671304430534284038573182967291381510286833568999459694156185600

noncomputable def p2630 :=
nat_lit 41538374868278621028243970633760768

noncomputable def p2632 :=
nat_lit 1267650600228229401496703205376000000000000000

noncomputable def p2646 :=
nat_lit
  18384732040517988058098928146181029592990301167271500207433495074180196305072615363872242148647474559264065962695855987953236410770294878979458770736738308867124182908928000

noncomputable def p2649 :=
nat_lit
  2812864002199252172889136006365697527727516078592539531737324746349570034676110150672453048743063607567402092292465966156845170847855116483857191922720961256669999985065984000

noncomputable def p2977 :=
nat_lit 6129982163463555433433388108601236734474956488734408704

noncomputable def p3100 :=
nat_lit
  22411863820821928299396788597249255122883414756292876443347498757095858352850426348339495190732159462721908983095900632933469148367597566755911644326690509857065670593740800

noncomputable def p3103 :=
nat_lit
  784415233728767490478887600903723929300919516470250675517162456498355042349764922191882331675625581195266814408356522152671420192865914836456907551434167844997298470780928000

noncomputable def p3178 :=
nat_lit 42817430781178796431748579083484854091482398720

noncomputable def p3179 :=
nat_lit 299722015468251575022240053584393978640376791040

noncomputable def p3705 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 32
    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))

noncomputable def p3710 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3711 :=
@OfNat.ofNat.{0} Real 63
  (@instOfNatAtLeastTwo.{0} Real 63
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 61))

noncomputable def p3712 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  p3711

noncomputable def p3713 :=
@HSub.hSub.{0, 0, 0} Real Real Real
  (@instHSub.{0} Real
    (@SubNegMonoid.toSub.{0} Real
      (@AddGroup.toSubNegMonoid.{0} Real
        (@AddGroupWithOne.toAddGroup.{0} Real
          (@Ring.toAddGroupWithOne.{0} Real
            (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField)))))))
  (p3710 Real.pi) p3712

noncomputable def p3726 :=
@Mathlib.Tactic.Ring.Common.neg_congr.{0} Real Real.commRing
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 1))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3727 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))
  1
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 1
      (@One.toOfNat1.{0} Real
        (@AddMonoidWithOne.toOne.{0} Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
            (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))
    1
    (@Nat.cast_one.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p3728 :=
@Mathlib.Tactic.Ring.Common.neg_add.{0} Real Real.commRing
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))

noncomputable def p3729 :=
@Neg.neg.{0} Real
  (@NegZeroClass.toNeg.{0} Real
    (@SubNegZeroMonoid.toNegZeroClass.{0} Real
      (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
        (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
          (@AddCommGroup.toDivisionAddCommMonoid.{0} Real
            (@Ring.toAddCommGroup.{0} Real
              (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))))))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)

noncomputable def p3730 :=
@Mathlib.Meta.NormNum.isInt_neg.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@Neg.neg.{0} Real
    (@NegZeroClass.toNeg.{0} Real
      (@SubNegZeroMonoid.toNegZeroClass.{0} Real
        (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
          (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
            (@AddCommGroup.toDivisionAddCommMonoid.{0} Real
              (@Ring.toAddCommGroup.{0} Real
                (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))))))))

noncomputable def p3731 :=
@Eq.refl.{1} (Real → Real)
  (@Neg.neg.{0} Real
    (@NegZeroClass.toNeg.{0} Real
      (@SubNegZeroMonoid.toNegZeroClass.{0} Real
        (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
          (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
            (@AddCommGroup.toDivisionAddCommMonoid.{0} Real
              (@Ring.toAddCommGroup.{0} Real
                (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))))))))

noncomputable def p3732 :=
@p3730
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (Int.ofNat 1) (Int.negOfNat 1) p3731

noncomputable def p3733 :=
p3732
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1)
    1
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1))

noncomputable def p3744 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3746 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  1

noncomputable def p3747 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  1

noncomputable def p3762 :=
@p3744
  (@OfNat.ofNat.{0} Real 32
    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3763 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 32
    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
  32
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    32
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 30)))))

noncomputable def p3764 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3765 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)

noncomputable def p3766 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32))
  32

noncomputable def p3767 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  1 32

noncomputable def p3768 :=
@p3767 32
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  (@Eq.refl.{1} Nat 32)

noncomputable def p3769 :=
@p3765
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p3766
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3768)

noncomputable def p3770 :=
p3769
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        32)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p3771 :=
@p3764
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p3770

noncomputable def p3772 :=
p3771
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        32)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p3773 :=
p3772
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        32)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p3777 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat
      (@NPow.toPow.{0} Real
        (@Monoid.toNPow.{0} Real
          (@Semiring.toMonoid.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)

noncomputable def p3781 :=
fun (_a : Real) =>
  @Eq.{1} Real p3777
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat
          (@NPow.toPow.{0} Real
            (@Monoid.toNPow.{0} Real
              (@Semiring.toMonoid.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
        Real.pi
        (@Nat.rawCast.{0} Nat
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
            (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
              (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
          1))
      _a)

noncomputable def p3782 :=
@congrArg.{1, 1} Real Prop
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  p3781
  (@Eq.symm.{1} Real
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1)
    (@rfl.{1} Real
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        1)))

noncomputable def p3819 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat
      (@NPow.toPow.{0} Real
        (@Monoid.toNPow.{0} Real
          (@Semiring.toMonoid.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)

noncomputable def p3824 :=
@Mathlib.Tactic.Ring.Common.sub_congr.{0} Real Real.commRing (p3710 Real.pi)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p3712
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3825 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3826 :=
@p3825
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      20)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  Real.pi

noncomputable def p3827 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3828 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3829 :=
@p3826
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3777
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p3827 20
    (@p3828 20
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 20
          (@instOfNatAtLeastTwo.{0} Real 20
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3830 :=
p3829
  (@Mathlib.Tactic.Ring.Common.atom_pf.{0} Real Real.instCommSemiring p3777 Real.pi
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@rfl.{1} Nat
      (@Nat.rawCast.{0} Nat
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
            (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
        1))
    (@Eq.mpr.{0} (@Eq.{1} Real p3777 p3777)
      (@Eq.{1} Real p3777 p3777)
      (@id.{0}
        (@Eq.{1} Prop (@Eq.{1} Real p3777 p3777)
          (@Eq.{1} Real p3777 p3777))
        p3782)
      (@Eq.refl.{1} Real p3777)))

noncomputable def p3831 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3777
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3832 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  p3777
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p3819

noncomputable def p3833 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  Real.pi

noncomputable def p3834 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      20)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1))
  20

noncomputable def p3835 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  20 1

noncomputable def p3836 :=
@p3835 20
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Eq.refl.{1} Nat 20)

noncomputable def p3837 :=
@p3832
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p3833
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p3834
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p3836))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      20))

noncomputable def p3838 :=
@p3831
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p3837
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p3819
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p3839 :=
p3838
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p3777
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p3840 :=
@p3824
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p3830 p3839)

noncomputable def p3841 :=
@p3744 p3711
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3842 :=
p3841
  (p3746
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring p3711 63
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p3711 63
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 63
          (@instOfNatAtLeastTwo.{0} Real 63
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 61))))))

noncomputable def p3843 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3844 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    63)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    63)

noncomputable def p3845 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63))
  63

noncomputable def p3846 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    63)
  1 63

noncomputable def p3847 :=
@p3846 63
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    63)
  (@Eq.refl.{1} Nat 63)

noncomputable def p3848 :=
@p3844
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p3845
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3847)

noncomputable def p3849 :=
p3848
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        63)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p3850 :=
@p3843
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p3849

noncomputable def p3851 :=
p3850
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        63)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p3852 :=
p3851
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        63)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p3853 :=
@Mathlib.Tactic.Ring.Common.sub_pf.{0} Real Real.commRing
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3854 :=
@Mathlib.Tactic.Ring.Common.neg_add.{0} Real Real.commRing
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    63)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 63))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))

noncomputable def p3855 :=
@Neg.neg.{0} Real
  (@NegZeroClass.toNeg.{0} Real
    (@SubNegZeroMonoid.toNegZeroClass.{0} Real
      (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
        (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
          (@AddCommGroup.toDivisionAddCommMonoid.{0} Real
            (@Ring.toAddCommGroup.{0} Real
              (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))))))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    63)

noncomputable def p3856 :=
@p3730
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    63)
  (Int.ofNat 63) (Int.negOfNat 63) p3731

noncomputable def p3857 :=
p3856
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63)
    63
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      63))

noncomputable def p3858 :=
@p3853
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p3854
    (@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real p3855 (Int.negOfNat 63)
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (p3857 (@Eq.refl.{1} Int (Int.negOfNat 63))))
    (@Mathlib.Tactic.Ring.Common.neg_zero.{0} Real Real.commRing))

noncomputable def p3859 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_gt.{0} Real Real.instCommSemiring
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p3860 :=
p3858
  (p3859
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63))
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p3819
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p3930 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@inferInstance.{1} (Mul.{0} Real)
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 32
    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))

noncomputable def p3938 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3939 :=
@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
  (p3938
    (@HSub.hSub.{0, 0, 0} Real Real Real
      (@instHSub.{0} Real
        (@SubNegMonoid.toSub.{0} Real
          (@AddGroup.toSubNegMonoid.{0} Real
            (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
      Real.pi
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 315
        true 2)))

noncomputable def p3940 :=
@congrArg.{1, 1} Real Prop
  (p3938
    (@HSub.hSub.{0, 0, 0} Real Real Real
      (@instHSub.{0} Real
        (@SubNegMonoid.toSub.{0} Real
          (@AddGroup.toSubNegMonoid.{0} Real
            (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
      Real.pi
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 315
        true 2)))

noncomputable def p3941 :=
@OfNat.ofNat.{0} Real 20
  (@instOfNatAtLeastTwo.{0} Real 20
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 18))

noncomputable def p3942 :=
@HSub.hSub.{0, 0, 0} Real Real Real
  (@instHSub.{0} Real
    (@SubNegMonoid.toSub.{0} Real
      (@AddGroup.toSubNegMonoid.{0} Real
        (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  Real.pi
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3711 p3941)

noncomputable def p3943 :=
@Mathlib.Tactic.CancelDenoms.derive_trans.{0} Real Real.instMul
  (@HSub.hSub.{0, 0, 0} Real Real Real
    (@instHSub.{0} Real
      (@SubNegMonoid.toSub.{0} Real
        (@AddGroup.toSubNegMonoid.{0} Real
          (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
    Real.pi
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 315 true
      2))
  p3942

noncomputable def p3944 :=
@p3943
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3945 :=
@Eq.trans.{1} Real
  (@HSub.hSub.{0, 0, 0} Real Real Real
    (@instHSub.{0} Real
      (@SubNegMonoid.toSub.{0} Real
        (@AddGroup.toSubNegMonoid.{0} Real
          (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
    Real.pi
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 315 true
      2))
  p3942

noncomputable def p3946 :=
@congrArg.{1, 1} Real Real
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 315 true
    2)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3711 p3941)

noncomputable def p3947 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (NNRat.divNat 315
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 2))
  63 20

noncomputable def p3948 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 315 315 63
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
    (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 2)
  100 20 (Mathlib.Meta.NormNum.IsNat.raw_refl 315)

noncomputable def p3949 :=
@Mathlib.Meta.NormNum.isNat_pow.{0} Nat Nat.instSemiring
  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))))
  (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 2 10 2 100

noncomputable def p3950 :=
p3948
  (p3949
    (@Eq.refl.{1} (Nat → Nat → Nat)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))))
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Nat Nat.instAddMonoidWithOne
      (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) 10
      (@Eq.refl.{1} Nat (@OfNat.ofNat.{0} Nat 10 (instOfNatNat 10))))
    (Mathlib.Meta.NormNum.IsNat.raw_refl 2)
    (@Mathlib.Meta.NormNum.IsNatPowT.run 10 2 100
      (@Mathlib.Meta.NormNum.IsNatPowT.bit0 10 1 10)))

noncomputable def p3951 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    315)
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100)

noncomputable def p3952 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
    (@instHMul.{0} NNRat
      (@Distrib.toMul.{0} NNRat
        (@instDistribOfSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    315)
  (@Inv.inv.{0} NNRat
    (@InvOneClass.toInv.{0} NNRat
      (@DivInvOneMonoid.toInvOneClass.{0} NNRat
        (@DivisionMonoid.toDivInvOneMonoid.{0} NNRat
          (@GroupWithZero.toDivisionMonoid.{0} NNRat
            (@DivisionSemiring.toGroupWithZero.{0} NNRat
              (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    (@Nat.cast.{0} NNRat
      (@AddMonoidWithOne.toNatCast.{0} NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
            (@Semiring.toNonAssocSemiring.{0} NNRat
              (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
      100))

noncomputable def p3953 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    315)
  315

noncomputable def p3954 :=
p3953
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    315 315 (Mathlib.Meta.NormNum.IsNat.raw_refl 315))

noncomputable def p3955 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)
  NNRat.instCharZero
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100)
  99

noncomputable def p3956 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} NNRat
  (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))
  (@Nat.cast.{0} NNRat
    (@AddMonoidWithOne.toNatCast.{0} NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
          (@Semiring.toNonAssocSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield))))))
    100)
  100

noncomputable def p3957 :=
p3956
  (@Mathlib.Meta.NormNum.isNat_natCast.{0} NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} NNRat
        (@Semiring.toNonAssocSemiring.{0} NNRat
          (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))
    100 100 (Mathlib.Meta.NormNum.IsNat.raw_refl 100))

noncomputable def p3958 :=
@p3952 315 1 63 1 100 20 5
  (@Eq.refl.{1} (NNRat → NNRat → NNRat)
    (@HMul.hMul.{0, 0, 0} NNRat NNRat NNRat
      (@instHMul.{0} NNRat
        (@Distrib.toMul.{0} NNRat
          (@instDistribOfSemiring.{0} NNRat
            (@DivisionSemiring.toSemiring.{0} NNRat (@Semifield.toDivisionSemiring.{0} NNRat NNRat.instSemifield)))))))
  p3954 (@p3955 1 p3957)

noncomputable def p3959 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 63 20
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 315 true
    2)
  p3711 p3941
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 315 2
    63 20
    (p3947
      (p3950
        (@p3951 63 20
          (p3958 (@Eq.refl.{1} Nat (Nat.mul 315 1))
            (@Eq.refl.{1} Nat 100))))))
  (@Eq.refl.{1} Real p3711)

noncomputable def p3960 :=
@p3945 p3942
  (p3946
    (@HSub.hSub.{0, 0, 0} Real Real Real
      (@instHSub.{0} Real
        (@SubNegMonoid.toSub.{0} Real
          (@AddGroup.toSubNegMonoid.{0} Real
            (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
      Real.pi)
    (p3959 (@Eq.refl.{1} Real p3941)))

noncomputable def p3961 :=
@congrArg.{1, 1} Real Real
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3711 p3941)

noncomputable def p3962 :=
@p3961
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3711 p3941)

noncomputable def p3963 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 63 20
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3711 p3941)

noncomputable def p3964 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  p3711
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p3941)

noncomputable def p3965 :=
@p3964 63 1 63 1 20 20 1
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p3711 63
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p3711 63
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 63
          (@instOfNatAtLeastTwo.{0} Real 63
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 61))))))

noncomputable def p3966 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  p3941 19 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p3941 20
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p3941 20
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 20
          (@instOfNatAtLeastTwo.{0} Real 20
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3967 :=
@p3963 p3711 p3941
  (@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) p3711
    p3941 63 20
    (p3965 p3966 (@Eq.refl.{1} Nat (Nat.mul 63 1))
      (@Eq.refl.{1} Nat 20)))
  (@Eq.refl.{1} Real p3711)

noncomputable def p3968 :=
p3960
  (p3962
    (@HSub.hSub.{0, 0, 0} Real Real Real
      (@instHSub.{0} Real
        (@SubNegMonoid.toSub.{0} Real
          (@AddGroup.toSubNegMonoid.{0} Real
            (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
      Real.pi)
    (p3967 (@Eq.refl.{1} Real p3941)))

noncomputable def p3969 :=
@Mathlib.Tactic.CancelDenoms.sub_subst.{0} Real
  (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3970 :=
@p3969 Real.pi
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3711 p3941)

noncomputable def p3971 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@inferInstance.{1} (Mul.{0} Real)
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3972 :=
@Mathlib.Tactic.CancelDenoms.div_subst.{0} Real Real.instField
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3973 :=
@p3972
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3974 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@inferInstance.{1} (Mul.{0} Real)
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  p3711

noncomputable def p3975 :=
@HDiv.hDiv.{0, 0, 0} Real Real Real
  (@instHDiv.{0} Real
    (@DivInvMonoid.toDiv.{0} Real
      (@DivisionRing.toDivInvMonoid.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3976 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne'.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))
  (p3975 p3941)
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  1

noncomputable def p3977 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3978 :=
p3710
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p3941)

noncomputable def p3979 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3980 :=
p3979
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p3941)

noncomputable def p3981 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3982 :=
@p3981
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p3941)

noncomputable def p3983 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3984 :=
@p3982 20 1 1 1 20 1 20
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@p3983 20
    (@p3828 20
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 20
          (@instOfNatAtLeastTwo.{0} Real 20
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3985 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (p3975 p3941) 1
  (@p3977 p3941 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
      (@DivisionSemiring.toSemiring.{0} Real
        (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
      p3978 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
        p3980 1
        (p3984 p3966 (@Eq.refl.{1} Nat (Nat.mul 20 1))
          (@Eq.refl.{1} Nat 20)))))

noncomputable def p3986 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3987 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  p3986
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3988 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real Real.semiring
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3989 :=
@p3988 1 20 20
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (p3747
    (@Nat.cast_one.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))
  (@p3828 20
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 20
        (@instOfNatAtLeastTwo.{0} Real 20
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 18)))))
  (@Eq.refl.{1} Nat 20)

noncomputable def p3990 :=
@p3973 p3711 p3941 p3712
  (@rfl.{1} Real p3974)
  (p3976 p3985
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@p3987 20 p3989
    (@p3828 20
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 20
          (@instOfNatAtLeastTwo.{0} Real 20
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3991 :=
@Eq.mp.{0}
  (p3939
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    p3713
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@p3940 p3713
    (fun (_a : Real) =>
      @LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder)) _a
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
    (@p3944 p3713 p3968
      (@p3970 (p3710 Real.pi) p3712
        (@rfl.{1} Real (p3971 Real.pi)) p3990)))

noncomputable def p3992 :=
@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (@HSub.hSub.{0, 0, 0} Real Real Real
    (@instHSub.{0} Real
      (@SubNegMonoid.toSub.{0} Real
        (@AddGroup.toSubNegMonoid.{0} Real
          (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
    Real.pi
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 315 true
      2))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 19 (instOfNatNat 19))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 18 (instOfNatNat 18))))))

noncomputable def p3993 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 20
    (@instOfNatAtLeastTwo.{0} Real 20 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 19 (instOfNatNat 19))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 18 (instOfNatNat 18))))))
  0 20
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p3994 :=
p3993
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 20
      (@instOfNatAtLeastTwo.{0} Real 20 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 19 (instOfNatNat 19))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 18 (instOfNatNat 18))))))
    20
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 20
        (@instOfNatAtLeastTwo.{0} Real 20
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 18)))))

noncomputable def p3995 :=
p3991
  (p3992
    (@Mathlib.Tactic.Linarith.sub_neg_of_lt.{0} Real Real.instRing Real.partialOrder Real.instIsOrderedRing Real.pi
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 315
        true 2)
      Real.pi_lt_d2)
    (p3994 (@Eq.refl.{1} Bool false)))

noncomputable def p4771 :=
nat_lit
  61832600368276133515125630254911797508782837275302959978515764023224306276632966792579100265310761247399417856504034834837841258576687802491886538775473291979151693037174784

noncomputable def p4831 :=
nat_lit 69206016000000000000000000

noncomputable def p4973 :=
nat_lit
  3599131035634557106248430806148785487095757694641533306480604458089470064537190296255232548883112685719936728506816716098566612844395439751206812144692131084107776

noncomputable def p4996 :=
nat_lit 951160241300648755200000000

noncomputable def p5018 :=
nat_lit 73786976294838206464000000000000000

noncomputable def p5362 :=
nat_lit 1532495540865888858358347027150309183618739122183602176

noncomputable def p5940 :=
nat_lit 87112285931760246646623899502532662132736

noncomputable def p5990 :=
nat_lit 25711008708143844408671393477458601640355247900524685364822016000000000

noncomputable def p5994 :=
nat_lit 87112285931760246646623899502532662132736000000

noncomputable def p6033 :=
@OfNat.ofNat.{0} Real 1000
  (@instOfNatAtLeastTwo.{0} Real 1000
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 998))

noncomputable def p6044 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@FloorSemiring.instCharZero.{0} Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  p6033 999 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p6033 1000
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p6033 1000
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 1000
          (@instOfNatAtLeastTwo.{0} Real 1000
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p6050 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6053 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 1600
    (@instOfNatAtLeastTwo.{0} Real 1600
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 1598
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 1598 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p6055 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat
      (@NPow.toPow.{0} Real
        (@Monoid.toNPow.{0} Real
          (@Semiring.toMonoid.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 32000))

noncomputable def p6057 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat
      (@NPow.toPow.{0} Real
        (@Monoid.toNPow.{0} Real
          (@Semiring.toMonoid.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32000)

noncomputable def p6089 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring p3705
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p6050 Real.pi)

noncomputable def p6090 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat
      (@NPow.toPow.{0} Real
        (@Monoid.toNPow.{0} Real
          (@Semiring.toMonoid.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
    Real.pi
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)

noncomputable def p6091 :=
@p6089
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6090
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p3762
    (p3746
      (p3747
        (@Nat.cast_one.{0} Real
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
    p3763 p3773)

noncomputable def p6092 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6093 :=
@p6092
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1000)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  Real.pi

noncomputable def p6094 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6095 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6096 :=
@p6093
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3777
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6090
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p6094 1000
    (@p6095 1000
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 1000
          (@instOfNatAtLeastTwo.{0} Real 1000
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p6097 :=
p6096
  (@Mathlib.Tactic.Ring.Common.atom_pf.{0} Real Real.instCommSemiring p3777 Real.pi
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@rfl.{1} Nat
      (@Nat.rawCast.{0} Nat
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
            (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
        1))
    (@Eq.mpr.{0} (@Eq.{1} Real p3777 p3777)
      (@Eq.{1} Real p3777 p3777)
      (@id.{0}
        (@Eq.{1} Prop (@Eq.{1} Real p3777 p3777)
          (@Eq.{1} Real p3777 p3777))
        p3782)
      (@Eq.refl.{1} Real p3777)))

noncomputable def p6098 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3777
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6090
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p6099 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)
  p3777
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p6090

noncomputable def p6100 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)
  Real.pi

noncomputable def p6101 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1000)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1))
  1000

noncomputable def p6102 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  1000 1

noncomputable def p6103 :=
@p6102 1000
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Eq.refl.{1} Nat 1000)

noncomputable def p6104 :=
@p6099
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6090
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p6100
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p6101
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6103))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1000))

noncomputable def p6105 :=
@p6098
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6090
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p6104
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p6090
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p6106 :=
p6105
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p3777
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6090
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p6107 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6090
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p6108 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  p6090
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p6057

noncomputable def p6109 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32000)
  Real.pi

noncomputable def p6110 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1000))
  32000

noncomputable def p6111 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)
  32 1000

noncomputable def p6112 :=
@p6111 32000
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1000)
  (@Eq.refl.{1} Nat 32000)

noncomputable def p6113 :=
@p6108
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p6109
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p6110
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6112))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32))

noncomputable def p6114 :=
@p6107
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p6113
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p6057
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p6115 :=
p6114
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6090
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6057
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p6117 :=
@Neg.neg.{0} Real
  (@NegZeroClass.toNeg.{0} Real
    (@SubNegZeroMonoid.toNegZeroClass.{0} Real
      (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
        (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
          (@AddCommGroup.toDivisionAddCommMonoid.{0} Real
            (@Ring.toAddCommGroup.{0} Real
              (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))))))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32000)

noncomputable def p6118 :=
@p3730
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32000)
  (Int.ofNat 32000) (Int.negOfNat 32000) p3731

noncomputable def p6119 :=
p6118
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32000)
    32000
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32000))

noncomputable def p6120 :=
@Mathlib.Tactic.Ring.Common.neg_mul.{0} Real Real.commRing Real.pi
  (@Nat.rawCast.{0} Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
        (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32000)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 32000))
  (@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real p6117 (Int.negOfNat 32000)
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p6119 (@Eq.refl.{1} Int (Int.negOfNat 32000))))

noncomputable def p6121 :=
@Mathlib.Tactic.Ring.Common.neg_add.{0} Real Real.commRing p6057
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p6055
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p6120 (@Mathlib.Tactic.Ring.Common.neg_zero.{0} Real Real.commRing)

noncomputable def p6131 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 1600
    (@instOfNatAtLeastTwo.{0} Real 1600
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 1598
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 1598 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p6132 :=
@p6131
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1600)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p3713

noncomputable def p6133 :=
@p6132
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6057
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p6134 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 1600
    (@instOfNatAtLeastTwo.{0} Real 1600
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 1598
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 1598 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p6135 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 1600
    (@instOfNatAtLeastTwo.{0} Real 1600
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 1598
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 1598 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p6136 :=
p6133
  (@p6134 1600
    (@p6135 1600
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 1600
          (@instOfNatAtLeastTwo.{0} Real 1600
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 1598))))))

noncomputable def p6137 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1600)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p3819
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6057
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p6138 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1600)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 63))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p3819
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 100800))

noncomputable def p6139 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1600)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 63)))
  (Int.negOfNat 100800)

noncomputable def p6140 :=
@Mathlib.Meta.NormNum.isInt_mul.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@Ring.toSemiring.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1600)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 63))

noncomputable def p6141 :=
@p6140 (Int.ofNat 1600) (Int.negOfNat 63) (Int.negOfNat 100800)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real
            (@Ring.toSemiring.{0} Real
              (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))))))))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1600)
    1600
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1600))

noncomputable def p6142 :=
@p6138
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6057
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@p6139 (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p6141
      (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 63))
      (@Eq.refl.{1} Int (Int.negOfNat 100800))))

noncomputable def p6143 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1600)
  p3819
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p6057

noncomputable def p6144 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1600)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32000)
  Real.pi

noncomputable def p6145 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1600)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      20))
  32000

noncomputable def p6146 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1600)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  1600 20

noncomputable def p6147 :=
@p6146 32000
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1600)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    20)
  (@Eq.refl.{1} Nat 32000)

noncomputable def p6148 :=
@p6143
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p6144
    (@Nat.rawCast.{0} Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
          (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
      1)
    (@p6145
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6147))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1600))

noncomputable def p6149 :=
p6142
  (p6148
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p6057
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p6150 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 100800))

noncomputable def p6151 :=
p6149
  (p6150
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p6057
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p6152 :=
@p6137
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6057
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  p6151

noncomputable def p6153 :=
p6152
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
        (Int.negOfNat 63))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p3819
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p6154 :=
p6153
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
        (Int.negOfNat 100800))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p6057
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p6155 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    100800)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6055
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 100800))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p6156 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    100800)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 100800))
  (Int.ofNat 100800) (Int.negOfNat 100800)

noncomputable def p6157 :=
@p6156 (Int.ofNat 0)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      100800)
    100800
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      100800))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 100800))

noncomputable def p6158 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      100800)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 100800)))
  0 (p6157 (@Eq.refl.{1} Int (Int.ofNat 0)))

noncomputable def p6159 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 32000))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32000)
  (Int.negOfNat 32000) (Int.ofNat 32000)

noncomputable def p6160 :=
@p6159 (Int.ofNat 0)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 32000))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32000)
    32000
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32000))

noncomputable def p6161 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 32000))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      32000))
  0 (p6160 (@Eq.refl.{1} Int (Int.ofNat 0)))

noncomputable def p6162 :=
@Mathlib.Tactic.Ring.Common.add_overlap_pf_zero.{0} Real Real.instCommSemiring
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 32000))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    32000)
  Real.pi
  (@Nat.rawCast.{0} Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
        (@Semiring.toNonAssocSemiring.{0} Nat (@CommSemiring.toSemiring.{0} Nat Nat.instCommSemiring))))
    1)
  p6161

noncomputable def p6163 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero.{0} Real Real.instCommSemiring p6055
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p6057
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  p6162

noncomputable def p6171 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6180 :=
@Mathlib.Tactic.CancelDenoms.sub_subst.{0} Real
  (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6184 :=
@Mathlib.Tactic.CancelDenoms.div_subst.{0} Real Real.instField
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6185 :=
@p6184
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6187 :=
@HDiv.hDiv.{0, 0, 0} Real Real Real
  (@instHDiv.{0} Real
    (@DivInvMonoid.toDiv.{0} Real
      (@DivisionRing.toDivInvMonoid.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6188 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne'.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))
  (p6187 p6033)
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  1

noncomputable def p6189 :=
@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6190 :=
p6050
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p6033)

noncomputable def p6191 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6192 :=
p6191
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p6033)

noncomputable def p6193 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6194 :=
@p6193
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p6033)

noncomputable def p6195 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6196 :=
@p6194 1000 1 1 1 1000 1 1000
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@p6195 1000
    (@p6095 1000
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 1000
          (@instOfNatAtLeastTwo.{0} Real 1000
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p6197 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (p6187 p6033) 1
  (@p6189 p6033 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
      (@DivisionSemiring.toSemiring.{0} Real
        (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
      p6190 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
        p6192 1
        (p6196 p6044 (@Eq.refl.{1} Nat (Nat.mul 1000 1))
          (@Eq.refl.{1} Nat 1000)))))

noncomputable def p6198 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6199 :=
@Mathlib.Meta.NormNum.isNat_eq_true.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  p6198
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6200 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real Real.semiring
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6201 :=
@p6200 1 1000 1000
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (p3747
    (@Nat.cast_one.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))
  (@p6095 1000
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 1000
        (@instOfNatAtLeastTwo.{0} Real 1000
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 998)))))
  (@Eq.refl.{1} Nat 1000)

noncomputable def p6203 :=
@Mathlib.Tactic.CancelDenoms.mul_subst.{0} Real (@Field.toCommRing.{0} Real Real.instField)
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6204 :=
@p6203
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6205 :=
@p6204
  (@OfNat.ofNat.{0} Real 32
    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
  Real.pi p3705 (p6050 Real.pi)

noncomputable def p6206 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@inferInstance.{1} (Mul.{0} Real)
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6207 :=
p6205 (@rfl.{1} Real p3930) (@rfl.{1} Real (p6206 Real.pi))
  (@p6199 1000 p6201
    (@p6095 1000
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 1000
          (@instOfNatAtLeastTwo.{0} Real 1000
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p6211 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 999 (instOfNatNat 999))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 998 (instOfNatNat 998))))))
  0 1000
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p6212 :=
p6211
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 1000
      (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 999 (instOfNatNat 999))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 998 (instOfNatNat 998))))))
    1000
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 1000
        (@instOfNatAtLeastTwo.{0} Real 1000
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 998)))))

noncomputable def p6213 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 1600
    (@instOfNatAtLeastTwo.{0} Real 1600 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1599 (instOfNatNat 1599))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1598 (instOfNatNat 1598))))))
  0 1600
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p6214 :=
p6213
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 1600
      (@instOfNatAtLeastTwo.{0} Real 1600 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1599 (instOfNatNat 1599))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1598 (instOfNatNat 1598))))))
    1600
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 1600
        (@instOfNatAtLeastTwo.{0} Real 1600
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 1598)))))

noncomputable def p8159 :=
nat_lit 12259964326927110866866776217202473468949912977468817408

noncomputable def p8228 :=
nat_lit 17422457186352049329324779900506532426547200000

noncomputable def p9404 :=
nat_lit 1902320482601297510400000000

noncomputable def p10404 :=
nat_lit 205688069665150755269371147819668813122841983204197482918576128000000

noncomputable def p10408 :=
nat_lit 3484491437270409865864955980101306485309440000

theorem d196 : Enclosure.Real.IsNear Real.pi false 226375608064910080 72057594037927936 1
  1000000000000000 :=
BSN.pi_near_15

theorem d197 : p2306 500000000000000 :=
@p501 1 1000000000000000 884279719003555 140737488355328
  1 500000000000000 (Enclosure.Real.IsNear.const false 2 1)
  d196 (Eq.refl true)

noncomputable def p11843 :=
Enclosure.Real.IsNear
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 11199533475045 70368744177664

noncomputable def p11844 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 11199533475045 70368744177664

noncomputable def p11845 :=
@p11844 1 70368744177664 11199533475045 70368744177664
  1 70368744177664
  (@p2309 5599766737522 5599766737523 35184372088832 d197
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))

theorem d198 : p11843 1 70368744177664 :=
p11845 (Eq.refl true)

theorem d199 : p2314 250000000000000 :=
@p2315 1 1000000000000000 884279719003555 70368744177664
  1 250000000000000 (Enclosure.Real.IsNear.const false 4 1)
  d196 (Eq.refl true)

theorem d200 : p2317 p2318 :=
@p2319 p2316 p1071 p2318 d196
  d196 (Eq.refl true)

noncomputable def p11846 :=
@p2321 p1068 p2316 p1071 p2318
  p1068 p1070 p1071 p1072
  (Enclosure.Real.IsNear.const false 4 1) d200 (Eq.refl true)

theorem d201 : p2320 p1071 p1072 :=
p11846

noncomputable def p11847 :=
@p2328 p2318 226375608064910080 72057594037927936 1
  1000000000000000 p1059 p2325 p1062
  p2326 d200 d196

theorem d202 : p2323 p1059 p1061 p1062 p1063 :=
p2327 (p11847 (Eq.refl true)) (Eq.refl true)

noncomputable def p11848 :=
Enclosure.Real.IsNear
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))
  false 74269213037

noncomputable def p11849 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))
  false 74269213037

noncomputable def p11850 :=
@p2337 p1068 p2316 p1071 p2318
  p2332 p2333 p2334 p2336
  (Enclosure.Real.IsNear.const false 96 1) d200 (Eq.refl true)

noncomputable def p11851 :=
@p2335 p2336 37134606518 37134606519 35184372088832
  p11850 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d203 : p11848 70368744177664 1 70368744177664 :=
@p11849 70368744177664 1 70368744177664 74269213037
  70368744177664 1 70368744177664 p11851 (Eq.refl true)

noncomputable def p12154 :=
nat_lit
  1842755090244893238399196572748178169393027939656465052918069482541808673043041431682679065028153695088607604995490158642466105776330465152617887818082371115063181312

noncomputable def p12162 :=
nat_lit
  26187124863169134960105517574620793217733136368344518315866330944769070371237396439066160738607233257207093473020480568073738052367083144426628220715008

noncomputable def p12185 :=
nat_lit 475580120650324377600000000

noncomputable def p12189 :=
nat_lit 9903520314283042199192993792

noncomputable def p12191 :=
nat_lit 302231454903657293676544000000000000000

noncomputable def p12201 :=
nat_lit 10141204801825835211973625643008

noncomputable def p12205 :=
nat_lit
  724395325779541883127972740267467641917054236400314122627846279324277345529845529720229616430545782367401373900304422017855283570911757419651361948377693681253993101024836647459626987279301240215309090298978493065512302911076452246852449566697292461376960433893740547516518998105653248000

noncomputable def p12208 :=
nat_lit
  110832484844269908118579829260922549213309298169248060762060480736614433866066366047195131313873504702212410206746576568731858386349498885206658378101787133231860944456800007061322929053733089752942290815743709439023382345394697193768424783704685746590674946385742303770027406710164946944000

noncomputable def p12222 :=
nat_lit 121416805764108066932466369176469931665150427440758720078238275608681517825325531136

noncomputable def p12261 :=
nat_lit 24519928653854221733733552434404946937899825954937634816

noncomputable def p12265 :=
nat_lit 4951760157141521099596496896

noncomputable def p12284 :=
nat_lit 696898287454081973172991196020261297061888

noncomputable def p12286 :=
nat_lit 21267647932558653966460912964485513216000000000000000

noncomputable def p12302 :=
nat_lit
  1961848167734627781231279786490110123562935172081945904365228885641390576241135963171198423910219637317516664724571812977087383204305824875125189264690483141925255757791594586255777610605882706058377906934724181744813017762103296000

noncomputable def p12305 :=
nat_lit
  111825345560873783530182947829936277043087304808670916548818046481559262845744749900758310162882519327098449889300593339693980842645432017882135788087357539089739578194120891416579323804535314245327540695279278359454342012439887872000

noncomputable def p12314 :=
nat_lit 348449143727040986586495598010130648530944

noncomputable def p12328 :=
nat_lit
  115402833396154575366545869793535889621349127769526229668542875625964151543596233127717554347659978665736274395563047822181610776723872051477952309687675478936779750458329093309163388859169570944610465113807304808518412809535488000

noncomputable def p12330 :=
nat_lit
  17656633509611650031081518078410991112066416548737513139287059970772515186170223668540785815191976735857649982521146316793786448838752423876126703382214348277327301820124351276301998495452944354525401162412517635703317159858929664000

noncomputable def p12342 :=
nat_lit 75153362648762663292463379097258784876021841565066235862633311089030688803667470190838367948312598497021919232

noncomputable def p12348 :=
nat_lit 1947976174183728650649600000000000000000000000

noncomputable def p12357 :=
nat_lit
  12314720538252212013175536584546949912589922018805340084673386748512714874007374005243903479319278300245823356305175174303539820705499876134073153122420792581317882717422223006813658783748121083660254535082634382113709149488299688196491642633853971843408327376193589307780822967796105216000

noncomputable def p12359 :=
nat_lit
  701939070680376084751005585319176145017625555071904384826383044665224747818420318298902498321198863114011931309394984935301769780213492939642169727977985177135119314893066711388378550673642901768634508499710159780481421520833082227200023630129676395074274660443034590543506909164377997312000

noncomputable def p12388 :=
nat_lit 431359146674410236714672241392314090778194310760649159697657763987456

noncomputable def p12402 :=
nat_lit 973988087091864325324800000000000000000000000

noncomputable def p12450 :=
nat_lit 1393796574908163946345982392040522594123776

noncomputable def p13950 :=
nat_lit 1298650782789152433766400000000000000000000000

noncomputable def p13957 :=
nat_lit 3895952348367457301299200000000000000000000000

noncomputable def p13995 :=
nat_lit 862718293348820473429344482784628181556388621521298319395315527974912

noncomputable def p14058 :=
nat_lit 16732987923012628099756482310963200000000000000000000000000000000000000

noncomputable def p14069 :=
nat_lit 5577662641004209366585494103654400000000000000000000000000000000000000

noncomputable def p14074 :=
nat_lit 196159429230833773869868419475239575503198607639501078528

noncomputable def p14077 :=
nat_lit 71867635893702203483464717089589446259507200000000000000000000000000000000000000000000000000000

noncomputable def p14421 :=
nat_lit 60446290980731458735308800000000000000

noncomputable def p14458 :=
nat_lit 300613450595050653169853516389035139504087366260264943450533244356122755214669880763353471793250393988087676928

noncomputable def p14478 :=
nat_lit 24530819718383685455689290099913197656578457600000000000000000000000000000000000000

noncomputable def p14484 :=
nat_lit
  3450873173395281893717377931138512726225554486085193277581262111899648000000000000000000000000000000000000000000000

noncomputable def p14489 :=
nat_lit 22835963083295358096932575511191922182123945984000000000000000000000000000000

noncomputable def p14492 :=
nat_lit 151115727451828646838272000000000000000

noncomputable def p14536 :=
nat_lit 324518553658426726783156020576256000000000000000000000000000000

noncomputable def p14587 :=
nat_lit 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576

noncomputable def p14600 :=
nat_lit 215679573337205118357336120696157045389097155380324579848828881993728

noncomputable def p14639 :=
nat_lit 11423053088776620782767091924284211200000000000000000000000

noncomputable def p15590 :=
nat_lit
  18994974788624060034901396673733261424848382610558035309863297026273392928713928882019081685863816714406389484898116195691524211215134748842126782327423468733794422534822715680801397629

noncomputable def p15591 :=
nat_lit
  8498207885068273579033411304839498037273489883632510771191106211206456957773635883826600036243668570702229271779944016245545269402443315830552319660265397631101300333366291504507650048

noncomputable def p15592 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  true p15590 p15591

noncomputable def p15593 :=
nat_lit
  1400958535703603935813978178447273072313877812725258230458396517068525565664464171023266961188273207510891238807246879119352575682727312108819827364452190124100406409634622004238981797579634622806265980657112558320190272438033147577

noncomputable def p15594 :=
nat_lit
  431895724276146852749811696737854258451490923356983996777672534970736407744462835550627905865973522286392407420818005931827993541327452770144817457363055730092933120000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15595 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  true p15590

noncomputable def p15596 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    12)

noncomputable def p15597 :=
@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p15598 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p15597
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p15599 :=
Real.sqrt
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p15600 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15598
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p15599)))

noncomputable def p15601 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  (p15596 p15600) true p15590

noncomputable def p15602 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  101656100 100000 12
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))

noncomputable def p15603 :=
@Enclosure.Real.IsNear.subLit_tf
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    12)

noncomputable def p15604 :=
nat_lit
  1122623990964671339023627350683797617048457773523016654317577697823520237795053674702965400532979495845254469074666368899762205833967033888062829539522591805609730323431935437686938493

noncomputable def p15605 :=
nat_lit
  28415902705303645446162898470782391888017064227581193311092417220057652585243059950064966334940923668886713457041193562571911992577667309964293627502961621060406409634622004238981797579634622806265980657112558320190272438033147577

noncomputable def p15606 :=
nat_lit
  652662364043878805509136938387260320377137320566734927727008695668626203070271871103534386309901106384908919128605559620024260732489601332080867177455956497236204598194151880055587023101175529472

noncomputable def p15607 :=
@p15603 p15600 72261035001 34359738368 218387
  68719476736 p15604 p15591 p15605
  p15594 p15606 p15590

noncomputable def p15608 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    12)

noncomputable def p15609 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    12)

noncomputable def p15610 :=
p15609
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    12)

noncomputable def p15611 :=
@p15608 p15610 true 72261035001 34359738368
  218387 68719476736
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    12)

noncomputable def p15612 :=
@Enclosure.Real.IsNear.addLit_tt
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    12)

noncomputable def p15613 :=
@p15612
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    12)

noncomputable def p15614 :=
@p15613 144522070002 137438953472 218387 137438953472
  144522070002 137438953472 218387 137438953472
  39725924109364009893888 72261035001 34359738368

noncomputable def p15615 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p15616 :=
p15615 11 12 101656100 100000 286
  137438953472 68719476736 2305843009213693952 false 285405146047951
  3368

noncomputable def p15617 :=
p15616 341522969406 43 39675208392 8 true
  105766209318 204786 true 29644718489 7244019458077122842 1

noncomputable def p15618 :=
p15617 false 134254239590 true true 144522070002 218387
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 134254239590 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p15619 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  Real.cos Real.sin

noncomputable def p15620 :=
p15619 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101656100
  100000 168 229 137438953472 68719476736

noncomputable def p15621 :=
p15620 2305843009213693952 false 285405146047951 3368
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p15622 :=
p15621 8 true 108181824726 175683 true 31429024297
  true 178493611336 7244019458077122842 1 false

noncomputable def p15623 :=
p15622 133861050192 false false 132382963940 true true
  105766209318 204786 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 168 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 133861050192 137438953472)

noncomputable def p15624 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  Real.sin Real.sin

noncomputable def p15625 :=
p15624 BSN.quadSignPos BSN.quadSignPos 7 8 9 101656100
  100000 23 99 137438953472 68719476736

noncomputable def p15626 :=
p15625 2305843009213693952 false 285405146047951 3368
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p15627 :=
p15626 8 true 198359096946 143317 true 158757386562
  true 207289779478 7244019458077122842 1 false

noncomputable def p15628 :=
p15627 125734679524 false false 137170049885 false true
  108181824726 175683 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 23 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 125734679524 137438953472)

noncomputable def p15629 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  Real.cos Real.cos

noncomputable def p15630 :=
p15629 BSN.quadSignNeg BSN.quadSignNeg 5 6 7 101656100
  100000 162 62 137438953472 68719476736

noncomputable def p15631 :=
p15630 2305843009213693952 false 285405146047951 3368
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p15632 :=
p15631 8 true 130285500979 106282 false 95374785423
  false 147060552015 7244019458077122842 1 false

noncomputable def p15633 :=
p15632 105653477820 true false 65987006829 true true
  198359096946 143317 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 162 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 105653477820 137438953472)

noncomputable def p15634 :=
p15629 BSN.quadSignPos BSN.quadSignPos 3 4 5 101656100
  100000 424 280 137438953472 68719476736

noncomputable def p15635 :=
p15634 2305843009213693952 false 285405146047951 3368
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p15636 :=
p15635 16 true 194741566682 62622 false 182150724687
  false 93590483680 7244019458077122842 1 false

noncomputable def p15637 :=
p15636 33400067575 false false 106785733705 false true
  130285500979 106282 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 424 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 33400067575 137438953472)

noncomputable def p15638 :=
p15624 BSN.quadSignNeg BSN.quadSignPos 1 2 3 101656100
  100000 873 611 137438953472 68719476736

noncomputable def p15639 :=
p15638 2305843009213693952 false 285405146047951 3368
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p15640 :=
p15639 16 true 137438334376 3418 false 91281631427
  false 4505679963 7244019458077122842 1 false

noncomputable def p15641 :=
p15640 84717221645 true false 4504872938 false true
  194741566682 62622 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 873 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 84717221645 137438953472)

noncomputable def p15642 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    1)

noncomputable def p15643 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    1)

noncomputable def p15644 :=
@p15643
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5)))
  true 17179791797

noncomputable def p15645 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5)))
  true 17179791797

noncomputable def p15646 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35675643255993)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false 35675643255993

noncomputable def p15647 :=
nat_lit 371548245794855656250616489476862335621357388314205638930591

noncomputable def p15648 :=
nat_lit 178921798620347223922940755093566505811639236628054016000

noncomputable def p15649 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  false p15647 p15648

noncomputable def p15650 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101656100 400000)
      (Real.log (Enclosure.sfrac false 41335860668840000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203312200))))))

noncomputable def p15651 :=
nat_lit 521085182976849665812700133824480000000000000000

noncomputable def p15652 :=
nat_lit 3178289606970480888089638595303059279680000000000000

noncomputable def p15653 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p15650 (Enclosure.sfrac false 101656100 200000))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 101656100 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p15651 p15652))
  false

noncomputable def p15654 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  101656100 100000 41335860668840000 160000000000

noncomputable def p15655 :=
p15654 203312200 400000 200000 p15651
  p15652
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15656 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (p15650 (Enclosure.sfrac false 101656100 200000))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101656100 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p15651 p15652) 37408626256283832399159
  18014398509481984000

noncomputable def p15657 :=
nat_lit 118895438654353810000197276632595947398834364260545804457789120000000000000

noncomputable def p15658 :=
@p15656 1695513633491111773 p4831 p15651
  p15652 0 1 p15657 p15647
  p15648 1695513633491111773 p4831

noncomputable def p15659 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p15650 (Enclosure.sfrac false 101656100 200000))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101656100 200000) (Real.log Real.pi))
  47890193758205356389687 18014398509481984000 1281271557221
  132000000000000000000

noncomputable def p15660 :=
nat_lit 5141402443488831188733859932930048000

noncomputable def p15661 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101656100 400000)
      (Real.log (Enclosure.sfrac false 41335860668840000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203312200))))))

noncomputable def p15662 :=
@p15661 (Enclosure.sfrac false 101656100 200000)
  57046561239804113958199 18014398509481984000 1281271557221
  132000000000000000000 101656100 200000 0

noncomputable def p15663 :=
nat_lit 9578038751641071277937400000

noncomputable def p15664 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101656100 400000)
    (Real.log (Enclosure.sfrac false 41335860668840000 160000000000)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast 100000)
          (@Nat.cast.{0} Real Real.instNatCast 203312200)))))
  57053633262441439550199

noncomputable def p15665 :=
nat_lit 128457435971174993964156487498414948352

noncomputable def p15666 :=
@p15664 18014398509481984000 1271271540721 132000000000000000000
  884002829665699 2251799813685248 20000033 264000000000000000
  p15665 57046561239804113958199 18014398509481984000 1281271557221

noncomputable def p15667 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101656100 400000)
  (Real.log (Enclosure.sfrac false 41335860668840000 160000000000)) 101656100
  400000 0 1 56124161031597159 4503599627370496

noncomputable def p15668 :=
nat_lit 30854583826706869830593544192

noncomputable def p15669 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 41335860668840000)
      (@Nat.cast.{0} Real Real.instNatCast 160000000000)))
  false p15668 p2333

noncomputable def p15670 :=
BSN.log_rat_reduce_isNear 41335860668840000 160000000000 17 82671721337680000
  41943040000000000 46630638156 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p15671 :=
nat_lit
  954723548729647829212117526767553689064598459773326730966576893121618485049001241816032699525630919808052916011154886137203165787325044697297106004765566070262650616521888188946824475252722090218411757022512206136206381389785997607672105894381603512425283484724315807214720717427712674758656000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15672 :=
nat_lit
  36355499221643871176909871006640045594325646216894950669328531125318561489250447522994648073077414132386531882788920636589124866712397674668937344400406606587837606092179922709670496158234759092208783579028038764832474772614451143895686419496310370639191794262204336946310279805087172368793600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15673 :=
nat_lit
  857884263413089866774780517100839772954483252258410576146538779182250690923952232706047872109975215043247930835481687881028675935192294435023894823257808814999522444288568305100336304872103824882893707126504793862203121899082618078901922404680164673313743104381029122065481859072000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15674 :=
BSN.log_dyadic_bound 20364340668840000 62307380668840000 12 11
  p15671 68719476736 26400000000 p15672 p15673
  46630638156 82671721337680000

noncomputable def p15675 :=
p15674 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p15676 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20364340668840000) (BSN.artanhQ 62307380668840000)
  0 11 p15672 p15671 p15673
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p15677 :=
p15670 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p15675 (p15676 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p15678 :=
@p15667 1250561 33000000000000000 57053633262441439550199
  18014398509481984000 1271271540721 132000000000000000000
  (Enclosure.Real.IsNear.const false 101656100 400000)
  (BSN.isNear_log_sfrac 41335860668840000 160000000000 56124161031597159
    4503599627370496 1250561 33000000000000000 false
    (@p15669 1000448800000000 p2422 56124161031597159
      4503599627370496 1250561 33000000000000000
      (p15677 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p15679 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast 100000)
        (@Nat.cast.{0} Real Real.instNatCast 203312200))))
  1 4

noncomputable def p15680 :=
@p15679 0 1 884002829665699 562949953421312 20000033
  66000000000000000 884002829665699 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p15681 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 100000) (@Nat.cast.{0} Real Real.instNatCast 203312200)))
  884279719003555 562949953421312 1

noncomputable def p15682 :=
nat_lit 7593526485971271635959808

noncomputable def p15683 :=
@p15681 2000000000000000 4224996 8589934592 1
  3300000000 p15682 884002829665699 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p15684 :=
BSN.arctan_dyadic_bound_f 100000 203312200 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p15685 :=
p15684 1 4224996 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 203312200) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 203312200) 0 0
    (Eq.refl true))

noncomputable def p15686 :=
p15680
  (p15683
    (p15685 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p15687 :=
@p15659 79968013778087799 137438953472000 1016561
  68719476736000 p15660 37408626256283832399159 18014398509481984000
  1695513633491111773 p4831
  (@p15662 1 p15663 47890193758205356389687
    18014398509481984000 1281271557221 132000000000000000000
    (@p15666 132000000000000000000 p15678 p15686
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101656100 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p15688 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101656100 200000) (Real.log Real.pi)
  101656100 200000 0 1 78665238759 68719476736

noncomputable def p15689 :=
p15687
  (@p15688 1 34359738368 79968013778087799 137438953472000
    1016561 68719476736000
    (Enclosure.Real.IsNear.const false 101656100 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p15690 :=
@p15646 17179869184 211 8589934592 true 17179791797
  17179869184 1 3300000000
  (@p15649 1695513633491111773 p4831 35675643255993
    17179869184 211 8589934592
    (@p15653 p15647 p15648 1695513633491111773
      p4831
      (p15655 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p15658 (p15689 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p15651 p15652)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p15691 :=
nat_lit 7431333797196155695661056

noncomputable def p15692 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35675643255993)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p15691)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p15693 :=
BSN.sin_reduce_arg_pos_rat_q2 35675643255993 17179869184 226375608064910080
  72057594037927936 330 p15691 p2333
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p15694 :=
BSN.cos_dyadic_bound_f 105605604932 35184372088832 1 0 17179869184
  6606445313 0 1 1 0 1

noncomputable def p15695 :=
p15694 1 17179791797 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.cosEvenP 105605604932) (BSN.cosEvenQ 35184372088832) 0
    0 (Eq.refl true))

noncomputable def p15696 :=
p15695
  (@BSN.binarySplit_of_le (BSN.cosOddP 105605604932) (BSN.cosOddQ 35184372088832) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p15697 :=
@BSN.cos_arg_round false 17179791797 17179869184 p15691
  p2333 105605604932 35184372088832 6606445313 6600000000
  p15696 (Eq.refl true)

noncomputable def p15698 :=
p15692 17179791797 17179869184 330 1000000000000000
  6600000000 3300000000 p15693 BSN.pi_near_15 p15697
  (Eq.refl true) (Eq.refl true)

noncomputable def p15699 :=
@p15644 17179869184 2753476307 110729625600000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  (@p15645 17179869184 704889934592 28346784153600000000
    17179791797 17179869184 2753476307 110729625600000000
    (p15690 (Enclosure.sfrac_false_div 35675643255993 17179869184)
      (p15698 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p15700 :=
@p15642 true 17179791797 17179869184 2753476307
  110729625600000000 137438334376 137438953472 3418 137438953472
  p15699 (Eq.refl true)

noncomputable def p15701 :=
p15641 BSN.abs_quadSignPos (BSN.cos_quad_nat3 611 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 4504872938 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p15700
  (@p15649 1695513633491111773 p4831 285405146047951
    137438953472 3368 137438953472
    (@p15653 p15647 p15648 1695513633491111773
      p4831
      (p15655 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p15658 (p15689 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p15651 p15652)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p15702 :=
nat_lit 74917394041192697113748098432696667441368566302983048205756192057888956221825443935408020385

noncomputable def p15703 :=
nat_lit 4820223182678160161977399328444319340589994438272309680466557448369396408096934444850081

noncomputable def p15704 :=
nat_lit 196204418317970823038601818201007123924651956516817447275593080963364192034405910508396010401

noncomputable def p15705 :=
BSN.sin_dyadic_bound_f 91281631427 137438953472 3 2 137438953472
  68719476736 p15702 p2477 p15703
  p15704 p2480

noncomputable def p15706 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 91281631427) (BSN.sinEvenQ 137438953472) 0
  2 p15702 p2477 p15703 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15707 :=
p15705 p15703 84717221645 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15706 (Eq.refl true))

noncomputable def p15708 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 91281631427) (BSN.sinOddQ 137438953472) 0
  2 p15704 p2480 p15703 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15709 :=
nat_lit 412136769643515437811159834448765714161

noncomputable def p15710 :=
BSN.sin_dyadic_bound_f 4505679963 137438953472 2 1 137438953472
  68719476736 p15709 p3178 p15709
  p15709 p3179

noncomputable def p15711 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 4505679963) (BSN.sinEvenQ 137438953472) 0
  1 p15709 p3178 p15709 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15712 :=
p15710 p15709 4504872938 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15711 (Eq.refl true))

noncomputable def p15713 :=
@BSN.binarySplit_of_base (BSN.sinOddP 4505679963) (BSN.sinOddQ 137438953472) 0 1
  p15709 p3179 p15709 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15714 :=
p15701 d93 d95 d97 d99 d103
  (p15707 (p15708 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p15712 (p15713 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p15715 :=
p15637 BSN.abs_quadSignPos (BSN.cos_quad_nat0 280 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 106785733705 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p15714 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p15649 1695513633491111773 p4831 285405146047951
    137438953472 3368 137438953472
    (@p15653 p15647 p15648 1695513633491111773
      p4831
      (p15655 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p15658 (p15689 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p15651 p15652)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p15716 :=
nat_lit
  43676423500984381023543324481686011132906378786996082684226405926887602099279237486309873838593799771632479223815048066490209852688807563476411322634306262772411707683845500166370050368664321

noncomputable def p15717 :=
nat_lit
  1468569332440493258710043264840176914084923477411231729235735501732150450022607143455462746771854912687707149726995257636268599198089843841944932857746847246784380940516352118813441

noncomputable def p15718 :=
nat_lit
  444954922758333611043092104377667425405886271295870457317781823613162361601235520724772021753866438038312320510937124871812867814263468271659000133865536196112314361315112258575555458394551041

noncomputable def p15719 :=
BSN.cos_dyadic_bound_f 182150724687 137438953472 5 4 137438953472
  68719476736 p15716 p2495 p15717
  p15718 p2498

noncomputable def p15720 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 182150724687) (BSN.cosEvenQ 137438953472) 0
  4 p15716 p2495 p15717 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15721 :=
p15719 p15717 33400067575 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15720 (Eq.refl true))

noncomputable def p15722 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 182150724687) (BSN.cosOddQ 137438953472) 0
  4 p15718 p2498 p15717 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15723 :=
nat_lit
  194978528710408488224212098327182744587689554378221992901642843190623362803066362722766503795370012315387540198855196950587350475341824000000

noncomputable def p15724 :=
nat_lit
  451627419094743082248465172134533288879509751250998530413412622304685756760072416506709261735754998492329574697141272576000000000000

noncomputable def p15725 :=
nat_lit
  1182768820654363404562083902456346999796846532792553731595175746992702669815576851203385598099963697543050838122778004697564054285818265600000

noncomputable def p15726 :=
BSN.cos_dyadic_bound_f 93590483680 137438953472 4 3 137438953472
  68719476736 p15723 p2457 p15724
  p15725 p2460

noncomputable def p15727 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 93590483680) (BSN.cosEvenQ 137438953472) 0
  3 p15723 p2457 p15724 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15728 :=
p15726 p15724 106785733705 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15727 (Eq.refl true))

noncomputable def p15729 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 93590483680) (BSN.cosOddQ 137438953472) 0
  3 p15725 p2460 p15724 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15730 :=
p15715 d105 d107 d109 d111 d103
  (p15721 (p15722 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p15728 (p15729 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p15731 :=
p15633 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 65987006829 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p15730 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p15649 1695513633491111773 p4831 285405146047951
    137438953472 3368 137438953472
    (@p15653 p15647 p15648 1695513633491111773
      p4831
      (p15655 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p15658 (p15689 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p15651 p15652)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p15732 :=
nat_lit
  210280343988952961107584181496683459352628663137833913194261405205469352362795817325726498842478902728405983462785749052021924813576760072001

noncomputable def p15733 :=
nat_lit
  566503877133337825771826359092894425378577758531790990312886474837832770778494671261862034147156221481988569506721560322259362649921

noncomputable def p15734 :=
nat_lit
  1275583373592749428960334625297699596457613563000679632128254630639469786457601170955127228811122838363142070107417828362978166668927062644545

noncomputable def p15735 :=
BSN.cos_dyadic_bound_f 95374785423 137438953472 4 3 137438953472
  68719476736 p15732 p2457 p15733
  p15734 p2460

noncomputable def p15736 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 95374785423) (BSN.cosEvenQ 137438953472) 0
  3 p15732 p2457 p15733 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15737 :=
p15735 p15733 105653477820 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15736 (Eq.refl true))

noncomputable def p15738 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 95374785423) (BSN.cosOddQ 137438953472) 0
  3 p15734 p2460 p15733 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15739 :=
nat_lit
  1189400102445226513954840254550526614007806577188866141243426660358268274859358390619359682523744872684036750744300620473610678800182021890625

noncomputable def p15740 :=
nat_lit
  102318532339438402001687452493315617853049386068753178551904104126230004887690275535935230176320880062257114620021245127518808837890625

noncomputable def p15741 :=
nat_lit
  7211942979271478203403831315483067823741284262193908185778978097123410111030748236874092458598795354137960454651482993084669062669206687490625

noncomputable def p15742 :=
BSN.cos_dyadic_bound_f 147060552015 137438953472 4 3 137438953472
  68719476736 p15739 p2457 p15740
  p15741 p2460

noncomputable def p15743 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 147060552015) (BSN.cosEvenQ 137438953472) 0
  3 p15739 p2457 p15740 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15744 :=
p15742 p15740 65987006829 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15743 (Eq.refl true))

noncomputable def p15745 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 147060552015) (BSN.cosOddQ 137438953472) 0
  3 p15741 p2460 p15740 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15746 :=
p15731 d113 d115 d117 d119 d103
  (p15737 (p15738 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p15744 (p15745 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p15747 :=
p15628 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 137170049885 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p15746 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p15649 1695513633491111773 p4831 285405146047951
    137438953472 3368 137438953472
    (@p15653 p15647 p15648 1695513633491111773
      p4831
      (p15655 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p15658 (p15689 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p15651 p15652)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p15748 :=
nat_lit
  4199225368813615252915400446687068493800830477074631922020062421300035450251954562406654353530651680202779096212208197919154681655673170169856

noncomputable def p15749 :=
nat_lit
  256334635992477520244316401318056502904878001143831485531017494872638937832819221843483924660394804038506859421728270021490307128365056

noncomputable def p15750 :=
nat_lit
  20988488966244885649876761362619076778954246646995962120940039666348931323133564245396987557385112144585153894914236586153715301036323354710016

noncomputable def p15751 :=
BSN.sin_dyadic_bound_f 158757386562 137438953472 4 3 137438953472
  68719476736 p15748 p2504 p15749
  p15750 p2507

noncomputable def p15752 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 158757386562) (BSN.sinEvenQ 137438953472) 0
  3 p15748 p2504 p15749 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15753 :=
p15751 p15749 125734679524 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15752 (Eq.refl true))

noncomputable def p15754 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 158757386562) (BSN.sinOddQ 137438953472) 0
  3 p15750 p2507 p15749 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15755 :=
nat_lit
  12218899157259494737462750559356566007563040626293394111731447301676708162631896844086528479261650852959858182089275090391023543559242484617216

noncomputable def p15756 :=
nat_lit
  6294115009106554653944257878608946512572265735614652751564935437543240111586345804344494325210101559880589909830841077319993844140937216

noncomputable def p15757 :=
nat_lit
  61029954824256631814637713196267954267832131609801579040976671294298485463954321461979006560130250465280607435552910144842707161366622850584576

noncomputable def p15758 :=
BSN.sin_dyadic_bound_f 207289779478 137438953472 4 3 137438953472
  68719476736 p15755 p2504 p15756
  p15757 p2507

noncomputable def p15759 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 207289779478) (BSN.sinEvenQ 137438953472) 0
  3 p15755 p2504 p15756 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15760 :=
p15758 p15756 137170049885 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15759 (Eq.refl true))

noncomputable def p15761 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 207289779478) (BSN.sinOddQ 137438953472) 0
  3 p15757 p2507 p15756 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15762 :=
p15747 d121 d123 d125 d127 d103
  (p15753 (p15754 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p15760 (p15761 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p15763 :=
p15623 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 132382963940 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p15762 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p15649 1695513633491111773 p4831 285405146047951
    137438953472 3368 137438953472
    (@p15653 p15647 p15648 1695513633491111773
      p4831
      (p15655 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p15658 (p15689 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p15651 p15652)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p15764 :=
nat_lit 584888310538039901381066852921578587870800877287175623460570711610232391388569461802930241

noncomputable def p15765 :=
nat_lit 952022449765197625581509844280158234327964601747108968422003330987320143564216733761

noncomputable def p15766 :=
nat_lit 1754663027569220173747949395745047203295933975932323376163775290824035199525421256975323201

noncomputable def p15767 :=
BSN.cos_dyadic_bound_f 31429024297 137438953472 3 2 137438953472
  68719476736 p15764 p2466 p15765
  p15766 p2469

noncomputable def p15768 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 31429024297) (BSN.cosEvenQ 137438953472) 0
  2 p15764 p2466 p15765 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15769 :=
p15767 p15765 133861050192 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15768 (Eq.refl true))

noncomputable def p15770 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 31429024297) (BSN.cosOddQ 137438953472) 0
  2 p15766 p2469 p15765 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15771 :=
nat_lit
  6712386051825956922900382686005609463237627240149438872223875020442394845414104397137359325102119152711437662159240603794488692189741078020096

noncomputable def p15772 :=
nat_lit
  1045856540950848968653676496510699947443381066554303328241610418321450286876199483349364932182646789693437785593130011302957673659498496

noncomputable def p15773 :=
nat_lit
  33542426539359152685017029407410375034075442388805795636522033722191335647911269795374678336424058993871053526458231407023236582621830820397056

noncomputable def p15774 :=
BSN.sin_dyadic_bound_f 178493611336 137438953472 4 3 137438953472
  68719476736 p15771 p2504 p15772
  p15773 p2507

noncomputable def p15775 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 178493611336) (BSN.sinEvenQ 137438953472) 0
  3 p15771 p2504 p15772 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15776 :=
p15774 p15772 132382963940 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15775 (Eq.refl true))

noncomputable def p15777 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 178493611336) (BSN.sinOddQ 137438953472) 0
  3 p15773 p2507 p15772 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15778 :=
p15763 d129 d131 d133 d135 d103
  (p15769 (p15770 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p15776 (p15777 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p15779 :=
p15618
  (p15778 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p15649 1695513633491111773 p4831 285405146047951
    137438953472 3368 137438953472
    (@p15653 p15647 p15648 1695513633491111773
      p4831
      (p15655 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p15658 (p15689 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p15651 p15652)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p15780 :=
nat_lit 462954725921675020165171619202674100766138233468886872828734178153870062415156801690164161

noncomputable def p15781 :=
nat_lit 596456319825785313421869392812044299926886206545718886244492371706744784915226450881

noncomputable def p15782 :=
nat_lit 1388862984852385408924888013869236678209814846634247527048430045476866773755900574617590721

noncomputable def p15783 :=
BSN.cos_dyadic_bound_f 29644718489 137438953472 3 2 137438953472
  68719476736 p15780 p2466 p15781
  p15782 p2469

noncomputable def p15784 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 29644718489) (BSN.cosEvenQ 137438953472) 0
  2 p15780 p2466 p15781 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15785 :=
p15783 p15781 134254239590 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15784 (Eq.refl true))

noncomputable def p15786 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 29644718489) (BSN.cosOddQ 137438953472) 0
  2 p15782 p2469 p15781 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15787 :=
p15779 d137 d139 d103
  (p15785 (p15786 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p15788 :=
@p15607 p15591 p15593 p15594
  (p15611
    (@p15614 218387 68719476736
      (p15787 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p15787 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p15789 :=
@Enclosure.Real.IsNear.mulLit_ff p15598
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p15599)))

noncomputable def p15790 :=
nat_lit
  14915328897891573974851498602900896627121222396326850640304171846632511804428765204737018391325935711221042949219470639634610761135541581517244348369339280403901162979275209927

noncomputable def p15791 :=
nat_lit
  31658291388557380359744322690514840324496812684955115509000071179890844813636078997800499335839109758668501942530065835436974724391264154875845907853042325493325666835033489408

noncomputable def p15792 :=
nat_lit
  23576416659078013494820218970779613214347814997415042274986846716179527810900743718354940200079660183699145969195940624170368381312715256235353586972340155707794398792423654883839644343854965682623485303802702111598663561

noncomputable def p15793 :=
nat_lit
  100558559474569478246805187486543845956095243654442950332926710827913230225551602326014057236251775707675238936398645381403154121089599274598252367545630720000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15794 :=
@p15789 75266459 268435456 1 8589934592
  p15790 p15791 p15792 p15793
  p15604 p15591 p15605

noncomputable def p15795 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p15597
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p15796 :=
@p15795 1 1 0 1 75266459 268435456
  1 8589934592 75266459 268435456 1

noncomputable def p15797 :=
@Enclosure.Real.IsNear.of_eq
  (p15597
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p15798 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p15799 :=
p15798
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    101656100 100000
    (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true)))

noncomputable def p15800 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv (Real.sqrt p15599)) false
  4817053376 17179869184 2 17179869184 75266459 268435456

noncomputable def p15801 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p15599) false 61271462477
  17179869184 7 17179869184 61271462477 17179869184 7
  17179869184

noncomputable def p15802 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p15803 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p15804 :=
@p15803
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101656100 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2779543201126783

noncomputable def p15805 :=
@p15804 17179869184000 1016561 17179869184000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    101656100 100000
    (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true)))

noncomputable def p15806 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101656100 100000)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101656100 100000 0

noncomputable def p15807 :=
@p15806 1 2734261103 17179869184 1 17179869184
  2779543201126783 17179869184000 1016561 17179869184000
  (Enclosure.Real.IsNear.const false 101656100 100000) d142

noncomputable def p15808 :=
@p15802 2779543201126783 17179869184000 1016561 17179869184000
  109261370768 109261370809 8589934592
  (p15805 (p15807 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15809 :=
@Enclosure.Real.IsNear.recentre' p15599 false 218522741577 17179869184
  41 17179869184 218522741577 17179869184 41 17179869184
  (p15808 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p15810 :=
@Enclosure.Real.IsNear.sqrt_image p15599 218522741577 17179869184 41
  17179869184 30635731235 30635731242 8589934592
  (p15809 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p15811 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p15599) 61271462477 17179869184
  7 17179869184 2408526687 2408526689 8589934592
  (p15801
    (p15810 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p15812 :=
@p15797 (@Inv.inv.{0} Real Real.instInv (Real.sqrt p15599)) false
  75266459 268435456 1 8589934592 p15799
  (@p15800 1 8589934592
    (p15811 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p15813 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv.{0} Real Real.instInv p15599))
  34821392726122221091

noncomputable def p15814 :=
nat_lit 86469112845513523200000000

noncomputable def p15815 :=
nat_lit
  24784558906729550069195398889522136546849579882673869922218728732404712075192012646284717509259262170219788904916055604803035707140018407112679878809673270957088535952589625

noncomputable def p15816 :=
nat_lit
  39376439543168460996476446394294751539303466703863432592760314029937505001672847181906976912012286047229320668974947425644501861392088280905682449930353769264799597474551627946548114618321894207828434600900703866221187

noncomputable def p15817 :=
nat_lit
  33519519824856492748935062495514615318698414551480983444308903609304410075183867442004685745417258569225079645466215127134384707029866424866084122515210240000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15818 :=
nat_lit
  1100557019818440840559613592859477278625776695126320007195985385060240848011074650400650927367157685786931406732006841422805425098625448534371948219102452179876321902114468813811768449533768368128

noncomputable def p15819 :=
@p15813 73786976294838206464 20171503110251844889 p15814
  p15815 p15791 p15816 p15817
  p15818 p15790 p15791 p15792

noncomputable def p15820 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p15821 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))

noncomputable def p15822 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (p15820
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p15823 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  101656100 100000 12
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))

noncomputable def p15824 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p15825 :=
@p15824
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p15821 (Enclosure.sfrac false 1 16))))
  90780098593

noncomputable def p15826 :=
@p15825 17179869184 7351 17179869184 383579587
  4294967296 8175311989 221459251200000000 34821392726122221091
  73786976294838206464 20171503110251844889 p15814

noncomputable def p15827 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p15828 :=
@Inv.inv.{0} Real Real.instInv
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p15829 :=
@p15827 (@Neg.neg.{0} Real Real.instNeg p15828) true 90780098593
  17179869184 7351 17179869184
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p15830 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p15831 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p15832 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p15833 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 77687259527)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false

noncomputable def p15834 :=
nat_lit 10933509783051780437916795

noncomputable def p15835 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  false p15834

noncomputable def p15836 :=
nat_lit 221285839595886359698780819

noncomputable def p15837 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p15838 :=
@Enclosure.Real.IsNear.subLit_ff_p p15599 (Enclosure.sfrac false 12 1)
  218522741577 17179869184 41 17179869184 12 1 0

noncomputable def p15839 :=
@p15837 500000000000000 12364311369 17179869184 41
  17179869184 p15834 p2602 p15836
  p2604 d141
  (@p15838 1 12364311369 12364311369 17179869184 41
    17179869184 (p15809 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p15840 :=
@p15833 77687259527 17179869184 129 8589934592 true
  3251240192 17179869184 1 3300000000
  (@p15835 p2602 p15836 p2604
    77687259527 17179869184 129 8589934592
    (p15839 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 77687259527 17179869184)

noncomputable def p15841 :=
nat_lit 3417707351824209780464943104

noncomputable def p15842 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 77687259527)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p15841)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p15843 :=
BSN.sin_reduce_arg_pos_rat_q2 77687259527 17179869184 226375608064910080
  72057594037927936 0 p15841 p2333 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p15844 :=
nat_lit
  261386020431720763110313823352407632702821402565519731700460862219481658383951320241915763403499830933141420913504696721467401444451636048323513487393821019514897419758481

noncomputable def p15845 :=
nat_lit
  172290314979208064976455288534770616065713382493357159048992198672622248759730896579982470223337118967008350688490881546278174956961093389254046243267420582007565201

noncomputable def p15846 :=
nat_lit
  1583461087957624259531586676340075687781007583947975854701260792074032436192959623994399043667971584468938218957792138516880018075629100825714343032080938567142035991325585

noncomputable def p15847 :=
BSN.cos_dyadic_bound_f 48568542635851 35184372088832 4 3 17179869184
  6606445313 p15844 p2613 p15845
  p15846 p2616

noncomputable def p15848 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 48568542635851) (BSN.cosEvenQ 35184372088832) 0
  3 p15844 p2613 p15845 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15849 :=
p15847 p15845 3251240192 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15848 (Eq.refl true))

noncomputable def p15850 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 48568542635851) (BSN.cosOddQ 35184372088832) 0
  3 p15846 p2616 p15845 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15851 :=
@BSN.cos_arg_round false 3251240192 17179869184 p15841
  p2333 48568542635851 35184372088832 6606445313 6600000000
  (p15849 (p15850 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p15852 :=
p15842 3251240192 17179869184 0 1000000000000000
  6600000000 3300000000 p15843 BSN.pi_near_15 p15851
  (Eq.refl true) (Eq.refl true)

noncomputable def p15853 :=
@p15831 12700157 67108864 1696445057 110729625600000000
  (@p15832 3251240192 17179869184 434289934592
    28346784153600000000 12700157 67108864 1696445057
    110729625600000000
    (p15840 (p15852 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p15854 :=
@p15830 12700157 67108864 1696445057 110729625600000000
  45390045621 45390052972 8589934592 p15853
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p15855 :=
@Enclosure.Real.IsNear.recentre' p15828 false 90780098593 17179869184
  7351 17179869184 90780098593 17179869184 7351 17179869184
  (p15854 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p15856 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p15821 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p15857 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p15821 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 3565305095))
    (@Nat.cast.{0} Real Real.instNatCast 2147483648))
  true

noncomputable def p15858 :=
nat_lit 68963030147184331603268857841997805

noncomputable def p15859 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p15821 (Enclosure.sfrac false 1 16)))
  true p15858

noncomputable def p15860 :=
nat_lit 46368775370016310644729648626537242853

noncomputable def p15861 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p15821 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p15862 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))

noncomputable def p15863 :=
@p15862 (Enclosure.sfrac false 1 16) 59541056240081298735
  295147905179352825856 1718248170483 295147905179352825856 1 16
  0

noncomputable def p15864 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
    (Enclosure.sfrac false 12 1))
  152876195629582654161

noncomputable def p15865 :=
nat_lit 1022907557281783609792124682240

noncomputable def p15866 :=
@p15864 295147905179352825856 1013873533939 295147905179352825856
  12364311369 17179869184 41 17179869184 p15865
  59541056240081298735 295147905179352825856 1718248170483

noncomputable def p15867 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
    (Enclosure.sfrac false 12 1))
  12364311369 17179869184 41

noncomputable def p15868 :=
@p15867 17179869184 12364311369 17179869184 41
  17179869184 152876195629582654161 295147905179352825856 1013873533939
  295147905179352825856
  (@p15838 1 12364311369 12364311369 17179869184 41
    17179869184 (p15809 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p15869 :=
p15868
  (@p15838 1 12364311369 12364311369 17179869184 41
    17179869184 (p15809 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p15870 :=
@p15866 295147905179352825856 (p15869 (Eq.refl true))
  (@p15838 1 12364311369 12364311369 17179869184 41
    17179869184 (p15809 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p15871 :=
@p15861 500000000000000 77987800313790850351 295147905179352825856
  1718248170483 295147905179352825856 p15858 p2630
  p15860 p2632 d141
  (@p15863 1 1247804805020653605616 77987800313790850351
    295147905179352825856 1718248170483 295147905179352825856
    (p15870 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p15872 :=
@p15857 3565305095 2147483648 629 17179869184 true
  767159174 8589934592 1 3300000000
  (@p15859 p2630 p15860 p2632
    3565305095 2147483648 629 17179869184
    (p15871 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 3565305095 2147483648)

noncomputable def p15873 :=
nat_lit
  1361176257597065774480281741266212866061791645428447827249599589287730354733152985042377837038103448653267326755868682973908563411315645546817513938496259082890625

noncomputable def p15874 :=
nat_lit
  4280528994397723129507835988463142326332233186641591649370616086334967125456923470802661531755578368730858425306122747239013298128334544361442972611807824314368000

noncomputable def p15875 :=
nat_lit
  681627646334583789685553233491933092124380739113620217537580751834450493636494594836630595302609149371626495462622575524097104803014323881787261962890625

noncomputable def p15876 :=
nat_lit
  13842294724791575550783154334548618220651303187005565724848212228458220393362388479413698107237965104434363885228351458116044688833413142479432034361241240586890625

noncomputable def p15877 :=
nat_lit
  654920936142851638814698906234860775928831677556163522353704261209249970194909291032807214358603490415821339071836780327569034613635185287300774809606597120098304000

noncomputable def p15878 :=
BSN.cos_dyadic_bound_t 3565305095 2147483648 5 4 8589934592
  3300000000 p15873 p15874 p15875
  p15876 p15877

noncomputable def p15879 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 3565305095) (BSN.cosEvenQ 2147483648) 0
  4 p15873 p15874 p15875 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15880 :=
p15878 p15875 767159174 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15879 (Eq.refl true))

noncomputable def p15881 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 3565305095) (BSN.cosOddQ 2147483648) 0 4
  p15876 p15877 p15875 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15882 :=
p15872
  (BSN.cos_neg_of_bound 3565305095 2147483648 true 767159174 8589934592
    1 3300000000
    (p15880 (p15881 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p15883 :=
p15826
  (p15829
    (@Enclosure.Real.IsNear.neg p15828 false 90780098593 17179869184
      7351 17179869184 (p15855 (Eq.refl true))))
  (@p15856 767159174 8589934592 2092879869184
    56693568307200000000 383579587 4294967296 8175311989
    221459251200000000 (p15882 (Eq.refl true)) (Eq.refl true))

noncomputable def p15884 :=
@p15819 p15793
  (@p15822 false 34821392726122221091 73786976294838206464
    20171503110251844889 p15814
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (p15823 (Eq.refl true) (Eq.refl true)
        (p15602 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p15883 (Eq.refl true)))

noncomputable def p15885 :=
nat_lit
  18350087088301296971770164802227349849413129214388501770594823985260355491552244097693258906172452992786873965848818903742671303738103357492361753263981467965058375

noncomputable def p15886 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv p15599) p15885 p12154

noncomputable def p15887 :=
nat_lit
  29139294946864613180009124400155326151110076069872128166465918224567937421006276403098526661227068197826360507354619860437044443016098175581964492863579271313045816763667529230824780088719882650453271832406781

noncomputable def p15888 :=
nat_lit
  1951092843947495144613498268620728941092873839165606969286973099765857336762353512575191314414682481974891831950879139309654984799555178316431360000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15889 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p15890 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg.{0} Real Real.instNeg p15889) true p15885

noncomputable def p15891 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p15892 :=
nat_lit
  247075286487275842976025053774494996463161853421706692839086316293861384914357081659961132007065849863326780114200591293693248451029811838779801197423875

noncomputable def p15893 :=
nat_lit
  392343370204022915119966935215102814250945621597804403291981935255635204885674938521857250564231108651313385156286455030276627424913530392317086478158552147930692143029245288399590028893405931267537

noncomputable def p15894 :=
nat_lit
  27726696941208148595784141841430837034364370753758165751704795806146213078056256230399744061041395780973912109614035718289741578240000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15895 :=
@p15891 p15892 p12162 p15893
  p15894 74269213037 70368744177664 1 70368744177664
  p15885 p12154 p15887

noncomputable def p15896 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p15897 :=
p15896
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p15898 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15897
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p15899 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15898
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p15900 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p15901 :=
p15899
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15900
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p15902 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p15903 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15901
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p15902)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))

noncomputable def p15904 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p15905 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15903
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p15904)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))

noncomputable def p15906 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))

noncomputable def p15907 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (p15820
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15905
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15906
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
            (Enclosure.sfrac false 12 1))))))

noncomputable def p15908 :=
@p15824
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15905
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15906
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))
  185917632376021

noncomputable def p15909 :=
nat_lit
  1328950263241103651975526546374071335896948040013764772375491921177527353732980358645769135918884194942693903543553561339156335439550496375

noncomputable def p15910 :=
nat_lit
  744282853678701455922507579277316643178128753343813693728245963960974631028119473486019635930893891134220822124816566203939432067701407744

noncomputable def p15911 :=
nat_lit
  348196127425179409289500780782918341068281922524735634384627858976981762307877303935054252346184648161622338680527338754589655495730443491459113077238248270666682921434004699338064361313

noncomputable def p15912 :=
nat_lit
  130026620448101781400520832330473925556763139592535974004229368234010881845940795017667078641120221614661872368012492800000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15913 :=
@p15908 35184372088832 3689 35184372088832 p15909
  p15910 p15911 p15912 p15892
  p12162 p15893 p15894

noncomputable def p15914 :=
@p15827 (@Neg.neg.{0} Real Real.instNeg p15828) true 185917632376021
  35184372088832 3689 35184372088832
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p15915 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 318207014327209)
    (@Nat.cast.{0} Real Real.instNatCast 70368744177664))
  false

noncomputable def p15916 :=
nat_lit 44783655973459377989848529395

noncomputable def p15917 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  false p15916

noncomputable def p15918 :=
nat_lit 221372824460336745806082707

noncomputable def p15919 :=
@Enclosure.Real.IsNear.subLit_ff_p p15599 (Enclosure.sfrac false 12 1)
  895069149388657 70368744177664 41 70368744177664 12 1
  0

noncomputable def p15920 :=
@p15803
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101656100 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2277001789785044049

noncomputable def p15921 :=
@p15920 14073748835532800 1016561 70368744177664000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    101656100 100000
    (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true)))

noncomputable def p15922 :=
@p15806 1 11199533475045 70368744177664 1
  70368744177664 2277001789785044049 14073748835532800 1016561
  70368744177664000 (Enclosure.Real.IsNear.const false 101656100 100000)
  d198

noncomputable def p15923 :=
@p15802 2277001789785044049 14073748835532800 1016561
  70368744177664000 447534574694308 447534574694349 35184372088832
  (p15921 (p15922 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p15924 :=
@Enclosure.Real.IsNear.recentre' p15599 false 895069149388657 70368744177664
  41 70368744177664 895069149388657 70368744177664 41
  70368744177664
  (p15923 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p15925 :=
@p15837 500000000000000 50644219256689 70368744177664 41
  70368744177664 p15916 p12189 p15918
  p14421 d197
  (@p15919 1 50644219256689 50644219256689 70368744177664
    41 70368744177664 (p15924 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p15926 :=
@p15915 318207014327209 70368744177664 259 70368744177664
  true 13317080509950 70368744177664 1 13516800000000
  (@p15917 p12189 p15918 p14421
    318207014327209 70368744177664 259 70368744177664
    (p15925 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 318207014327209 70368744177664)

noncomputable def p15927 :=
nat_lit 13998929212856711431031523115008

noncomputable def p15928 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 318207014327209)
    (@Nat.cast.{0} Real Real.instNatCast 70368744177664))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p15927)
    (@Nat.cast.{0} Real Real.instNatCast p12201))
  226375608064910080 72057594037927936 false

noncomputable def p15929 :=
BSN.sin_reduce_arg_pos_rat_q2 318207014327209 70368744177664 226375608064910080
  72057594037927936 0 p15927 p12201
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p15930 :=
nat_lit
  109830601225299538660920493772451378623119423412184069251070242815231034636008568453465117621880723930769545272871191578373115643196745382637472304876299393572702805748589603662450634392060997563278023063261144257076806182523621296437246488238102207084713586719833236405146335402604363776

noncomputable def p15931 :=
nat_lit
  6017834933126951632973723859434233404306636521537722068938763745854679243214647078915794670994776084580209938212083616737591414702486918141872658164398934788659204434166194214932108340002268701180108881876426775861531079930013630214034086246267142232407406145200141577901572096

noncomputable def p15932 :=
nat_lit
  1118660847330889184887804219721703588192575668306238922345285824490248134709594254946736196334554801123464245366016159215688101305549999232874133662905385378104612099352212190777524997752215658588930487468172983800584996720354256071498273225913049292569532888309304623059205457450417258496

noncomputable def p15933 :=
BSN.cos_dyadic_bound_f 198936749212303872 144115188075855872 5 4
  70368744177664 27060000000001 p15930 p12205
  p15931 p15932 p12208

noncomputable def p15934 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 198936749212303872) (BSN.cosEvenQ 144115188075855872)
  0 4 p15930 p12205 p15931
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p15935 :=
p15933 p15931 13317080509950 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p15934 (Eq.refl true))

noncomputable def p15936 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 198936749212303872) (BSN.cosOddQ 144115188075855872)
  0 4 p15932 p12208 p15931
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p15937 :=
@BSN.cos_arg_round false 13317080509950 70368744177664 p15927
  p12201 198936749212303872 144115188075855872 27060000000001
  27033600000000
  (p15935 (p15936 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p15938 :=
p15928 13317080509950 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p15929 BSN.pi_near_15 p15937
  (Eq.refl true) (Eq.refl true)

noncomputable def p15939 :=
@p15831 6658540254975 35184372088832 3405780739
  907097092915200000000
  (@p15832 13317080509950 70368744177664 3571219944177664
    p4996 6658540254975 35184372088832 3405780739
    907097092915200000000
    (p15926 (p15938 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p15940 :=
@p15830 6658540254975 35184372088832 3405780739
  907097092915200000000 185917632372332 185917632379710 35184372088832
  p15939 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p15941 :=
@Enclosure.Real.IsNear.recentre' p15828 false 371835264752042 70368744177664
  7378 70368744177664 185917632376021 35184372088832 3689
  35184372088832
  (p15940 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p15942 :=
nat_lit
  86879803863906880360673550475192942222164472414601418890786494992272871439091734419451988346204407162991396663298649454031286217643300896375

noncomputable def p15943 :=
@Enclosure.Real.IsNear.subLit_tt_n p15905
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15906
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))
  p15942 p15910

noncomputable def p15944 :=
nat_lit
  346331780328858254305591578481787399470286217580130216843188111056959554073923202269701298057416392723536046953462585886434341756344833922260022231235539710171042373955271899338064361313

noncomputable def p15945 :=
nat_lit 27912268362075602626627911431184570235110740709277238982032730996681517477372145278125

noncomputable def p15946 :=
nat_lit 242833611528216133864932738352939863330300854881517440156476551217363035650651062272

noncomputable def p15947 :=
nat_lit
  9059929320745524641106719302513274406188740224298366983069430622987620267924886656140951197051088769332722750427393641

noncomputable def p15948 :=
nat_lit
  631873750011343120187508166102022593913370572403294667525865865216000000000000000000000000000000000000000000000000000000000000

noncomputable def p15949 :=
nat_lit
  322713791964210733582504802901053202358080700637150659270935237455726965411494201350425385348798594834682696544582986832081497519051903556403884737958498698971601597535645306997732468288325776767538074848788633578635264000

noncomputable def p15950 :=
@p15943 p15944 p15912 p15945
  p15946 p15947 p15948 p15949
  p15909 p15910 p15911 p15912

noncomputable def p15951 :=
@Enclosure.Real.IsNear.subLit_tf p15903
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p15904)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))

noncomputable def p15952 :=
nat_lit
  72617595501487579058720447165486072614337044682935106202854787119658994806206534290666630217092841894594862365072571528018433352517720096375

noncomputable def p15953 :=
nat_lit
  340143797764377270993873904056835083121571546587451740940913380283219247187699508311159751938955297650758480792662060319236595513032223844669555466081419015720928537316850891609424361313

noncomputable def p15954 :=
nat_lit 5760460082805132510137828289976533408950037453103528727336550488565396170349402434596941909814310480947849678125

noncomputable def p15955 :=
nat_lit
  969427880332355084834876460838438595574314870082159616853606393706956038551024096937673936454264104726046120916465829071486884288969299835664926989863

noncomputable def p15956 :=
nat_lit
  20370359763344860862684456884093781610514683936659362506361404493543812997633367061833973760000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15957 :=
nat_lit
  26117237626550261820445872811382827249282061561824609178845457540963851987243642955863406983971404185953230703272898610328735347633083079211605687394338100567129691735711830838254844023268982089984350641367616254675227099888660914754015015873806336000

noncomputable def p15958 :=
@p15951 p15952 p15910 p15953
  p15912 p15954 p14458 p15955
  p15956 p15957 p15942 p15910

noncomputable def p15959 :=
@Enclosure.Real.IsNear.subLit_tf p15901
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p15902)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))

noncomputable def p15960 :=
nat_lit 24913192551065303695164650536679773441990706206878908695281037933498633319945867062723109242789125

noncomputable def p15961 :=
nat_lit
  1033686114502090070237751284459640351333490121422299291970401218045123463316520994816016625974962296453561741136364688183737411

noncomputable def p15962 :=
nat_lit
  782569255901477775150662145082716356435539864364265188004270135759080095358543462400000000000000000000000000000000000000000000000000000

noncomputable def p15963 :=
nat_lit
  63936614889561978157759739929584986909242355094109179278602827911906586504862032267893826963389865071972633743533806290291981675111290912375

noncomputable def p15964 :=
nat_lit
  10302183248457454006457374032044794511694937697017866823833561948018013486691160863918758503525071324269184040214805942767019557645044790031282196858762077239338240767177299745740132161

noncomputable def p15965 :=
nat_lit
  3940200619639447921227904010014361380507973927046544666794829340424572177149721061141426625488491564080662799030681600000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p15966 :=
nat_lit
  155110242570926067939567662860756496283763616866046197673556798959007911135257052132874213478292238585961408511050526978531518850673397423771469836172441653004282986171368561772778067906604497063810570438922325306405447194527255232512000

noncomputable def p15967 :=
@p15959 p15960 p14587 p15961
  p15962 p15963 p15910 p15964
  p15965 p15966 p15952 p15910

noncomputable def p15968 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15898
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p15969 :=
@p15968
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15900
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p15970 :=
nat_lit 44767769487755623752605582293966459254773432506607223120480135136615307803925307216941921650597125

noncomputable def p15971 :=
nat_lit
  279158831982804057733862361148000946311323038981783286551606275988625758984584716558682665674830413795499863888364688183737411

noncomputable def p15972 :=
nat_lit 113959682749247800382119750781998602932481466892979067125

noncomputable def p15973 :=
nat_lit 47303603100944684403709722876248173610532891650878222770160935540150875429

noncomputable def p15974 :=
nat_lit 49061639436767370911378580199826395313156915200000000000000000000000000000000000000

noncomputable def p15975 :=
nat_lit
  305434851945926848141511660005177099831499099072749921702281495029536057913454993549025584848049572667461344396444941453367503655607955008880365273088000

noncomputable def p15976 :=
@p15969 p15970 p14587 p15971
  p15962 p15972 p8159 p15973
  p15974 p15975 p15960 p14587

noncomputable def p15977 :=
nat_lit 2554962807628475161829428312230102498992074584379192846609845364406222565832433472875

noncomputable def p15978 :=
@Enclosure.Real.IsNear.mulLit_ft p15898
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p15821 (Enclosure.sfrac false 1 16))))
  p15977

noncomputable def p15979 :=
nat_lit 577812344350977103362365030482196125912234700219923616605487738935918166288023806335992589604745858621521

noncomputable def p15980 :=
@p15978 p12222 p15979 p14484
  17521886954319 17592186044416 4094101307 453548546457600000000
  p15970 p14587 p15971 p15962

noncomputable def p15981 :=
@Enclosure.Real.IsNear.mulLit_ff p15897
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p15982 :=
nat_lit 186891574007583825131496118519969131513985742760569773225

noncomputable def p15983 :=
nat_lit 923316572882510342768372346718396198551912492849467123424989765331

noncomputable def p15984 :=
nat_lit 13670829309430493548864731635

noncomputable def p15985 :=
nat_lit 1106561890846780071736736991

noncomputable def p15986 :=
@p15981 p15982 p12261 p15983
  p14489 p15984 p12265 p15985
  p14492 p15977 p12222 p15979

noncomputable def p15987 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p15988 :=
@p15987
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p15989 :=
@p15988 p15984 p12265 p15985
  p14492 p15984 p12265 p15985
  p14492 p15982 p12261 p15983

noncomputable def p15990 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p15991 :=
@p15990 140737488355328 1 500000000000000 15459847167857
  35184372088832 41 35184372088832 p15984 p12265
  p15985 p14492

noncomputable def p15992 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 50644219256689 35184372088832

noncomputable def p15993 :=
@p15992 41 35184372088832 1 1 0 1
  15459847167857 15459847167857 35184372088832 41 35184372088832

noncomputable def p15994 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p15995 :=
@p15994 50644219256689 70368744177664 41 70368744177664
  50644219256689 35184372088832 41 35184372088832
  (Enclosure.Real.IsNear.const false 2 1)
  (@p15919 1 50644219256689 50644219256689 70368744177664
    41 70368744177664 (p15924 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p15996 :=
@p15989 p14489
  (p15991 d197
    (p15993 (p15995 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p15991 d197
    (p15993 (p15995 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p15997 :=
@p15986 p14484 (p15996 (Eq.refl true))
  (p15991 d197
    (p15993 (p15995 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p15998 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p15821 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p15999 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p15821 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 58413958830015))
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  true

noncomputable def p16000 :=
nat_lit 1157007655821501901126489680872652200214205

noncomputable def p16001 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p15821 (Enclosure.sfrac false 1 16)))
  true p16000

noncomputable def p16002 :=
nat_lit 189937739967369515724977047662365861461653

noncomputable def p16003 :=
nat_lit 1308418174653229239689932831

noncomputable def p16004 :=
nat_lit 998933164831884170965151775

noncomputable def p16005 :=
@p15862 (Enclosure.sfrac false 1 16) p16004
  p12265 7037944490334403 p12265 1 16 0

noncomputable def p16006 :=
nat_lit 20934690794451667835038925296

noncomputable def p16007 :=
nat_lit 2564836944119588927671242721

noncomputable def p16008 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
    (Enclosure.sfrac false 12 1))
  p16007

noncomputable def p16009 :=
nat_lit 70293672326639122060990867526473324953600

noncomputable def p16010 :=
@p16008 p12265 4152825979050179 p12265
  50644219256689 70368744177664 41 70368744177664 p16009
  p16004 p12265 7037944490334403

noncomputable def p16011 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
    (Enclosure.sfrac false 12 1))
  50644219256689 70368744177664 41

noncomputable def p16012 :=
@p16011 70368744177664 50644219256689 70368744177664 41
  70368744177664 p16007 p12265 4152825979050179
  p12265
  (@p15919 1 50644219256689 50644219256689 70368744177664
    41 70368744177664 (p15924 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16013 :=
p16012
  (@p15919 1 50644219256689 50644219256689 70368744177664
    41 70368744177664 (p15924 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16014 :=
@p16010 p12265 (p16013 (Eq.refl true))
  (@p15919 1 50644219256689 50644219256689 70368744177664
    41 70368744177664 (p15924 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16015 :=
@p15861 500000000000000 p16003 p12265
  7037944490334403 p12265 p16000 p12284
  p16002 p12286 d197
  (@p16005 1 p16006 p16003 p12265
    7037944490334403 p12265
    (p16014 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16016 :=
@p15999 58413958830015 35184372088832 315 35184372088832
  true 35043773908638 35184372088832 1 13516800000000
  (@p16001 p12284 p16002 p12286
    58413958830015 35184372088832 315 35184372088832
    (p16015 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 58413958830015 35184372088832)

noncomputable def p16017 :=
nat_lit
  124520746477024735309398828568193147860880742112388562827539135674086894155632734021727157275973969244737841964550130139676527321488760548299166094581775924809421641315107976188742494408365373821547025331052542210521990821140890625

noncomputable def p16018 :=
nat_lit
  18376645764853338377993715151286535276458371027463034014662192850447399102523241800636181556512939629074745407046002417586687251234360254270284328901491264378504256839114493956069418812471492731768139483526416168212890625

noncomputable def p16019 :=
nat_lit
  1012382916475998193614602867776728341832686997412227287790684255890692197321158202122818505487437434962587517970862473576948544760426715544813307263059733588027389038812551460314993791435523494983669013629279070721398520280340890625

noncomputable def p16020 :=
BSN.sin_dyadic_bound_f 58413958830015 35184372088832 5 4
  35184372088832 13516800000000 p16017 p12302
  p16018 p16019 p12305

noncomputable def p16021 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 58413958830015) (BSN.sinEvenQ 35184372088832) 0
  4 p16017 p12302 p16018 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16022 :=
p16020 p16018 35043773908638 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16021 (Eq.refl true))

noncomputable def p16023 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 58413958830015) (BSN.sinOddQ 35184372088832) 0
  4 p16019 p12305 p16018 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16024 :=
p16016
  (BSN.sin_neg_of_bound 58413958830015 35184372088832 false 35043773908638
    35184372088832 1 13516800000000
    (p16022 (p16023 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p16025 :=
p15980 p15997
  (@p15998 35043773908638 35184372088832 4292976372088832
    p12185 17521886954319 17592186044416 4094101307
    453548546457600000000 (p16024 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16026 :=
nat_lit 36266511300866282050849329191323274057887275

noncomputable def p16027 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15900
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p15821 (Enclosure.sfrac false 1 16))))
  p16026

noncomputable def p16028 :=
nat_lit 89596039071132192750545600512472294605095201432474891

noncomputable def p16029 :=
@p16027 p12314 p16028 p14536
  3142284125535 35184372088832 4094101307 453548546457600000000
  p15972 p8159 p15973 p15974

noncomputable def p16030 :=
nat_lit 41012487928291480646594194905

noncomputable def p16031 :=
nat_lit 3319685672540340215210210973

noncomputable def p16032 :=
@Enclosure.Real.IsNear.mulLit_ff p15900
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p16030 p12265 p16031 p14492

noncomputable def p16033 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16034 :=
@p16033 3 1 0 1 p15984
  p12265 p15985 p14492 p16030
  p12265 p16031

noncomputable def p16035 :=
@p16034 p14492 (Enclosure.Real.IsNear.const false 3 1)
  (p15991 d197
    (p15993 (p15995 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p16036 :=
@p16032 884279719003555 70368744177664 1 250000000000000
  p16026 p12314 p16028 p14536
  p16035 d199 (Eq.refl true)

noncomputable def p16037 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p15821 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 58413958830015))
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  true

noncomputable def p16038 :=
@p16037 58413958830015 35184372088832 315 35184372088832
  true 3142284125535 35184372088832 1 13516800000000
  (@p16001 p12284 p16002 p12286
    58413958830015 35184372088832 315 35184372088832
    (p16015 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 58413958830015 35184372088832)

noncomputable def p16039 :=
nat_lit
  36697239696967213607314291833476216177286942122942918157265060719940286565246381589049821418348979177939482041754970028567315249444075427761399740371203350339314752926966977191184042526941217994404606315408755169479229306132890625

noncomputable def p16040 :=
nat_lit
  373187531460808847111123923577126449061443215393082549760567851229035668823217863527386678465270925749366693740924277143637766680844272856688058524037531526506549214991723375371260110971654601089345173388409168382538483102996890625

noncomputable def p16041 :=
BSN.cos_dyadic_bound_t 58413958830015 35184372088832 5 4
  35184372088832 13516800000000 p16039 p12328
  p16018 p16040 p12330

noncomputable def p16042 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 58413958830015) (BSN.cosEvenQ 35184372088832) 0
  4 p16039 p12328 p16018 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16043 :=
p16041 p16018 3142284125535 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16042 (Eq.refl true))

noncomputable def p16044 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 58413958830015) (BSN.cosOddQ 35184372088832) 0
  4 p16040 p12330 p16018 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16045 :=
p16038
  (BSN.cos_neg_of_bound 58413958830015 35184372088832 true 3142284125535
    35184372088832 1 13516800000000
    (p16043 (p16044 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p16046 :=
p16029 p16036
  (@p15856 3142284125535 35184372088832 4292976372088832
    p12185 3142284125535 35184372088832 4094101307
    453548546457600000000 (p16045 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16047 :=
nat_lit 183303613365664341689287848525

noncomputable def p16048 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p15902)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  p16047

noncomputable def p16049 :=
nat_lit 91916306950381077534156011799126613

noncomputable def p16050 :=
nat_lit 348801715992459070074539385773239090470762532332995814624488528076603664616950716792938114672479958659172298195

noncomputable def p16051 :=
nat_lit
  4714043411862198928458718073655773998299820777508136230496972986032695041882363918290653486742486701819381071432801699585426481270849020217

noncomputable def p16052 :=
nat_lit
  33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384000000000000000000000000000000000000000000000000000

noncomputable def p16053 :=
@p16048 p12189 p16049 p13950
  p16050 p12342 p16051 p16052
  p15963 p15910 p15964 p15965

noncomputable def p16054 :=
nat_lit 61101204455221447229762616175

noncomputable def p16055 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p15902
  3 1 0 1 p16054 p12189

noncomputable def p16056 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16057 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p16058 :=
@p16057 140737488355328 1 500000000000000 69097145554885
  70368744177664 3405780739 907097092915200000000 p16054
  p12189 p16049 p13957

noncomputable def p16059 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p16060 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 318207014327209)
    (@Nat.cast.{0} Real Real.instNatCast 70368744177664))
  false

noncomputable def p16061 :=
@p16060 318207014327209 70368744177664 259 70368744177664
  true 69097145554885 70368744177664 1 13516800000000
  (@p15917 p12189 p15918 p14421
    318207014327209 70368744177664 259 70368744177664
    (p15925 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 318207014327209 70368744177664)

noncomputable def p16062 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 318207014327209)
    (@Nat.cast.{0} Real Real.instNatCast 70368744177664))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p15927)
    (@Nat.cast.{0} Real Real.instNatCast p12201))
  226375608064910080 72057594037927936 false

noncomputable def p16063 :=
nat_lit
  373065966367657514316339927938995358843990755729217512877279279342866198817309789404735164958580535515241818953873664674934297060490566736694501674294069904877999468095198669358827579507808081545569606879985046312770230929680613586182907068072895920450827044281643158885815742416463855616

noncomputable def p16064 :=
nat_lit
  3035570105510637527123923459520583548871007621750868137071084121185808343261185105387606157543363683218514795020655602217710175509785431378073256968152294231518955665480265312010982091405894814049820221486507241365785834888362453226384038603702013000065045084652290347481072801136498442240

noncomputable def p16065 :=
BSN.sin_dyadic_bound_f 198936749212303872 144115188075855872 5 4
  70368744177664 27060000000001 p16063 p12357
  p15931 p16064 p12359

noncomputable def p16066 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 198936749212303872) (BSN.sinEvenQ 144115188075855872)
  0 4 p16063 p12357 p15931
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16067 :=
p16065 p15931 69097145554885 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16066 (Eq.refl true))

noncomputable def p16068 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 198936749212303872) (BSN.sinOddQ 144115188075855872)
  0 4 p16064 p12359 p15931
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16069 :=
@BSN.sin_arg_round false 69097145554885 70368744177664 p15927
  p12201 198936749212303872 144115188075855872 27060000000001
  27033600000000
  (p16067 (p16068 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16070 :=
p16062 69097145554885 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p15929 BSN.pi_near_15 p16069
  (Eq.refl true) (Eq.refl true)

noncomputable def p16071 :=
p16058 d197
  (@p16059 69097145554885 70368744177664 3571219944177664
    p4996 69097145554885 70368744177664 3405780739
    907097092915200000000
    (p16061 (p16070 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16072 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15897
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p16073 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16072
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p16074 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16073
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p15902)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))

noncomputable def p16075 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (p15820
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16074
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15904
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
            (Enclosure.sfrac false 12 1))))))

noncomputable def p16076 :=
@p15824
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16074
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15904
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))
  185917632376021

noncomputable def p16077 :=
nat_lit 1876108852801022891338493151360961596169976992712368969113111530711204162321694246151824494732295

noncomputable def p16078 :=
nat_lit
  1393645887154518150552219324013283728393716323127568622834842690106107406238082757771497604626988028567126789586076848453174211

noncomputable def p16079 :=
nat_lit
  52171283726765185010044143005514423762369324290951012533618009050605339690569564160000000000000000000000000000000000000000000000000000

noncomputable def p16080 :=
@p16076 35184372088832 3689 35184372088832 p16077
  p14587 p16078 p16079 p16050
  p12342 p16051 p16052

noncomputable def p16081 :=
nat_lit 5654914524748615711890442115604518803722950525863690332974204806828529873897585957541023428467705

noncomputable def p16082 :=
@Enclosure.Real.IsNear.subLit_ff_n p16074
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15904
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))
  p16081 p14587

noncomputable def p16083 :=
nat_lit
  4103263588953951221705509041356557810003357586969090428996577731302248131123609852047151512681108849565063284750841607119522633

noncomputable def p16084 :=
nat_lit
  156513851180295555030132429016543271287107972872853037600854027151816019071708692480000000000000000000000000000000000000000000000000000

noncomputable def p16085 :=
nat_lit 3041756118453457748088982196240254417148716670394473054535966577228125

noncomputable def p16086 :=
nat_lit 36505958453398799628379080364695469789792958423667653113998759380606521904787303956613225799

noncomputable def p16087 :=
nat_lit 73559785961562665201200657303214840813699477864812904448000000000000000000000000000000000000000000000

noncomputable def p16088 :=
nat_lit
  1618553427625111915708506461628357499178285700048702454048384013074449190032547636646811139029382715911739327823048916652263389675952283849908541563078443652916183040

noncomputable def p16089 :=
@p16082 p16083 p16084 p16085
  p13995 p16086 p16087 p16088
  p16077 p14587 p16078 p16079

noncomputable def p16090 :=
@Enclosure.Real.IsNear.subLit_ff_p p16073
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p15902)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))

noncomputable def p16091 :=
nat_lit 11385182209506649490196518634910728997963306760995283477436780033937335

noncomputable def p16092 :=
nat_lit 641636642286260916274781127177012922730931041258271515315376882258295129480173314087539

noncomputable def p16093 :=
nat_lit 3452405954462674420109684182764216528856295494455218982092800000000000000000000000000000000000000

noncomputable def p16094 :=
nat_lit 22533431298667132826867226988637739325971043722875564370707965950569919409160808678863756564538375

noncomputable def p16095 :=
nat_lit
  370379561142390918073575276648642273719765698471838433556374172134992799657177058106736007568601832246215294269858327919956603

noncomputable def p16096 :=
nat_lit
  14228531925481414093648402637867570117009815715713912509168547922892365370155335680000000000000000000000000000000000000000000000000000

noncomputable def p16097 :=
nat_lit
  4878598207824581962800390715525970761827533889058083054901003129808096259127464479101606883452530730161879844498291713678018547882467868039008984070186837249842216960

noncomputable def p16098 :=
@p16090 p16091 p13995 p16092
  p16093 p16094 p14587 p16095
  p16096 p16097 p16081 p14587

noncomputable def p16099 :=
@Enclosure.Real.IsNear.subLit_ft p16072
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p16100 :=
nat_lit 587266426200280275411533637169767920854618100312854446736672381800375

noncomputable def p16101 :=
nat_lit 750004163704290831377786640490788774333635575742443448937249548007681036440519942262617

noncomputable def p16102 :=
nat_lit 10357217863388023260329052548292649586568886483365656946278400000000000000000000000000000000000000

noncomputable def p16103 :=
nat_lit 15494249272377261464483604045

noncomputable def p16104 :=
nat_lit 110487606986932300652920610500539869

noncomputable def p16105 :=
nat_lit 14094172911707874269378834552121129064846997124369627351841085378699224641529197318202389996503040

noncomputable def p16106 :=
@p16099 p16100 p13995 p16101
  p16102 p16103 p2445 p16104
  p12402 p16105 p16091 p13995

noncomputable def p16107 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15897
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p16108 :=
@Enclosure.Real.IsNear.mulLit_ft p15897
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p15821 (Enclosure.sfrac false 1 16))))
  p15982

noncomputable def p16109 :=
@p16108 p12261 p15983 p14489
  3142284125535 35184372088832 4094101307 453548546457600000000
  p16100 p13995 p16101 p16102

noncomputable def p16110 :=
p16109 (p15996 (Eq.refl true))
  (@p15856 3142284125535 35184372088832 4292976372088832
    p12185 3142284125535 35184372088832 4094101307
    453548546457600000000 (p16045 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16111 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p15821 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p16112 :=
@p16111 70368744177664 1 250000000000000 17521886954319
  17592186044416 4094101307 453548546457600000000 p16103
  p2445 p16104 p12402

noncomputable def p16113 :=
p16112 d199
  (@p15998 35043773908638 35184372088832 4292976372088832
    p12185 17521886954319 17592186044416 4094101307
    453548546457600000000 (p16024 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16114 :=
@p16098 p16083 p16084
  (@p16106 p16092 p16093
    (@p16107 true p16100 p13995 p16101
      p16102 (p16110 (Eq.refl true)))
    (p16113 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16115 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) p15902)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  p16054

noncomputable def p16116 :=
nat_lit 368788659725700747641720157984827758479752091073818373951185982108905

noncomputable def p16117 :=
nat_lit 169235831179021688927283894473324251165659246081760850697540228748265673175144291

noncomputable def p16118 :=
nat_lit 80346902212949513777098104617058130126110149689139641765068800000000000000000000000000000

noncomputable def p16119 :=
@p16115 p12265 p16049 p12348
  p16116 p12388 p16117 p16118
  p16094 p14587 p16095 p16096

noncomputable def p16120 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p15902
  2 1 0 1 p16054 p12189

noncomputable def p16121 :=
@Neg.neg.{0} Real Real.instNeg
  (p15896
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p16122 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  (p15820
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16121
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15902
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
            (Enclosure.sfrac false 12 1))))))

noncomputable def p16123 :=
@p15824
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16121
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15902
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))
  185917632376021

noncomputable def p16124 :=
nat_lit 1983613146384203886187542602181496167425710976687972805

noncomputable def p16125 :=
nat_lit 148985423492120577506746443312047896958887003021681469071056085606259

noncomputable def p16126 :=
nat_lit 376793390874373408599387495934666716005045108736000000000000000000000000000000

noncomputable def p16127 :=
@p16123 35184372088832 3689 35184372088832 p16124
  p8159 p16125 p16126 p16116
  p12388 p16117 p16118

noncomputable def p16128 :=
nat_lit 239538725731631988633342430188105439181565

noncomputable def p16129 :=
@Enclosure.Real.IsNear.subLit_ff_n p16121
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p15902
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))
  p16128 p5940

noncomputable def p16130 :=
nat_lit 551983883490459751352659620152881349161918551653

noncomputable def p16131 :=
nat_lit 17134579633164931174150637886426316800000000000000000000000

noncomputable def p16132 :=
nat_lit 35695691769689868443658040527779122190855074478915101125

noncomputable def p16133 :=
nat_lit 12440651775206028257383540306947698948637705583572638341889229600569

noncomputable def p16134 :=
nat_lit 34253944624943037145398863266787883273185918976000000000000000000000000000000

noncomputable def p16135 :=
nat_lit 172797075585819362958108265938578876998794827463738149009129186623588411212112784281911668244480

noncomputable def p16136 :=
@p16129 p16130 p16131 p16132
  p8159 p16133 p16134 p16135
  p16124 p8159 p16125 p16126

noncomputable def p16137 :=
@Enclosure.Real.IsNear.neg
  (p15896
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p15821 (Enclosure.sfrac false 1 16)))))

noncomputable def p16138 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16139 :=
@p16138
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p15821 (Enclosure.sfrac false 1 16))))
  p15984

noncomputable def p16140 :=
@p16139 p12265 p15985 p14492
  17521886954319 17592186044416 4094101307 453548546457600000000
  p16128 p5940 p16130 p16131

noncomputable def p16141 :=
p16140
  (p15991 d197
    (p15993 (p15995 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p15998 35043773908638 35184372088832 4292976372088832
    p12185 17521886954319 17592186044416 4094101307
    453548546457600000000 (p16024 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16142 :=
@Enclosure.Real.IsNear.mulLit_ff p15902
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  p16054 p12189 p16049

noncomputable def p16143 :=
nat_lit 584206024872222752287796235

noncomputable def p16144 :=
nat_lit 96714065569170333976494080000000

noncomputable def p16145 :=
@p15824
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p15821 (Enclosure.sfrac false 1 16))))
  185917632376021

noncomputable def p16146 :=
@p16145 35184372088832 3689 35184372088832 3142284125535
  35184372088832 4094101307 453548546457600000000 p16143
  p2445 5518741084738995850093 p16144

noncomputable def p16147 :=
p16146
  (p15914
    (@Enclosure.Real.IsNear.neg p15828 false 185917632376021 35184372088832
      3689 35184372088832 (p15941 (Eq.refl true))))
  (@p15856 3142284125535 35184372088832 4292976372088832
    p12185 3142284125535 35184372088832 4094101307
    453548546457600000000 (p16045 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16148 :=
@p16142 p13957 p16143 p2445
  5518741084738995850093 p16144 p16132 p8159
  p16133 p16134
  (@p16056 true p16054 p12189 p16049
    p13957 (p16071 (Eq.refl true)))
  (@p15822 false p16143 p2445
    5518741084738995850093 p16144
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (p15823 (Eq.refl true) (Eq.refl true)
        (p15602 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16147 (Eq.refl true)))

noncomputable def p16149 :=
p16127
  (p15914
    (@Enclosure.Real.IsNear.neg p15828 false 185917632376021 35184372088832
      3689 35184372088832 (p15941 (Eq.refl true))))
  (p16136
    (@p16137 true p16128 p5940 p16130
      p16131 (p16141 (Eq.refl true)))
    (p16148 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16150 :=
p16119
  (@p16120 p16049 p13957 p16054
    p12265 p16049 p12348
    (Enclosure.Real.IsNear.const false 2 1)
    (@p16056 true p16054 p12189 p16049
      p13957 (p16071 (Eq.refl true)))
    (Eq.refl true))
  (@p16122 false p16116 p12388 p16117
    p16118
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (p15823 (Eq.refl true) (Eq.refl true)
        (p15602 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16149 (Eq.refl true)))

noncomputable def p16151 :=
nat_lit 5206649690267657056965445744186103630424375

noncomputable def p16152 :=
nat_lit 2480333504575757548196162229837121340315081616302944941418771

noncomputable def p16153 :=
@Enclosure.Real.IsNear.mulLit_ff p15904
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  p16151 p12284 p16152

noncomputable def p16154 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16155 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p16156 :=
@p16155 p1070 p1071 p1072
  6658540254975 35184372088832 3405780739 907097092915200000000
  p16151 p12284 p16152 p14058

noncomputable def p16157 :=
p16156 d201
  (@p15832 13317080509950 70368744177664 3571219944177664
    p4996 6658540254975 35184372088832 3405780739
    907097092915200000000
    (p15926 (p15938 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16158 :=
@p16153 p14058 p16143 p2445
  5518741084738995850093 p16144 p16085 p13995
  p16086 p16087
  (@p16154 true p16151 p12284 p16152
    p14058 (p16157 (Eq.refl true)))
  (@p15822 false p16143 p2445
    5518741084738995850093 p16144
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (p15823 (Eq.refl true) (Eq.refl true)
        (p15602 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16147 (Eq.refl true)))

noncomputable def p16159 :=
p16080
  (p15914
    (@Enclosure.Real.IsNear.neg p15828 false 185917632376021 35184372088832
      3689 35184372088832 (p15941 (Eq.refl true))))
  (p16089
    (p16114 (p16150 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p16158 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16160 :=
p16053
  (@p16055 p16049 p13957 p16047
    p12189 p16049 p13950
    (Enclosure.Real.IsNear.const false 3 1)
    (@p16056 true p16054 p12189 p16049
      p13957 (p16071 (Eq.refl true)))
    (Eq.refl true))
  (@p16075 false p16050 p12342 p16051
    p16052
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (p15823 (Eq.refl true) (Eq.refl true)
        (p15602 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16159 (Eq.refl true)))

noncomputable def p16161 :=
@p15967 p15953 p15912
  (@p15976 p15961 p15962
    (p16025 (Eq.refl true)) (p16046 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p16160 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p16162 :=
nat_lit 15619949070802971170896337232558310891273125

noncomputable def p16163 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p15904)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  p16162

noncomputable def p16164 :=
@p16163 p12284 p16152 p14069
  p16116 p12388 p16117 p16118
  p15954 p14458 p15955 p15956

noncomputable def p16165 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p15904
  3 1 0 1 p16151 p12284

noncomputable def p16166 :=
p16164
  (@p16165 p16152 p14058 p16162
    p12284 p16152 p14069
    (Enclosure.Real.IsNear.const false 3 1)
    (@p16154 true p16151 p12284 p16152
      p14058 (p16157 (Eq.refl true)))
    (Eq.refl true))
  (@p16122 false p16116 p12388 p16117
    p16118
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (p15823 (Eq.refl true) (Eq.refl true)
        (p15602 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16149 (Eq.refl true)))

noncomputable def p16167 :=
nat_lit 47778124794554386722948076274526119217557429803493035054375

noncomputable def p16168 :=
nat_lit 66949034954296207251730123005125979943441618530590945582223848725901203048056510479557

noncomputable def p16169 :=
@Enclosure.Real.IsNear.mulLit_tf p15906
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
      (Enclosure.sfrac false 12 1)))
  p16167 p14074 p16168

noncomputable def p16170 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))))

noncomputable def p16171 :=
@p16170 p1059 p1061 p1062
  p1063 69097145554885 70368744177664 3405780739
  907097092915200000000 p16167 p14074 p16168

noncomputable def p16172 :=
@p16171 p14077 d202
  (@p16059 69097145554885 70368744177664 3571219944177664
    p4996 69097145554885 70368744177664 3405780739
    907097092915200000000
    (p16061 (p16070 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16173 :=
@p16169 p14077 p16143 p2445
  5518741084738995850093 p16144 p15945 p15946
  p15947 p15948 (p16172 (Eq.refl true))
  (@p15822 false p16143 p2445
    5518741084738995850093 p16144
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (p15823 (Eq.refl true) (Eq.refl true)
        (p15602 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16147 (Eq.refl true)))

noncomputable def p16174 :=
p15913
  (p15914
    (@Enclosure.Real.IsNear.neg p15828 false 185917632376021 35184372088832
      3689 35184372088832 (p15941 (Eq.refl true))))
  (p15950
    (@p15958 p15944 p15912 p16161
      (p16166 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p16173 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16175 :=
@p15895 p15888
  (@p15907 false p15892 p12162 p15893
    p15894
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1))
      (p15823 (Eq.refl true) (Eq.refl true)
        (p15602 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16174 (Eq.refl true)))

noncomputable def p16176 :=
@p15886 p15887 p15888 1350650751 17179869184
  1 17179869184 p15815 p15791 p15816
  p15817
  (@p15890 p12154 p15887 p15888
    (BSN.correctionLinear_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p15599
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p15889 false p15885 p12154
      p15887 p15888
      (p16175 d203 (Eq.refl true))))

noncomputable def p16177 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p15599) false
  1350650751 17179869184 1 17179869184 1350650751
  17179869184

noncomputable def p16178 :=
@Enclosure.Real.IsNear.inv_image p15599 218522741577 17179869184 41
  17179869184 675325375 675325376 8589934592
  (p15809 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p16179 :=
p15884
  (p16176
    (@p16177 1 17179869184
      (p16178 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p16180 :=
@p15794 p15594
  (@p15796 8589934592
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p15812 (Eq.refl true))
  (p16179 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p16181 :=
@p15601 p15591 p15593 p15594
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    12
    (p15602 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p15788 p16180 (Eq.refl true) (Eq.refl true))

theorem d225 : p15592 p15593 p15594 :=
@p15595 p15591 p15593 p15594
  (@Eq.refl.{1} Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
        true 5)))
  p16181

noncomputable def p16182 :=
nat_lit
  2406291773408183294514162696007290686622001726402441810443690042116225818505633072214207670211570461853242846278058178443470119069794150202214760743014070049874262669396252610461454375

noncomputable def p16183 :=
nat_lit
  1062275985633534197379176413104937254659186235454063846398888276400807119721704485478325004530458571337778658972493002030693158675305414478819039957533174703887662541670786438063456256

noncomputable def p16184 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  false p16182 p16183

noncomputable def p16185 :=
nat_lit
  6463530253967356454036410561103252443629192511795407973266153035325525839527313283637444800562705804950297832114874642390787208584522602939120983207781303459975486122197010819033759037373111874816166745542400952909174637421766107401

noncomputable def p16186 :=
nat_lit
  1976057905977208147221872828730913811871337065271750842756844870158297420558337617280232240557411981185959761577561382764966766699554761252403210122891405920090823065600000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16187 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  false p16182

noncomputable def p16188 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    12)

noncomputable def p16189 :=
@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p16190 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p16189
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p16191 :=
Real.sqrt
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p16192 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16190
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p16191)))

noncomputable def p16193 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  (p16188 p16192) false p16182

noncomputable def p16194 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
    true 5)
  101779300 100000 12
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))

noncomputable def p16195 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    12)

noncomputable def p16196 :=
nat_lit
  142284705836348263834804979344338451494272454470533278964041693581245427805141415348317958285455396553707813742554788947022362341053656369045006989016782979730725220685060712581279705

noncomputable def p16197 :=
nat_lit
  176213621945314175868501749854808726462467742054318158529257871514664216463638456311585301553073898105451597961345694035634622497691177181341227593462300365754686122197010819033759037373111874816166745542400952909174637421766107401

noncomputable def p16198 :=
nat_lit
  20669888942843979417423729976349006553213764257908054620797359960900105042865051273872056500222097068918587152620430397600072692315983633141248368319420182664126094154341130053773148018442240000

noncomputable def p16199 :=
@p16195 p16192 20608679435 8589934592 27331
  8589934592 p16196 p16183 p16197
  p16186 p16198 p16182

noncomputable def p16200 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    12)

noncomputable def p16201 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    12)

noncomputable def p16202 :=
p16201
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    12)

noncomputable def p16203 :=
@p16200 p16202 false 20608679435 8589934592 27331
  8589934592
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    12)

noncomputable def p16204 :=
@Enclosure.Real.IsNear.addLit_ff
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    12)

noncomputable def p16205 :=
@p16204
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    12)

noncomputable def p16206 :=
@p16205 164869435480 137438953472 218648 137438953472
  164869435480 137438953472 218648 137438953472
  45318965343781251973120 20608679435 8589934592

noncomputable def p16207 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p16208 :=
p16207 11 12 101779300 100000 286
  137438953472 68719476736 2305843009213693952 false 285835815970105
  3372

noncomputable def p16209 :=
p16208 341522969406 43 39675208392 8 false
  204136488174 205030 true 19731094643 7244019458077122842 1

noncomputable def p16210 :=
p16209 false 136025060657 true false 164869435480 218648
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 136025060657 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p16211 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
    true 5)
  Real.sin Real.sin

noncomputable def p16212 :=
p16211 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101779300
  100000 167 229 137438953472 68719476736

noncomputable def p16213 :=
p16212 2305843009213693952 false 285835815970105 3372
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p16214 :=
p16213 8 false 198063617819 175892 true 206532444295
  true 153846804297 7244019458077122842 1 false

noncomputable def p16215 :=
p16214 137120616100 false false 123671883084 true false
  204136488174 205030 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 167 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 137120616100 137438953472)

noncomputable def p16216 :=
p16211 BSN.quadSignPos BSN.quadSignPos 7 8 9 101779300
  100000 23 99 137438953472 68719476736

noncomputable def p16217 :=
p16216 2305843009213693952 false 285835815970105 3372
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p16218 :=
p16217 8 false 130852794472 143487 true 80188468179
  true 148664448945 7244019458077122842 1 false

noncomputable def p16219 :=
p16218 75715766741 false false 121323771891 false false
  198063617819 175892 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 23 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 75715766741 137438953472)

noncomputable def p16220 :=
p16211 BSN.quadSignPos BSN.quadSignPos 5 6 7 101779300
  100000 163 63 137438953472 68719476736

noncomputable def p16221 :=
p16220 2305843009213693952 false 285835815970105 3372
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p16222 :=
p16221 8 false 115976429164 106407 false 6766807253
  false 32351042251 7244019458077122842 1 false

noncomputable def p16223 :=
p16222 6764073697 false false 32053128399 false false
  130852794472 143487 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 163 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 6764073697 137438953472)

noncomputable def p16224 :=
p16211 BSN.quadSignNeg BSN.quadSignNeg 3 4 5 101779300
  100000 425 281 137438953472 68719476736

noncomputable def p16225 :=
p16224 2305843009213693952 false 285835815970105 3372
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p16226 :=
p16225 16 false 195371867454 62694 false
  162198041061 false 35854064944 7244019458077122842 1 false

noncomputable def p16227 :=
p16226 127084528796 true false 35448774496 true false
  115976429164 106407 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 425 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 127084528796 137438953472)

noncomputable def p16228 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
    true 5)
  Real.cos Real.cos

noncomputable def p16229 :=
p16228 BSN.quadSignNeg BSN.quadSignPos 1 2 3 101779300
  100000 874 612 137438953472 68719476736

noncomputable def p16230 :=
p16229 2305843009213693952 false 285835815970105 3372
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p16231 :=
p16230 16 false 137437197440 3418 false 188695949064
  false 33264703043 7244019458077122842 1 false

noncomputable def p16232 :=
p16231 27015588771 true false 133432995781 false false
  195371867454 62694 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 874 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 27015588771 137438953472)

noncomputable def p16233 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    1)

noncomputable def p16234 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    1)

noncomputable def p16235 :=
@p16234
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5)))
  false 1073728105

noncomputable def p16236 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5)))
  false 17179649680

noncomputable def p16237 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35729476996263)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  false 35729476996263

noncomputable def p16238 :=
nat_lit 374822932425775577589299012518042936934402671861780143296239

noncomputable def p16239 :=
nat_lit 180226789967050657305659705088442551330944518868434944000

noncomputable def p16240 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  false p16238 p16239

noncomputable def p16241 :=
nat_lit 23068672000000000000000000

noncomputable def p16242 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101779300 400000)
      (Real.log (Enclosure.sfrac false 41436113633960000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203558600))))))

noncomputable def p16243 :=
nat_lit 524250436884990985485152114652640000000000000000

noncomputable def p16244 :=
nat_lit 3201470910011228761960561419081062541120000000000000

noncomputable def p16245 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p16242 (Enclosure.sfrac false 101779300 200000))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 101779300 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p16243 p16244))
  false

noncomputable def p16246 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
    true 5)
  101779300 100000 41436113633960000 160000000000

noncomputable def p16247 :=
p16246 203558600 400000 200000 p16243
  p16244
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16248 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (p16242 (Enclosure.sfrac false 101779300 200000))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101779300 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p16243 p16244) 37465075020745319605479
  18014398509481984000

noncomputable def p16249 :=
nat_lit 119943338376248184828575684005773739819008854995769645854796480000000000000

noncomputable def p16250 :=
@p16248 565854040676687183 p16241 p16243
  p16244 0 1 p16249 p16238
  p16239 565854040676687183 p16241

noncomputable def p16251 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p16242 (Enclosure.sfrac false 101779300 200000))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101779300 200000) (Real.log Real.pi))
  47959345440801975002343 18014398509481984000 427604082791 44000000000000000000

noncomputable def p16252 :=
nat_lit 5149160702601205416019197677273088000

noncomputable def p16253 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 101779300 400000)
      (Real.log (Enclosure.sfrac false 41436113633960000 160000000000)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast 100000)
            (@Nat.cast.{0} Real Real.instNatCast 203558600))))))

noncomputable def p16254 :=
@p16253 (Enclosure.sfrac false 101779300 200000)
  57126809791882573472999 18014398509481984000 427604082791 44000000000000000000
  101779300 200000 0

noncomputable def p16255 :=
nat_lit 9591869088160395000468600000

noncomputable def p16256 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101779300 400000)
    (Real.log (Enclosure.sfrac false 41436113633960000 160000000000)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast 100000)
          (@Nat.cast.{0} Real Real.instNatCast 203558600)))))
  57133881817201107896999

noncomputable def p16257 :=
nat_lit 128638139645793780020725858456412618752

noncomputable def p16258 :=
@p16256 18014398509481984000 1272812231873 132000000000000000000
  884003164816803 2251799813685248 20000033 264000000000000000
  p16257 57126809791882573472999 18014398509481984000 427604082791

noncomputable def p16259 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101779300 400000)
  (Real.log (Enclosure.sfrac false 41436113633960000 160000000000)) 101779300
  400000 0 1 56135070507658343 4503599627370496

noncomputable def p16260 :=
nat_lit 30860581374597977692998467584

noncomputable def p16261 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 41436113633960000)
      (@Nat.cast.{0} Real Real.instNatCast 160000000000)))
  false p16260 p2333

noncomputable def p16262 :=
BSN.log_rat_reduce_isNear 41436113633960000 160000000000 17 82872227267920000
  41943040000000000 46797103550 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p16263 :=
nat_lit
  989096115048330846080099984839097216691208153713293210958726125249929198334696379984341692470236319883151820102383856469979392261020130698720782226952898528297340875095262645827149901389299385214156416969162015033080891942247617687427681895083337740803203088980147034085863505346290952175616000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16264 :=
nat_lit
  37931734482860953853965628198847270024578869696156781242410548077332537204647088510266998739669692606676264738591066369645628718867963839149190443861865087358016927714174840502764602044863204697789910334713750987500142487721244405124889128715434400311834689563627698933242261051372364994969600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16265 :=
nat_lit
  955761820696915971832870608498556136065143682832608393958256107061803637894662567826070833989067464202983204746210128133728844597441917705199760568505420195161917817756695689126546507371675895101947106620725484035338650311565458208110968701266551382163541321370153110384874094592000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16266 :=
BSN.log_dyadic_bound 20464593633960000 62407633633960000 12 11
  p16263 68719476736 26400000000 p16264 p16265
  46797103550 82872227267920000

noncomputable def p16267 :=
p16266 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p16268 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 20464593633960000) (BSN.artanhQ 62407633633960000)
  0 11 p16264 p16263 p16265
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16269 :=
p16262 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p16267 (p16268 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p16270 :=
@p16259 1250561 33000000000000000 57133881817201107896999
  18014398509481984000 1272812231873 132000000000000000000
  (Enclosure.Real.IsNear.const false 101779300 400000)
  (BSN.isNear_log_sfrac 41436113633960000 160000000000 56135070507658343
    4503599627370496 1250561 33000000000000000 false
    (@p16261 1000448800000000 p2422 56135070507658343
      4503599627370496 1250561 33000000000000000
      (p16269 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p16271 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast 100000)
        (@Nat.cast.{0} Real Real.instNatCast 203558600))))
  1 4

noncomputable def p16272 :=
@p16271 0 1 884003164816803 562949953421312 20000033
  66000000000000000 884003164816803 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p16273 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast 100000) (@Nat.cast.{0} Real Real.instNatCast 203558600)))
  884279719003555 562949953421312 1

noncomputable def p16274 :=
nat_lit 7593529364897333432549376

noncomputable def p16275 :=
@p16273 2000000000000000 4219882 8589934592 1
  3300000000 p16274 884003164816803 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p16276 :=
BSN.arctan_dyadic_bound_f 100000 203558600 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p16277 :=
p16276 1 4219882 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 203558600) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 203558600) 0 0
    (Eq.refl true))

noncomputable def p16278 :=
p16272
  (p16275
    (p16277 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16279 :=
@p16251 80064929352238887 137438953472000 1017793
  68719476736000 p16252 37465075020745319605479 18014398509481984000
  565854040676687183 p16241
  (@p16254 1 p16255 47959345440801975002343
    18014398509481984000 427604082791 44000000000000000000
    (@p16258 44000000000000000000 p16270 p16278
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101779300 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16280 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101779300 200000) (Real.log Real.pi)
  101779300 200000 0 1 78665238759 68719476736

noncomputable def p16281 :=
p16279
  (@p16280 1 34359738368 80064929352238887 137438953472000
    1017793 68719476736000
    (Enclosure.Real.IsNear.const false 101779300 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p16282 :=
@p16237 17179869184 211 8589934592 false 17179649680
  17179869184 1 3300000000
  (@p16240 565854040676687183 p16241 35729476996263
    17179869184 211 8589934592
    (@p16245 p16238 p16239 565854040676687183
      p16241
      (p16247 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p16250 (p16281 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p16243 p16244)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p16283 :=
nat_lit 3876587604631411671775051776

noncomputable def p16284 :=
BSN.cos_reduce3
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 35729476996263)
    (@Nat.cast.{0} Real Real.instNatCast 17179869184))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p16283)
    (@Nat.cast.{0} Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p16285 :=
BSN.sin_reduce_arg_pos_rat_q3 35729476996263 17179869184 226375608064910080
  72057594037927936 330 p16283 p2333
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p16286 :=
nat_lit
  1124706761210517333144901212108476276634121564984802877845858954654704821335874154158064772812130536758521859843291879360996390282163981047170676668546144638603145289630561

noncomputable def p16287 :=
nat_lit
  781335625582080377180723654987598779369949574456046779965086519437690429260269732078886274744329221142541587066824349630393241778927475835120297925855108470238315361

noncomputable def p16288 :=
nat_lit
  5616635253905877444806551179979065154810805642986404490988527428954701876727411237997677073967259327373827638298148357967604960213020065973760612248268191424815954079482721

noncomputable def p16289 :=
BSN.sin_dyadic_bound_f 55089623240169 35184372088832 4 3 17179869184
  6606445313 p16286 p3100 p16287
  p16288 p3103

noncomputable def p16290 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 55089623240169) (BSN.sinEvenQ 35184372088832) 0
  3 p16286 p3100 p16287 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16291 :=
p16289 p16287 17179649680 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16290 (Eq.refl true))

noncomputable def p16292 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 55089623240169) (BSN.sinOddQ 35184372088832) 0
  3 p16288 p3103 p16287 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16293 :=
@BSN.sin_arg_round false 17179649680 17179869184 p16283
  p2333 55089623240169 35184372088832 6606445313 6600000000
  (p16291 (p16292 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16294 :=
p16284 17179649680 17179869184 330 1000000000000000
  6600000000 3300000000 p16285 BSN.pi_near_15 p16293
  (Eq.refl true) (Eq.refl true)

noncomputable def p16295 :=
@p16235 1073741824 2753476307 110729625600000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  (@p16236 17179869184 704889934592 28346784153600000000
    1073728105 1073741824 2753476307 110729625600000000
    (p16282 (Enclosure.sfrac_false_div 35729476996263 17179869184)
      (p16294 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16296 :=
@p16233 false 1073728105 1073741824 2753476307
  110729625600000000 137437197440 137438953472 3418 137438953472
  p16295 (Eq.refl true)

noncomputable def p16297 :=
p16232 BSN.abs_quadSignPos (BSN.cos_quad_nat0 612 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 133432995781 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p16296
  (@p16240 565854040676687183 p16241 285835815970105
    137438953472 3372 137438953472
    (@p16245 p16238 p16239 565854040676687183
      p16241
      (p16247 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p16250 (p16281 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p16243 p16244)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p16298 :=
nat_lit
  50314661207931447017196741720137091607657811834353517292970631780287997616343696083812497636633862295955854344741090046869498259674638797696689907147855950722282947163639949912908439450812416

noncomputable def p16299 :=
nat_lit
  2583456949391570486492505639730373926861100008300163617627256778050511779212295982447448045513206027662963322905622659475045392844980034793359776951512210370304138772022228561166336

noncomputable def p16300 :=
nat_lit
  512487190426805113371999987841119470060410796308312184596746777905419937185719323857358327537814089368654750054406430306254833151942940072733483361569090490332809463655719278118813403380187136

noncomputable def p16301 :=
BSN.cos_dyadic_bound_f 188695949064 137438953472 5 4 137438953472
  68719476736 p16298 p2495 p16299
  p16300 p2498

noncomputable def p16302 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 188695949064) (BSN.cosEvenQ 137438953472) 0
  4 p16298 p2495 p16299 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16303 :=
p16301 p16299 27015588771 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16302 (Eq.refl true))

noncomputable def p16304 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 188695949064) (BSN.cosOddQ 137438953472) 0
  4 p16300 p2498 p16299 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16305 :=
nat_lit 733979838136028716358533333880998954406510698672015872623590013595416364225590065989451681

noncomputable def p16306 :=
nat_lit 1499233253701968988044084548984859345133167382488757116537450780942066088257798045601

noncomputable def p16307 :=
nat_lit 2201936515941578745137623913473898893500841829681282640356536965884687208544593682372263841

noncomputable def p16308 :=
BSN.cos_dyadic_bound_f 33264703043 137438953472 3 2 137438953472
  68719476736 p16305 p2466 p16306
  p16307 p2469

noncomputable def p16309 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 33264703043) (BSN.cosEvenQ 137438953472) 0
  2 p16305 p2466 p16306 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16310 :=
p16308 p16306 133432995781 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16309 (Eq.refl true))

noncomputable def p16311 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 33264703043) (BSN.cosOddQ 137438953472) 0
  2 p16307 p2469 p16306 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16312 :=
p16297 d93 d95 d97 d99 d103
  (p16303 (p16304 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p16310 (p16311 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16313 :=
p16227 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 281 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 35448774496 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p16312 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p16240 565854040676687183 p16241 285835815970105
    137438953472 3372 137438953472
    (@p16245 p16238 p16239 565854040676687183
      p16241
      (p16247 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p16250 (p16281 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p16243 p16244)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p16314 :=
nat_lit
  4575501743729689146143201184160240159055903402796846097995888840806734840910409131165881151739052495635016278254752003524229358331668709555921

noncomputable def p16315 :=
nat_lit
  331548644612796386787285474091718485372542175475717070585593186053924744253862631239421423137330241275659263070398865769525019289370321

noncomputable def p16316 :=
nat_lit
  22868441559520334180361891900467004459627383923155079103904114593753697463635425448558471091390096372578946877764036396070020106658334842076881

noncomputable def p16317 :=
BSN.sin_dyadic_bound_f 162198041061 137438953472 4 3 137438953472
  68719476736 p16314 p2504 p16315
  p16316 p2507

noncomputable def p16318 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 162198041061) (BSN.sinEvenQ 137438953472) 0
  3 p16314 p2504 p16315 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16319 :=
p16317 p16315 127084528796 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16318 (Eq.refl true))

noncomputable def p16320 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 162198041061) (BSN.sinOddQ 137438953472) 0
  3 p16316 p2507 p16315 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16321 :=
nat_lit 1783098823504619570032149261802584142752797450019488298402522447978907074599186567570391040

noncomputable def p16322 :=
nat_lit 2730908859847030067339608482328904267599592043239327338258516563156448522290400854016

noncomputable def p16323 :=
nat_lit 4670016306754897216797424754878748984221845779282970775000439707108416275414547778225831936

noncomputable def p16324 :=
BSN.sin_dyadic_bound_f 35854064944 137438953472 3 2 137438953472
  68719476736 p16321 p2477 p16322
  p16323 p2480

noncomputable def p16325 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 35854064944) (BSN.sinEvenQ 137438953472) 0
  2 p16321 p2477 p16322 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16326 :=
p16324 p16322 35448774496 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16325 (Eq.refl true))

noncomputable def p16327 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 35854064944) (BSN.sinOddQ 137438953472) 0
  2 p16323 p2480 p16322 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16328 :=
p16313 d105 d107 d109 d111 d103
  (p16319 (p16320 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p16326 (p16327 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16329 :=
p16223 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 32053128399 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p16328 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p16240 565854040676687183 p16241 285835815970105
    137438953472 3372 137438953472
    (@p16245 p16238 p16239 565854040676687183
      p16241
      (p16247 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p16250 (p16281 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p16243 p16244)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p16330 :=
nat_lit 2096694831065771559527656449787397308081

noncomputable def p16331 :=
BSN.sin_dyadic_bound_f 6766807253 137438953472 2 1 137438953472
  68719476736 p16330 p3178 p16330
  p16330 p3179

noncomputable def p16332 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 6766807253) (BSN.sinEvenQ 137438953472) 0
  1 p16330 p3178 p16330 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16333 :=
p16331 p16330 6764073697 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16332 (Eq.refl true))

noncomputable def p16334 :=
@BSN.binarySplit_of_base (BSN.sinOddP 6766807253) (BSN.sinOddQ 137438953472) 0 1
  p16330 p3179 p16330 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16335 :=
nat_lit 1181883564803527034762933503132253488440286916601980828483442420322891081455197473347771745

noncomputable def p16336 :=
nat_lit 1199792699163014185890521722121372915384205007149544498053509791248079977193602588001

noncomputable def p16337 :=
nat_lit 3095407393868676922356143923549304273216031302387557261051257109448862240253173164363783521

noncomputable def p16338 :=
BSN.sin_dyadic_bound_f 32351042251 137438953472 3 2 137438953472
  68719476736 p16335 p2477 p16336
  p16337 p2480

noncomputable def p16339 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 32351042251) (BSN.sinEvenQ 137438953472) 0
  2 p16335 p2477 p16336 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16340 :=
p16338 p16336 32053128399 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16339 (Eq.refl true))

noncomputable def p16341 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 32351042251) (BSN.sinOddQ 137438953472) 0
  2 p16337 p2480 p16336 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16342 :=
p16329 d113 d115 d117 d119 d103
  (p16333 (p16334 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p16340 (p16341 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16343 :=
p16219 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 121323771891 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p16342 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p16240 565854040676687183 p16241 285835815970105
    137438953472 3372 137438953472
    (@p16245 p16238 p16239 565854040676687183
      p16241
      (p16247 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p16250 (p16281 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p16243 p16244)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p16344 :=
nat_lit 44615468346884728992260549114747926055048241656421617039603121776733918497811567313450075425

noncomputable def p16345 :=
nat_lit 1709603265345751687973728403292570093277140940173543427093259186727563412759115112809761

noncomputable def p16346 :=
nat_lit 116847268217506587572235194978353523125927708014820144604840501281334132391600113920281838881

noncomputable def p16347 :=
BSN.sin_dyadic_bound_f 80188468179 137438953472 3 2 137438953472
  68719476736 p16344 p2477 p16345
  p16346 p2480

noncomputable def p16348 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 80188468179) (BSN.sinEvenQ 137438953472) 0
  2 p16344 p2477 p16345 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16349 :=
p16347 p16345 75715766741 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16348 (Eq.refl true))

noncomputable def p16350 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 80188468179) (BSN.sinOddQ 137438953472) 0
  2 p16346 p2480 p16345 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16351 :=
nat_lit
  3228515407530721372052493707294286935902877287179086971697151500531275214559658749614290994960257977862418247601283826039567025396176540290625

noncomputable def p16352 :=
nat_lit
  116542815219981456606920607893505830343168580042016796027208970876808739939385333794521741043660879835533883658582893334717558837890625

noncomputable def p16353 :=
nat_lit
  16138061133551716339627942566889147834978273469761069580678209606501692435943247909542295202529638074105889230332076945317581124480823349890625

noncomputable def p16354 :=
BSN.sin_dyadic_bound_f 148664448945 137438953472 4 3 137438953472
  68719476736 p16351 p2504 p16352
  p16353 p2507

noncomputable def p16355 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 148664448945) (BSN.sinEvenQ 137438953472) 0
  3 p16351 p2504 p16352 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16356 :=
p16354 p16352 121323771891 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16355 (Eq.refl true))

noncomputable def p16357 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 148664448945) (BSN.sinOddQ 137438953472) 0
  3 p16353 p2507 p16352 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16358 :=
p16343 d121 d123 d125 d127 d103
  (p16349 (p16350 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p16356 (p16357 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16359 :=
p16215 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 123671883084 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p16358 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p16240 565854040676687183 p16241 285835815970105
    137438953472 3372 137438953472
    (@p16245 p16238 p16239 565854040676687183
      p16241
      (p16247 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p16250 (p16281 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p16243 p16244)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p16360 :=
nat_lit
  12041008777689610654593081009922466063265458414248442648416272691439558475894392924275027442337658940394750258873757993510373898637301135790625

noncomputable def p16361 :=
nat_lit
  6023645691636429182679907065419722455373711733224093822462254456350168975843359147320227394703651742523731391672180703607516426025390625

noncomputable def p16362 :=
nat_lit
  60142365743342874498007586636687650090937019736307192776627077970584311084475609460796264658002921701673485095160537553745241745677217577390625

noncomputable def p16363 :=
BSN.sin_dyadic_bound_f 206532444295 137438953472 4 3 137438953472
  68719476736 p16360 p2504 p16361
  p16362 p2507

noncomputable def p16364 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 206532444295) (BSN.sinEvenQ 137438953472) 0
  3 p16360 p2504 p16361 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16365 :=
p16363 p16361 137120616100 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16364 (Eq.refl true))

noncomputable def p16366 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 206532444295) (BSN.sinOddQ 137438953472) 0
  3 p16362 p2507 p16361 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16367 :=
nat_lit
  3703029328786376960625934639954954643918721111452496223480032416920817077538129234450469720375545974519106308194315756420933816152576804534241

noncomputable def p16368 :=
nat_lit
  175817359861897713396316944676801874291840463458052098800029122911429661722489091172166136242337565731755564715511958164409789761206241

noncomputable def p16369 :=
nat_lit
  18509206429404741779363368965419867773923833008142495152460384794885388861518343977030546259547254400524916935399883442100751831510764652869601

noncomputable def p16370 :=
BSN.sin_dyadic_bound_f 153846804297 137438953472 4 3 137438953472
  68719476736 p16367 p2504 p16368
  p16369 p2507

noncomputable def p16371 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 153846804297) (BSN.sinEvenQ 137438953472) 0
  3 p16367 p2504 p16368 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16372 :=
p16370 p16368 123671883084 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16371 (Eq.refl true))

noncomputable def p16373 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 153846804297) (BSN.sinOddQ 137438953472) 0
  3 p16369 p2507 p16368 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16374 :=
p16359 d129 d131 d133 d135 d103
  (p16365 (p16366 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p16372 (p16373 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16375 :=
p16210
  (p16374 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p16240 565854040676687183 p16241 285835815970105
    137438953472 3372 137438953472
    (@p16245 p16238 p16239 565854040676687183
      p16241
      (p16247 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (p16250 (p16281 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p16243 p16244)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p16376 :=
nat_lit 90855969871552296422397803510256141053788478341792156725172897450325193154354122966965281

noncomputable def p16377 :=
nat_lit 22972562296643789598963734691931441390373141747111054115226167940080450882797575201

noncomputable def p16378 :=
nat_lit 272567863669532295979614212603299039298482654279092975953410461898639699302160603305745441

noncomputable def p16379 :=
BSN.cos_dyadic_bound_f 19731094643 137438953472 3 2 137438953472
  68719476736 p16376 p2466 p16377
  p16378 p2469

noncomputable def p16380 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 19731094643) (BSN.cosEvenQ 137438953472) 0
  2 p16376 p2466 p16377 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16381 :=
p16379 p16377 136025060657 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16380 (Eq.refl true))

noncomputable def p16382 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 19731094643) (BSN.cosOddQ 137438953472) 0
  2 p16378 p2469 p16377 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16383 :=
p16375 d137 d139 d103
  (p16381 (p16382 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p16384 :=
@p16199 p16183 p16185 p16186
  (p16203
    (@p16206 27331 8589934592
      (p16383 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p16383 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p16385 :=
@Enclosure.Real.IsNear.mulLit_ff p16190
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv.{0} Real Real.instInv p16191)))

noncomputable def p16386 :=
nat_lit
  29546651216702175961954266358838880315539686121044848058253765451517246208756895369538936238407576383004673384194364835750665738461046268946216045569238905119712958794245295

noncomputable def p16387 :=
nat_lit
  11431522151447464638149000629651821989699872327784894142862558883193081711135952401460931184229054383816259566592243210461759888275155233127894859882247610690930759056086657940471385944885134310327421997322770137238924535919

noncomputable def p16388 :=
nat_lit
  35944283917655559839147332763439659390702892147087383687118651690221621184870630118534468066307672073634598956733705249734462389816231029770337229327040512000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16389 :=
@p16385 4815594999 17179869184 1 17179869184
  p16386 p4771 p16387 p16388
  p16196 p16183 p16197

noncomputable def p16390 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)))
    12)
  (p16189
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p16391 :=
@p16390 1 1 0 1 4815594999 17179869184
  1 17179869184 4815594999 17179869184 1

noncomputable def p16392 :=
@Enclosure.Real.IsNear.of_eq
  (p16189
    (@Neg.neg.{0} Real Real.instNeg
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real 4
          (@instOfNatAtLeastTwo.{0} Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))))

noncomputable def p16393 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p16394 :=
p16393
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    101779300 100000
    (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true)))

noncomputable def p16395 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv (Real.sqrt p16191)) false
  4815594999 17179869184 1 17179869184 4815594999
  17179869184

noncomputable def p16396 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p16191) false 61290018215
  17179869184 7 17179869184 61290018215 17179869184 7
  17179869184

noncomputable def p16397 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p16398 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p16399 :=
@p16398
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101779300 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2782911810805679

noncomputable def p16400 :=
@p16399 17179869184000 1017793 17179869184000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    101779300 100000
    (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true)))

noncomputable def p16401 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101779300 100000)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101779300 100000 0

noncomputable def p16402 :=
@p16401 1 2734261103 17179869184 1 17179869184
  2782911810805679 17179869184000 1017793 17179869184000
  (Enclosure.Real.IsNear.const false 101779300 100000) d142

noncomputable def p16403 :=
@p16397 2782911810805679 17179869184000 1017793 17179869184000
  109327559246 109327559287 8589934592
  (p16400 (p16402 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16404 :=
@Enclosure.Real.IsNear.recentre' p16191 false 218655118533 17179869184
  41 17179869184 218655118533 17179869184 41 17179869184
  (p16403 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p16405 :=
@Enclosure.Real.IsNear.sqrt_image p16191 218655118533 17179869184 41
  17179869184 30645009104 30645009111 8589934592
  (p16404 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p16406 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p16191) 61290018215 17179869184
  7 17179869184 2407797499 2407797500 8589934592
  (p16396
    (p16405 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p16407 :=
@p16392 (@Inv.inv.{0} Real Real.instInv (Real.sqrt p16191)) false
  4815594999 17179869184 1 17179869184 p16394
  (@p16395 1 17179869184
    (p16406 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16408 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv.{0} Real Real.instInv p16191))
  2207355985858979495

noncomputable def p16409 :=
nat_lit
  49153874704108536953186107070969104017198599674138985031418241235559356313260326945077347860863126716819294845198976799321658267794450837360443589299878473454969915366225

noncomputable def p16410 :=
nat_lit
  44121485552774218895304369817999168573687179722622520598891569633875730898612445332310743616076744310367609196553865604357674365171501363389508744595589910310253018695552646823795314961711436775807332440923379079641511973

noncomputable def p16411 :=
nat_lit
  11981427972551853279715777587813219796900964049029127895706217230073873728290210039511489355435890691211532985577901749911487463272077009923445743109013504000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16412 :=
nat_lit
  136259878307415994287645582899123852708911659540296546421274587530229087943219253013804211314792285996092323442598163087297628036015233212715810881890853474089214370779200156354496173891911680

noncomputable def p16413 :=
@p16408 4611686018427387904 597998256640228986457 p9404
  p16409 p4771 p16410 p16411
  p16412 p16386 p4771 p16387

noncomputable def p16414 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16415 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))

noncomputable def p16416 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (p16414
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16417 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
    true 5)
  101779300 100000 12
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))

noncomputable def p16418 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16419 :=
@p16418
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p16415 (Enclosure.sfrac false 1 16))))
  15176067835

noncomputable def p16420 :=
@p16419 2147483648 6573 8589934592 145449797
  2147483648 8226874489 221459251200000000 2207355985858979495
  4611686018427387904 597998256640228986457 p9404

noncomputable def p16421 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv.{0} Real Real.instInv
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16422 :=
@Inv.inv.{0} Real Real.instInv
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16423 :=
@p16421 (@Neg.neg.{0} Real Real.instNeg p16422) true 15176067835
  2147483648 6573 8589934592
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16424 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg.{0} Real Real.instNeg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16425 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p16426 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p16427 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 9814876059)
    (@Nat.cast.{0} Real Real.instNatCast 2147483648))
  false

noncomputable def p16428 :=
nat_lit 11050568040506006401995375

noncomputable def p16429 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  false p16428

noncomputable def p16430 :=
nat_lit 1106429199116541192021966047

noncomputable def p16431 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p16432 :=
@Enclosure.Real.IsNear.subLit_ff_p p16191 (Enclosure.sfrac false 12 1)
  218655118533 17179869184 41 17179869184 12 1 0

noncomputable def p16433 :=
@p16431 500000000000000 12496688325 17179869184 41
  17179869184 p16428 p2602 p16430
  p5018 d141
  (@p16432 1 12496688325 12496688325 17179869184 41
    17179869184 (p16404 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16434 :=
@p16427 9814876059 2147483648 129 8589934592 true
  2431030788 17179869184 1 3300000000
  (@p16429 p2602 p16430 p5018
    9814876059 2147483648 129 8589934592
    (p16433 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 9814876059 2147483648)

noncomputable def p16435 :=
nat_lit 442196875933097435246624768

noncomputable def p16436 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 9814876059)
    (@Nat.cast.{0} Real Real.instNatCast 2147483648))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p16435)
    (@Nat.cast.{0} Real Real.instNatCast p976))
  226375608064910080 72057594037927936 false

noncomputable def p16437 :=
BSN.sin_reduce_arg_pos_rat_q2 9814876059 2147483648 226375608064910080
  72057594037927936 0 p16435 p976 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16438 :=
nat_lit
  300126287206655724427814074985397627552021067928545732303726761171651223523998570313022245215445423353243976818329322435165043408524007465488342211800060481571019219110801

noncomputable def p16439 :=
nat_lit
  260561519120190649193050265838537423548132949246455626396819171058866419596492940273950225269345575508262719694729342623106575215344847635806501891253073425465183121

noncomputable def p16440 :=
nat_lit
  1817760950461990584523918673402999318616264862345635122860583573561919467734020862083141339335045101371224716328419654411830455080567906450491854770669567072360180800654225

noncomputable def p16441 :=
BSN.cos_dyadic_bound_f 50271964475211 35184372088832 4 3 17179869184
  6606445313 p16438 p2613 p16439
  p16440 p2616

noncomputable def p16442 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 50271964475211) (BSN.cosEvenQ 35184372088832) 0
  3 p16438 p2613 p16439 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16443 :=
p16441 p16439 2431030788 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16442 (Eq.refl true))

noncomputable def p16444 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 50271964475211) (BSN.cosOddQ 35184372088832) 0
  3 p16440 p2616 p16439 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16445 :=
@BSN.cos_arg_round false 2431030788 17179869184 p16435 p976
  50271964475211 35184372088832 6606445313 6600000000
  (p16443 (p16444 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16446 :=
p16436 2431030788 17179869184 0 1000000000000000
  6600000000 3300000000 p16437 BSN.pi_near_15 p16445
  (Eq.refl true) (Eq.refl true)

noncomputable def p16447 :=
@p16425 607757697 4294967296 1696445057 110729625600000000
  (@p16426 2431030788 17179869184 434289934592
    28346784153600000000 607757697 4294967296 1696445057
    110729625600000000
    (p16434 (p16446 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16448 :=
@p16424 607757697 4294967296 1696445057 110729625600000000
  60704264767 60704277913 8589934592 p16447
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16449 :=
@Enclosure.Real.IsNear.recentre' p16422 false 121408542680 17179869184
  13146 17179869184 15176067835 2147483648 6573 8589934592
  (p16448 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p16450 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p16415 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p16451 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p16415 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 14075282637))
    (@Nat.cast.{0} Real Real.instNatCast 8589934592))
  true

noncomputable def p16452 :=
nat_lit 68063890394405241622150712966522005

noncomputable def p16453 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p16415 (Enclosure.sfrac false 1 16)))
  true p16452

noncomputable def p16454 :=
nat_lit 46661706791678952848690689415864092397

noncomputable def p16455 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p16415 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p16456 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))

noncomputable def p16457 :=
@p16456 (Enclosure.sfrac false 1 16) 58524251564528771175
  295147905179352825856 1729103080875 295147905179352825856 1 16
  0

noncomputable def p16458 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
    (Enclosure.sfrac false 12 1))
  156167219092191305625

noncomputable def p16459 :=
nat_lit 1005438985970111623390769971200

noncomputable def p16460 :=
@p16458 295147905179352825856 1024728444331 295147905179352825856
  12496688325 17179869184 41 17179869184 p16459
  58524251564528771175 295147905179352825856 1729103080875

noncomputable def p16461 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
    (Enclosure.sfrac false 12 1))
  12496688325 17179869184 41

noncomputable def p16462 :=
@p16461 17179869184 12496688325 17179869184 41
  17179869184 156167219092191305625 295147905179352825856 1024728444331
  295147905179352825856
  (@p16432 1 12496688325 12496688325 17179869184 41
    17179869184 (p16404 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16463 :=
p16462
  (@p16432 1 12496688325 12496688325 17179869184 41
    17179869184 (p16404 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16464 :=
@p16460 295147905179352825856 (p16463 (Eq.refl true))
  (@p16432 1 12496688325 12496688325 17179869184 41
    17179869184 (p16404 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16465 :=
@p16455 500000000000000 76970995638238322791 295147905179352825856
  1729103080875 295147905179352825856 p16452 p2630
  p16454 p2632 d141
  (@p16457 1 1231535930211813164656 76970995638238322791
    295147905179352825856 1729103080875 295147905179352825856
    (p16464 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16466 :=
@p16451 14075282637 8589934592 633 17179869184 true
  581799188 8589934592 1 3300000000
  (@p16453 p2630 p16454 p2632
    14075282637 8589934592 633 17179869184
    (p16465 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 14075282637 8589934592)

noncomputable def p16467 :=
nat_lit
  5545948533771638402528839870321854605148491968110790203280114299680297276167310158019212872087329330143195769689900375128670902613048819602299160160745085303913572689453121

noncomputable def p16468 :=
nat_lit
  2373088804884414560940728832305105308261648308196641774412693784878817864135690692874316686208514933507018717120234415982120125751850792553504460161861419409023041

noncomputable def p16469 :=
nat_lit
  56407419777464624080567035244387585415136761040059631408579955186323908698758168698124420777244030000485487168446528711157417718850306652969673278797522239889340628344447041

noncomputable def p16470 :=
BSN.cos_dyadic_bound_t 14075282637 8589934592 5 4 8589934592
  3300000000 p16467 p2646 p16468
  p16469 p2649

noncomputable def p16471 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 14075282637) (BSN.cosEvenQ 8589934592) 0
  4 p16467 p2646 p16468 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16472 :=
p16470 p16468 581799188 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16471 (Eq.refl true))

noncomputable def p16473 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 14075282637) (BSN.cosOddQ 8589934592) 0 4
  p16469 p2649 p16468 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16474 :=
p16466
  (BSN.cos_neg_of_bound 14075282637 8589934592 true 581799188 8589934592
    1 3300000000
    (p16472 (p16473 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p16475 :=
p16420
  (p16423
    (@Enclosure.Real.IsNear.neg p16422 false 15176067835 2147483648
      6573 8589934592 (p16449 (Eq.refl true))))
  (@p16450 581799188 8589934592 2106079869184
    56693568307200000000 145449797 2147483648 8226874489
    221459251200000000 (p16474 (Eq.refl true)) (Eq.refl true))

noncomputable def p16476 :=
@p16413 p16388
  (@p16416 false 2207355985858979495 4611686018427387904
    597998256640228986457 p9404
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (p16417 (Eq.refl true) (Eq.refl true)
        (p16194 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16475 (Eq.refl true)))

noncomputable def p16477 :=
nat_lit
  36414780880141672211484064108856401260922601454351400334855959831784616730969021447538545087780797636122550474906157672037898271813946998241294053024685183460025

noncomputable def p16478 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv p16191) p16477 p4973

noncomputable def p16479 :=
nat_lit
  3268139670092378573376148270614900487895549511105880445525598395219753836496186549204718230631465009073258970634410509654434473166408924650409105124833096961713974008934433660903432399060847655373708069895966304561

noncomputable def p16480 :=
nat_lit
  69741089668543155303433174196474835025734291697323368255201594613456829266449262152376406333850991744615213163068411813068014239380584388991385600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16481 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p16482 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg.{0} Real Real.instNeg p16481) true p16477

noncomputable def p16483 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi)))

noncomputable def p16484 :=
nat_lit
  490307886553211226420498743285430367484325946168721894583873532255973899137695012056258488180011192167367336512823506303526180337786510889016598979325

noncomputable def p16485 :=
nat_lit
  51146728248377216718956089012931236753385031969422887335676427626502090568823039920051095192592252455482604439493126109519019633529459266458258243584

noncomputable def p16486 :=
nat_lit
  88007669278121897887499355528611040868185105171520701388610397318738485618153783825400281122118689526590571224288358861442853289134840071914487870657171526522372543204677072449425045833062767269201206569

noncomputable def p16487 :=
nat_lit
  1982160985919084490189822366701117602637347422879752464700732008778255398807722888033606703113804080220893785140913559333398957260800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16488 :=
@p16483 p16484 p16485 p16486
  p16487 74269213037 70368744177664 1 70368744177664
  p16477 p4973 p16479

noncomputable def p16489 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16490 :=
p16489
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16491 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16490
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16492 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16491
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16493 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16494 :=
p16492
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16493
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16495 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16496 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16494
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p16495)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))

noncomputable def p16497 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16498 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16496
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p16497)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))

noncomputable def p16499 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))

noncomputable def p16500 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (p16414
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16498
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16499
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
            (Enclosure.sfrac false 12 1))))))

noncomputable def p16501 :=
@p16418
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16498
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16499
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))
  62161169265797

noncomputable def p16502 :=
nat_lit
  7887687640763118765809955483453691642266011257435375779231612524268148577205713822413979558908273867053962055821079454803218460860275225

noncomputable def p16503 :=
nat_lit
  5814709794364855124394590463104036274829130885498544482251921593445114304907183386609528405710108524486100172850129423468276813028917248

noncomputable def p16504 :=
nat_lit
  2123685077639848324189060106902383483169989225261620112901612134165534365367787689130296404984317620447531269833896703397213099687136784184081854532073523184313330502571789103125407460700949

noncomputable def p16505 :=
nat_lit
  338018421516452091882994585609103115070413552339190198046150955311461882298724996422880628264318388611552640862938726400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16506 :=
@p16501 8796093022208 3299 17592186044416 p16502
  p16503 p16504 p16505 p16484
  p16485 p16486 p16487

noncomputable def p16507 :=
@p16421 (@Neg.neg.{0} Real Real.instNeg p16422) true 62161169265797
  8796093022208 3299 17592186044416
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16508 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 80403464490481)
    (@Nat.cast.{0} Real Real.instNatCast 17592186044416))
  false

noncomputable def p16509 :=
nat_lit 45263126589828457897259614725

noncomputable def p16510 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  false p16509

noncomputable def p16511 :=
nat_lit 1106868779901699748128062687

noncomputable def p16512 :=
@Enclosure.Real.IsNear.subLit_ff_p p16191 (Enclosure.sfrac false 12 1)
  895611365393463 70368744177664 41 70368744177664 12 1
  0

noncomputable def p16513 :=
@p16398
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 101779300 100000)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2279761354833295137

noncomputable def p16514 :=
@p16513 14073748835532800 1017793 70368744177664000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    101779300 100000
    (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true)))

noncomputable def p16515 :=
@p16401 1 11199533475045 70368744177664 1
  70368744177664 2279761354833295137 14073748835532800 1017793
  70368744177664000 (Enclosure.Real.IsNear.const false 101779300 100000)
  d198

noncomputable def p16516 :=
@p16397 2279761354833295137 14073748835532800 1017793
  70368744177664000 447805682696711 447805682696752 35184372088832
  (p16514 (p16515 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16517 :=
@Enclosure.Real.IsNear.recentre' p16191 false 895611365393463 70368744177664
  41 70368744177664 895611365393463 70368744177664 41
  70368744177664
  (p16516 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p16518 :=
@p16431 500000000000000 51186435261495 70368744177664 41
  70368744177664 p16509 p12189 p16511
  p12191 d197
  (@p16512 1 51186435261495 51186435261495 70368744177664
    41 70368744177664 (p16517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16519 :=
@p16508 80403464490481 17592186044416 259 70368744177664
  true 9957502842265 70368744177664 1 13516800000000
  (@p16510 p12189 p16511 p12191
    80403464490481 17592186044416 259 70368744177664
    (p16518 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 80403464490481 17592186044416)

noncomputable def p16520 :=
nat_lit 3622476781004674019282619727872

noncomputable def p16521 :=
nat_lit 2535301200456458802993406410752

noncomputable def p16522 :=
BSN.cos_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 80403464490481)
    (@Nat.cast.{0} Real Real.instNatCast 17592186044416))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p16520)
    (@Nat.cast.{0} Real Real.instNatCast p16521))
  226375608064910080 72057594037927936 false

noncomputable def p16523 :=
BSN.sin_reduce_arg_pos_rat_q2 80403464490481 17592186044416 226375608064910080
  72057594037927936 0 p16520 p16521
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p16524 :=
nat_lit
  126108697350439288727078278093206996097643637134600237196558590116444917301163558829378782459625391199384218128676308901147797545194835927104415059419291722045337411798194610011404923303926380828047575142017400985502866819826133516777273240664600562817687269311225260698776378697670721536

noncomputable def p16525 :=
nat_lit
  10446548377952347980138584632951276018828049670723845826496064713699056985301517364745592472670528379968035383085886758114953259561281531373355708327060119959420727943941251202865439257084879042515663432253301875649556650092495109834868033186487570678792426234645492848977248256

noncomputable def p16526 :=
nat_lit
  1284185648112629058326645568306107427254698272883736052867306863780004320138846750625430833099947223830578961603297378042512542737354552764605456205762147215596563250143191724510747931665201147817986799433906336691754925345395931045891232941312961767535157363705863527262173288280941920256

noncomputable def p16527 :=
BSN.cos_dyadic_bound_f 205913964976200192 144115188075855872 5 4
  70368744177664 27060000000001 p16524 p12205
  p16525 p16526 p12208

noncomputable def p16528 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 205913964976200192) (BSN.cosEvenQ 144115188075855872)
  0 4 p16524 p12205 p16525
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16529 :=
p16527 p16525 9957502842265 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16528 (Eq.refl true))

noncomputable def p16530 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 205913964976200192) (BSN.cosOddQ 144115188075855872)
  0 4 p16526 p12208 p16525
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16531 :=
@BSN.cos_arg_round false 9957502842265 70368744177664 p16520
  p16521 205913964976200192 144115188075855872 27060000000001
  27033600000000
  (p16529 (p16530 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16532 :=
p16522 9957502842265 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p16523 BSN.pi_near_15 p16531
  (Eq.refl true) (Eq.refl true)

noncomputable def p16533 :=
@p16425 9957502842265 70368744177664 3405780739
  907097092915200000000
  (@p16426 9957502842265 70368744177664 3571219944177664
    p4996 9957502842265 70368744177664 3405780739
    907097092915200000000
    (p16519 (p16532 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16534 :=
@p16424 9957502842265 70368744177664 3405780739
  907097092915200000000 248644677056590 248644677069786 35184372088832
  p16533 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16535 :=
@Enclosure.Real.IsNear.recentre' p16422 false 497289354126376 70368744177664
  13196 70368744177664 62161169265797 8796093022208 3299
  17592186044416
  (p16534 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p16536 :=
nat_lit
  691308362431985967530725425595675556094102339695287052806766670847430960494979053475000215809856555953386376240832921550030388702502771225

noncomputable def p16537 :=
@Enclosure.Real.IsNear.subLit_tt_n p16498
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16499
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))
  p16536 p16503

noncomputable def p16538 :=
nat_lit
  705717320796046377039315604865366871558474439596388842930415760839467784276640673222370941393013184493646398931941850350332410188452375288590373519336735924409937132819798287708469153566983

noncomputable def p16539 :=
nat_lit
  112672807172150697294331528536367705023471184113063399348716985103820627432908332140960209421439462870517546954312908800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16540 :=
nat_lit 3567622386190186442622483178777906821315004397056343704646744410992668801836324489875

noncomputable def p16541 :=
nat_lit 30354201441027016733116592294117482916287606860189680019559568902170379456331382784

noncomputable def p16542 :=
nat_lit
  1847164814993287743998947510420739214988845361996612483161964078847806718411790512009604633603960449010219165479860351247

noncomputable def p16543 :=
nat_lit
  95570904689215646928360610122930917329397299075998318463287212113920000000000000000000000000000000000000000000000000000000000000

noncomputable def p16544 :=
nat_lit
  239424459551622849532700232961257764074781765932962782744833982534047181159368253361136614769505618065981593469154340371224402688191442500982248152830395276224317467448447186508391816363445122099476640565850639066726400

noncomputable def p16545 :=
@p16537 p16538 p16539 p16540
  p16541 p16542 p16543 p16544
  p16502 p16503 p16504 p16505

noncomputable def p16546 :=
@Enclosure.Real.IsNear.subLit_tf p16496
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p16497)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))

noncomputable def p16547 :=
nat_lit
  604481873842105904332775550523264309527207679190485715873104163281289298491099464745986284465379757638851900640250175390029556371709811225

noncomputable def p16548 :=
nat_lit
  698651059609950134619778816211774862170673179988743212135401699044203006438131359748817421246067794123161883638112135670506728913086424912162473753703369081671901785117966684228302753566983

noncomputable def p16549 :=
nat_lit 280551515693771323378082511547620466585247148964598907314634247106703627958110760370144931854252634979199863125

noncomputable def p16550 :=
nat_lit 18788340662190665823115844774314696219005460391266558965658327772257672200916867547709591987078149624255479808

noncomputable def p16551 :=
nat_lit
  1328425967357903111198565704184165386313834865905595737556355057619708313843046943912720680881313482424297241087996839518751422925848756997688467502082931

noncomputable def p16552 :=
nat_lit
  21181991285165632662682040713069393221558628374760633981224241703833449296757821530703921152000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p16553 :=
nat_lit
  12988537015993324041120901595327979295584480300201846816320967096222068254961548731904137163884177546615362272637484467104894180513888816483028535497985958360864046635043662738098856299769756043843843122919891661339357004909439605072546512030924800

noncomputable def p16554 :=
@p16546 p16547 p16503 p16548
  p16539 p16549 p16550 p16551
  p16552 p16553 p16536 p16503

noncomputable def p16555 :=
@Enclosure.Real.IsNear.subLit_tf p16494
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 3 1) p16495)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))

noncomputable def p16556 :=
nat_lit 34144543383537172804184388792209941045420195003984543466116002882937448213803303660092797949673175

noncomputable def p16557 :=
nat_lit
  362130177363973673034504887209768323926665998562276672072773157985020995586120848234518710591412089885031179564212526821589279

noncomputable def p16558 :=
nat_lit
  260856418633825925050220715027572118811846621454755062668090045253026698452847820800000000000000000000000000000000000000000000000000000

noncomputable def p16559 :=
nat_lit
  511531585522228320892359739879971763637047521202436826198917212020574723271495318431101872478479979555097890376309661967754391015782668825

noncomputable def p16560 :=
nat_lit
  698494643203334419443688386426650586595375055755378427620338520214514031270518681473767654459778031335356594978391031743443784535833701668351679580681389599366308441117966684228302753566983

noncomputable def p16561 :=
nat_lit
  1291165445975917300997989766048137147459457167719244781081895435294861348795954042327420795279460234922105236769352379215997740881706489409259922575806331648111634911104893537156436333376785795209252025352855082121544190782703507865600

noncomputable def p16562 :=
@p16555 p16556 p14587 p16557
  p16558 p16559 p16503 p16560
  p16539 p16561 p16547 p16503

noncomputable def p16563 :=
@Enclosure.Real.IsNear.subLit_tt_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16491
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16564 :=
@p16563
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16493
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16565 :=
nat_lit 49729983097699468496982950045854765811462105048688859092915330293004388940205863547706660506140375

noncomputable def p16566 :=
nat_lit
  101982241392701628799331014863622946141174333272927532780514454910596622742981938488082819469837682701952132396212526821589279

noncomputable def p16567 :=
nat_lit 44728018405954848518236172021973203135879827597093695675

noncomputable def p16568 :=
nat_lit 24464194328984675862753974539341963763909152146820964553035768258074091071

noncomputable def p16569 :=
nat_lit
  209305441920690425744639693346187617951451492783679413944186333327374454703381191845964660082697792283937877782677596792747916324608030207762733675315200

noncomputable def p16570 :=
@p16564 p16565 p14587 p16566
  p16558 p16567 p2977 p16568
  p14478 p16569 p16556 p14587

noncomputable def p16571 :=
nat_lit 2833328534498852617871430243557839752351733576828241139050050053422649418490282432125

noncomputable def p16572 :=
@Enclosure.Real.IsNear.mulLit_ft p16491
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p16415 (Enclosure.sfrac false 1 16))))
  p16571

noncomputable def p16573 :=
nat_lit 619056392292062524966528888203635384462704887291629739581602968347263323131113921166033886137467177366207

noncomputable def p16574 :=
@p16572 p12222 p16573 p14484
  17551788467939 17592186044416 4119882557 453548546457600000000
  p16565 p14587 p16566 p16558

noncomputable def p16575 :=
@Enclosure.Real.IsNear.mulLit_ff p16490
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16576 :=
nat_lit 200230987990083414062382684870287311033933037078181811225

noncomputable def p16577 :=
nat_lit 955703646752871757004468691613299181266256232619599086279829635199

noncomputable def p16578 :=
nat_lit 14150299925799573456275816965

noncomputable def p16579 :=
nat_lit 1106566548446796090834386143

noncomputable def p16580 :=
@p16575 p16576 p12261 p16577
  p14489 p16578 p12265 p16579
  p14492 p16571 p12222 p16573

noncomputable def p16581 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16582 :=
@p16581
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16583 :=
@p16582 p16578 p12265 p16579
  p14492 p16578 p12265 p16579
  p14492 p16576 p12261 p16577

noncomputable def p16584 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p16585 :=
@p16584 140737488355328 1 500000000000000 16002063172663
  35184372088832 41 35184372088832 p16578 p12265
  p16579 p14492

noncomputable def p16586 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 51186435261495 35184372088832

noncomputable def p16587 :=
@p16586 41 35184372088832 1 1 0 1
  16002063172663 16002063172663 35184372088832 41 35184372088832

noncomputable def p16588 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p16589 :=
@p16588 51186435261495 70368744177664 41 70368744177664
  51186435261495 35184372088832 41 35184372088832
  (Enclosure.Real.IsNear.const false 2 1)
  (@p16512 1 51186435261495 51186435261495 70368744177664
    41 70368744177664 (p16517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16590 :=
@p16583 p14489
  (p16585 d197
    (p16587 (p16589 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p16585 d197
    (p16587 (p16589 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p16591 :=
@p16580 p14484 (p16590 (Eq.refl true))
  (p16585 d197
    (p16587 (p16589 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p16592 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p16415 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p16593 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p16415 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 57652357850545))
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  true

noncomputable def p16594 :=
nat_lit 1141922594278384048010714691146249123642605

noncomputable def p16595 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p16415 (Enclosure.sfrac false 1 16)))
  true p16594

noncomputable def p16596 :=
nat_lit 191137440553857604702054691491044004765577

noncomputable def p16597 :=
nat_lit 1291359023324827906273393711

noncomputable def p16598 :=
nat_lit 981874013503482837548612655

noncomputable def p16599 :=
@p16456 (Enclosure.sfrac false 1 16) p16598
  p12265 7082406202728495 p12265 1 16 0

noncomputable def p16600 :=
nat_lit 20661744373197246500374299376

noncomputable def p16601 :=
nat_lit 2620051154779218709029635025

noncomputable def p16602 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
    (Enclosure.sfrac false 12 1))
  p16601

noncomputable def p16603 :=
nat_lit 69093241270922791638934686325092038737920

noncomputable def p16604 :=
@p16602 p12265 4197287691444271 p12265
  51186435261495 70368744177664 41 70368744177664 p16603
  p16598 p12265 7082406202728495

noncomputable def p16605 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
    (Enclosure.sfrac false 12 1))
  51186435261495 70368744177664 41

noncomputable def p16606 :=
@p16605 70368744177664 51186435261495 70368744177664 41
  70368744177664 p16601 p12265 4197287691444271
  p12265
  (@p16512 1 51186435261495 51186435261495 70368744177664
    41 70368744177664 (p16517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16607 :=
p16606
  (@p16512 1 51186435261495 51186435261495 70368744177664
    41 70368744177664 (p16517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16608 :=
@p16604 p12265 (p16607 (Eq.refl true))
  (@p16512 1 51186435261495 51186435261495 70368744177664
    41 70368744177664 (p16517 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16609 :=
@p16455 500000000000000 p16597 p12265
  7082406202728495 p12265 p16594 p12284
  p16596 p12286 d197
  (@p16599 1 p16600 p16597 p12265
    7082406202728495 p12265
    (p16608 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16610 :=
@p16593 57652357850545 35184372088832 317 35184372088832
  true 35103576935878 35184372088832 1 13516800000000
  (@p16595 p12284 p16596 p12286
    57652357850545 35184372088832 317 35184372088832
    (p16609 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 57652357850545 35184372088832)

noncomputable def p16611 :=
nat_lit
  118137489338458426187907074344058014154083979596074062110084185434900158087589238543085357177490731163531138342863783592052275910886280923487195409240209713673394919125256274753402806448044431421067451733188362841944025389680890625

noncomputable def p16612 :=
nat_lit
  14896120555646363582798084926650655351392187224125744770339392771199387870434553802299311911821096849435520952841516555813972058959946728611221317960749686611138819692659820053699064038168883742407712444514502105712890625

noncomputable def p16613 :=
nat_lit
  960561655923383148907785645935885150382021548350318219061266230194907140501882465695009430755473093254922528741456724479916542381837225104765562939707581674660725323671079886875843035176008780129450164391111163437230333024880890625

noncomputable def p16614 :=
BSN.sin_dyadic_bound_f 57652357850545 35184372088832 5 4
  35184372088832 13516800000000 p16611 p12302
  p16612 p16613 p12305

noncomputable def p16615 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 57652357850545) (BSN.sinEvenQ 35184372088832) 0
  4 p16611 p12302 p16612 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16616 :=
p16614 p16612 35103576935878 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16615 (Eq.refl true))

noncomputable def p16617 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 57652357850545) (BSN.sinOddQ 35184372088832) 0
  4 p16613 p12305 p16612 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16618 :=
p16610
  (BSN.sin_neg_of_bound 57652357850545 35184372088832 false 35103576935878
    35184372088832 1 13516800000000
    (p16616 (p16617 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p16619 :=
p16574 p16591
  (@p16592 35103576935878 35184372088832 4320009972088832
    p12185 17551788467939 17592186044416 4119882557
    453548546457600000000 (p16618 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16620 :=
nat_lit 37538469726606215947414967087828080092931725

noncomputable def p16621 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16493
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p16415 (Enclosure.sfrac false 1 16))))
  p16620

noncomputable def p16622 :=
nat_lit 89596793213203737487165116180268686328182431365272843

noncomputable def p16623 :=
@p16621 p12314 p16622 p14536
  1191524820583 17592186044416 4119882557 453548546457600000000
  p16567 p2977 p16568 p14478

noncomputable def p16624 :=
nat_lit 42450899777398720368827450895

noncomputable def p16625 :=
nat_lit 3319699645340388272503158429

noncomputable def p16626 :=
@Enclosure.Real.IsNear.mulLit_ff p16493
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p16624 p12265 p16625 p14492

noncomputable def p16627 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16628 :=
@p16627 3 1 0 1 p16578
  p12265 p16579 p14492 p16624
  p12265 p16625

noncomputable def p16629 :=
@p16628 p14492 (Enclosure.Real.IsNear.const false 3 1)
  (p16585 d197
    (p16587 (p16589 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p16630 :=
@p16626 884279719003555 70368744177664 1 250000000000000
  p16620 p12314 p16622 p14536
  p16629 d199 (Eq.refl true)

noncomputable def p16631 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p16415 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@Nat.cast.{0} Real Real.instNatCast 57652357850545))
    (@Nat.cast.{0} Real Real.instNatCast 35184372088832))
  true

noncomputable def p16632 :=
@p16631 57652357850545 35184372088832 317 35184372088832
  true 2383049641166 35184372088832 1 13516800000000
  (@p16595 p12284 p16596 p12286
    57652357850545 35184372088832 317 35184372088832
    (p16609 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 57652357850545 35184372088832)

noncomputable def p16633 :=
nat_lit
  34812483576594774759018915565601476525588443748583226749648936194976186416380047668063413454490226111275966206895551744457372248684144660555171805891156456346834958123461966073970935052947269657100356592317359264932517829232890625

noncomputable def p16634 :=
nat_lit
  354075116741100932250768794042334177778479391595824417683681137742926006392255104950696380952264508873925786759809095845008510843825929070201453760819103399401603851661503105149444587182625066371586027198596062045233524693616890625

noncomputable def p16635 :=
BSN.cos_dyadic_bound_t 57652357850545 35184372088832 5 4
  35184372088832 13516800000000 p16633 p12328
  p16612 p16634 p12330

noncomputable def p16636 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 57652357850545) (BSN.cosEvenQ 35184372088832) 0
  4 p16633 p12328 p16612 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16637 :=
p16635 p16612 2383049641166 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16636 (Eq.refl true))

noncomputable def p16638 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 57652357850545) (BSN.cosOddQ 35184372088832) 0
  4 p16634 p12330 p16612 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p16639 :=
p16632
  (BSN.cos_neg_of_bound 57652357850545 35184372088832 true 2383049641166
    35184372088832 1 13516800000000
    (p16637 (p16638 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p16640 :=
p16623 p16630
  (@p16450 2383049641166 35184372088832 4320009972088832
    p12185 1191524820583 17592186044416 4119882557
    453548546457600000000 (p16639 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16641 :=
nat_lit 184798540692163024545092771835

noncomputable def p16642 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p16495)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  p16641

noncomputable def p16643 :=
nat_lit 91916369348714849468386130199126613

noncomputable def p16644 :=
nat_lit 2768049918610214762169201174936818023957231388778538151872898375274492125495794754601979724468885634365836795

noncomputable def p16645 :=
nat_lit 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744

noncomputable def p16646 :=
nat_lit
  57645893661581433522086167503449012066572163253203489768982445845784603862788993423312884598271877663551090777143683636551195920313360420772857

noncomputable def p16647 :=
nat_lit
  173522872608076862772691277521464469271008283646039113574188988037803616639040073979526522077184000000000000000000000000000000000000000000000000000000

noncomputable def p16648 :=
@p16642 p12189 p16643 p13950
  p16644 p16645 p16646 p16647
  p16559 p16503 p16560 p16539

noncomputable def p16649 :=
nat_lit 61599513564054341515030923945

noncomputable def p16650 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p16495
  3 1 0 1 p16649 p12189

noncomputable def p16651 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16652 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p16653 :=
@p16652 140737488355328 1 500000000000000 69660665330499
  70368744177664 3405780739 907097092915200000000 p16649
  p12189 p16643 p13957

noncomputable def p16654 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p16655 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 80403464490481)
    (@Nat.cast.{0} Real Real.instNatCast 17592186044416))
  false

noncomputable def p16656 :=
@p16655 80403464490481 17592186044416 259 70368744177664
  true 69660665330499 70368744177664 1 13516800000000
  (@p16510 p12189 p16511 p12191
    80403464490481 17592186044416 259 70368744177664
    (p16518 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 80403464490481 17592186044416)

noncomputable def p16657 :=
BSN.sin_reduce2
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast 80403464490481)
    (@Nat.cast.{0} Real Real.instNatCast 17592186044416))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Nat.cast.{0} Real Real.instNatCast p16520)
    (@Nat.cast.{0} Real Real.instNatCast p16521))
  226375608064910080 72057594037927936 false

noncomputable def p16658 :=
nat_lit
  428297756979634575860614877435504483573105669246092865254184250162645310983821253102189408537889422764951037380684779291746047328519974310565840654722771602467948637378683349843220143613113530377082548119268778649451433133479962592848403998374706580321663054950808083590527760515177906176

noncomputable def p16659 :=
nat_lit
  3484599206696516637088454104790743904304720184461976871766350527440884178074369037936270703945141449334486409499675589969949296194890645799369408936317928938526648189378352558338720762920183287862625159507874381583125475335852763307309049895654532477987944965038190170609414981792175226880

noncomputable def p16660 :=
BSN.sin_dyadic_bound_f 205913964976200192 144115188075855872 5 4
  70368744177664 27060000000001 p16658 p12357
  p16525 p16659 p12359

noncomputable def p16661 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 205913964976200192) (BSN.sinEvenQ 144115188075855872)
  0 4 p16658 p12357 p16525
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16662 :=
p16660 p16525 69660665330499 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p16661 (Eq.refl true))

noncomputable def p16663 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 205913964976200192) (BSN.sinOddQ 144115188075855872)
  0 4 p16659 p12359 p16525
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p16664 :=
@BSN.sin_arg_round false 69660665330499 70368744177664 p16520
  p16521 205913964976200192 144115188075855872 27060000000001
  27033600000000
  (p16662 (p16663 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p16665 :=
p16657 69660665330499 70368744177664 0 1000000000000000
  27033600000000 13516800000000 p16523 BSN.pi_near_15 p16664
  (Eq.refl true) (Eq.refl true)

noncomputable def p16666 :=
p16653 d197
  (@p16654 69660665330499 70368744177664 3571219944177664
    p4996 69660665330499 70368744177664 3405780739
    907097092915200000000
    (p16656 (p16665 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16667 :=
@Neg.neg.{0} Real Real.instNeg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16490
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16668 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16667
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16669 :=
@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16668
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p16495)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))

noncomputable def p16670 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (p16414
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16669
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16497
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
            (Enclosure.sfrac false 12 1))))))

noncomputable def p16671 :=
@p16418
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16669
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16497
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))
  62161169265797

noncomputable def p16672 :=
nat_lit 44530209957509302086855882780402423715271641248099464201707742800866232297754130211994970308735

noncomputable def p16673 :=
nat_lit 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768

noncomputable def p16674 :=
nat_lit
  1390518857613562974069911117868020427577450396545189098932930513386401846445975794217611020377795370944536872221445221217821118997

noncomputable def p16675 :=
nat_lit
  29590899988774628372884412360940212227718851121273777421411464508390216105744924672000000000000000000000000000000000000000000000000000000

noncomputable def p16676 :=
@p16671 8796093022208 3299 17592186044416 p16672
  p16673 p16674 p16675 p16644
  p16645 p16646 p16647

noncomputable def p16677 :=
nat_lit 133950652216543241341391427889970864596279021245473026572554449206500030482502952552868501307265

noncomputable def p16678 :=
@Enclosure.Real.IsNear.subLit_ff_n p16669
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16497
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))
  p16677 p16673

noncomputable def p16679 :=
nat_lit
  1375708272851295913726575373697739738558640189190935097385963882292849162133344730146580130756062189929934991142458937800221118997

noncomputable def p16680 :=
nat_lit 576702769148926912540214157969498190013508440441994933243369509307875

noncomputable def p16681 :=
nat_lit 2784324676345591985637240597549836667120069651853918843485203993988468168118398751258809449429

noncomputable def p16682 :=
nat_lit 5562958813343176555840799708555622336536023013526475898880000000000000000000000000000000000000000000000

noncomputable def p16683 :=
nat_lit
  9604256684251769136820037386912889983235442015470664236655695596861488073251619523282419799384898972451637653927710655067748957909324431470738629662092430493614080

noncomputable def p16684 :=
@p16678 p16679 p16675 p16680
  p14600 p16681 p16682 p16683
  p16672 p16673 p16674 p16675

noncomputable def p16685 :=
@Enclosure.Real.IsNear.subLit_ff_p p16668
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) p16495)
    (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
      Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))

noncomputable def p16686 :=
nat_lit 5646751532755644123442517038000718350503993057422765123579231757143055

noncomputable def p16687 :=
nat_lit 989968313567330912326603278843991132474394703673226217917398151968814693873723557091609

noncomputable def p16688 :=
nat_lit 5178608931694011630164526274146324793284443241682828473139200000000000000000000000000000000000000

noncomputable def p16689 :=
nat_lit 739841824570244679702284464770656409968177927582589357393993449854628492831818591103940971675775

noncomputable def p16690 :=
nat_lit
  1370051531099752959553599797449946615992745324929440799728422590524440796069872776319589041819288393456220284137018937800221118997

noncomputable def p16691 :=
nat_lit
  57780839036608790726538164139150467465120124186069706470860091866307167612844044202040084868364395287089522530566815022053218355256027838171336211369394375061667840

noncomputable def p16692 :=
@p16685 p16686 p12388 p16687
  p16688 p16689 p16673 p16690
  p16675 p16691 p16677 p16673

noncomputable def p16693 :=
@Enclosure.Real.IsNear.subLit_ft p16667
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16694 :=
nat_lit 238580192040040967723884627759554916907368578229416869163722100444175

noncomputable def p16695 :=
nat_lit 132938745439002454922588286985117177035443396704143740232517020595070839291241185697203

noncomputable def p16696 :=
nat_lit 1726202977231337210054842091382108264428147747227609491046400000000000000000000000000000000000000

noncomputable def p16697 :=
nat_lit 15520690574438936037144523145

noncomputable def p16698 :=
nat_lit 111183348365538533481613029431008619

noncomputable def p16699 :=
nat_lit 6990339814294303368349407141285018196515655590624499071732383192489028186514572349254475783864320

noncomputable def p16700 :=
@p16693 p16694 p12388 p16695
  p16696 p16697 p2445 p16698
  p12402 p16699 p16686 p12388

noncomputable def p16701 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16490
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16702 :=
@Enclosure.Real.IsNear.mulLit_ft p16490
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p16415 (Enclosure.sfrac false 1 16))))
  p16576

noncomputable def p16703 :=
@p16702 p12261 p16577 p14489
  1191524820583 17592186044416 4119882557 453548546457600000000
  p16694 p12388 p16695 p16696

noncomputable def p16704 :=
p16703 (p16590 (Eq.refl true))
  (@p16450 2383049641166 35184372088832 4320009972088832
    p12185 1191524820583 17592186044416 4119882557
    453548546457600000000 (p16639 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16705 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p16415 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p16706 :=
@p16705 70368744177664 1 250000000000000 17551788467939
  17592186044416 4119882557 453548546457600000000 p16697
  p2445 p16698 p12402

noncomputable def p16707 :=
p16706 d199
  (@p16592 35103576935878 35184372088832 4320009972088832
    p12185 17551788467939 17592186044416 4119882557
    453548546457600000000 (p16618 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16708 :=
@p16692 p16679 p16675
  (@p16700 p16687 p16688
    (@p16701 true p16694 p12388 p16695
      p16696 (p16704 (Eq.refl true)))
    (p16707 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16709 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 2 1) p16495)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  p16649

noncomputable def p16710 :=
nat_lit 12010514073311944411367405001333463085493768870425768587022203441895

noncomputable def p16711 :=
nat_lit 13479973333575319897333507543509815336818572211270286240551805124608

noncomputable def p16712 :=
nat_lit 112972058332483492196411043413436079376662242162522274766428128539184060202740841563

noncomputable def p16713 :=
nat_lit 30381172399271534896965220808325105453935400351205927042416640000000000000000000000000000000

noncomputable def p16714 :=
@p16709 p12265 p16643 p12348
  p16710 p16711 p16712 p16713
  p16689 p16673 p16690 p16675

noncomputable def p16715 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p16495
  2 1 0 1 p16649 p12189

noncomputable def p16716 :=
@Neg.neg.{0} Real Real.instNeg
  (p16489
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16717 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  (p16414
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16716
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16495
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
            (Enclosure.sfrac false 12 1))))))

noncomputable def p16718 :=
@p16418
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16716
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16495
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))
  62161169265797

noncomputable def p16719 :=
nat_lit 193215703873841078645288472947664849118640207188487035

noncomputable def p16720 :=
nat_lit 2708775086426430463607962153386764641514054077972425901394704758373823

noncomputable def p16721 :=
nat_lit 5180909124522634368241578069101667345069370245120000000000000000000000000000000

noncomputable def p16722 :=
@p16718 8796093022208 3299 17592186044416 p16719
  p5362 p16720 p16721 p16710
  p16711 p16712 p16713

noncomputable def p16723 :=
nat_lit 248363071055527040773707012452732934785135

noncomputable def p16724 :=
@Enclosure.Real.IsNear.subLit_ff_n p16716
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16495
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))
  p16723 p5940

noncomputable def p16725 :=
nat_lit 379971654118259005799233085817975287390563698671

noncomputable def p16726 :=
nat_lit 4562465056445183271968215188525429511285191193715043195

noncomputable def p16727 :=
nat_lit 2536439495006004150551799098345199669183826286809889770516855158373823

noncomputable def p16728 :=
nat_lit 16831461642364359985146991650100829129139348924541021112868481506397783033923216992408185077760

noncomputable def p16729 :=
@p16724 p16725 p14639 p16726
  p5362 p16727 p16721 p16728
  p16719 p5362 p16720 p16721

noncomputable def p16730 :=
@Enclosure.Real.IsNear.neg
  (p16489
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p16415 (Enclosure.sfrac false 1 16)))))

noncomputable def p16731 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p16732 :=
@p16731
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p16415 (Enclosure.sfrac false 1 16))))
  p16578

noncomputable def p16733 :=
@p16732 p12265 p16579 p14492
  17551788467939 17592186044416 4119882557 453548546457600000000
  p16723 p5940 p16725 p14639

noncomputable def p16734 :=
p16733
  (p16585 d197
    (p16587 (p16589 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p16592 35103576935878 35184372088832 4320009972088832
    p12185 17551788467939 17592186044416 4119882557
    453548546457600000000 (p16618 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16735 :=
@Enclosure.Real.IsNear.mulLit_ff p16495
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  p16649 p12189 p16643

noncomputable def p16736 :=
nat_lit 74066576056658264263499651

noncomputable def p16737 :=
nat_lit 2659636803152184184353587200000000

noncomputable def p16738 :=
@p16418
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p16415 (Enclosure.sfrac false 1 16))))
  62161169265797

noncomputable def p16739 :=
@p16738 8796093022208 3299 17592186044416 1191524820583
  17592186044416 4119882557 453548546457600000000 p16736
  p982 204511804200745665989217 p16737

noncomputable def p16740 :=
p16739
  (p16507
    (@Enclosure.Real.IsNear.neg p16422 false 62161169265797 8796093022208
      3299 17592186044416 (p16535 (Eq.refl true))))
  (@p16450 2383049641166 35184372088832 4320009972088832
    p12185 1191524820583 17592186044416 4119882557
    453548546457600000000 (p16639 (Eq.refl true))
    (Eq.refl true))

noncomputable def p16741 :=
@p16735 p13957 p16736 p982
  204511804200745665989217 p16737 p16726 p5362
  p16727 p16721
  (@p16651 true p16649 p12189 p16643
    p13957 (p16666 (Eq.refl true)))
  (@p16416 false p16736 p982
    204511804200745665989217 p16737
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (p16417 (Eq.refl true) (Eq.refl true)
        (p16194 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16740 (Eq.refl true)))

noncomputable def p16742 :=
p16722
  (p16507
    (@Enclosure.Real.IsNear.neg p16422 false 62161169265797 8796093022208
      3299 17592186044416 (p16535 (Eq.refl true))))
  (p16729
    (@p16730 true p16723 p5940 p16725
      p14639 (p16734 (Eq.refl true)))
    (p16741 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16743 :=
p16714
  (@p16715 p16643 p13957 p16649
    p12265 p16643 p12348
    (Enclosure.Real.IsNear.const false 2 1)
    (@p16651 true p16649 p12189 p16643
      p13957 (p16666 (Eq.refl true)))
    (Eq.refl true))
  (@p16717 false p16710 p16711 p16712
    p16713
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (p16417 (Eq.refl true) (Eq.refl true)
        (p16194 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16742 (Eq.refl true)))

noncomputable def p16744 :=
nat_lit 7786275535509702184975895076007191966126625

noncomputable def p16745 :=
nat_lit 2480313426677811152207904624057467084959209401787232941418771

noncomputable def p16746 :=
@Enclosure.Real.IsNear.mulLit_ff p16497
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  p16744 p12450 p16745

noncomputable def p16747 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
          (Enclosure.sfrac false 12 1)))))

noncomputable def p16748 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi))
  (Real.cos
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p16749 :=
@p16748 p1070 p1071 p1072
  9957502842265 70368744177664 3405780739 907097092915200000000
  p16744 p12450 p16745 p14058

noncomputable def p16750 :=
p16749 d201
  (@p16426 9957502842265 70368744177664 3571219944177664
    p4996 9957502842265 70368744177664 3405780739
    907097092915200000000
    (p16519 (p16532 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16751 :=
@p16746 p14058 p16736 p982
  204511804200745665989217 p16737 p16680 p14600
  p16681 p16682
  (@p16747 true p16744 p12450 p16745
    p14058 (p16750 (Eq.refl true)))
  (@p16416 false p16736 p982
    204511804200745665989217 p16737
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (p16417 (Eq.refl true) (Eq.refl true)
        (p16194 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16740 (Eq.refl true)))

noncomputable def p16752 :=
p16676
  (p16507
    (@Enclosure.Real.IsNear.neg p16422 false 62161169265797 8796093022208
      3299 17592186044416 (p16535 (Eq.refl true))))
  (p16684
    (p16708 (p16743 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p16751 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16753 :=
p16648
  (@p16650 p16643 p13957 p16641
    p12189 p16643 p13950
    (Enclosure.Real.IsNear.const false 3 1)
    (@p16651 true p16649 p12189 p16643
      p13957 (p16666 (Eq.refl true)))
    (Eq.refl true))
  (@p16670 false p16644 p16645 p16646
    p16647
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (p16417 (Eq.refl true) (Eq.refl true)
        (p16194 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16752 (Eq.refl true)))

noncomputable def p16754 :=
@p16562 p16548 p16539
  (@p16570 p16557 p16558
    (p16619 (Eq.refl true)) (p16640 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p16753 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p16755 :=
nat_lit 23358826606529106554927685228021575898379875

noncomputable def p16756 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 3 1) p16497)
  (@iteratedDeriv.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.normedAddCommGroup
    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
    (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  p16755

noncomputable def p16757 :=
@p16756 p12450 p16745 p14069
  p16710 p16711 p16712 p16713
  p16549 p16550 p16551 p16552

noncomputable def p16758 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p16497
  3 1 0 1 p16744 p12450

noncomputable def p16759 :=
p16757
  (@p16758 p16745 p14058 p16755
    p12450 p16745 p14069
    (Enclosure.Real.IsNear.const false 3 1)
    (@p16747 true p16744 p12450 p16745
      p14058 (p16750 (Eq.refl true)))
    (Eq.refl true))
  (@p16717 false p16710 p16711 p16712
    p16713
    (BSN.deriv_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (p16417 (Eq.refl true) (Eq.refl true)
        (p16194 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16742 (Eq.refl true)))

noncomputable def p16760 :=
nat_lit 48167777911875982395971056684229550974793874890737640008625

noncomputable def p16761 :=
nat_lit 66949171278731316097720004392210142757846625623198642679873819112578909413394110479557

noncomputable def p16762 :=
@Enclosure.Real.IsNear.mulLit_tf p16499
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
      (Enclosure.sfrac false 12 1)))
  p16760 p14074 p16761

noncomputable def p16763 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Real.pi) Real.pi))
  (Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))))

noncomputable def p16764 :=
@p16763 p1059 p1061 p1062
  p1063 69660665330499 70368744177664 3405780739
  907097092915200000000 p16760 p14074 p16761

noncomputable def p16765 :=
@p16764 p14077 d202
  (@p16654 69660665330499 70368744177664 3571219944177664
    p4996 69660665330499 70368744177664 3405780739
    907097092915200000000
    (p16656 (p16665 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p16766 :=
@p16762 p14077 p16736 p982
  204511804200745665989217 p16737 p16540 p16541
  p16542 p16543 (p16765 (Eq.refl true))
  (@p16416 false p16736 p982
    204511804200745665989217 p16737
    (BSN.correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (p16417 (Eq.refl true) (Eq.refl true)
        (p16194 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16740 (Eq.refl true)))

noncomputable def p16767 :=
p16506
  (p16507
    (@Enclosure.Real.IsNear.neg p16422 false 62161169265797 8796093022208
      3299 17592186044416 (p16535 (Eq.refl true))))
  (p16545
    (@p16554 p16538 p16539 p16754
      (p16759 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p16766 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16768 :=
@p16488 p16480
  (@p16500 false p16484 p16485 p16486
    p16487
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1))
      (p16417 (Eq.refl true) (Eq.refl true)
        (p16194 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p16767 (Eq.refl true)))

noncomputable def p16769 :=
@p16478 p16479 p16480 1349833049 17179869184
  1 17179869184 p16409 p4771 p16410
  p16411
  (@p16482 p4973 p16479 p16480
    (BSN.correctionLinear_mk
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p16191
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p16481 false p16477 p4973
      p16479 p16480
      (p16768 d203 (Eq.refl true))))

noncomputable def p16770 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p16191) false
  1349833049 17179869184 1 17179869184 1349833049
  17179869184

noncomputable def p16771 :=
@Enclosure.Real.IsNear.inv_image p16191 218655118533 17179869184 41
  17179869184 674916524 674916525 8589934592
  (p16404 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p16772 :=
p16476
  (p16769
    (@p16770 1 17179869184
      (p16771 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p16773 :=
@p16389 p16186
  (@p16391 17179869184
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p16407 (Eq.refl true))
  (p16772 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p16774 :=
@p16193 p16183 p16185 p16186
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    12
    (p16194 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))
  (p16384 p16773 (Eq.refl true) (Eq.refl true))

theorem d226 : p16184 p16185 p16186 :=
@p16187 p16183 p16185 p16186
  (@Eq.refl.{1} Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
        true 5)))
  p16774

noncomputable def p16775 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  false 5954672689 549755813888

noncomputable def p16776 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.sqrt p15599)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p16777 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p16776))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16776
          p16776)
        p16776)))

noncomputable def p16778 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  p16777 false 5954672689

noncomputable def p16779 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
    true 5)
  101656100 100000
  (Enclosure.sfrac_ofScientific_eq 101656100 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p16780 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p16776))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16776
          p16776)
        p16776)))

noncomputable def p16781 :=
@p16780 744334075 68719476736 25 68719476736 89
  549755813888 1 549755813888 409201991322230063104 5954672689
  549755813888

noncomputable def p16782 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv.{0} Real Real.instInv p16776) 25 4 0 1
  29773363 17179869184

noncomputable def p16783 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p16776) false 29773363
  17179869184 1 17179869184 29773363 17179869184

noncomputable def p16784 :=
nat_lit 170306676951040148704221491

noncomputable def p16785 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p15599)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p16786 :=
@p16785 61271462477 17179869184 7 17179869184
  2779543201126783 17179869184000 1016561 17179869184000
  p16784 295147905179352825856000 16348596316417001

noncomputable def p16787 :=
@p16786 59029581035870565171200
  (p15801
    (p15810 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p15805 (p15807 (Eq.refl true))) (Eq.refl true)

noncomputable def p16788 :=
@Enclosure.Real.IsNear.inv_image p16776 p16784 295147905179352825856000
  16348596316417001 59029581035870565171200 14886681 14886682
  8589934592 p16787 (Eq.refl true) (Eq.refl true)

noncomputable def p16789 :=
@p16781 201 549755813888
  (@p16782 1 17179869184 744334075 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p16783 1 17179869184
      (p16788 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p16790 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16776
        p16776)
      p16776))
  1

noncomputable def p16791 :=
@p16790 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p16792 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16776
        p16776)
      p16776))
  false

noncomputable def p16793 :=
nat_lit 4939636886382051484532342421868805718609251880732934247072196235813554820073771

noncomputable def p16794 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16776
      p16776)
    p16776)
  p16793 p5990

noncomputable def p16795 :=
nat_lit 1422541926535033694644114772547470030935625030387378822116711048127633

noncomputable def p16796 :=
nat_lit 5142201741628768881734278695491720328071049580104937072964403200000000

noncomputable def p16797 :=
nat_lit 29004364214105949841200703047295558546769244386263081

noncomputable def p16798 :=
nat_lit 5568550224262373291724194338325425053106987

noncomputable def p16799 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16776
    p16776)
  p16776 p16797 p5994 p16798

noncomputable def p16800 :=
@Enclosure.Real.IsNear.mulLit_ff p16776 p16776 p16784
  295147905179352825856000 16348596316417001 59029581035870565171200
  p16784 295147905179352825856000 16348596316417001
  59029581035870565171200 p16797

noncomputable def p16801 :=
@p16799 p8228 p16784 295147905179352825856000
  16348596316417001 59029581035870565171200 p16793 p5990
  p16795 p16796
  (@p16800 p5994 p16798 p8228
    p16787 p16787 (Eq.refl true))
  p16787

noncomputable def p16802 :=
@p16794 p16795 p16796 44 45
  8589934592 (p16801 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p16803 :=
p16791 (Enclosure.Real.IsNear.const false 1 32)
  (@p16792 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p16802 (Eq.refl true))
    (Eq.refl true))

theorem d227 : p16775 201 549755813888 :=
@p16778 549755813888 201 549755813888
  (p16779 (Eq.refl true))
  (p16789 (p16803 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16804 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  false 5945663889 549755813888

noncomputable def p16805 :=
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.sqrt p16191)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p16806 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p16805))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16805
          p16805)
        p16805)))

noncomputable def p16807 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  p16806 false 5945663889

noncomputable def p16808 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
    true 5)
  101779300 100000
  (Enclosure.sfrac_ofScientific_eq 101779300 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p16809 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv.{0} Real Real.instInv p16805))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv.{0} Real Real.instInv
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16805
          p16805)
        p16805)))

noncomputable def p16810 :=
@p16809 743207975 68719476736 25 68719476736 89
  549755813888 1 549755813888 408582911300210786304 5945663889
  549755813888

noncomputable def p16811 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv.{0} Real Real.instInv p16805) 25 4 0 1
  29728319 17179869184

noncomputable def p16812 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv.{0} Real Real.instInv p16805) false 29728319
  17179869184 1 17179869184 29728319 17179869184

noncomputable def p16813 :=
nat_lit 34112943115003739947088597

noncomputable def p16814 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p16191)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 2
        (@instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
      Real.pi))

noncomputable def p16815 :=
@p16814 61290018215 17179869184 7 17179869184
  2782911810805679 17179869184000 1017793 17179869184000
  p16813 59029581035870565171200 81860934191863799

noncomputable def p16816 :=
@p16815 295147905179352825856000
  (p16396
    (p16405 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p16400 (p16402 (Eq.refl true))) (Eq.refl true)

noncomputable def p16817 :=
@Enclosure.Real.IsNear.inv_image p16805 p16813 59029581035870565171200
  81860934191863799 295147905179352825856000 14864159 14864160
  8589934592 p16816 (Eq.refl true) (Eq.refl true)

noncomputable def p16818 :=
@p16810 201 549755813888
  (@p16811 1 17179869184 743207975 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p16812 1 17179869184
      (p16817 (Eq.refl true) (Eq.refl true)
        (Eq.refl true) (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p16819 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16805
        p16805)
      p16805))
  1

noncomputable def p16820 :=
@p16819 32 0 1 89 17179869184 1
  17179869184 89 549755813888 1 549755813888

noncomputable def p16821 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv.{0} Real Real.instInv
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16805
        p16805)
      p16805))
  false

noncomputable def p16822 :=
nat_lit 39696989290569101670554043661540069074958548526869623897217011304298777752173

noncomputable def p16823 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16805
      p16805)
    p16805)
  p16822 p10404

noncomputable def p16824 :=
nat_lit 7144574022537413730406646795601385586736897694810145019911215725076679

noncomputable def p16825 :=
nat_lit 1163692887967481064429572852639523535505176567428409

noncomputable def p16826 :=
nat_lit 27925173920982356813537601376929001466712431

noncomputable def p16827 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) p16805
    p16805)
  p16805 p16825 p10408 p16826

noncomputable def p16828 :=
@Enclosure.Real.IsNear.mulLit_ff p16805 p16805 p16813
  59029581035870565171200 81860934191863799 295147905179352825856000
  p16813 59029581035870565171200 81860934191863799
  295147905179352825856000 p16825

noncomputable def p16829 :=
@p16827 p5994 p16813 59029581035870565171200
  81860934191863799 295147905179352825856000 p16822 p10404
  p16824 p5990
  (@p16828 p10408 p16826 p5994
    p16816 p16816 (Eq.refl true))
  p16816

noncomputable def p16830 :=
@p16823 p16824 p5990 44 45
  8589934592 (p16829 (Eq.refl true)) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p16831 :=
p16820 (Enclosure.Real.IsNear.const false 1 32)
  (@p16821 89 17179869184 1 17179869184 89
    17179869184 1 17179869184 (p16830 (Eq.refl true))
    (Eq.refl true))

theorem d228 : p16804 201 549755813888 :=
@p16807 549755813888 201 549755813888
  (p16808 (Eq.refl true))
  (p16818 (p16831 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p16832 :=
@LE.le.{0} Real Real.instLE
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d43))

noncomputable def p16833 :=
@OfNat.ofNat.{0} Real 1016561
  (@instOfNatAtLeastTwo.{0} Real 1016561
    (@AddMonoidWithOne.toNatCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real
            (@DivisionSemiring.toSemiring.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 1016559))

noncomputable def p16834 :=
@LE.le.{0} Real Real.instLE
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16835 :=
@congrArg.{1, 1} Real Prop (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d43))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16836 :=
p16835
  (@LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p16837 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 1016561 1000
  (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d43)) p16833
  p6033
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 101656100
    5 1016561 1000
    (p260
      (p261 p4
        (@p262 1016561 1000
          (p266 (@Eq.refl.{1} Nat (Nat.mul 101656100 1))
            (@Eq.refl.{1} Nat 100000))))))
  (@Eq.refl.{1} Real p16833)

noncomputable def p16838 :=
@congrArg.{1, 1} Real Prop
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16839 :=
@p16838
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16840 :=
p16839
  (@LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p16841 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq.{0} Real
  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) 1016561 1000
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16842 :=
@Mathlib.Meta.NormNum.isNNRat_mul.{0} Real
  (@DivisionSemiring.toSemiring.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring))))
  p16833
  (@Inv.inv.{0} Real
    (@InvOneClass.toInv.{0} Real
      (@DivInvOneMonoid.toInvOneClass.{0} Real
        (@DivisionMonoid.toDivInvOneMonoid.{0} Real
          (@GroupWithZero.toDivisionMonoid.{0} Real
            (@DivisionSemiring.toGroupWithZero.{0} Real
              (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
    p6033)

noncomputable def p16843 :=
@p16842 1016561 1 1016561 1 1000 1000
  1
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat.{0} Real
    (@DivisionSemiring.toSemiring.{0} Real
      (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))
    p16833 1016561
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p16833 1016561
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 1016561
          (@instOfNatAtLeastTwo.{0} Real 1016561
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 1016559))))))

noncomputable def p16844 :=
@p16841 p16833 p6033
  (@Mathlib.Meta.NormNum.isNNRat_div.{0} Real
    (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)) p16833
    p6033 1016561 1000
    (p16843 p6044 (@Eq.refl.{1} Nat (Nat.mul 1016561 1))
      (@Eq.refl.{1} Nat 1000)))
  (@Eq.refl.{1} Real p16833)

noncomputable def p16845 :=
@le_of_not_gt.{0} Real Real.linearOrder
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16846 :=
@LT.lt.{0} Real
  (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real (@LinearOrder.toPartialOrder.{0} Real Real.linearOrder)))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16847 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@OfNat.ofNat.{0} Real 915761
    (@instOfNatAtLeastTwo.{0} Real 915761
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 915759
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 915759 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p16848 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real
        (@DivisionSemiring.toSemiring.{0} Real
          (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  p16833

noncomputable def p16849 :=
@HSub.hSub.{0, 0, 0} Real Real Real
  (@instHSub.{0} Real
    (@SubNegMonoid.toSub.{0} Real
      (@AddGroup.toSubNegMonoid.{0} Real
        (@AddGroupWithOne.toAddGroup.{0} Real
          (@Ring.toAddGroupWithOne.{0} Real
            (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField)))))))
  p16848
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3705 (p6050 Real.pi))

noncomputable def p16850 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real
  (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
  (p16847
    (@Neg.neg.{0} Real
      (@NegZeroClass.toNeg.{0} Real
        (@SubNegZeroMonoid.toNegZeroClass.{0} Real
          (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
            (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
              (@AddCommGroup.toDivisionAddCommMonoid.{0} Real Real.instAddCommGroup)))))
      (@OfNat.ofNat.{0} Real 1
        (@One.toOfNat1.{0} Real
          (@AddMonoidWithOne.toOne.{0} Real
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
              (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))))
  p16849

noncomputable def p16851 :=
@Eq.mp.{0}
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
      p16850 (p6053 p3713))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))

noncomputable def p16852 :=
@Mathlib.Tactic.Ring.Common.add_congr.{0} Real Real.instCommSemiring p16850
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      100800)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6055
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p6053 p3713)

noncomputable def p16853 :=
@p16852
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6057
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))

noncomputable def p16854 :=
@Mathlib.Tactic.Ring.Common.add_congr.{0} Real Real.instCommSemiring
  (p16847
    (@Neg.neg.{0} Real
      (@NegZeroClass.toNeg.{0} Real
        (@SubNegZeroMonoid.toNegZeroClass.{0} Real
          (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
            (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
              (@AddCommGroup.toDivisionAddCommMonoid.{0} Real Real.instAddCommGroup)))))
      (@OfNat.ofNat.{0} Real 1
        (@One.toOfNat1.{0} Real
          (@AddMonoidWithOne.toOne.{0} Real
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
              (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 915761))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p16855 :=
@p16854 p16849
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6055
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
      100800)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6055
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p16856 :=
@Mathlib.Tactic.Ring.Common.mul_congr.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 915761
    (@instOfNatAtLeastTwo.{0} Real 915761
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 915759
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 915759 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p16857 :=
@p16856
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      915761)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Neg.neg.{0} Real
    (@NegZeroClass.toNeg.{0} Real
      (@SubNegZeroMonoid.toNegZeroClass.{0} Real
        (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
          (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
            (@AddCommGroup.toDivisionAddCommMonoid.{0} Real Real.instAddCommGroup)))))
    (@OfNat.ofNat.{0} Real 1
      (@One.toOfNat1.{0} Real
        (@AddMonoidWithOne.toOne.{0} Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
            (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))))

noncomputable def p16858 :=
@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 915761
    (@instOfNatAtLeastTwo.{0} Real 915761
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 915759
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 915759 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p16859 :=
@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
  (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
  (@OfNat.ofNat.{0} Real 915761
    (@instOfNatAtLeastTwo.{0} Real 915761
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) 915759
          (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 915759 (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))

noncomputable def p16860 :=
@p16857
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 1))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 915761))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p16858 915761
    (@p16859 915761
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 915761
          (@instOfNatAtLeastTwo.{0} Real 915761
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 915759))))))

noncomputable def p16861 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    915761)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 1))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 915761))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p16862 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    915761)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 915761))

noncomputable def p16863 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      915761)
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 1)))
  (Int.negOfNat 915761)

noncomputable def p16864 :=
@Mathlib.Meta.NormNum.isInt_mul.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@Ring.toSemiring.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    915761)
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 1))

noncomputable def p16865 :=
@p16864 (Int.ofNat 915761) (Int.negOfNat 1) (Int.negOfNat 915761)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real
            (@Ring.toSemiring.{0} Real
              (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))))))))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      915761)
    915761
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      915761))

noncomputable def p16866 :=
@p16862
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 915761))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p16863 (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (p16865
      (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
        (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 1))
      (@Eq.refl.{1} Int (Int.negOfNat 915761))))
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      915761))

noncomputable def p16867 :=
@p16861
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 915761))
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (p16866
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
          (Int.negOfNat 915761))
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p16868 :=
p16867
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
        (Int.negOfNat 1))
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
        (Int.negOfNat 915761))
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p16869 :=
p16855
  (p16860
    (p3726 p3727
      (p3728
        (@Mathlib.Meta.NormNum.IsInt.to_raw_eq.{0} Real p3729 (Int.negOfNat 1)
          (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
          (p3733 (@Eq.refl.{1} Int (Int.negOfNat 1))))
        (@Mathlib.Tactic.Ring.Common.neg_zero.{0} Real Real.commRing)))
    p16868)

noncomputable def p16870 :=
@Mathlib.Tactic.Ring.Common.sub_congr.{0} Real Real.commRing p16848
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3705 (p6050 Real.pi))

noncomputable def p16871 :=
@p3744 p16833
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p16872 :=
p16871
  (p3746
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@Mathlib.Tactic.Ring.cast_pos.{0} Real Real.instCommSemiring p16833 1016561
    (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
      p16833 1016561
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 1016561
          (@instOfNatAtLeastTwo.{0} Real 1016561
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 1016559))))))

noncomputable def p16873 :=
@Mathlib.Tactic.Ring.Common.add_mul.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p16874 :=
@Mathlib.Tactic.Ring.Common.mul_add.{0} Real Real.instCommSemiring
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1016561)
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1016561)

noncomputable def p16875 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1)
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561))
  1016561

noncomputable def p16876 :=
@Mathlib.Meta.NormNum.isNat_mul.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1016561)
  1 1016561

noncomputable def p16877 :=
@p16876 1016561
  (@Eq.refl.{1} (Real → Real → Real)
    (@HMul.hMul.{0, 0, 0} Real Real Real
      (@instHMul.{0} Real
        (@Distrib.toMul.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1)
  (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1016561)
  (@Eq.refl.{1} Nat 1016561)

noncomputable def p16878 :=
@p16874
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@p16875
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p16877)

noncomputable def p16879 :=
p16878
  (@Mathlib.Tactic.Ring.Common.mul_zero.{0} Real Real.instCommSemiring
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        1016561)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p16880 :=
@p16873
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  p16879

noncomputable def p16881 :=
p16880
  (@Mathlib.Tactic.Ring.Common.zero_mul.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        1016561)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p16882 :=
p16881
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero.{0} Real Real.instCommSemiring
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      (@Nat.rawCast.{0} Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
          (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
            (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        1016561)
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))

noncomputable def p16883 :=
@p16870
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6055
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  (p16872 p16882)

noncomputable def p16884 :=
@Mathlib.Tactic.Ring.Common.sub_pf.{0} Real Real.commRing
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6057
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p16885 :=
@p16884
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6055
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      p6055
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))
  p6121

noncomputable def p16886 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt.{0} Real Real.instCommSemiring
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6055
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6055
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1016561)

noncomputable def p16887 :=
p16885
  (p16886
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p6055
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p16888 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap.{0} Real Real.instCommSemiring
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 915761))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1016561)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6055
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Nat.rawCast.{0} Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
      (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))
    100800)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    p6055
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))

noncomputable def p16889 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq.{0} Real
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 915761))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561))
  100800
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)))

noncomputable def p16890 :=
@Mathlib.Meta.NormNum.isInt_add.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (Int.negOfNat 915761))
  (@Nat.rawCast.{0} Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
      (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
        (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    1016561)
  (Int.negOfNat 915761) (Int.ofNat 1016561)

noncomputable def p16891 :=
@p16890 (Int.ofNat 100800)
  (@Eq.refl.{1} (Real → Real → Real)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real
      (@instHAdd.{0} Real
        (@Distrib.toAdd.{0} Real
          (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing)) (Int.negOfNat 915761))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt.{0} Real
    (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561)
    1016561
    (@Mathlib.Meta.NormNum.IsNat.of_raw.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561))

noncomputable def p16892 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat.{0} Real
  (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real
      (@Distrib.toAdd.{0} Real
        (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
    (@Int.rawCast.{0} Real (@inferInstance.{1} (Ring.{0} Real) (@CommRing.toRing.{0} Real Real.commRing))
      (Int.negOfNat 915761))
    (@Nat.rawCast.{0} Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
        (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
          (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
      1016561))
  100800 (p16891 (@Eq.refl.{1} Int (Int.ofNat 100800)))

noncomputable def p16893 :=
p16869
  (p16883
    (p6091 (p6097 p6106) p6115)
    p16887)
  (p16888 (p16889 p16892)
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
      (@HAdd.hAdd.{0, 0, 0} Real Real Real
        (@instHAdd.{0} Real
          (@Distrib.toAdd.{0} Real
            (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
        p6055
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))))))

noncomputable def p16894 :=
@Mathlib.Tactic.Ring.of_eq.{1} Real
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
    p16850 (p6053 p3713))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 0
    (@Zero.toOfNat0.{0} Real
      (@MulZeroClass.toZero.{0} Real
        (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
  (p16853 p16893
    (p6136
      (p3840 (p3842 p3852) p3860)
      p6154)
    (@p6155
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real
          (@MulZeroClass.toZero.{0} Real
            (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))
      p6158
      (p6163
        (@Mathlib.Tactic.Ring.Common.add_pf_zero_add.{0} Real Real.instCommSemiring
          (@OfNat.ofNat.{0} Real 0
            (@Zero.toOfNat0.{0} Real
              (@MulZeroClass.toZero.{0} Real
                (@instMulZeroClassOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))))))))

noncomputable def p16895 :=
@congrArg.{1, 1} Real Prop
  (@HAdd.hAdd.{0, 0, 0} Real Real Real
    (@instHAdd.{0} Real (@AddSemigroup.toAdd.{0} Real (@AddMonoid.toAddSemigroup.{0} Real Real.instAddMonoid)))
    p16850 (p6053 p3713))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (fun (_a : Real) =>
    @LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder)) _a
      (@OfNat.ofNat.{0} Real 0
        (@Zero.toOfNat0.{0} Real (@MulZeroClass.toZero.{0} Real (@instMulZeroClassOfSemiring.{0} Real Real.semiring)))))
  (p16894
    (@Mathlib.Tactic.Ring.cast_zero.{0} Real Real.instCommSemiring
      (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
      (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
        (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
        (@Nat.cast_zero.{0} Real
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))))

noncomputable def p16896 :=
@HAdd.hAdd.{0, 0, 0} Real Real Real
  (@instHAdd.{0} Real (@Distrib.toAdd.{0} Real (@instDistribOfSemiring.{0} Real Real.semiring)))
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
    (@OfNat.ofNat.{0} Real 915761
      (@instOfNatAtLeastTwo.{0} Real 915761 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 915760 (instOfNatNat 915760))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 915759 (instOfNatNat 915759))))))
    (@Neg.neg.{0} Real
      (@NegZeroClass.toNeg.{0} Real
        (@SubNegZeroMonoid.toNegZeroClass.{0} Real
          (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
            (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
              (@AddCommGroup.toDivisionAddCommMonoid.{0} Real Real.instAddCommGroup)))))
      (@OfNat.ofNat.{0} Real 1
        (@One.toOfNat1.{0} Real
          (@AddMonoidWithOne.toOne.{0} Real
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
              (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))))
  p16849

noncomputable def p16897 :=
@Mathlib.Tactic.Linarith.add_neg.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
    (@OfNat.ofNat.{0} Real 915761
      (@instOfNatAtLeastTwo.{0} Real 915761 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 915760 (instOfNatNat 915760))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 915759 (instOfNatNat 915759))))))
    (@Neg.neg.{0} Real
      (@NegZeroClass.toNeg.{0} Real
        (@SubNegZeroMonoid.toNegZeroClass.{0} Real
          (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
            (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
              (@AddCommGroup.toDivisionAddCommMonoid.{0} Real Real.instAddCommGroup)))))
      (@OfNat.ofNat.{0} Real 1
        (@One.toOfNat1.{0} Real
          (@AddMonoidWithOne.toOne.{0} Real
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
              (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
                (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))))
  p16849

noncomputable def p16898 :=
@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (@Neg.neg.{0} Real
    (@NegZeroClass.toNeg.{0} Real
      (@SubNegZeroMonoid.toNegZeroClass.{0} Real
        (@SubtractionMonoid.toSubNegZeroMonoid.{0} Real
          (@SubtractionCommMonoid.toSubtractionMonoid.{0} Real
            (@AddCommGroup.toDivisionAddCommMonoid.{0} Real Real.instAddCommGroup)))))
    (@OfNat.ofNat.{0} Real 1
      (@One.toOfNat1.{0} Real
        (@AddMonoidWithOne.toOne.{0} Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
            (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))))
  (@OfNat.ofNat.{0} Real 915761
    (@instOfNatAtLeastTwo.{0} Real 915761 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 915760 (instOfNatNat 915760))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 915759 (instOfNatNat 915759))))))
  (@neg_neg_of_pos.{0} Real Real.instAddCommGroup Real.partialOrder Real.instIsOrderedAddMonoid
    (@OfNat.ofNat.{0} Real 1
      (@One.toOfNat1.{0} Real
        (@AddMonoidWithOne.toOne.{0} Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real
            (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Real
              (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))))))
    (@Mathlib.Tactic.Linarith.zero_lt_one.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing))

noncomputable def p16899 :=
@Mathlib.Meta.NormNum.isNat_lt_true.{0} Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero.{0} Real (@Ring.toSemiring.{0} Real Real.instRing) Real.partialOrder
    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing))
  (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
  (@OfNat.ofNat.{0} Real 915761
    (@instOfNatAtLeastTwo.{0} Real 915761 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 915760 (instOfNatNat 915760))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 915759 (instOfNatNat 915759))))))
  0 915761
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero)) 0
    (@Nat.cast_zero.{0} Real
      (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))

noncomputable def p16900 :=
p16899
  (@Mathlib.Meta.NormNum.isNat_ofNat.{0} Real
    (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))
    (@OfNat.ofNat.{0} Real 915761
      (@instOfNatAtLeastTwo.{0} Real 915761 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 915760 (instOfNatNat 915760))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 915759 (instOfNatNat 915759))))))
    915761
    (@Eq.refl.{1} Real
      (@OfNat.ofNat.{0} Real 915761
        (@instOfNatAtLeastTwo.{0} Real 915761
          (@AddMonoidWithOne.toNatCast.{0} Real
            (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
          (Mathlib.Meta.NormNum.instAtLeastTwo 915759)))))

noncomputable def p16901 :=
@HSub.hSub.{0, 0, 0} Real Real Real
  (@instHSub.{0} Real
    (@SubNegMonoid.toSub.{0} Real
      (@AddGroup.toSubNegMonoid.{0} Real
        (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16902 :=
p6171
  (p16901
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p16903 :=
@Mathlib.Tactic.CancelDenoms.derive_trans.{0} Real Real.instMul
  (p16901
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p16904 :=
@p16903
  (p16901
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p16905 :=
@p16904
  (@OfNat.ofNat.{0} Real 1000
    (@instOfNatAtLeastTwo.{0} Real 1000
      (@AddMonoidWithOne.toNatCast.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p16906 :=
@congrArg.{1, 1} Real (Real → Real)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16907 :=
@p16906
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16908 :=
@congrFun'.{1, 1} Real Real p16901 p16901
  (p16907
    (@HSub.hSub.{0, 0, 0} Real Real Real
      (@instHSub.{0} Real
        (@SubNegMonoid.toSub.{0} Real
          (@AddGroup.toSubNegMonoid.{0} Real
            (@AddGroupWithOne.toAddGroup.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing))))))
    (p16844 (@Eq.refl.{1} Real p6033)))
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)

noncomputable def p16909 :=
@p6180
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16910 :=
@p16909
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real 32
      (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
    Real.pi)
  p16848

noncomputable def p16911 :=
@p16910
  (@HMul.hMul.{0, 0, 0} Real Real Real
    (@instHMul.{0} Real
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p3705 (p6050 Real.pi))

noncomputable def p16912 :=
@HMul.hMul.{0, 0, 0} Real Real Real
  (@instHMul.{0} Real
    (@inferInstance.{1} (Mul.{0} Real)
      (@Distrib.toMul.{0} Real
        (@instDistribOfSemiring.{0} Real
          (@DivisionSemiring.toSemiring.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField)))))))
  (@OfNat.ofNat.{0} Real 1
    (@One.toOfNat1.{0} Real
      (@AddMonoidWithOne.toOne.{0} Real
        (@inferInstance.{1} (AddMonoidWithOne.{0} Real)
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Real
            (@Ring.toAddGroupWithOne.{0} Real
              (@DivisionRing.toRing.{0} Real (@Field.toDivisionRing.{0} Real Real.instField))))))))
  p16833

noncomputable def p16913 :=
@p6185 p16833 p6033 p16848
  (@rfl.{1} Real p16912)
  (p6188 p6197
    (p3747
      (@Nat.cast_one.{0} Real
        (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))))
  (@p6199 1000 p6201
    (@p6095 1000
      (@Eq.refl.{1} Real
        (@OfNat.ofNat.{0} Real 1000
          (@instOfNatAtLeastTwo.{0} Real 1000
            (@AddMonoidWithOne.toNatCast.{0} Real
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Real (@Ring.toAddGroupWithOne.{0} Real Real.instRing)))
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p16914 :=
@Eq.mp.{0}
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    p16902
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder))
    p16849
    (@OfNat.ofNat.{0} Real 0
      (@Zero.toOfNat0.{0} Real
        (@MulZeroClass.toZero.{0} Real
          (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
  (@congrArg.{1, 1} Real Prop p16902 p16849
    (fun (_a : Real) =>
      @LT.lt.{0} Real (@Preorder.toLT.{0} Real (@PartialOrder.toPreorder.{0} Real Real.partialOrder)) _a
        (@OfNat.ofNat.{0} Real 0
          (@Zero.toOfNat0.{0} Real
            (@MulZeroClass.toZero.{0} Real
              (@instMulZeroClassOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
    (@p16905 p16849 p16908
      (p16911 p16913 p6207)))

noncomputable def p16915 :=
@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (p16901
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real 32
        (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
      Real.pi))

noncomputable def p16916 :=
@Mathlib.Tactic.Linarith.sub_neg_of_lt.{0} Real Real.instRing Real.partialOrder Real.instIsOrderedRing
  (@HDiv.hDiv.{0, 0, 0} Real Real Real
    (@instHDiv.{0} Real
      (@DivInvMonoid.toDiv.{0} Real
        (@GroupWithZero.toDivInvMonoid.{0} Real
          (@DivisionSemiring.toGroupWithZero.{0} Real
            (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
    p16833 p6033)

noncomputable def p16917 :=
fun
    (a :
      p16846
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real 32
            (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
          Real.pi)) =>
  @Mathlib.Tactic.Linarith.lt_irrefl.{0} Real Real.instPreorder
    (@OfNat.ofNat.{0} Real 0 (@Zero.toOfNat0.{0} Real Real.instZero))
    (p16851 p16895
      (@Mathlib.Tactic.Linarith.add_neg.{0} Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
        p16896
        (@HMul.hMul.{0, 0, 0} Real Real Real
          (@instHMul.{0} Real
            (@Distrib.toMul.{0} Real (@instDistribOfSemiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))
          (@OfNat.ofNat.{0} Real 1600
            (@instOfNatAtLeastTwo.{0} Real 1600 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1599 (instOfNatNat 1599))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1598 (instOfNatNat 1598))))))
          p3713)
        (p16897 (p16898 (p16900 (@Eq.refl.{1} Bool false)))
          (p16914
            (@p16915
              (@OfNat.ofNat.{0} Real 1000
                (@instOfNatAtLeastTwo.{0} Real 1000 Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 999 (instOfNatNat 999))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 998 (instOfNatNat 998))))))
              (@p16916
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real 32
                    (@instOfNatAtLeastTwo.{0} Real 32 Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 31 (instOfNatNat 31))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 30 (instOfNatNat 30))))))
                  Real.pi)
                a)
              (p6212 (@Eq.refl.{1} Bool false)))))
        (@Mathlib.Tactic.Linarith.mul_neg.{0} Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
          p3713
          (@OfNat.ofNat.{0} Real 1600
            (@instOfNatAtLeastTwo.{0} Real 1600 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat 1599 (instOfNatNat 1599))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat 1598 (instOfNatNat 1598))))))
          p3995 (p6214 (@Eq.refl.{1} Bool false)))))

noncomputable def p16918 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal d43)
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  true p15590 p15591

noncomputable def p16919 :=
@Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal d43) p15590
  p15591 p15593 p15594
  (@p16918 p15593 p15594
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
          true 5)))
    d225)

noncomputable def p16920 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal d43)
  (hardyZApproximantRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  false p16182 p16183

noncomputable def p16921 :=
@Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal d43) p16182
  p16183 p16185 p16186
  (@p16920 p16185 p16186
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
          true 5)))
    d226)

noncomputable def p16922 :=
@Zeta.Certificates.ZIntervalRS.Certificate.mk d43
  (@Eq.mpr.{0} p16832 p16834
    (@id.{0} (@Eq.{1} Prop p16832 p16834)
      (@Eq.trans.{1} Prop p16832 p16834 p16834
        (p16836 (p16837 (@Eq.refl.{1} Real p6033)))
        (p16840 (p16844 (@Eq.refl.{1} Real p6033)))))
    (p16845 p16917))
  (BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal d43)
    (Zeta.Certificates.ZIntervalRS.sndVal d43)
    (p16919 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (p16921 (Eq.refl true) (Eq.refl true)
      (Eq.refl true)))

noncomputable def p16923 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal d43)
  (hardyZErrorBoundRS (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d43)))
  true false p15590 p15591 p15593

noncomputable def p16924 :=
@p16923 p15594 5954672689 549755813888 201
  549755813888
  (@p16918 p15593 p15594
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
          true 5)))
    d225)

noncomputable def p16925 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.fst.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d43)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
      true 5))
  false 5954672689 549755813888

noncomputable def p16926 :=
p16924
  (@p16925 201 549755813888
    (@Eq.refl.{1} Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101656100
          true 5)))
    d227)

noncomputable def p16927 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal d43)
  (hardyZErrorBoundRS (@Prod.snd.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d43)))
  false false p16182 p16183 p16185

noncomputable def p16928 :=
@p16927 p16186 5945663889 549755813888 201
  549755813888
  (@p16920 p16185 p16186
    (@Eq.refl.{1} Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
          true 5)))
    d226)

noncomputable def p16929 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.snd.{0, 0} Real Real (@NonemptyInterval.toProd.{0} Real Real.instLE d43)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
      true 5))
  false 5945663889 549755813888

noncomputable def p16930 :=
p16928
  (@p16929 201 549755813888
    (@Eq.refl.{1} Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific.{0} Real (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) 101779300
          true 5)))
    d228)

theorem d229 : Zeta.Certificates.ZIntervalRS.Certificate d43 :=
p16922
  (p16926 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (p16930 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
end RHHeight1000.GramZero661

theorem solution : ∃ t ∈ Set.Ioo (1016.56100 : ℝ) (1017.79300 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  exact riemannZeta.exists_zero_of_zIntervalRS_certificate _ RHHeight1000.GramZero661.d229
