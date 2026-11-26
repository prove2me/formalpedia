-- Prove2me | solution 1 for RHHeight1000.gram_zero656_exists
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T16:54:16.022795+00:00
-- url     : https://prove2.me/submissions/182e2433-bd55-499c-b123-568fc801b8f3

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

namespace RHHeight1000.GramZero656
noncomputable abbrev c0 := (@CommSemiring.toSemiring Real Real.instCommSemiring)

noncomputable abbrev c1 := (@AddGroupWithOne.toAddMonoidWithOne Real
            (@Ring.toAddGroupWithOne Real
              (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))))

noncomputable abbrev c2 := (@NNRatCast.toOfScientific Real Real.instNNRatCast)

noncomputable abbrev c3 := (@Semifield.toDivisionSemiring Real (@Field.toSemifield Real Real.instField))

noncomputable abbrev c4 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev c5 := (@AddGroupWithOne.toAddMonoidWithOne Real (@Ring.toAddGroupWithOne Real Real.instRing))

noncomputable abbrev c6 := (@AddMonoidWithOne.toNatCast NNRat
      (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
        (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
          (@Semiring.toNonAssocSemiring NNRat
            (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))

noncomputable abbrev c7 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 2
        (@instOfNatAtLeastTwo Real 2 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1 (instOfNatNat 1))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0))))))
      Real.pi)

noncomputable abbrev c8 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
      (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))

noncomputable abbrev c9 := (@Nat.rawCast Nat
      (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
        (@NonAssocSemiring.toAddCommMonoidWithOne Nat
          (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))))
      1)

noncomputable abbrev c10 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))

noncomputable abbrev c11 := (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField)

noncomputable abbrev c12 := (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))

noncomputable abbrev c13 := (@Neg.neg Real
      (@NegZeroClass.toNeg Real
        (@SubNegZeroMonoid.toNegZeroClass Real
          (@SubtractionMonoid.toSubNegZeroMonoid Real
            (@SubtractionCommMonoid.toSubtractionMonoid Real
              (@AddCommGroup.toDivisionAddCommMonoid Real Real.instAddCommGroup)))))
      (@OfNat.ofNat Real 1
        (@One.toOfNat1 Real
          (@AddMonoidWithOne.toOne Real
            (@AddCommMonoidWithOne.toAddMonoidWithOne Real
              (@NonAssocSemiring.toAddCommMonoidWithOne Real
                (@Semiring.toNonAssocSemiring Real Real.semiring)))))))

noncomputable abbrev c14 := (@OfNat.ofNat Real 909581
    (@instOfNatAtLeastTwo Real 909581
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 909579
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 909579 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable abbrev c15 := (@OfNat.ofNat Real 1600
    (@instOfNatAtLeastTwo Real 1600
      (@AddMonoidWithOne.toNatCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 1598
          (@OfNat.ofNat Nat 1 (instOfNatNat 1)))
        (@instNeZeroNatHAdd_1 1598 (@OfNat.ofNat Nat 1 (instOfNatNat 1))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 0 (instOfNatNat 0)))))))

noncomputable abbrev c16 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi)

noncomputable abbrev c17 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@OfNat.ofNat Real 32
        (@instOfNatAtLeastTwo Real 32 Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
      Real.pi)

noncomputable abbrev c18 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@OfNat.ofNat Real 32
      (@instOfNatAtLeastTwo Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))
    Real.pi)

noncomputable abbrev c19 := (@instHMul Real (@Distrib.toMul Real (@instDistribOfSemiring Real Real.semiring)))

noncomputable abbrev c20 := (@OfNat.ofNat Real 4
          (@instOfNatAtLeastTwo Real 4 Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 3 (instOfNatNat 3))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 2 (instOfNatNat 2))))))

noncomputable abbrev c21 := (@OfNat.ofNat Real 32
    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30))))))

noncomputable abbrev c22 := (@HPow.hPow Real Nat Real
    (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
    (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)))
    12)

noncomputable abbrev c23 := (@OfNat.ofNat Real 1
      (@One.toOfNat1 Real
        (@AddMonoidWithOne.toOne Real
          (@AddCommMonoidWithOne.toAddMonoidWithOne Real
            (@NonAssocSemiring.toAddCommMonoidWithOne Real
              (@Semiring.toNonAssocSemiring Real Real.semiring))))))

noncomputable abbrev c24 := (@instHSub Real
        (@SubNegMonoid.toSub Real
          (@AddGroup.toSubNegMonoid Real
            (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))

noncomputable abbrev c25 := (@OfNat.ofNat Real 0 (@Zero.toOfNat0 Real Real.instZero))

noncomputable abbrev c26 := (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing)

noncomputable abbrev c27 := (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))

noncomputable abbrev c28 := (@InvOneClass.toInv NNRat
      (@DivInvOneMonoid.toInvOneClass NNRat
        (@DivisionMonoid.toDivInvOneMonoid NNRat
          (@GroupWithZero.toDivisionMonoid NNRat
            (@DivisionSemiring.toGroupWithZero NNRat
              (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))

noncomputable abbrev c29 := (@Preorder.toLT Real (@PartialOrder.toPreorder Real Real.partialOrder))

noncomputable abbrev c30 := (@OfNat.ofNat Real 909581
      (@instOfNatAtLeastTwo Real 909581 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 909580 (instOfNatNat 909580))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 909579 (instOfNatNat 909579))))))

noncomputable abbrev c31 := (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing)))))

noncomputable abbrev c32 := (@DivisionRing.toRing Real (@Field.toDivisionRing Real Real.instField))

noncomputable abbrev c33 := (@Nat.cast Real Real.instNatCast 4398046511104)

noncomputable abbrev c34 := (@instHSub Real
      (@SubNegMonoid.toSub Real
        (@AddGroup.toSubNegMonoid Real
          (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))

noncomputable abbrev c35 := (@Semiring.toNonAssocSemiring Nat (@CommSemiring.toSemiring Nat Nat.instCommSemiring))

noncomputable abbrev c36 := (@instHAdd Real (@AddSemigroup.toAdd Real (@AddMonoid.toAddSemigroup Real Real.instAddMonoid)))

noncomputable abbrev c37 := (@NegZeroClass.toNeg Real
      (@SubNegZeroMonoid.toNegZeroClass Real
        (@SubtractionMonoid.toSubNegZeroMonoid Real
          (@SubtractionCommMonoid.toSubtractionMonoid Real
            (@AddCommGroup.toDivisionAddCommMonoid Real Real.instAddCommGroup)))))

noncomputable abbrev c38 := (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))

noncomputable abbrev c39 := (@OfNat.ofNat Real 1600
            (@instOfNatAtLeastTwo Real 1600 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1599 (instOfNatNat 1599))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 1598 (instOfNatNat 1598))))))

noncomputable abbrev c40 := (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real (@Semiring.toNonAssocSemiring Real Real.semiring))))))

noncomputable abbrev c41 := (@OfNat.ofNat Real 909581
    (@instOfNatAtLeastTwo Real 909581 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 909580 (instOfNatNat 909580))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 909579 (instOfNatNat 909579))))))

noncomputable abbrev c42 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable abbrev c43 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable abbrev c44 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev c45 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev c46 := (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 19 (instOfNatNat 19))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 18 (instOfNatNat 18))))))

noncomputable abbrev c47 := (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)

noncomputable abbrev c48 := (@Zero.toOfNat0 Real (@MulZeroClass.toZero Real (@instMulZeroClassOfSemiring Real Real.semiring)))

noncomputable abbrev c49 := (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real (@Ring.toSemiring Real Real.instRing)))))

noncomputable abbrev c50 := (@Distrib.toMul Real (@instDistribOfSemiring Real (@Ring.toSemiring Real Real.instRing)))

noncomputable abbrev c51 := (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real (@Ring.toAddGroupWithOne Real Real.instRing)))))

noncomputable abbrev c52 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

noncomputable abbrev c53 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

noncomputable abbrev c54 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

noncomputable abbrev c55 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable abbrev c56 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable abbrev c57 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable abbrev c58 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev c59 := (@Nat.cast Real Real.instNatCast 19031814991885)

noncomputable abbrev c60 := (@Nat.cast Real Real.instNatCast 18817890855163)

noncomputable abbrev c61 := (@instHDiv Real
    (@DivInvMonoid.toDiv Real
      (@DivisionRing.toDivInvMonoid Real (@Field.toDivisionRing Real Real.instField))))

noncomputable abbrev c62 := (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 998 (instOfNatNat 998)))

noncomputable abbrev c63 := (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 30 (instOfNatNat 30)))

noncomputable abbrev c64 := (@Mathlib.Tactic.Ring.Common.neg_zero Real Real.commRing)

noncomputable def p3 :=
@Mathlib.Meta.NormNum.isNat_pow Nat Nat.instSemiring
  (@HPow.hPow Nat Nat Nat
    c27)
  (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5 10 5 100000

noncomputable def p4 :=
p3
  (@Eq.refl (Nat → Nat → Nat)
    (@HPow.hPow Nat Nat Nat
      c27))
  (@Mathlib.Meta.NormNum.isNat_ofNat Nat Nat.instAddMonoidWithOne
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 10
    (@Eq.refl Nat (@OfNat.ofNat Nat 10 (instOfNatNat 10))))
  (Mathlib.Meta.NormNum.IsNat.raw_refl 5)
  (@Mathlib.Meta.NormNum.IsNatPowT.run 10 5 100000
    (@Mathlib.Meta.NormNum.IsNatPowT.trans 10 2 100
      (@Eq Nat (Nat.pow 10 1) 10) 5 100000
      (@Mathlib.Meta.NormNum.IsNatPowT.bit0 10 1 10)
      (@Mathlib.Meta.NormNum.IsNatPowT.bit1 10 2 100)))

noncomputable def p9 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos NNRat c47
  NNRat.instCharZero
  (@Nat.cast NNRat
    c6
    100000)
  99999

noncomputable def p10 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c12
  (@Nat.cast NNRat
    c6
    100000)
  100000

noncomputable def p11 :=
p10
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          c12)))
    100000 100000 (Mathlib.Meta.NormNum.IsNat.raw_refl 100000))

noncomputable def p54 :=
@Mathlib.Meta.NormNum.isRat_le_true Real
  c32 Real.linearOrder
  Real.instIsStrictOrderedRing
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  (@OfScientific.ofScientific Real c2 101161500
    true 5)
  (Int.ofNat 1010381) (Int.ofNat 202323) 1000

noncomputable def p55 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  (NNRat.divNat 101038100
    (@HPow.hPow Nat Nat Nat
      c27
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5))
  1010381 1000

noncomputable def p56 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101038100 101038100 1010381
  (@HPow.hPow Nat Nat Nat
    c27
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5)
  100000 1000 (Mathlib.Meta.NormNum.IsNat.raw_refl 101038100)

noncomputable def p57 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat c47
  (@Nat.cast NNRat
    c6
    101038100)
  (@Nat.cast NNRat
    c6
    100000)

noncomputable def p58 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  c12
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          c12))))
  (@Nat.cast NNRat
    c6
    101038100)
  (@Inv.inv NNRat
    c28
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              c12))))
      100000))

noncomputable def p59 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c12
  (@Nat.cast NNRat
    c6
    101038100)
  101038100

noncomputable def p60 :=
p59
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          c12)))
    101038100 101038100 (Mathlib.Meta.NormNum.IsNat.raw_refl 101038100))

noncomputable def p61 :=
@p58 101038100 1 1010381 1 100000 1000
  100
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            c12)))))
  p60 (@p9 1 p11)

noncomputable def p62 :=
@p54 200
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat Real
    c32
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    1010381 1000
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
      c3 101038100
      5 1010381 1000
      (p55
        (p56 p4
          (@p57 1010381 1000
            (p61 (@Eq.refl Nat (Nat.mul 101038100 1))
              (@Eq.refl Nat 100000)))))))

noncomputable def p63 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  (NNRat.divNat 101161500
    (@HPow.hPow Nat Nat Nat
      c27
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5))
  202323 200

noncomputable def p64 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 101161500 101161500 202323
  (@HPow.hPow Nat Nat Nat
    c27
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 5)
  100000 200 (Mathlib.Meta.NormNum.IsNat.raw_refl 101161500)

noncomputable def p65 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat c47
  (@Nat.cast NNRat
    c6
    101161500)
  (@Nat.cast NNRat
    c6
    100000)

noncomputable def p66 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  c12
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          c12))))
  (@Nat.cast NNRat
    c6
    101161500)
  (@Inv.inv NNRat
    c28
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              c12))))
      100000))

noncomputable def p67 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c12
  (@Nat.cast NNRat
    c6
    101161500)
  101161500

noncomputable def p68 :=
p67
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          c12)))
    101161500 101161500 (Mathlib.Meta.NormNum.IsNat.raw_refl 101161500))

noncomputable def p69 :=
@p66 101161500 1 202323 1 100000 200
  500
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            c12)))))
  p68 (@p9 1 p11)

noncomputable def p70 :=
p62
  (@Mathlib.Meta.NormNum.IsNNRat.to_isRat Real
    c32
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    202323 200
    (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
      c3 101161500
      5 202323 200
      (p63
        (p64 p4
          (@p65 202323 200
            (p69 (@Eq.refl Nat (Nat.mul 101161500 1))
              (@Eq.refl Nat 100000)))))))

theorem d7 : @LE.le Real
  (@Preorder.toLE Real
    (@PartialOrder.toPreorder Real
      (@SemilatticeInf.toPartialOrder Real
        (@Lattice.toSemilatticeInf Real
          (@DistribLattice.toLattice Real (@instDistribLatticeOfLinearOrder Real Real.linearOrder))))))
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  (@OfScientific.ofScientific Real c2 101161500
    true 5) :=
p70 (Eq.refl true)

noncomputable def d8 :=
@NonemptyInterval.mk Real Real.instLE
  (@Prod.mk Real Real
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  d7

noncomputable def p497 :=
nat_lit 26986075409044028275299783

noncomputable def p499 :=
nat_lit 26986075409044045455168967

noncomputable def p501 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) Real.pi 2 1
  0 1 226375608064910080 72057594037927936

noncomputable def p504 :=
nat_lit 618970019642690137449562112

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
Enclosure.Real.IsNear c45
  false 759250125 1073741824 1 8589934592

noncomputable def p2077 :=
@Enclosure.Real.IsNear.recentre'
  c45 false
  12148002000 17179869184 2 17179869184

noncomputable def p2078 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) 24296003999
  17179869184 1 17179869184 6074000999 6074001001

noncomputable def p2079 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 2))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 2) (@Nat.cast Real Real.instNatCast 1)))
  false 24296003999 17179869184

noncomputable def p2080 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 2) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c45
  false 97184016000 137438953472 16 137438953472

noncomputable def p2084 :=
@Enclosure.Real.IsNear.recentre'
  c45 false
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
Enclosure.Real.IsNear c44
  false 4959401049 8589934592 1 8589934592

noncomputable def p2093 :=
@Enclosure.Real.IsNear.recentre'
  c44 false
  9918802098 17179869184 2 17179869184

noncomputable def p2094 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) 29756406295
  17179869184 1 17179869184 4959401048 4959401050

noncomputable def p2095 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 3))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 3) (@Nat.cast Real Real.instNatCast 1)))
  false 29756406295 17179869184

noncomputable def p2096 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 3) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c44
  false 79350416784 137438953472 16 137438953472

noncomputable def p2100 :=
@Enclosure.Real.IsNear.recentre'
  c44 false
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
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 1) (@Nat.cast Real Real.instNatCast 5)))
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
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 1) (@Nat.cast Real Real.instNatCast 239)))
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
Enclosure.Real.IsNear c58
  false 8589934591 17179869184 1 17179869184

noncomputable def p2159 :=
@Enclosure.Real.IsNear.recentre'
  c58 false
  8589934591 17179869184 1 17179869184

noncomputable def p2160 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) 34359738369
  17179869184 1 17179869184 4294967295 4294967296

noncomputable def p2161 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 4))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 4) (@Nat.cast Real Real.instNatCast 1)))
  false 34359738369 17179869184

noncomputable def p2162 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 4) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c58
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
Enclosure.Real.IsNear c43
  false 1920767767 4294967296 1 8589934592

noncomputable def p2183 :=
@Enclosure.Real.IsNear.recentre'
  c43 false
  7683071068 17179869184 2 17179869184

noncomputable def p2184 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 5)) 38415355339
  17179869184 1 17179869184 3841535533 3841535535

noncomputable def p2185 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 5))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 5) (@Nat.cast Real Real.instNatCast 1)))
  false 38415355339 17179869184

noncomputable def p2186 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 5) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c43
  false 61464568544 137438953472 16 137438953472

noncomputable def p2190 :=
@Enclosure.Real.IsNear.recentre'
  c43 false
  1920767767 4294967296 1 8589934592

theorem d111 : p2189 :=
@p2190 61464568544 137438953472 16 137438953472
  d110 (Eq.refl true)

noncomputable def p2191 :=
nat_lit 554522696895959841336459264

noncomputable def p2192 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c57
  false 7013652225 17179869184 1 17179869184

noncomputable def p2201 :=
@Enclosure.Real.IsNear.recentre'
  c57 false
  7013652225 17179869184 1 17179869184

noncomputable def p2202 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 6)) 42081913349
  17179869184 1 17179869184 3506826112 3506826113

noncomputable def p2203 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 6))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1)))
  false 42081913349 17179869184

noncomputable def p2204 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c57
  false 56109217800 137438953472 8 137438953472

theorem d115 : p2207 :=
@p2201 56109217800 137438953472 8 137438953472
  d114 (Eq.refl true)

noncomputable def p2208 :=
nat_lit 602230021555239699653591040

noncomputable def p2209 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c56
  false 6493380203 17179869184 1 17179869184

noncomputable def p2218 :=
@Enclosure.Real.IsNear.recentre'
  c56 false
  6493380203 17179869184 1 17179869184

noncomputable def p2219 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 7)) 45453661417
  17179869184 1 17179869184 3246690101 3246690102

noncomputable def p2220 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 7))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1)))
  false 45453661417 17179869184

noncomputable def p2221 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c56
  false 51947041624 137438953472 8 137438953472

theorem d119 : p2224 :=
@p2218 51947041624 137438953472 8 137438953472
  d118 (Eq.refl true)

noncomputable def p2225 :=
nat_lit 643555985949696828723167232

noncomputable def p2226 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c42
  false 759250125 2147483648 1 8589934592

noncomputable def p2234 :=
@Enclosure.Real.IsNear.recentre'
  c42 false
  6074001000 17179869184 2 17179869184

noncomputable def p2235 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 8)) 48592007999
  17179869184 1 17179869184 3037000499 3037000501

noncomputable def p2236 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 8))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1)))
  false 48592007999 17179869184

noncomputable def p2237 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c42
  false 48592008000 137438953472 16 137438953472

noncomputable def p2241 :=
@Enclosure.Real.IsNear.recentre'
  c42 false
  759250125 2147483648 1 8589934592

theorem d123 : p2240 :=
@p2241 48592008000 137438953472 16 137438953472
  d122 (Eq.refl true)

noncomputable def p2242 :=
nat_lit 680008069884511480266620928

noncomputable def p2243 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 9) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c55
  false 5726623061 17179869184 1 17179869184

noncomputable def p2251 :=
@Enclosure.Real.IsNear.recentre'
  c55 false
  5726623061 17179869184 1 17179869184

noncomputable def p2252 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) 51539607553
  17179869184 1 17179869184 2863311530 2863311531

noncomputable def p2253 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 9))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 9) (@Nat.cast Real Real.instNatCast 1)))
  false 51539607553 17179869184

noncomputable def p2254 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 9) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c55
  false 45812984488 137438953472 8 137438953472

theorem d127 : p2257 :=
@p2251 45812984488 137438953472 8 137438953472
  d126 (Eq.refl true)

noncomputable def p2258 :=
nat_lit 712615570104769214689574912

noncomputable def p2259 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 10) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c54
  false 5432751653 17179869184 1 17179869184

noncomputable def p2267 :=
@Enclosure.Real.IsNear.recentre'
  c54 false
  5432751653 17179869184 1 17179869184

noncomputable def p2268 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) 54327516525
  17179869184 1 17179869184 2716375826 2716375827

noncomputable def p2269 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 10))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 10) (@Nat.cast Real Real.instNatCast 1)))
  false 54327516525 17179869184

noncomputable def p2270 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 10) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c54
  false 43462013224 137438953472 8 137438953472

theorem d131 : p2273 :=
@p2267 43462013224 137438953472 8 137438953472
  d130 (Eq.refl true)

noncomputable def p2274 :=
nat_lit 742112642020618540985352192

noncomputable def p2275 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 11) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c53
  false 5179925457 17179869184 1 17179869184

noncomputable def p2283 :=
@Enclosure.Real.IsNear.recentre'
  c53 false
  5179925457 17179869184 1 17179869184

noncomputable def p2284 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) 56979180031
  17179869184 1 17179869184 2589962728 2589962729

noncomputable def p2285 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 11))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 11) (@Nat.cast Real Real.instNatCast 1)))
  false 56979180031 17179869184

noncomputable def p2286 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 11) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c53
  false 41439403656 137438953472 8 137438953472

theorem d135 : p2289 :=
@p2283 41439403656 137438953472 8 137438953472
  d134 (Eq.refl true)

noncomputable def p2290 :=
nat_lit 769041358879192117577515008

noncomputable def p2291 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 12) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c52
  false 4959401049 17179869184 1 17179869184

noncomputable def p2299 :=
@Enclosure.Real.IsNear.recentre'
  c52 false
  4959401049 17179869184 1 17179869184

noncomputable def p2300 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) 59512812589
  17179869184 1 17179869184 2479700524 2479700525

noncomputable def p2301 :=
@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 12))
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 12) (@Nat.cast Real Real.instNatCast 1)))
  false 59512812589 17179869184

noncomputable def p2302 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sqrt
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 12) (@Nat.cast Real Real.instNatCast 1)))
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
Enclosure.Real.IsNear c52
  false 39675208392 137438953472 8 137438953472

theorem d139 : p2305 :=
@p2299 39675208392 137438953472 8 137438953472
  d138 (Eq.refl true)

theorem d140 : Enclosure.Real.IsNear Real.pi false 226375608064910080 72057594037927936 1
  1000000000000000 :=
BSN.pi_near_15

noncomputable def p2306 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  false 884279719003555 140737488355328 1

theorem d141 : p2306 500000000000000 :=
@p501 1 1000000000000000 884279719003555 140737488355328
  1 500000000000000 (Enclosure.Real.IsNear.const false 2 1)
  d140 (Eq.refl true)

noncomputable def p2307 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 2734261103 17179869184

noncomputable def p2308 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 2734261103 17179869184

noncomputable def p2309 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
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

theorem d143 : Enclosure.Real.IsNear Real.pi false 226375608064910080 72057594037927936 1
  1000000000000000 :=
BSN.pi_near_15

theorem d144 : p2306 500000000000000 :=
@p501 1 1000000000000000 884279719003555 140737488355328
  1 500000000000000 (Enclosure.Real.IsNear.const false 2 1)
  d143 (Eq.refl true)

noncomputable def p2311 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 699970842191 4398046511104

noncomputable def p2312 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  false 699970842191 4398046511104

noncomputable def p2313 :=
@p2312 1 4398046511104 699970842191 4398046511104 1
  4398046511104
  (@p2309 349985421095 349985421096 2199023255552 d144
    (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))

theorem d145 : p2311 1 4398046511104 :=
p2313 (Eq.refl true)

noncomputable def p2314 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  false 884279719003555 70368744177664 1

noncomputable def p2315 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 4 1) Real.pi 4 1
  0 1 226375608064910080 72057594037927936

theorem d146 : p2314 250000000000000 :=
@p2315 1 1000000000000000 884279719003555 70368744177664
  1 250000000000000 (Enclosure.Real.IsNear.const false 4 1)
  d143 (Eq.refl true)

noncomputable def p2316 :=
nat_lit 79228162514264337593543950336

noncomputable def p2317 :=
Enclosure.Real.IsNear c16 false
  p1068 p2316 p1071

noncomputable def p2318 :=
nat_lit 4294967296000000000000000000000000000000

noncomputable def p2319 :=
@Enclosure.Real.IsNear.mulLit_ff Real.pi Real.pi 226375608064910080 72057594037927936 1
  1000000000000000 226375608064910080 72057594037927936 1
  1000000000000000 p1068

theorem d147 : p2317 p2318 :=
@p2319 p2316 p1071 p2318 d143
  d143 (Eq.refl true)

noncomputable def p2320 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    c16)
  false p1068 p1070

noncomputable def p2321 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 4 1)
  c16 4 1
  0 1

noncomputable def p2322 :=
@p2321 p1068 p2316 p1071 p2318
  p1068 p1070 p1071 p1072
  (Enclosure.Real.IsNear.const false 4 1) d147 (Eq.refl true)

theorem d148 : p2320 p1071 p1072 :=
p2322

noncomputable def p2323 :=
Enclosure.Real.IsNear
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c16 Real.pi))
  false

noncomputable def p2324 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 8 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    c16 Real.pi)
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
@Enclosure.Real.IsNear.mulLit_ff c16
  Real.pi p1068 p2316 p1071

noncomputable def p2329 :=
@p2328 p2318 226375608064910080 72057594037927936 1
  1000000000000000 p1059 p2325 p1062
  p2326 d147 d143

theorem d149 : p2323 p1059 p1061 p1062 p1063 :=
p2327 (p2329 (Eq.refl true)) (Eq.refl true)

noncomputable def p2330 :=
Enclosure.Real.IsNear
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))
  false 4641825815

noncomputable def p2331 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))
  false 4641825815

noncomputable def p2332 :=
nat_lit 2345851864323018569406307914075

noncomputable def p2333 :=
nat_lit 2475880078570760549798248448

noncomputable def p2334 :=
nat_lit 80958226227132123480605013

noncomputable def p2335 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 96 1)
    c16)
  p2332 p2333 p2334

noncomputable def p2336 :=
nat_lit 134217728000000000000000000000000000000

noncomputable def p2337 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 96 1)
  c16 96 1
  0 1

noncomputable def p2338 :=
@p2337 p1068 p2316 p1071 p2318
  p2332 p2333 p2334 p2336
  (Enclosure.Real.IsNear.const false 96 1) d147 (Eq.refl true)

noncomputable def p2339 :=
@p2335 p2336 2320912907 2320912908 2199023255552
  p2338 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

theorem d150 : p2330 4398046511104 1 4398046511104 :=
@p2331 4398046511104 1 4398046511104 4641825815
  4398046511104 1 4398046511104 p2339 (Eq.refl true)

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

noncomputable def p2486 :=
nat_lit 8563486156235759286349715816696970818296479744

noncomputable def p2487 :=
nat_lit 128452292343536389295245737250454562274447196160

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
  c22
  (Enclosure.sfrac false 1 1) false 1

noncomputable def p2602 :=
nat_lit 2417851639229258349412352

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

noncomputable def p2689 :=
nat_lit 3715469692580659200000000

noncomputable def p2694 :=
nat_lit 18889465931478580854784000000000000000

noncomputable def p2704 :=
nat_lit 633825300114114700748351602688

noncomputable def p2708 :=
nat_lit
  39269549297426202274627953190813615617062075509851135656156147621532437066659824993342760834661157342726800723004878364386749398774385139417224707831388179934939555033566573801472986402768684388462515827139319970167616786293934721803025338359040256570233635920150528000

noncomputable def p2711 :=
nat_lit
  6008241042506208948018076838194483189410497553007223755391890586094462871198953223981442407703157073437200510619746389751172658012480926330835380298202391530045751920135685791625366919623608711434764921552315955435645368302972012435862876768933159255245746295783030784000

noncomputable def p2734 :=
nat_lit 1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888

noncomputable def p2761 :=
nat_lit 29642774844752946028434172162224104410437116074403984394101141506025761187823616

noncomputable def p2767 :=
nat_lit 95780971304118053647396689196894323976171195136475136

noncomputable def p2789 :=
nat_lit 2722258935367507707706996859454145691648

noncomputable def p2791 :=
nat_lit 83076749736557242056487941267521536000000000000000

noncomputable def p2793 :=
nat_lit 19342813113834066795298816

noncomputable def p2808 :=
nat_lit
  6969884821240511674145351813401241697800028774459043405774241668529322795113273383446988958348170361452093376629235212423507246641583722901903247989318697157746583165020107437668804133344773909394042401767152418816000

noncomputable def p2811 :=
nat_lit
  397283434810709165426285053363870776774601640144165474129131775106171399321456582856478370625845710602769322467866407108139913058570272205408485135391165737991555240406146123947121835600652112835460416900727687872512000

noncomputable def p2820 :=
nat_lit 21778071482940061661655974875633165533184

noncomputable def p2834 :=
nat_lit
  409993224778853627890903047847131864576472280850531965045543627560548399712545493143940526961657080085417257448778541907265132155387277817759014587606982185749799009707065143392282596079104347611414258927479554048000

noncomputable def p2836 :=
nat_lit
  62728963391164605067308166320611175280200258970131390651968175016763905156019460451022900625133533253068840389663116911811565219774253506117129231903868274419719248485180966939019237200102965184546381615904371769344000

noncomputable def p2846 :=
nat_lit 81165673924322027110400000000000000000000000

noncomputable def p2854 :=
nat_lit 243497021772966081331200000000000000000000000

noncomputable def p2863 :=
nat_lit
  1775650789043641010508695207816569540385605730861858341110199241010197423195744501641372399941234194234170066092175719067958164164066441064014355355829104873268767904920662283604813707431425027656908800

noncomputable def p2866 :=
nat_lit
  62147777616527435367804332273579933913496200580165041938856973435356909811851057557448033997943196798195952313226150167378535745742325437240502437454018670564406876672223179926168479760099875967991808000

noncomputable def p2888 :=
nat_lit 3291009114642412084309938365114701009965471731267159726697218048

noncomputable def p2908 :=
nat_lit 121748510886483040665600000000000000000000000

noncomputable def p2961 :=
nat_lit 1045811745188289256234780144435200000000000000000000000000000000000000

noncomputable def p2972 :=
nat_lit 348603915062763085411593381478400000000000000000000000000000000000000

noncomputable def p2977 :=
nat_lit 6129982163463555433433388108601236734474956488734408704

noncomputable def p2980 :=
nat_lit 4491727243356387717716544818099340391219200000000000000000000000000000000000000000000000000000

noncomputable def p2994 :=
nat_lit
  494660802946209068121005042039294380070262698202423679828126112185794450213063734340632802122486089979195342852032278678702730068613502419935092310203786335833213544297398272

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

noncomputable def p3287 :=
nat_lit
  1204861799007386865375571354988119955406212377298305037594361533181473345049238920486731261453760892715929826931235618026503301416242045188797809999002881809915850451119505408000

noncomputable def p3290 :=
nat_lit
  184343855248130190402462417313182353177150493726640670751937314576765421792533554834469883002425416585537263520479049558055005116685032913886064929847440916917125119021284327424000

noncomputable def p3325 :=
nat_lit
  346583711765101857447301773017885462929554634421977071896309947576827663475703202879996800763017447262173901370175446478621769728

noncomputable def p3327 :=
nat_lit
  2833237679347459997001058673934944007204586613041080331816671972911019754305970825074171325544701421171402342400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p3364 :=
nat_lit
  139996442415843232805215737484762085931734324818356911811455877120000000000000000000000000000000000000000000000000000000000000

noncomputable def p3378 :=
nat_lit 509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344

noncomputable def p3390 :=
nat_lit 1496577676626844588240573268701473812127674924007424

noncomputable def p3406 :=
nat_lit 77371252455336267181195264

noncomputable def p3422 :=
nat_lit 1857734846290329600000000

noncomputable def p3426 :=
nat_lit 170141183460469231731687303715884105728

noncomputable def p3441 :=
nat_lit
  106352002277229487215352658285541407742310009375900930874240748115986981126606344351913283666201329978211874033038867377067676492944087568693592040852641253017373400345155447962475649007336027670197180202745856000

noncomputable def p3444 :=
nat_lit
  6062064129802080771275101522275860241311670534426353059831722642611257924216561628059057168973475808758076819883215440492857560097812991415534746328600551421990283819673860533861111993418153577201239271556513792000

noncomputable def p3453 :=
nat_lit 5444517870735015415413993718908291383296

noncomputable def p3467 :=
nat_lit
  6256000133954675718550156369737729867194706433876525345543573418587469478035667314818428450953019410483051413708168669239275087820240445217270120050155367824551376490891496938969155823960942804129245894279168000

noncomputable def p3469 :=
nat_lit
  957168020495065384938173924569872669680790084383108377868166733043882830139457099167219552995811969803906866297349806393609088436496788118242328367673771277156360603106399031662280841066024249031774621824712704000

noncomputable def p3486 :=
nat_lit 60874255443241520332800000000000000000000000

noncomputable def p3512 :=
nat_lit
  1015922927471052762435759396547172203252676620832305895968258592893646030241792000000000000000000000000000000000000000000000000000000

noncomputable def p3520 :=
nat_lit 8148865449233168782969921448079524907035189961220423680000000000000000000000000000000000000000000000

noncomputable def p3552 :=
nat_lit 16688876440029529667522399125666867009608069040579427696640000000000000000000000000000000

noncomputable def p3560 :=
nat_lit 7589222350374952687853874124660645525003960320000000000000000000000000000000

noncomputable def p3576 :=
nat_lit 62335237573879316820787200000000

noncomputable def p3705 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          c3))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  c21

noncomputable def p3710 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          c3))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3711 :=
@OfNat.ofNat Real 63
  (@instOfNatAtLeastTwo Real 63
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              c3)))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 61))

noncomputable def p3712 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          c3))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  p3711

noncomputable def p3713 :=
@HSub.hSub Real Real Real
  (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real
          (@Ring.toAddGroupWithOne Real
            c32)))))
  (p3710 Real.pi) p3712

noncomputable def p3726 :=
@Mathlib.Tactic.Ring.Common.neg_congr Real Real.commRing
  c40
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3727 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  c40
  1
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c23
    1
    (@Nat.cast_one Real
      c5))

noncomputable def p3728 :=
@Mathlib.Tactic.Ring.Common.neg_add Real Real.commRing
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))

noncomputable def p3729 :=
@Neg.neg Real
  (@NegZeroClass.toNeg Real
    (@SubNegZeroMonoid.toNegZeroClass Real
      (@SubtractionMonoid.toSubNegZeroMonoid Real
        (@SubtractionCommMonoid.toSubtractionMonoid Real
          (@AddCommGroup.toDivisionAddCommMonoid Real
            (@Ring.toAddCommGroup Real
              (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))))))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)

noncomputable def p3730 :=
@Mathlib.Meta.NormNum.isInt_neg Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@Neg.neg Real
    (@NegZeroClass.toNeg Real
      (@SubNegZeroMonoid.toNegZeroClass Real
        (@SubtractionMonoid.toSubNegZeroMonoid Real
          (@SubtractionCommMonoid.toSubtractionMonoid Real
            (@AddCommGroup.toDivisionAddCommMonoid Real
              (@Ring.toAddCommGroup Real
                (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))))))))

noncomputable def p3731 :=
@Eq.refl (Real → Real)
  (@Neg.neg Real
    (@NegZeroClass.toNeg Real
      (@SubNegZeroMonoid.toNegZeroClass Real
        (@SubtractionMonoid.toSubNegZeroMonoid Real
          (@SubtractionCommMonoid.toSubtractionMonoid Real
            (@AddCommGroup.toDivisionAddCommMonoid Real
              (@Ring.toAddCommGroup Real
                (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))))))))

noncomputable def p3732 :=
@p3730
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (Int.ofNat 1) (Int.negOfNat 1) p3731

noncomputable def p3733 :=
p3732
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1)
    1
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1))

noncomputable def p3744 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3746 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  1

noncomputable def p3747 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  1

noncomputable def p3762 :=
@p3744
  c21
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3763 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  c21
  32
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    (@OfNat.ofNat Real 32
      (@instOfNatAtLeastTwo Real 32 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
          c63)))
    32
    (@Eq.refl Real
      (@OfNat.ofNat Real 32
        (@instOfNatAtLeastTwo Real 32
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 30)))))

noncomputable def p3764 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3765 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)

noncomputable def p3766 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32))
  32

noncomputable def p3767 :=
@Mathlib.Meta.NormNum.isNat_mul Real c0
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)
  1 32

noncomputable def p3768 :=
@p3767 32
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)
  (@Eq.refl Nat 32)

noncomputable def p3769 :=
@p3765
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p3766
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    p3768)

noncomputable def p3770 :=
p3769
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        32)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p3771 :=
@p3764
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  p3770

noncomputable def p3772 :=
p3771
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        32)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p3773 :=
p3772
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        32)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p3777 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real c0)))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real c0))))
    Real.pi
    c9)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)

noncomputable def p3781 :=
fun (_a : Real) =>
  @Eq Real p3777
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))
      (@HPow.hPow Real Nat Real
        (@instHPow Real Nat
          (@NPow.toPow Real
            (@Monoid.toNPow Real
              (@Semiring.toMonoid Real c0))))
        Real.pi
        (@Nat.rawCast Nat
          (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
            (@NonAssocSemiring.toAddCommMonoidWithOne Nat
              c35))
          1))
      _a)

noncomputable def p3782 :=
@congrArg Real Prop
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  p3781
  (@Eq.symm Real
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1)
    (@rfl Real
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        1)))

noncomputable def p3819 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real c0)))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real c0))))
    Real.pi
    c9)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)

noncomputable def p3824 :=
@Mathlib.Tactic.Ring.Common.sub_congr Real Real.commRing (p3710 Real.pi)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  p3712
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3825 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3826 :=
@p3825
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      20)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  Real.pi

noncomputable def p3827 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3828 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3829 :=
@p3826
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3777
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p3827 20
    (@p3828 20
      (@Eq.refl Real
        (@OfNat.ofNat Real 20
          (@instOfNatAtLeastTwo Real 20
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3830 :=
p3829
  (@Mathlib.Tactic.Ring.Common.atom_pf Real Real.instCommSemiring p3777 Real.pi
    c9
    (@rfl Nat
      (@Nat.rawCast Nat
        (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
          (@NonAssocSemiring.toAddCommMonoidWithOne Nat
            c35))
        1))
    (@Eq.mpr (@Eq Real p3777 p3777)
      (@Eq Real p3777 p3777)
      (@id
        (@Eq Prop (@Eq Real p3777 p3777)
          (@Eq Real p3777 p3777))
        p3782)
      (@Eq.refl Real p3777)))

noncomputable def p3831 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3777
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3832 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  p3777
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p3819

noncomputable def p3833 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  Real.pi

noncomputable def p3834 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      20)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1))
  20

noncomputable def p3835 :=
@Mathlib.Meta.NormNum.isNat_mul Real c0
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  20 1

noncomputable def p3836 :=
@p3835 20
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Eq.refl Nat 20)

noncomputable def p3837 :=
@p3832
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p3833
    c9
    (@p3834
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      p3836))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      20))

noncomputable def p3838 :=
@p3831
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p3837
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p3819
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p3839 :=
p3838
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p3777
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p3840 :=
@p3824
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (p3830 p3839)

noncomputable def p3841 :=
@p3744 p3711
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3842 :=
p3841
  (p3746
    (p3747
      (@Nat.cast_one Real
        c5)))
  (@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring p3711 63
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p3711 63
      (@Eq.refl Real
        (@OfNat.ofNat Real 63
          (@instOfNatAtLeastTwo Real 63
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 61))))))

noncomputable def p3843 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3844 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    63)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    63)

noncomputable def p3845 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63))
  63

noncomputable def p3846 :=
@Mathlib.Meta.NormNum.isNat_mul Real c0
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    63)
  1 63

noncomputable def p3847 :=
@p3846 63
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    63)
  (@Eq.refl Nat 63)

noncomputable def p3848 :=
@p3844
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p3845
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    p3847)

noncomputable def p3849 :=
p3848
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        63)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p3850 :=
@p3843
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  p3849

noncomputable def p3851 :=
p3850
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        63)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p3852 :=
p3851
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        63)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p3853 :=
@Mathlib.Tactic.Ring.Common.sub_pf Real Real.commRing
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3854 :=
@Mathlib.Tactic.Ring.Common.neg_add Real Real.commRing
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    63)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 63))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))

noncomputable def p3855 :=
@Neg.neg Real
  (@NegZeroClass.toNeg Real
    (@SubNegZeroMonoid.toNegZeroClass Real
      (@SubtractionMonoid.toSubNegZeroMonoid Real
        (@SubtractionCommMonoid.toSubtractionMonoid Real
          (@AddCommGroup.toDivisionAddCommMonoid Real
            (@Ring.toAddCommGroup Real
              (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))))))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    63)

noncomputable def p3856 :=
@p3730
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    63)
  (Int.ofNat 63) (Int.negOfNat 63) p3731

noncomputable def p3857 :=
p3856
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63)
    63
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      63))

noncomputable def p3858 :=
@p3853
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (p3854
    (@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real p3855 (Int.negOfNat 63)
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (p3857 (@Eq.refl Int (Int.negOfNat 63))))
    c64)

noncomputable def p3859 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_gt Real Real.instCommSemiring
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p3860 :=
p3858
  (p3859
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p3819
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p3930 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3)))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  c21

noncomputable def p3938 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3939 :=
@LT.lt Real c29
  (p3938
    (@HSub.hSub Real Real Real
      c24
      Real.pi
      (@OfScientific.ofScientific Real c2 315
        true 2)))

noncomputable def p3940 :=
@congrArg Real Prop
  (p3938
    (@HSub.hSub Real Real Real
      c24
      Real.pi
      (@OfScientific.ofScientific Real c2 315
        true 2)))

noncomputable def p3941 :=
@OfNat.ofNat Real 20
  (@instOfNatAtLeastTwo Real 20
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              c3)))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 18))

noncomputable def p3942 :=
@HSub.hSub Real Real Real
  c51
  Real.pi
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p3711 p3941)

noncomputable def p3943 :=
@Mathlib.Tactic.CancelDenoms.derive_trans Real Real.instMul
  (@HSub.hSub Real Real Real
    c34
    Real.pi
    (@OfScientific.ofScientific Real c2 315 true
      2))
  p3942

noncomputable def p3944 :=
@p3943
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3945 :=
@Eq.trans Real
  (@HSub.hSub Real Real Real
    c34
    Real.pi
    (@OfScientific.ofScientific Real c2 315 true
      2))
  p3942

noncomputable def p3946 :=
@congrArg Real Real
  (@OfScientific.ofScientific Real c2 315 true
    2)
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p3711 p3941)

noncomputable def p3947 :=
@Mathlib.Meta.NormNum.isNNRat_nnratCast Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  (NNRat.divNat 315
    (@HPow.hPow Nat Nat Nat
      c27
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 2))
  63 20

noncomputable def p3948 :=
@Mathlib.Meta.NormNum.isNNRat_divNat 315 315 63
  (@HPow.hPow Nat Nat Nat
    c27
    (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 2)
  100 20 (Mathlib.Meta.NormNum.IsNat.raw_refl 315)

noncomputable def p3949 :=
@Mathlib.Meta.NormNum.isNat_pow Nat Nat.instSemiring
  (@HPow.hPow Nat Nat Nat
    c27)
  (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 2 10 2 100

noncomputable def p3950 :=
p3948
  (p3949
    (@Eq.refl (Nat → Nat → Nat)
      (@HPow.hPow Nat Nat Nat
        c27))
    (@Mathlib.Meta.NormNum.isNat_ofNat Nat Nat.instAddMonoidWithOne
      (@OfNat.ofNat Nat 10 (instOfNatNat 10)) 10
      (@Eq.refl Nat (@OfNat.ofNat Nat 10 (instOfNatNat 10))))
    (Mathlib.Meta.NormNum.IsNat.raw_refl 2)
    (@Mathlib.Meta.NormNum.IsNatPowT.run 10 2 100
      (@Mathlib.Meta.NormNum.IsNatPowT.bit0 10 1 10)))

noncomputable def p3951 :=
@Mathlib.Meta.NormNum.isNNRat_div NNRat c47
  (@Nat.cast NNRat
    c6
    315)
  (@Nat.cast NNRat
    c6
    100)

noncomputable def p3952 :=
@Mathlib.Meta.NormNum.isNNRat_mul NNRat
  c12
  (@HMul.hMul NNRat NNRat NNRat
    (@instHMul NNRat
      (@Distrib.toMul NNRat
        (@instDistribOfSemiring NNRat
          c12))))
  (@Nat.cast NNRat
    c6
    315)
  (@Inv.inv NNRat
    c28
    (@Nat.cast NNRat
      (@AddMonoidWithOne.toNatCast NNRat
        (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
          (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
            (@Semiring.toNonAssocSemiring NNRat
              c12))))
      100))

noncomputable def p3953 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c12
  (@Nat.cast NNRat
    c6
    315)
  315

noncomputable def p3954 :=
p3953
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          c12)))
    315 315 (Mathlib.Meta.NormNum.IsNat.raw_refl 315))

noncomputable def p3955 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos NNRat c47
  NNRat.instCharZero
  (@Nat.cast NNRat
    c6
    100)
  99

noncomputable def p3956 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat NNRat
  c12
  (@Nat.cast NNRat
    c6
    100)
  100

noncomputable def p3957 :=
p3956
  (@Mathlib.Meta.NormNum.isNat_natCast NNRat
    (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
      (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
        (@Semiring.toNonAssocSemiring NNRat
          c12)))
    100 100 (Mathlib.Meta.NormNum.IsNat.raw_refl 100))

noncomputable def p3958 :=
@p3952 315 1 63 1 100 20 5
  (@Eq.refl (NNRat → NNRat → NNRat)
    (@HMul.hMul NNRat NNRat NNRat
      (@instHMul NNRat
        (@Distrib.toMul NNRat
          (@instDistribOfSemiring NNRat
            c12)))))
  p3954 (@p3955 1 p3957)

noncomputable def p3959 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  c3 63 20
  (@OfScientific.ofScientific Real c2 315 true
    2)
  p3711 p3941
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
    c3 315 2
    63 20
    (p3947
      (p3950
        (@p3951 63 20
          (p3958 (@Eq.refl Nat (Nat.mul 315 1))
            (@Eq.refl Nat 100))))))
  (@Eq.refl Real p3711)

noncomputable def p3960 :=
@p3945 p3942
  (p3946
    (@HSub.hSub Real Real Real
      c24
      Real.pi)
    (p3959 (@Eq.refl Real p3941)))

noncomputable def p3961 :=
@congrArg Real Real
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p3711 p3941)

noncomputable def p3962 :=
@p3961
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p3711 p3941)

noncomputable def p3963 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  c3 63 20
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p3711 p3941)

noncomputable def p3964 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@HMul.hMul Real Real Real
    c19)
  p3711
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p3941)

noncomputable def p3965 :=
@p3964 63 1 63 1 20 20 1
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      c3)
    p3711 63
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p3711 63
      (@Eq.refl Real
        (@OfNat.ofNat Real 63
          (@instOfNatAtLeastTwo Real 63
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 61))))))

noncomputable def p3966 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  p3941 19 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      c3)
    p3941 20
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p3941 20
      (@Eq.refl Real
        (@OfNat.ofNat Real 20
          (@instOfNatAtLeastTwo Real 20
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3967 :=
@p3963 p3711 p3941
  (@Mathlib.Meta.NormNum.isNNRat_div Real
    c3 p3711
    p3941 63 20
    (p3965 p3966 (@Eq.refl Nat (Nat.mul 63 1))
      (@Eq.refl Nat 20)))
  (@Eq.refl Real p3711)

noncomputable def p3968 :=
p3960
  (p3962
    (@HSub.hSub Real Real Real
      c24
      Real.pi)
    (p3967 (@Eq.refl Real p3941)))

noncomputable def p3969 :=
@Mathlib.Tactic.CancelDenoms.sub_subst Real
  c32
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3970 :=
@p3969 Real.pi
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p3711 p3941)

noncomputable def p3971 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3)))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3972 :=
@Mathlib.Tactic.CancelDenoms.div_subst Real Real.instField
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3973 :=
@p3972
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3974 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3)))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  p3711

noncomputable def p3975 :=
@HDiv.hDiv Real Real Real
  c61
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3976 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne' Real
    (@DivisionSemiring.toSemiring Real
      c3))
  (p3975 p3941)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  1

noncomputable def p3977 :=
@Mathlib.Meta.NormNum.isNNRat_div Real
  c3
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3978 :=
p3710
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p3941)

noncomputable def p3979 :=
@HMul.hMul Real Real Real
  c19
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3980 :=
p3979
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p3941)

noncomputable def p3981 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@HMul.hMul Real Real Real
    c19)
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3982 :=
@p3981
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p3941)

noncomputable def p3983 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3984 :=
@p3982 20 1 1 1 20 1 20
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (@p3983 20
    (@p3828 20
      (@Eq.refl Real
        (@OfNat.ofNat Real 20
          (@instOfNatAtLeastTwo Real 20
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3985 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (p3975 p3941) 1
  (@p3977 p3941 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
      (@DivisionSemiring.toSemiring Real
        c3)
      p3978 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
        (@DivisionSemiring.toSemiring Real
          c3)
        p3980 1
        (p3984 p3966 (@Eq.refl Nat (Nat.mul 20 1))
          (@Eq.refl Nat 20)))))

noncomputable def p3986 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          c3))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3987 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  c5
  p3986
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3988 :=
@Mathlib.Meta.NormNum.isNat_mul Real Real.semiring
  (@HMul.hMul Real Real Real
    c19)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 20
    (@instOfNatAtLeastTwo Real 20
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 18)))

noncomputable def p3989 :=
@p3988 1 20 20
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (p3747
    (@Nat.cast_one Real
      c5))
  (@p3828 20
    (@Eq.refl Real
      (@OfNat.ofNat Real 20
        (@instOfNatAtLeastTwo Real 20
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 18)))))
  (@Eq.refl Nat 20)

noncomputable def p3990 :=
@p3973 p3711 p3941 p3712
  (@rfl Real p3974)
  (p3976 p3985
    (p3747
      (@Nat.cast_one Real
        c5)))
  (@p3987 20 p3989
    (@p3828 20
      (@Eq.refl Real
        (@OfNat.ofNat Real 20
          (@instOfNatAtLeastTwo Real 20
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 18))))))

noncomputable def p3991 :=
@Eq.mp
  (p3939
    c31)
  (@LT.lt Real c29
    p3713
    c31)
  (@p3940 p3713
    (fun (_a : Real) =>
      @LT.lt Real c29 _a
        c49)
    (@p3944 p3713 p3968
      (@p3970 (p3710 Real.pi) p3712
        (@rfl Real (p3971 Real.pi)) p3990)))

noncomputable def p3992 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (@HSub.hSub Real Real Real
    c34
    Real.pi
    (@OfScientific.ofScientific Real c2 315 true
      2))
  c46

noncomputable def p3993 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  c46
  0 20
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c25 0
    (@Nat.cast_zero Real
      c5))

noncomputable def p3994 :=
p3993
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    (@OfNat.ofNat Real 20
      (@instOfNatAtLeastTwo Real 20 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 19 (instOfNatNat 19))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 18 (instOfNatNat 18))))))
    20
    (@Eq.refl Real
      (@OfNat.ofNat Real 20
        (@instOfNatAtLeastTwo Real 20
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 18)))))

noncomputable def p3995 :=
p3991
  (p3992
    (@Mathlib.Tactic.Linarith.sub_neg_of_lt Real Real.instRing Real.partialOrder Real.instIsOrderedRing Real.pi
      (@OfScientific.ofScientific Real c2 315
        true 2)
      Real.pi_lt_d2)
    (p3994 (@Eq.refl Bool false)))

noncomputable def p4770 :=
nat_lit
  26058612959094777273138844178752166176216959742574418045655900254773901756476352499460743036689523008726224761646110373029719459051406520497668209080349829916507777840702945

noncomputable def p4771 :=
nat_lit
  61832600368276133515125630254911797508782837275302959978515764023224306276632966792579100265310761247399417856504034834837841258576687802491886538775473291979151693037174784

noncomputable def p4772 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  false p4770 p4771

noncomputable def p4773 :=
nat_lit
  5728386971943698780433774130111007596439148382838874286224429982452505640296741647155725842779531520597452779768902790084878122624968681451955446440887794225647285943244824226490704840477494181406096416755065980909230232175423

noncomputable def p4774 :=
nat_lit
  1797214195882777991957366638171982969535144607354369184355932584511081059243531505926723403315383603681729947836685262486723119490811551488516861466352025600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p4775 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  false p4770

noncomputable def p4776 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    12)

noncomputable def p4777 :=
@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    c7)

noncomputable def p4778 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  c22
  (p4777
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p4779 :=
Real.sqrt
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    c7)

noncomputable def p4780 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p4778
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p4779)))

noncomputable def p4781 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (p4776 p4780) false p4770

noncomputable def p4782 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  101038100 100000 12
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))

noncomputable def p4783 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    12)

noncomputable def p4784 :=
nat_lit
  7666195382505795970209826897934719344415002820015419254296671658123023093460104977482407545771867984296106391192634364122204766940164180495568793936916475822785658311154207

noncomputable def p4785 :=
nat_lit
  51636625648457296622572333453447212431941374405995418671658184903653380080937831107667308219895420065135966328041739530674433574987563649029137064887794225647285943244824226490704840477494181406096416755065980909230232175423

noncomputable def p4786 :=
nat_lit
  223841780876867708305070790029961063632018430189811408704648652927383951836765780365103497956882458856637315937630878355538011025361204376677277204517985511461126632710905292851773440

noncomputable def p4787 :=
@p4783 p4780 4685132051 8589934592 54265
  17179869184 p4784 p4771 p4785 p4774
  p4786 p4770

noncomputable def p4788 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    12)

noncomputable def p4789 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    12)

noncomputable def p4790 :=
p4789
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    12)

noncomputable def p4791 :=
@p4788 p4790 false 4685132051 8589934592 54265
  17179869184
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    12)

noncomputable def p4792 :=
@Enclosure.Real.IsNear.addLit_ff
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    12)

noncomputable def p4793 :=
@p4792
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    12)

noncomputable def p4794 :=
@p4793 37481056408 137438953472 217060 137438953472
  37481056408 137438953472 217060 137438953472 10302714335481038897152
  4685132051 8589934592

noncomputable def p4795 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p4796 :=
p4795 11 12 101038100 100000 286
  137438953472 68719476736 2305843009213693952 false 283246355808369
  3348

noncomputable def p4797 :=
p4796 341522969406 43 39675208392 8 false
  70963984342 203541 true 77823007141 7244019458077122842 1

noncomputable def p4798 :=
p4797 false 115988264735 true false 37481056408 217060
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 115988264735 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p4799 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  Real.sin Real.cos

noncomputable def p4800 :=
p4799 BSN.quadSignNeg BSN.quadSignNeg 9 10 11 101038100
  100000 169 230 137438953472 68719476736

noncomputable def p4801 :=
p4800 2305843009213693952 false 283246355808369 3348
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p4802 :=
p4801 8 false 110639035798 174615 true 18577668501
  true 84688387736 7244019458077122842 1 false

noncomputable def p4803 :=
p4802 18521148008 true false 112162115311 true false
  70963984342 203541 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 169 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 18521148008 137438953472)

noncomputable def p4804 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  Real.sin Real.sin

noncomputable def p4805 :=
p4804 BSN.quadSignNeg BSN.quadSignNeg 7 8 9 101038100
  100000 25 101 137438953472 68719476736

noncomputable def p4806 :=
p4805 2305843009213693952 false 283246355808369 3348
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p4807 :=
p4806 8 false 169539134356 142445 true 119549475363
  true 68040169479 7244019458077122842 1 false

noncomputable def p4808 :=
p4807 105034114572 true false 65294793671 true false
  110639035798 174615 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 25 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 105034114572 137438953472)

noncomputable def p4809 :=
p4799 BSN.quadSignPos BSN.quadSignPos 5 6 7 101038100
  100000 159 60 137438953472 68719476736

noncomputable def p4810 :=
p4809 2305843009213693952 false 283246355808369 3348
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p4811 :=
p4810 8 false 85574687117 105635 false 106121991841
  false 72850539293 7244019458077122842 1 false

noncomputable def p4812 :=
p4811 95886943675 false false 118579309967 false false
  169539134356 142445 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 159 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 95886943675 137438953472)

noncomputable def p4813 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  Real.cos Real.cos

noncomputable def p4814 :=
p4813 BSN.quadSignPos BSN.quadSignPos 3 4 5 101038100
  100000 420 276 137438953472 68719476736

noncomputable def p4815 :=
p4814 2305843009213693952 false 283246355808369 3348
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p4816 :=
p4815 16 false 2172779123 62239 false 64395527661
  false 165367334523 7244019458077122842 1 false

noncomputable def p4817 :=
p4816 122627012412 false false 49391167929 false false
  85574687117 105635 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 420 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 122627012412 137438953472)

noncomputable def p4818 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  Real.cos Real.sin

noncomputable def p4819 :=
p4818 BSN.quadSignNeg BSN.quadSignNeg 1 2 3 101038100
  100000 866 605 137438953472 68719476736

noncomputable def p4820 :=
p4819 2305843009213693952 false 283246355808369 3348
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p4821 :=
p4820 16 false 137438013472 3394 false 32451929435
  false 74178381490 7244019458077122842 1 false

noncomputable def p4822 :=
p4821 133625464138 true false 70629156497 true false
  2172779123 62239 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat2 866 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 133625464138 137438953472)

noncomputable def p4823 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    1)

noncomputable def p4824 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    1)

noncomputable def p4825 :=
@p4824
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5)))
  false 4294937921

noncomputable def p4826 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5)))
  false 17179751684

noncomputable def p4827 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 17702897238023)
    (@Nat.cast Real Real.instNatCast 8589934592))
  false 17702897238023

noncomputable def p4828 :=
nat_lit 355490591164500304105390679722318449068838718405751728698827

noncomputable def p4829 :=
nat_lit 172493851436685536716997510705954276620863352954945536000

noncomputable def p4830 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  false p4828 p4829

noncomputable def p4831 :=
nat_lit 69206016000000000000000000

noncomputable def p4832 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101038100 400000)
      (Real.log (Enclosure.sfrac false 40834800606440000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 202076200))))))

noncomputable def p4833 :=
nat_lit 505437384077389814928115575632480000000000000000

noncomputable def p4834 :=
nat_lit 3064106327540470728312227612128180649280000000000000

noncomputable def p4835 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (p4832 (Enclosure.sfrac false 101038100 200000))
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 101038100 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p4833 p4834))
  false

noncomputable def p4836 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  101038100 100000 40834800606440000 160000000000

noncomputable def p4837 :=
p4836 202076200 400000 200000 p4833
  p4834
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4838 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (p4832 (Enclosure.sfrac false 101038100 200000))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101038100 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p4833 p4834) 37125669320066391461563
  18014398509481984000

noncomputable def p4839 :=
nat_lit 113756989172640097313725017511141903702028389889840553183624640000000000000

noncomputable def p4840 :=
@p4838 1685237936112289033 p4831 p4833
  p4834 0 1 p4839 p4828
  p4829 1685237936112289033 p4831

noncomputable def p4841 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p4832 (Enclosure.sfrac false 101038100 200000))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101038100 200000) (Real.log Real.pi))
  47543516015108766027451 18014398509481984000 1273543090241
  132000000000000000000

noncomputable def p4842 :=
nat_lit 5102513138297462652036695233396736000

noncomputable def p4843 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101038100 400000)
      (Real.log (Enclosure.sfrac false 40834800606440000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 202076200))))))

noncomputable def p4844 :=
@p4843 (Enclosure.sfrac false 101038100 200000)
  56644219005313224265403 18014398509481984000 1273543090241
  132000000000000000000 101038100 200000 0

noncomputable def p4845 :=
nat_lit 9508703203021753205490200000

noncomputable def p4846 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101038100 400000)
    (Real.log (Enclosure.sfrac false 40834800606440000 160000000000)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv Real Real Real c4
          (@Nat.cast Real Real.instNatCast 100000)
          (@Nat.cast Real Real.instNatCast 202076200)))))
  56651291014401899361403

noncomputable def p4847 :=
nat_lit 127551441802510702192214414071057874944

noncomputable def p4848 :=
@p4846 18014398509481984000 1263543073741 132000000000000000000
  884001136084387 2251799813685248 20000033 264000000000000000
  p4847 56644219005313224265403 18014398509481984000 1273543090241

noncomputable def p4849 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101038100 400000)
  (Real.log (Enclosure.sfrac false 40834800606440000 160000000000)) 101038100
  400000 0 1 56069236272655463 4503599627370496

noncomputable def p4850 :=
nat_lit 30824388621152275540574470144

noncomputable def p4851 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 40834800606440000)
      (@Nat.cast Real Real.instNatCast 160000000000)))
  false p4850 p2333

noncomputable def p4852 :=
BSN.log_rat_reduce_isNear 40834800606440000 160000000000 17 81669601212880000
  41943040000000000 45792552845 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p4853 :=
nat_lit
  9097849104573093408433154872569274694571829758242443960107786229478693412662878723346481674987316500587273152000965072198500836122173354457705921259885089970414195180687611201458441451544553279401956335944903369378792344020938890007379405897289776043032537328517120000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p4854 :=
nat_lit
  334191411003239985674103445128703146675524826442560135740287112459856244555952599868765902103158984525333342964472667941519949156362520938418291628942579757377612417202521148758002111580103908753058553298067829940848010404490004679881110596714461028522748471672832000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p4855 :=
nat_lit
  59852346964615774953019290429129308872622746963810058269715965462957927774451440810745678916912175412538171044672854191620469454392006097150823659300589155661873739864385802342315748275138874865175350635300667173326475527854376125585185132361745663262720000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p4856 :=
BSN.log_dyadic_bound 19863280606440000 61806320606440000 11 10
  p4853 68719476736 26400000000 p4854 p4855
  45792552845 81669601212880000

noncomputable def p4857 :=
p4856 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p4858 :=
@BSN.binarySplit_of_base10 (BSN.artanhP 19863280606440000) (BSN.artanhQ 61806320606440000)
  0 10 p4854 p4853 p4855
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p4859 :=
p4852 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p4857 (p4858 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p4860 :=
@p4849 1250561 33000000000000000 56651291014401899361403
  18014398509481984000 1263543073741 132000000000000000000
  (Enclosure.Real.IsNear.const false 101038100 400000)
  (BSN.isNear_log_sfrac 40834800606440000 160000000000 56069236272655463
    4503599627370496 1250561 33000000000000000 false
    (@p4851 1000448800000000 p2422 56069236272655463
      4503599627370496 1250561 33000000000000000
      (p4859 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p4861 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv Real Real Real c4
        (@Nat.cast Real Real.instNatCast 100000)
        (@Nat.cast Real Real.instNatCast 202076200))))
  1 4

noncomputable def p4862 :=
@p4861 0 1 884001136084387 562949953421312 20000033
  66000000000000000 884001136084387 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p4863 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 100000) (@Nat.cast Real Real.instNatCast 202076200)))
  884279719003555 562949953421312 1

noncomputable def p4864 :=
nat_lit 7593511938218575322415104

noncomputable def p4865 :=
@p4863 2000000000000000 4250838 8589934592 1
  3300000000 p4864 884001136084387 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p4866 :=
BSN.arctan_dyadic_bound_f 100000 202076200 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p4867 :=
p4866 1 4250838 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 202076200) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 202076200) 0 0
    (Eq.refl true))

noncomputable def p4868 :=
p4862
  (p4865
    (p4867 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p4869 :=
@p4841 79481862602557179 137438953472000 1010381
  68719476736000 p4842 37125669320066391461563 18014398509481984000
  1685237936112289033 p4831
  (@p4844 1 p4845 47543516015108766027451
    18014398509481984000 1273543090241 132000000000000000000
    (@p4848 132000000000000000000 p4860 p4868
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101038100 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p4870 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101038100 200000) (Real.log Real.pi)
  101038100 200000 0 1 78665238759 68719476736

noncomputable def p4871 :=
p4869
  (@p4870 1 34359738368 79481862602557179 137438953472000
    1010381 68719476736000
    (Enclosure.Real.IsNear.const false 101038100 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p4872 :=
@p4827 8589934592 419 17179869184 false 17179751684
  17179869184 1 3300000000
  (@p4830 1685237936112289033 p4831 17702897238023
    8589934592 419 17179869184
    (@p4835 p4828 p4829 1685237936112289033
      p4831
      (p4837 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p4840 (p4871 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p4833 p4834)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p4873 :=
nat_lit 4578494865576079954804736

noncomputable def p4874 :=
BSN.cos_reduce0
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 17702897238023)
    (@Nat.cast Real Real.instNatCast 8589934592))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p4873)
    (@Nat.cast Real Real.instNatCast p2445))
  226375608064910080 72057594037927936 false

noncomputable def p4875 :=
BSN.sin_reduce_arg_pos_rat_q0 17702897238023 8589934592 226375608064910080
  72057594037927936 328 p4873 p2445
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p4876 :=
BSN.cos_dyadic_bound_f 130128650698 35184372088832 1 0 17179869184
  6606445313 0 1 1 0 1

noncomputable def p4877 :=
p4876 1 17179751684 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.cosEvenP 130128650698) (BSN.cosEvenQ 35184372088832) 0
    0 (Eq.refl true))

noncomputable def p4878 :=
p4877
  (@BSN.binarySplit_of_le (BSN.cosOddP 130128650698) (BSN.cosOddQ 35184372088832) 0
    0 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p4879 :=
@BSN.cos_arg_round false 17179751684 17179869184 p4873
  p2445 130128650698 35184372088832 6606445313 6600000000
  p4878 (Eq.refl true)

noncomputable def p4880 :=
p4874 17179751684 17179869184 328 1000000000000000
  6600000000 3300000000 p4875 BSN.pi_near_15 p4879
  (Eq.refl true) (Eq.refl true)

noncomputable def p4881 :=
@p4825 4294967296 5468280739 221459251200000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101038100
        true 5))
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  (@p4826 17179869184 1399879869184 56693568307200000000
    4294937921 4294967296 5468280739 221459251200000000
    (p4872 (Enclosure.sfrac_false_div 17702897238023 8589934592)
      (p4880 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p4882 :=
@p4823 false 4294937921 4294967296 5468280739
  221459251200000000 137438013472 137438953472 3394 137438953472
  p4881 (Eq.refl true)

noncomputable def p4883 :=
p4822 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 605 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 70629156497 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p4882
  (@p4830 1685237936112289033 p4831 283246355808369
    137438953472 3348 137438953472
    (@p4835 p4828 p4829 1685237936112289033
      p4831
      (p4837 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p4840 (p4871 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p4833 p4834)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p4884 :=
nat_lit 664831418898220911003416962123658762406491687141428041047521617158358561749963876657190625

noncomputable def p4885 :=
nat_lit 1230054017119148215907359060088108995756013265670242764328702067213339330534500390625

noncomputable def p4886 :=
nat_lit 1994491796586628494713819071652856111001483549397752782657036194070941258571230560970790625

noncomputable def p4887 :=
BSN.cos_dyadic_bound_f 32451929435 137438953472 3 2 137438953472
  68719476736 p4884 p2466 p4885 p4886
  p2469

noncomputable def p4888 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 32451929435) (BSN.cosEvenQ 137438953472) 0
  2 p4884 p2466 p4885 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4889 :=
p4887 p4885 133625464138 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4888 (Eq.refl true))

noncomputable def p4890 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 32451929435) (BSN.cosOddQ 137438953472) 0
  2 p4886 p2469 p4885 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4891 :=
nat_lit 32669519267151459382970327734497545591175808645623396377671171691713236885443466329633440000

noncomputable def p4892 :=
nat_lit 916682256725240607802563379600934630537346851089568357520584087733432363762480100000000

noncomputable def p4893 :=
nat_lit 85561542499838171803938225630593265511296724081730940735607559199297385333286796371735200000

noncomputable def p4894 :=
BSN.sin_dyadic_bound_f 74178381490 137438953472 3 2 137438953472
  68719476736 p4891 p2477 p4892 p4893
  p2480

noncomputable def p4895 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 74178381490) (BSN.sinEvenQ 137438953472) 0
  2 p4891 p2477 p4892 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4896 :=
p4894 p4892 70629156497 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4895 (Eq.refl true))

noncomputable def p4897 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 74178381490) (BSN.sinOddQ 137438953472) 0
  2 p4893 p2480 p4892 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4898 :=
p4883 d93 d95 d97 d99 d103
  (p4889 (p4890 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p4896 (p4897 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p4899 :=
p4817 BSN.abs_quadSignPos (BSN.cos_quad_nat0 276 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 49391167929 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p4898 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p4830 1685237936112289033 p4831 283246355808369
    137438953472 3348 137438953472
    (@p4835 p4828 p4829 1685237936112289033
      p4831
      (p4837 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p4840 (p4871 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p4833 p4834)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p4900 :=
nat_lit 10308225793338899020941860440040397845907439151761820329581022263749616236837713426250435361

noncomputable def p4901 :=
nat_lit 295696136036862318737824628773376539336994687223734619813132103233273647097452396514081

noncomputable def p4902 :=
nat_lit 30924085987744623338188105670863646784643643465911013519503440527042382163218945373958277921

noncomputable def p4903 :=
BSN.cos_dyadic_bound_f 64395527661 137438953472 3 2 137438953472
  68719476736 p4900 p2466 p4901 p4902
  p2469

noncomputable def p4904 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 64395527661) (BSN.cosEvenQ 137438953472) 0
  2 p4900 p2466 p4901 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4905 :=
p4903 p4901 122627012412 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4904 (Eq.refl true))

noncomputable def p4906 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 64395527661) (BSN.cosOddQ 137438953472) 0
  2 p4902 p2469 p4901 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4907 :=
nat_lit
  1902588626602201641466387186076343267947295957776598198968080153112421848874160726879466725484184423178466858567781182350342434607107084088401

noncomputable def p4908 :=
nat_lit
  418212216799886168286411483329173964107843560009296889996278132912947977153475818221990734481743404969931481935135975353298588911498321

noncomputable def p4909 :=
nat_lit
  11532781225563670875177401237047226260208311558617325152743890323125914192690299311722730343556610916765011851531985813718563842790210755851345

noncomputable def p4910 :=
BSN.cos_dyadic_bound_f 165367334523 137438953472 4 3 137438953472
  68719476736 p4907 p2457 p4908 p4909
  p2460

noncomputable def p4911 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 165367334523) (BSN.cosEvenQ 137438953472) 0
  3 p4907 p2457 p4908 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4912 :=
p4910 p4908 49391167929 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4911 (Eq.refl true))

noncomputable def p4913 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 165367334523) (BSN.cosOddQ 137438953472) 0
  3 p4909 p2460 p4908 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4914 :=
p4899 d105 d107 d109 d111 d103
  (p4905 (p4906 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p4912 (p4913 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p4915 :=
p4812 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 118579309967 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p4914 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p4830 1685237936112289033 p4831 283246355808369
    137438953472 3348 137438953472
    (@p4835 p4828 p4829 1685237936112289033
      p4831
      (p4837 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p4840 (p4871 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p4833 p4834)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p4916 :=
nat_lit
  838012322810662527632256519532961560756499172266993799825167375787934752090281238664692625336872742783603704925043973659873773920364885956481

noncomputable def p4917 :=
nat_lit
  2040162280002063437698879294637944236708817286439038361749340767545510799610941736874561476977339593001028225644946290440459037431681

noncomputable def p4918 :=
nat_lit
  4189757176896117362858462461838150851687564787324295513521639883922496243111931339597803908706961068137640492772921673298380605247092950816641

noncomputable def p4919 :=
BSN.sin_dyadic_bound_f 106121991841 137438953472 4 3 137438953472
  68719476736 p4916 p2504 p4917 p4918
  p2507

noncomputable def p4920 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 106121991841) (BSN.sinEvenQ 137438953472) 0
  3 p4916 p2504 p4917 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4921 :=
p4919 p4917 95886943675 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4920 (Eq.refl true))

noncomputable def p4922 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 106121991841) (BSN.sinOddQ 137438953472) 0
  3 p4918 p2507 p4917 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4923 :=
nat_lit 16884963659503939682513798547720905428682570064405128961958702133086305268712928739874731681

noncomputable def p4924 :=
nat_lit 793345145580968441125640683470029469083984376051557710886396076832886857195388080125601

noncomputable def p4925 :=
nat_lit 50653304288220657110659144361795776227109542224463283770454333607105250032424395443463943841

noncomputable def p4926 :=
BSN.cos_dyadic_bound_f 72850539293 137438953472 3 2 137438953472
  68719476736 p4923 p2466 p4924 p4925
  p2469

noncomputable def p4927 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 72850539293) (BSN.cosEvenQ 137438953472) 0
  2 p4923 p2466 p4924 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4928 :=
p4926 p4924 118579309967 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4927 (Eq.refl true))

noncomputable def p4929 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 72850539293) (BSN.cosOddQ 137438953472) 0
  2 p4925 p2469 p4924 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4930 :=
p4915 d113 d115 d117 d119 d103
  (p4921 (p4922 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p4928 (p4929 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p4931 :=
p4808 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 101 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 65294793671 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p4930 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p4830 1685237936112289033 p4831 283246355808369
    137438953472 3348 137438953472
    (@p4835 p4828 p4829 1685237936112289033
      p4831
      (p4837 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p4840 (p4871 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p4833 p4834)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p4932 :=
nat_lit
  1349741793679353189084180645763788978947396333687240225057388165117386706567933154434559190873444996006234524437531312075754984967860911981681

noncomputable def p4933 :=
nat_lit
  8522599787724385270844096661542751593467260224104458617710132370159141614990306730301372918785772195810283067676950512887882527392881

noncomputable def p4934 :=
nat_lit
  6747919303160223572074081479507746547628450987588756492561912651605898839728901688265928489593873900331241516485612428657019981451034791625841

noncomputable def p4935 :=
BSN.sin_dyadic_bound_f 119549475363 137438953472 4 3 137438953472
  68719476736 p4932 p2504 p4933 p4934
  p2507

noncomputable def p4936 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 119549475363) (BSN.sinEvenQ 137438953472) 0
  3 p4932 p2504 p4933 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4937 :=
p4935 p4933 105034114572 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4936 (Eq.refl true))

noncomputable def p4938 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 119549475363) (BSN.sinOddQ 137438953472) 0
  3 p4934 p2507 p4933 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4939 :=
nat_lit 23125509941571910198662148643027952444494183222531481513259378145319889678016231025007212225

noncomputable def p4940 :=
nat_lit 459328183476053496548782416555205718110055657887024158651167316790992724280686728263361

noncomputable def p4941 :=
nat_lit 60566068077534136909882643655446405116798301683183967828946269443039192311346055382220748481

noncomputable def p4942 :=
BSN.sin_dyadic_bound_f 68040169479 137438953472 3 2 137438953472
  68719476736 p4939 p2477 p4940 p4941
  p2480

noncomputable def p4943 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 68040169479) (BSN.sinEvenQ 137438953472) 0
  2 p4939 p2477 p4940 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4944 :=
p4942 p4940 65294793671 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4943 (Eq.refl true))

noncomputable def p4945 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 68040169479) (BSN.sinOddQ 137438953472) 0
  2 p4941 p2480 p4940 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4946 :=
p4931 d121 d123 d125 d127 d103
  (p4937 (p4938 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p4944 (p4945 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p4947 :=
p4803 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 112162115311 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p4946 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p4830 1685237936112289033 p4831 283246355808369
    137438953472 3348 137438953472
    (@p4835 p4828 p4829 1685237936112289033
      p4831
      (p4837 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p4840 (p4871 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p4833 p4834)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p4948 :=
nat_lit 119114556023259747607617343140388664174001

noncomputable def p4949 :=
BSN.sin_dyadic_bound_f 18577668501 137438953472 2 1 137438953472
  68719476736 p4948 p3178 p4948 p4948
  p3179

noncomputable def p4950 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 18577668501) (BSN.sinEvenQ 137438953472) 0
  1 p4948 p3178 p4948 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4951 :=
p4949 p4948 18521148008 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4950 (Eq.refl true))

noncomputable def p4952 :=
@BSN.binarySplit_of_base (BSN.sinOddP 18577668501) (BSN.sinOddQ 137438953472) 0
  1 p4948 p3179 p4948 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4953 :=
nat_lit
  130718533031461176890987806441206004038359496441861628420631175441983442838108131704021935710665498996631103323956052053999100640819859685376

noncomputable def p4954 :=
nat_lit
  136108854898886949043416165559898759100033758787810329841854183770684032094747255188251459283451882257132042091208118386682857783296

noncomputable def p4955 :=
nat_lit
  792980402968364936068350503237314605133138586897982734278483868224638682212032081667563263112163390011252442606462665399509489997618002001920

noncomputable def p4956 :=
BSN.cos_dyadic_bound_f 84688387736 137438953472 4 3 137438953472
  68719476736 p4953 p2457 p4954 p4955
  p2460

noncomputable def p4957 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 84688387736) (BSN.cosEvenQ 137438953472) 0
  3 p4953 p2457 p4954 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4958 :=
p4956 p4954 112162115311 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4957 (Eq.refl true))

noncomputable def p4959 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 84688387736) (BSN.cosOddQ 137438953472) 0
  3 p4955 p2460 p4954 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4960 :=
p4947 d129 d131 d133 d135 d103
  (p4951 (p4952 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p4958 (p4959 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p4961 :=
p4798
  (p4960 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p4830 1685237936112289033 p4831 283246355808369
    137438953472 3348 137438953472
    (@p4835 p4828 p4829 1685237936112289033
      p4831
      (p4837 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p4840 (p4871 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p4833 p4834)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p4962 :=
nat_lit 21989089497882013613317685025860520821062522387056739498857936319009660289614340977374424801

noncomputable def p4963 :=
nat_lit 1345439166606434347092437174115653204196256373821997167430387867706317333238696288349921

noncomputable def p4964 :=
nat_lit 65964577615312827971258870203233331156779174648422574502238948181293568234176545539546574561

noncomputable def p4965 :=
BSN.cos_dyadic_bound_f 77823007141 137438953472 3 2 137438953472
  68719476736 p4962 p2466 p4963 p4964
  p2469

noncomputable def p4966 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 77823007141) (BSN.cosEvenQ 137438953472) 0
  2 p4962 p2466 p4963 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4967 :=
p4965 p4963 115988264735 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p4966 (Eq.refl true))

noncomputable def p4968 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 77823007141) (BSN.cosOddQ 137438953472) 0
  2 p4964 p2469 p4963 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4969 :=
p4961 d137 d139 d103
  (p4967 (p4968 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p4970 :=
@p4787 p4771 p4773 p4774
  (p4791
    (@p4794 54265 17179869184
      (p4969 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p4969 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p4971 :=
@Enclosure.Real.IsNear.mulLit_ff p4778
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p4779)))

noncomputable def p4972 :=
nat_lit
  1589045587482036626572232964392307151532786389203631169450781046115692802242029090673642493063615639489970132450668152755424641519413352739618420081561358552278809

noncomputable def p4973 :=
nat_lit
  3599131035634557106248430806148785487095757694641533306480604458089470064537190296255232548883112685719936728506816716098566612844395439751206812144692131084107776

noncomputable def p4974 :=
nat_lit
  10693643321591676965247647610904511477017426859536038531934398310111718378820998337762947957272176040729250697245595517763762266547611991090654319336891464214768202669279145977564980311493846580528295808861573031927

noncomputable def p4975 :=
nat_lit
  104611634502814732955149761294712252538601437545985052382802391920185243899673893228564609500776487616922819744602617719602021359070876583487078400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p4976 :=
@p4971 4824402423 17179869184 1 17179869184
  p4972 p4973 p4974 p4975
  p4784 p4771 p4785

noncomputable def p4977 :=
@Enclosure.Real.IsNear.mulLit_ff
  c22
  (p4777
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p4978 :=
@p4977 1 1 0 1 4824402423 17179869184
  1 17179869184 4824402423 17179869184 1

noncomputable def p4979 :=
@Enclosure.Real.IsNear.of_eq
  (p4777
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p4980 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    c7)

noncomputable def p4981 :=
p4980
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    101038100 100000
    (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true)))

noncomputable def p4982 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt p4779)) false
  4824402423 17179869184 1 17179869184 4824402423
  17179869184

noncomputable def p4983 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p4779) false 61178127213
  17179869184 7 17179869184 61178127213 17179869184 7
  17179869184

noncomputable def p4984 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    c7)

noncomputable def p4985 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    c7)

noncomputable def p4986 :=
@p4985
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101038100 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 2762645467510243

noncomputable def p4987 :=
@p4986 17179869184000 1010381 17179869184000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    101038100 100000
    (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true)))

noncomputable def p4988 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101038100 100000)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101038100 100000 0

noncomputable def p4989 :=
@p4988 1 2734261103 17179869184 1 17179869184
  2762645467510243 17179869184000 1010381 17179869184000
  (Enclosure.Real.IsNear.const false 101038100 100000) d142

noncomputable def p4990 :=
@p4984 2762645467510243 17179869184000 1010381 17179869184000
  108928747027 108928747068 8589934592
  (p4987 (p4989 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p4991 :=
@Enclosure.Real.IsNear.recentre' p4779 false 217857494095 17179869184
  41 17179869184 217857494095 17179869184 41 17179869184
  (p4990 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p4992 :=
@Enclosure.Real.IsNear.sqrt_image p4779 217857494095 17179869184 41
  17179869184 30589063603 30589063610 8589934592
  (p4991 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p4993 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p4779) 61178127213 17179869184
  7 17179869184 2412201211 2412201212 8589934592
  (p4983
    (p4992 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p4994 :=
@p4979 (@Inv.inv Real Real.instInv (Real.sqrt p4779)) false
  4824402423 17179869184 1 17179869184 p4981
  (@p4982 1 17179869184
    (p4993 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p4995 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p4779))
  16314403013864294613

noncomputable def p4996 :=
nat_lit 951160241300648755200000000

noncomputable def p4997 :=
nat_lit
  2500161199267005206366864727163154040993782717969877428651699829309189288342802727260685489318951803154508089575892742831765716773824482191203538780327139334375

noncomputable def p4998 :=
nat_lit
  85257064496996159862179094445420378199790783982992041967831842917115388464414764411806433980170448843657007954127490155412578018612243202829423336891464214768202669279145977564980311493846580528295808861573031927

noncomputable def p4999 :=
nat_lit
  58625434547477143999371602403269056869891944375111199849172990754014334791560943181335988801297377938542537103068738870006187505227468772485869685459080889304631388656347812817010688

noncomputable def p5000 :=
@p4995 36893488147419103232 96454617883225681613 p4996
  p4997 p4973 p4998 p4975
  p4999 p4972 p4973 p4974

noncomputable def p5001 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5002 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))

noncomputable def p5003 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (p5001
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5004 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  101038100 100000 12
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))

noncomputable def p5005 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5006 :=
@p5005
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5002 (Enclosure.sfrac false 1 16))))
  40882310621

noncomputable def p5007 :=
@p5006 17179869184 1497 17179869184 399057753
  2147483648 3965195057 110729625600000000 16314403013864294613
  36893488147419103232 96454617883225681613 p4996

noncomputable def p5008 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5009 :=
@Inv.inv Real Real.instInv
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5010 :=
@p5008 (@Neg.neg Real Real.instNeg p5009) true 40882310621
  17179869184 1497 17179869184
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5011 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5012 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p5013 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p5014 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 36753693161)
    (@Nat.cast Real Real.instNatCast 8589934592))
  false

noncomputable def p5015 :=
nat_lit 10345244926600997925118285

noncomputable def p5016 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  false p5015

noncomputable def p5017 :=
nat_lit 1106429192264999440621206751

noncomputable def p5018 :=
nat_lit 73786976294838206464000000000000000

noncomputable def p5019 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p5020 :=
@Enclosure.Real.IsNear.subLit_ff_p p4779 (Enclosure.sfrac false 12 1)
  217857494095 17179869184 41 17179869184 12 1 0

noncomputable def p5021 :=
@p5019 500000000000000 11699063887 17179869184 41
  17179869184 p5015 p2602 p5017 p5018
  d141
  (@p5020 1 11699063887 11699063887 17179869184 41
    17179869184 (p4991 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5022 :=
@p5014 36753693161 8589934592 259 17179869184 true
  7219452636 17179869184 1 3300000000
  (@p5016 p2602 p5017 p5018
    36753693161 8589934592 259 17179869184
    (p5021 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 36753693161 8589934592)

noncomputable def p5023 :=
nat_lit 1407662069376202156825116672

noncomputable def p5024 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 36753693161)
    (@Nat.cast Real Real.instNatCast 8589934592))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p5023)
    (@Nat.cast Real Real.instNatCast p2445))
  226375608064910080 72057594037927936 false

noncomputable def p5025 :=
BSN.sin_reduce_arg_pos_rat_q2 36753693161 8589934592 226375608064910080
  72057594037927936 0 p5023 p2445 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5026 :=
nat_lit
  120212770598551404737485128703386090431772525458617371636535665082289747831365743648441411904282146889682712526190844705675283108895239049344270703158969612059185660480401

noncomputable def p5027 :=
nat_lit
  16818344400234189301006900766005339441735562772368814172986513767622603926081226788744156271296918683126537974344094185597969751437027739762348026097267268083960721

noncomputable def p5028 :=
nat_lit
  728807371260626320433143458673946274520379355816923538718704998241956981501080936576835622788054933957210142709449724497270484253131594755408516064706516726018758006721425

noncomputable def p5029 :=
BSN.cos_dyadic_bound_f 40008162312011 35184372088832 4 3 17179869184
  6606445313 p5026 p2613 p5027 p5028
  p2616

noncomputable def p5030 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 40008162312011) (BSN.cosEvenQ 35184372088832) 0
  3 p5026 p2613 p5027 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5031 :=
p5029 p5027 7219452636 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5030 (Eq.refl true))

noncomputable def p5032 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 40008162312011) (BSN.cosOddQ 35184372088832) 0
  3 p5028 p2616 p5027 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5033 :=
@BSN.cos_arg_round false 7219452636 17179869184 p5023 p2445
  40008162312011 35184372088832 6606445313 6600000000
  (p5031 (p5032 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5034 :=
p5024 7219452636 17179869184 0 1000000000000000
  6600000000 3300000000 p5025 BSN.pi_near_15 p5033
  (Eq.refl true) (Eq.refl true)

noncomputable def p5035 :=
@p5012 1804863159 4294967296 3405780739 221459251200000000
  (@p5013 7219452636 17179869184 871879869184
    56693568307200000000 1804863159 4294967296 3405780739
    221459251200000000
    (p5022 (p5034 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5036 :=
@p5011 1804863159 4294967296 3405780739 221459251200000000
  20441154562 20441156059 8589934592 p5035 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5037 :=
@Enclosure.Real.IsNear.recentre' p5009 false 40882310621 17179869184
  1497 17179869184 40882310621 17179869184 1497 17179869184
  (p5036 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p5038 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5002 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p5039 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5002 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 30197202207))
    (@Nat.cast Real Real.instNatCast 17179869184))
  true

noncomputable def p5040 :=
nat_lit 73012354858507501399268819139550525

noncomputable def p5041 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5002 (Enclosure.sfrac false 1 16)))
  true p5040

noncomputable def p5042 :=
nat_lit 44896677074727489434355772464113645913

noncomputable def p5043 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p5002 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p5044 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))

noncomputable def p5045 :=
@p5044 (Enclosure.sfrac false 1 16) 64120291321811009439
  295147905179352825856 1663697876959 295147905179352825856 1 16
  0

noncomputable def p5046 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
    (Enclosure.sfrac false 12 1))
  136868095832107548769

noncomputable def p5047 :=
nat_lit 1101578216948683588133009227776

noncomputable def p5048 :=
@p5046 295147905179352825856 959323240415 295147905179352825856
  11699063887 17179869184 41 17179869184 p5047
  64120291321811009439 295147905179352825856 1663697876959

noncomputable def p5049 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
    (Enclosure.sfrac false 12 1))
  11699063887 17179869184 41

noncomputable def p5050 :=
@p5049 17179869184 11699063887 17179869184 41
  17179869184 136868095832107548769 295147905179352825856 959323240415
  295147905179352825856
  (@p5020 1 11699063887 11699063887 17179869184 41
    17179869184 (p4991 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5051 :=
p5050
  (@p5020 1 11699063887 11699063887 17179869184 41
    17179869184 (p4991 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5052 :=
@p5048 295147905179352825856 (p5051 (Eq.refl true))
  (@p5020 1 11699063887 11699063887 17179869184 41
    17179869184 (p4991 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5053 :=
@p5043 500000000000000 82567035395520561055 295147905179352825856
  1663697876959 295147905179352825856 p5040 p2630
  p5042 p2632 d141
  (@p5045 1 1321072566328328976880 82567035395520561055
    295147905179352825856 1663697876959 295147905179352825856
    (p5052 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5054 :=
@p5039 30197202207 17179869184 305 8589934592 true
  1596231012 8589934592 1 3300000000
  (@p5041 p2630 p5042 p2632
    30197202207 17179869184 305 8589934592
    (p5053 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 30197202207 17179869184)

noncomputable def p5055 :=
nat_lit
  481921087105145011267326831634849449218020777907199304331084481556043775952534252470550668208532457007635329364406688222483742044670095022368826729745980679717688023541496942081

noncomputable def p5056 :=
nat_lit
  478043386025562578454332561384505397033145301705946062251537207608085917772683241207270807140676338550338000908575994850641579854314269094060362860075282383403493363201

noncomputable def p5057 :=
nat_lit
  4897062440261300193245660615258018600305248682638990499706351365317604279120216451222621158131856334007916033606075640556567758792073373310647892875099569893002610992799819763201

noncomputable def p5058 :=
BSN.cos_dyadic_bound_t 30197202207 17179869184 5 4 8589934592
  3300000000 p5055 p3287 p5056 p5057
  p3290

noncomputable def p5059 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 30197202207) (BSN.cosEvenQ 17179869184) 0
  4 p5055 p3287 p5056 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5060 :=
p5058 p5056 1596231012 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5059 (Eq.refl true))

noncomputable def p5061 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 30197202207) (BSN.cosOddQ 17179869184) 0
  4 p5057 p3290 p5056 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5062 :=
p5054
  (BSN.cos_neg_of_bound 30197202207 17179869184 true 1596231012 8589934592
    1 3300000000
    (p5060 (p5061 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p5063 :=
p5007
  (p5010
    (@Enclosure.Real.IsNear.neg p5009 false 40882310621 17179869184
      1497 17179869184 (p5037 (Eq.refl true))))
  (@p5038 1596231012 8589934592 1015089934592
    28346784153600000000 399057753 2147483648 3965195057
    110729625600000000 (p5062 (Eq.refl true)) (Eq.refl true))

noncomputable def p5064 :=
@p5000 p4975
  (@p5003 false 16314403013864294613 36893488147419103232
    96454617883225681613 p4996
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (p5004 (Eq.refl true) (Eq.refl true)
        (p4782 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5063 (Eq.refl true)))

noncomputable def p5065 :=
nat_lit
  1845443739664732029203847314008696905578081780246111795487957197935323181960349327844839639429117345448162039070782544566625032651692500081076955131875

noncomputable def p5066 :=
nat_lit
  209496998905353079680844140596966345741865090946756146526930647558152562969899171512529285908857866057656747784163844544589904418936665155413025765720064

noncomputable def p5067 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv p4779) p5065 p5066

noncomputable def p5068 :=
nat_lit
  62891195795414642531033488391444214682287040227007955032132092363247250068490402476238824270815632224437073630815895306178582911215519362195359425046289914213280701375380225791354676944686644955769238707

noncomputable def p5069 :=
nat_lit
  6089198548743427553863134310505833275301931283086599571560648730966800585137324712039239791965606134438585707952886454272201596705177600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5070 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))

noncomputable def p5071 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg Real Real.instNeg p5070) true p5065

noncomputable def p5072 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))

noncomputable def p5073 :=
nat_lit
  397568502829469491673256014672040619339371264245966066154069419327257367575381397167924458067825482470880273449205793726369078037386997487125

noncomputable def p5074 :=
nat_lit
  47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616

noncomputable def p5075 :=
nat_lit
  121916845603550465833211758611291603399764369905008939068830357518268839526125715356952451802799521247574718543320509006932750581959582507887262316249895854315040122269716525860275290213841321693

noncomputable def p5076 :=
nat_lit
  12460711090782489915174712403893977233955725193431907460773308816601730829060198268133071480335833077776276552771373210009600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5077 :=
@p5072 p5073 p5074 p5075 p5076
  4641825815 4398046511104 1 4398046511104 p5065
  p5066 p5068

noncomputable def p5078 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5079 :=
p5078
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5080 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5079
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5081 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5080
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5082 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5083 :=
p5081
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5082
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5084 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5085 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5083
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p5084)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))

noncomputable def p5086 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c16)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5087 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5085
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p5086)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))

noncomputable def p5088 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c16 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))

noncomputable def p5089 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (p5001
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5087
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5088
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
            (Enclosure.sfrac false 12 1))))))

noncomputable def p5090 :=
@p5005
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5087
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5088
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))
  10465871295845

noncomputable def p5091 :=
nat_lit
  37987138537362489093096067104690536196385335078785760857428492904348322685082958924255465705765648243575911534595662967173507825

noncomputable def p5092 :=
nat_lit
  10830740992659433045228180406808920716548582325686783496759685861775864483615725089999900023844295226942934417817982702456930304

noncomputable def p5093 :=
nat_lit
  11647575807517308742459446417641392456339543783459390769199039206967453551221919804412238117300540706271795278823349593552979686938151870693451520330154717893875008899083590109169963

noncomputable def p5094 :=
@p5090 4398046511104 1491 4398046511104 p5091
  p5092 p5093 p3327 p5073
  p5074 p5075 p5076

noncomputable def p5095 :=
@p5008 (@Neg.neg Real Real.instNeg p5009) true 10465871295845
  4398046511104 1491 4398046511104
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5096 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c60
    c33)
  false

noncomputable def p5097 :=
nat_lit 2648382695100366890234719465

noncomputable def p5098 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  false p5097

noncomputable def p5099 :=
nat_lit 1106454818284302217379282143

noncomputable def p5100 :=
@Enclosure.Real.IsNear.subLit_ff_p p4779 (Enclosure.sfrac false 12 1)
  55771518481411 4398046511104 41 4398046511104 12 1
  0

noncomputable def p5101 :=
@p4985
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101038100 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 707237239503784771

noncomputable def p5102 :=
@p5101 4398046511104000 1010381 4398046511104000
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    101038100 100000
    (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true)))

noncomputable def p5103 :=
@p4988 1 699970842191 4398046511104 1 4398046511104
  707237239503784771 4398046511104000 1010381 4398046511104000
  (Enclosure.Real.IsNear.const false 101038100 100000) d145

noncomputable def p5104 :=
@p4984 707237239503784771 4398046511104000 1010381
  4398046511104000 27885759240685 27885759240726 2199023255552
  (p5102 (p5103 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5105 :=
@Enclosure.Real.IsNear.recentre' p4779 false 55771518481411 4398046511104
  41 4398046511104 55771518481411 4398046511104 41
  4398046511104
  (p5104 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p5106 :=
@p5019 500000000000000 2994960348163 4398046511104 41
  4398046511104 p5097 p504 p5099 p2694
  d144
  (@p5100 1 2994960348163 2994960348163 4398046511104
    41 4398046511104 (p5105 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5107 :=
@p5096 18817890855163 4398046511104 129 2199023255552
  true 1848179914224 4398046511104 1 844800000000
  (@p5098 p504 p5099 p2694
    18817890855163 4398046511104 129 2199023255552
    (p5106 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 18817890855163 4398046511104)

noncomputable def p5108 :=
nat_lit 720722973284895431440252010496

noncomputable def p5109 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    c60
    c33)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p5108)
    (@Nat.cast Real Real.instNatCast p2704))
  226375608064910080 72057594037927936 false

noncomputable def p5110 :=
BSN.sin_reduce_arg_pos_rat_q2 18817890855163 4398046511104 226375608064910080
  72057594037927936 0 p5108 p2704 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5111 :=
nat_lit
  2738242367550622824061907186846228054180052032510876497800124191525200102413473825862954059029590453893201801802460994031887042210884968456529989901388814191403926998746114639297169895028036799027707048432242598460989199655486809682995553762136896636108991935981551616

noncomputable def p5112 :=
nat_lit
  14662804370152634534387705050068882121443354369034164297253541836338776498679827959944303312758636205891762974987093923756532256754028678459342255269915736140140291075503042152335692138419634930070779223533437279528646629065417708777410925344387769707790336

noncomputable def p5113 :=
nat_lit
  27911557681525844921106560593150048464133937892691745613308313031414582611318169433344467853614283799620157538919538525428788964161881438707759261579411004664153326337793890865785514141309081147129517190953714517429905861941604010890506944349904812842511364323106881536

noncomputable def p5114 :=
BSN.cos_dyadic_bound_f 10242089463260064 9007199254740992 5 4
  4398046511104 1691250000001 p5111 p2708
  p5112 p5113 p2711

noncomputable def p5115 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 10242089463260064) (BSN.cosEvenQ 9007199254740992)
  0 4 p5111 p2708 p5112
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5116 :=
p5114 p5112 1848179914224 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5115 (Eq.refl true))

noncomputable def p5117 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 10242089463260064) (BSN.cosOddQ 9007199254740992) 0
  4 p5113 p2711 p5112 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5118 :=
@BSN.cos_arg_round false 1848179914224 4398046511104 p5108
  p2704 10242089463260064 9007199254740992 1691250000001
  1689600000000
  (p5116 (p5117 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5119 :=
p5109 1848179914224 4398046511104 0 1000000000000000
  1689600000000 844800000000 p5110 BSN.pi_near_15 p5118
  (Eq.refl true) (Eq.refl true)

noncomputable def p5120 :=
@p5012 115511244639 274877906944 1696445057
  28346784153600000000
  (@p5013 1848179914224 4398046511104 111178223255552
    p3422 115511244639 274877906944 1696445057
    28346784153600000000
    (p5107 (p5119 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5121 :=
@p5011 115511244639 274877906944 1696445057
  28346784153600000000 5232935647177 5232935648668 2199023255552
  p5120 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5122 :=
@Enclosure.Real.IsNear.recentre' p5009 false 10465871295845 4398046511104
  1491 4398046511104 10465871295845 4398046511104 1491
  4398046511104
  (p5121 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p5123 :=
nat_lit
  1116007630068725840030476706529450216806416690012519194453702589925151827191527718517520130626832930821843550866085001977098627825

noncomputable def p5124 :=
@Enclosure.Real.IsNear.subLit_tt_n p5087
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5088
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))
  p5123 p5092

noncomputable def p5125 :=
nat_lit
  11376523263531227354543900911998211116839739960784465858164307266810161179685282397016485326540389324612293502591080954730901893960022514404018844492928821893707400579083590109169963

noncomputable def p5126 :=
nat_lit 368805776194722639147807892184172887380159415756027547782612689665000775872731875

noncomputable def p5127 :=
nat_lit 3705346855594118253554271520278013051304639509300498049262642688253220148477952

noncomputable def p5128 :=
nat_lit
  3348324087176028911682877439031086412329521441319636118781547173107610834504355513334812438060514574328650105770183979

noncomputable def p5129 :=
nat_lit
  34999110603960808201303934371190521482933581204589227952863969280000000000000000000000000000000000000000000000000000000000000

noncomputable def p5130 :=
nat_lit
  140755524332434251361417280735071227708667558122546547542629680666382502668976603737553753195805536353808817204099579700526432710314714967439093453020528388536343726165593463078054249035894699612170511974400

noncomputable def p5131 :=
@p5124 p5125 p3327 p5126 p5127
  p5128 p5129 p5130 p5091
  p5092 p5093 p3327

noncomputable def p5132 :=
@Enclosure.Real.IsNear.subLit_tf p5085
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p5086)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))

noncomputable def p5133 :=
nat_lit
  748347981615351769798256212325895064921641740584022003409301064017078875222985505315560272799394210446503618179550620415652227825

noncomputable def p5134 :=
nat_lit
  10390595964815104246516603957073485244054037608496367200274430975844050411874396638003893837378062321010993582651120749102373714332783032166646470879592930708097127603413113309169963

noncomputable def p5135 :=
nat_lit 152060466609346388703914051706166891275450225325873949622969081570611253279915163409404286071521820621875

noncomputable def p5136 :=
nat_lit 4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986543214231552

noncomputable def p5137 :=
nat_lit
  63266129212877933255105006503613775823598139480012191952020683674780049491859804554962810399975445724453301080554642946771130410979224621700050767101

noncomputable def p5138 :=
nat_lit
  181806489531031316723001829545616663927104621289106088477152037939549487753696817184768000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5139 :=
nat_lit
  4999144443353481308976490410666627437169944018436571676399953400680618978396150831786493368729196526502982778555169688377725952549765929771549522127575019536857142231358543602830935818063584311081324299872715217154117266471020134400

noncomputable def p5140 :=
@p5132 p5133 p5092 p5134 p3327
  p5135 p5136 p5137 p5138
  p5139 p5123 p5092

noncomputable def p5141 :=
@Enclosure.Real.IsNear.subLit_ff_n p5083
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p5084)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))

noncomputable def p5142 :=
nat_lit 71289072596916471886814529569513506574398095570039417485305014568172017054409661223424586225

noncomputable def p5143 :=
nat_lit 16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008

noncomputable def p5144 :=
nat_lit
  96990101885143236966686429010290751970569694853691923205656741526912904125122330326926979538493545217431576502217954156757

noncomputable def p5145 :=
nat_lit
  5970529601299116326527878914510470248684233584322091583284531675408020747059200000000000000000000000000000000000000000000000000000

noncomputable def p5146 :=
nat_lit
  795727697160034094675504166452238219722062359328538652571580510757767130372677754979172413456381274426582461686409798112263760625

noncomputable def p5147 :=
nat_lit
  10344570565137838668327278973052199117120012496991896249878997626179667309332686070945890640646275759649617045176744981785666476052873397802633495845122432404097127603413113309169963

noncomputable def p5148 :=
nat_lit
  12195294090942161092093823413286691131824757910306880904954287477860367119337616216005912708687793173698815685178013100965487577674528723380692725031471716820440987894636152271958631114727911606745981983197538893273497600

noncomputable def p5149 :=
@p5141 p5142 p5143 p5144 p5145
  p5146 p5092 p5147 p3327
  p5148 p5133 p5092

noncomputable def p5150 :=
@Enclosure.Real.IsNear.subLit_tt_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5080
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5151 :=
@p5150
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5082
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5152 :=
nat_lit 188340698767468973026115712874849312323371388326574332762842306292317320805669180828501839375

noncomputable def p5153 :=
nat_lit
  20486800015389827445371004336432431958811302688407808377897321838465599045592859579275311518773670573152280502217954156757

noncomputable def p5154 :=
nat_lit 190745830965073249629436927308347524778638288930126275

noncomputable def p5155 :=
nat_lit 11972621413014756705924586149611790497021399392059392

noncomputable def p5156 :=
nat_lit 306958333157196043029852159424432274613106115633556061065325720112572387

noncomputable def p5157 :=
nat_lit 23955878631234067827821572363196482086502400000000000000000000000000000000000000

noncomputable def p5158 :=
nat_lit
  853517077087805660964437318510532003380684766007404108099600077036631510060291522119099567467392479797437177217782623279614864727448208225075200

noncomputable def p5159 :=
@p5151 p5152 p5143 p5153 p5145
  p5154 p5155 p5156 p5157
  p5158 p5142 p5143

noncomputable def p5160 :=
nat_lit 348662489505308250235065362530514619762541238030936288781968606417419969709557625

noncomputable def p5161 :=
@Enclosure.Real.IsNear.mulLit_ft p5080
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5002 (Enclosure.sfrac false 1 16))))
  p5160

noncomputable def p5162 :=
nat_lit 1531385295538717815551140622617785650761182342904653350196273204937271732586670921889011521003910141779

noncomputable def p5163 :=
nat_lit 842498333348457493583344221469363458551160763204392890034487820288000000000000000000000000000000000000000000000

noncomputable def p5164 :=
@p5161 p2761 p5162 p5163 540180559815
  549755813888 3965195057 28346784153600000000 p5152
  p5143 p5153 p5145

noncomputable def p5165 :=
@Enclosure.Real.IsNear.mulLit_ff p5079
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5166 :=
nat_lit 495378116818109254696553565255488212491147987202731025

noncomputable def p5167 :=
nat_lit 47530757927166508585109104287133344934043676301711849457283308631

noncomputable def p5168 :=
nat_lit 89202980794122492566142873090593446023921664000000000000000000000000000000

noncomputable def p5169 :=
nat_lit 703831028598561612673232105

noncomputable def p5170 :=
nat_lit 1106435928818370738798427359

noncomputable def p5171 :=
nat_lit 9444732965739290427392000000000000000

noncomputable def p5172 :=
@p5165 p5166 p2767 p5167 p5168
  p5169 p976 p5170 p5171 p5160
  p2761 p5162

noncomputable def p5173 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5174 :=
@p5173
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5175 :=
@p5174 p5169 p976 p5170 p5171
  p5169 p976 p5170 p5171 p5166
  p2767 p5167

noncomputable def p5176 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p5177 :=
@p5176 140737488355328 1 500000000000000 795937092611
  2199023255552 41 2199023255552 p5169 p976
  p5170 p5171

noncomputable def p5178 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 2994960348163 2199023255552

noncomputable def p5179 :=
@p5178 41 2199023255552 1 1 0 1
  795937092611 795937092611 2199023255552 41 2199023255552

noncomputable def p5180 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p5181 :=
@p5180 2994960348163 4398046511104 41 4398046511104
  2994960348163 2199023255552 41 2199023255552
  (Enclosure.Real.IsNear.const false 2 1)
  (@p5100 1 2994960348163 2994960348163 4398046511104
    41 4398046511104 (p5105 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5182 :=
@p5175 p5168
  (p5177 d144
    (p5179 (p5181 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p5177 d144
    (p5179 (p5181 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p5183 :=
@p5172 p5163 (p5182 (Eq.refl true))
  (p5177 d144
    (p5179 (p5181 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p5184 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5002 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p5185 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5002 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3865241890467))
    (@Nat.cast Real Real.instNatCast 2199023255552))
  true

noncomputable def p5186 :=
nat_lit 4784937697732684807087862284565038802245

noncomputable def p5187 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5002 (Enclosure.sfrac false 1 16)))
  true p5186

noncomputable def p5188 :=
nat_lit 2298719120763175498470040275130842644733

noncomputable def p5189 :=
nat_lit 16615349947311448411297588253504307200000000000000

noncomputable def p5190 :=
nat_lit 5411113242679094282733559

noncomputable def p5191 :=
nat_lit 4202187423064465108027383

noncomputable def p5192 :=
@p5044 (Enclosure.sfrac false 1 16) p5191
  p2793 425906655506311 p2793 1 16 0

noncomputable def p5193 :=
nat_lit 86577811882865508523736944

noncomputable def p5194 :=
nat_lit 8969787487068638177474569

noncomputable def p5195 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
    (Enclosure.sfrac false 12 1))
  p5194

noncomputable def p5196 :=
nat_lit 18481415735013779188439774266845560832

noncomputable def p5197 :=
@p5195 p2793 245586748551047 p2793
  2994960348163 4398046511104 41 4398046511104 p5196
  p5191 p2793 425906655506311

noncomputable def p5198 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
    (Enclosure.sfrac false 12 1))
  2994960348163 4398046511104 41

noncomputable def p5199 :=
@p5198 4398046511104 2994960348163 4398046511104 41
  4398046511104 p5194 p2793 245586748551047
  p2793
  (@p5100 1 2994960348163 2994960348163 4398046511104
    41 4398046511104 (p5105 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5200 :=
p5199
  (@p5100 1 2994960348163 2994960348163 4398046511104
    41 4398046511104 (p5105 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5201 :=
@p5197 p2793 (p5200 (Eq.refl true))
  (@p5100 1 2994960348163 2994960348163 4398046511104
    41 4398046511104 (p5105 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5202 :=
@p5043 500000000000000 p5190 p2793
  425906655506311 p2793 p5186 p2789
  p5188 p5189 d144
  (@p5192 1 p5193 p5190 p2793
    425906655506311 p2793
    (p5201 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5203 :=
@p5185 3865241890467 2199023255552 305 2199023255552 true
  2160722239260 2199023255552 1 844800000000
  (@p5187 p2789 p5188 p5189
    3865241890467 2199023255552 305 2199023255552
    (p5202 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 3865241890467 2199023255552)

noncomputable def p5204 :=
nat_lit
  8486357004283518565711381002870821669605438143584119525601147597060812273983947574741077797842279269060485917066492045278645538735200750122525578646194689520407955845111947272630511314939440740874070044626683201

noncomputable def p5205 :=
nat_lit
  2482143253403701007620813219319613157657659797014656194373591914940073784016843883837728475704307707046199955609473014179286797711592682705274660430788638310150988887732388867329333285814777006580598081

noncomputable def p5206 :=
nat_lit
  68968680108805309793209579743976724943472054078602031866254720841854890497602290691039829897388001403669570954710513153592467275251483648278866602277638182310916945048926647890248382675296769117989633354125313345

noncomputable def p5207 :=
BSN.sin_dyadic_bound_f 3865241890467 2199023255552 5 4 2199023255552
  844800000000 p5204 p3441 p5205 p5206
  p3444

noncomputable def p5208 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 3865241890467) (BSN.sinEvenQ 2199023255552) 0
  4 p5204 p3441 p5205 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5209 :=
p5207 p5205 2160722239260 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5208 (Eq.refl true))

noncomputable def p5210 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 3865241890467) (BSN.sinOddQ 2199023255552) 0
  4 p5206 p3444 p5205 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5211 :=
p5203
  (BSN.sin_neg_of_bound 3865241890467 2199023255552 false 2160722239260
    2199023255552 1 844800000000
    (p5209 (p5210 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p5212 :=
p5164 p5183
  (@p5184 2160722239260 2199023255552 259863023255552
    p3422 540180559815 549755813888 3965195057
    28346784153600000000 (p5211 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5213 :=
nat_lit 1867150512585357437896621233492695505399825

noncomputable def p5214 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5082
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5002 (Enclosure.sfrac false 1 16))))
  p5213

noncomputable def p5215 :=
nat_lit 89575643746348210311506697850420093457802471661704459

noncomputable def p5216 :=
nat_lit 20282409603651670423947251286016000000000000000000000000000000

noncomputable def p5217 :=
@p5214 p2820 p5215 p5216 102158786707
  549755813888 3965195057 28346784153600000000 p5154
  p5155 p5156 p5157

noncomputable def p5218 :=
nat_lit 2111493085795684838019696315

noncomputable def p5219 :=
nat_lit 3319307786455112216395282077

noncomputable def p5220 :=
@Enclosure.Real.IsNear.mulLit_ff p5082
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p5218 p976 p5219 p5171

noncomputable def p5221 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5222 :=
@p5221 3 1 0 1 p5169 p976
  p5170 p5171 p5218 p976 p5219

noncomputable def p5223 :=
@p5222 p5171 (Enclosure.Real.IsNear.const false 3 1)
  (p5177 d144
    (p5179 (p5181 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p5224 :=
@p5220 884279719003555 70368744177664 1 250000000000000
  p5213 p2820 p5215 p5216
  p5223 d146 (Eq.refl true)

noncomputable def p5225 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5002 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3865241890467))
    (@Nat.cast Real Real.instNatCast 2199023255552))
  true

noncomputable def p5226 :=
@p5225 3865241890467 2199023255552 305 2199023255552 true
  408635146828 2199023255552 1 844800000000
  (@p5187 p2789 p5188 p5189
    3865241890467 2199023255552 305 2199023255552
    (p5202 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 3865241890467 2199023255552)

noncomputable def p5227 :=
nat_lit
  2502277367395573687012186131589175547068874475365981480198890469759789180394838562512940684331105153003634122488612365211538323361418178798308361961394170343937426109562146647538014163079096023068452046383908161

noncomputable def p5228 :=
nat_lit
  25427002134759283356453467788072627115358782467288410722534545648394716366971987434520750651635349924295115343884678290488280159692595513585144550752867064039142078565156644353304787144888726823104240493690127681

noncomputable def p5229 :=
BSN.cos_dyadic_bound_t 3865241890467 2199023255552 5 4 2199023255552
  844800000000 p5227 p3467 p5205 p5228
  p3469

noncomputable def p5230 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 3865241890467) (BSN.cosEvenQ 2199023255552) 0
  4 p5227 p3467 p5205 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5231 :=
p5229 p5205 408635146828 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5230 (Eq.refl true))

noncomputable def p5232 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 3865241890467) (BSN.cosOddQ 2199023255552) 0
  4 p5228 p3469 p5205 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5233 :=
p5226
  (BSN.cos_neg_of_bound 3865241890467 2199023255552 true 408635146828
    2199023255552 1 844800000000
    (p5231 (p5232 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p5234 :=
p5217 p5224
  (@p5038 408635146828 2199023255552 259863023255552
    p3422 102158786707 549755813888 3965195057
    28346784153600000000 (p5233 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5235 :=
nat_lit 1323392057457806704234951455

noncomputable def p5236 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p5084)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  p5235

noncomputable def p5237 :=
nat_lit 45780615189277765832682833966946119

noncomputable def p5238 :=
nat_lit 40582836962161013555200000000000000000000000

noncomputable def p5239 :=
nat_lit 601278882305370064074071609498709748905374157390448978312010155368714961972246614099571560134161723375

noncomputable def p5240 :=
nat_lit 139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736

noncomputable def p5241 :=
nat_lit
  59531169999608258284297742505182796637834964371503955341370228467940515414091056754587457368810951956889734078663361369127842148100849233

noncomputable def p5242 :=
nat_lit
  279254767919664102486530810182067195792032698300066951900905530275148013189678311195803648000000000000000000000000000000000000000000000000000000

noncomputable def p5243 :=
@p5236 p3406 p5237 p5238 p5239
  p5240 p5241 p5242 p5146
  p5092 p5147 p3327

noncomputable def p5244 :=
nat_lit 441130685819268901411650485

noncomputable def p5245 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p5084
  3 1 0 1 p5244 p3406

noncomputable def p5246 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5247 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p5248 :=
@p5247 140737488355328 1 500000000000000 498858761927
  549755813888 1696445057 28346784153600000000 p5244
  p3406 p5237 p2908

noncomputable def p5249 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p5250 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c60
    c33)
  false

noncomputable def p5251 :=
@p5250 18817890855163 4398046511104 129 2199023255552
  true 3990870095416 4398046511104 1 844800000000
  (@p5098 p504 p5099 p2694
    18817890855163 4398046511104 129 2199023255552
    (p5106 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 18817890855163 4398046511104)

noncomputable def p5252 :=
BSN.sin_reduce2
  (@HDiv.hDiv Real Real Real c4
    c60
    c33)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p5108)
    (@Nat.cast Real Real.instNatCast p2704))
  226375608064910080 72057594037927936 false

noncomputable def p5253 :=
nat_lit
  24752071566094419662999160585786504966529762554680197125514545504868213653996454309558146801757413769905822415215792018704119502659459959093613513305792775925482518100633064830273731959196164498128896

noncomputable def p5254 :=
nat_lit
  1332486385018246094629758694083729724218886400404329405878106957629766356343083981684252890681314554362516792166674385732772426575028772899484943262246581645909145653824879194274501021396893696

noncomputable def p5255 :=
nat_lit
  123718078717277764628654641929619872560732143887994919154088255518979583256960444697757033370114656613842769908656552039197288981379739273897778347544737379199703613493000076019414083540886022998982656

noncomputable def p5256 :=
BSN.sin_dyadic_bound_f 10242089463260064 9007199254740992 4 3
  4398046511104 1691250000001 p5253 p2863
  p5254 p5255 p2866

noncomputable def p5257 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 10242089463260064) (BSN.sinEvenQ 9007199254740992)
  0 3 p5253 p2863 p5254
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5258 :=
p5256 p5254 3990870095416 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5257 (Eq.refl true))

noncomputable def p5259 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 10242089463260064) (BSN.sinOddQ 9007199254740992) 0
  3 p5255 p2866 p5254 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5260 :=
@BSN.sin_arg_round false 3990870095416 4398046511104 p5108
  p2704 10242089463260064 9007199254740992 1691250000001
  1689600000000
  (p5258 (p5259 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5261 :=
p5252 3990870095416 4398046511104 0 1000000000000000
  1689600000000 844800000000 p5110 BSN.pi_near_15 p5260
  (Eq.refl true) (Eq.refl true)

noncomputable def p5262 :=
p5248 d144
  (@p5249 3990870095416 4398046511104 111178223255552
    p3422 498858761927 549755813888 1696445057
    28346784153600000000
    (p5251 (p5261 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5263 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5079
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5264 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5263
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5265 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5264
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p5084)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))

noncomputable def p5266 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (p5001
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5265
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5086
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
            (Enclosure.sfrac false 12 1))))))

noncomputable def p5267 :=
@p5005
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5265
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5086
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))
  10465871295845

noncomputable def p5268 :=
nat_lit 57451392751607847590959982112444711085123121277932736209150658513996436025149841636603075

noncomputable def p5269 :=
nat_lit 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584

noncomputable def p5270 :=
nat_lit
  2835897975561563887274545179690396785512019530103216403348785710626686797840618298972857586473312111714061311433580983249989

noncomputable def p5271 :=
nat_lit
  31747591483470398826117481142099131351646144401009559249008081027926438445056000000000000000000000000000000000000000000000000000000

noncomputable def p5272 :=
@p5267 4398046511104 1491 4398046511104 p5268
  p5269 p5270 p5271 p5239
  p5240 p5241 p5242

noncomputable def p5273 :=
nat_lit 176047248332369618188164934232033594242200127702268430120741974715386700520264461812484925

noncomputable def p5274 :=
@Enclosure.Real.IsNear.subLit_ff_n p5265
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5086
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))
  p5273 p5269

noncomputable def p5275 :=
nat_lit
  2594229061400050760722992919888952895747380709158563150158438522358650738730175397702730320931372446282805090710790583249989

noncomputable def p5276 :=
nat_lit 96572774481072017050845623560810457254422982353041623815778859625

noncomputable def p5277 :=
nat_lit 13164036458569648337239753460458804039861886925068638906788872192

noncomputable def p5278 :=
nat_lit 62030767461203934659300415585207457279571805693074899954250047946591132933065411575817037887

noncomputable def p5279 :=
nat_lit
  756292228777769734159366110423965675390956315486967507385105343648808099115234090878245228889933692589348562739099732219073821540651782324555885209190400

noncomputable def p5280 :=
@p5274 p5275 p5271 p5276 p5277
  p5278 p3520 p5279 p5268
  p5269 p5270 p5271

noncomputable def p5281 :=
@Enclosure.Real.IsNear.subLit_ff_p p5264
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p5084)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))

noncomputable def p5282 :=
nat_lit 700778911566245611896816153080977474813178182638762071081648385475

noncomputable def p5283 :=
nat_lit 52656145834278593348959013841835216159447547700274555627155488768

noncomputable def p5284 :=
nat_lit 543713913768489998157362644447773290845409936943530051053912212397670322095365247091

noncomputable def p5285 :=
nat_lit 210718136869059718024272716233167512747576629300245299200000000000000000000000000000000000000

noncomputable def p5286 :=
nat_lit 247547611684565988404319289133626312599768917605051008825394214642085978007779027143111875

noncomputable def p5287 :=
nat_lit
  2512311066704951319850875378277827663631850216956200258810007385716193007259981686519880052307905714216890210710790583249989

noncomputable def p5288 :=
nat_lit
  9269969581912713510594845646439246434612180652494084044442527898347552490607178905042105187113683454219390335144475328583003598694647735212829303006822400

noncomputable def p5289 :=
@p5281 p5282 p5283 p5284 p5285
  p5286 p5269 p5287 p5271
  p5288 p5273 p5269

noncomputable def p5290 :=
@Enclosure.Real.IsNear.subLit_ft p5263
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5291 :=
nat_lit 50607227375336552865567953680935826261035880350216164350866484675

noncomputable def p5292 :=
nat_lit 519935257522586026247224823795475711856462095586151373028498789178162966286095741273

noncomputable def p5293 :=
nat_lit 632154410607179154072818148699502538242729887900735897600000000000000000000000000000000000000

noncomputable def p5294 :=
nat_lit 477670713644391233875142325

noncomputable def p5295 :=
nat_lit 38685626227668133590597632

noncomputable def p5296 :=
nat_lit 107005292075735280987540359048196119

noncomputable def p5297 :=
nat_lit 27110071041083878821918990295402234037886018899668444092552716118878251425794783293158195200

noncomputable def p5298 :=
@p5290 p5291 p5283 p5292 p5293
  p5294 p5295 p5296 p3486
  p5297 p5282 p5283

noncomputable def p5299 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5079
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5300 :=
@Enclosure.Real.IsNear.mulLit_ft p5079
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5002 (Enclosure.sfrac false 1 16))))
  p5166

noncomputable def p5301 :=
@p5300 p2767 p5167 p5168 102158786707
  549755813888 3965195057 28346784153600000000 p5291
  p5283 p5292 p5293

noncomputable def p5302 :=
p5301 (p5182 (Eq.refl true))
  (@p5038 408635146828 2199023255552 259863023255552
    p3422 102158786707 549755813888 3965195057
    28346784153600000000 (p5233 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5303 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5002 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p5304 :=
@p5303 70368744177664 1 250000000000000 540180559815
  549755813888 3965195057 28346784153600000000 p5294
  p5295 p5296 p3486

noncomputable def p5305 :=
p5304 d146
  (@p5184 2160722239260 2199023255552 259863023255552
    p3422 540180559815 549755813888 3965195057
    28346784153600000000 (p5211 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5306 :=
@p5289 p5275 p5271
  (@p5298 p5284 p5285
    (@p5299 true p5291 p5283 p5292
      p5293 (p5302 (Eq.refl true)))
    (p5305 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p5307 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) p5084)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  p5244

noncomputable def p5308 :=
nat_lit 561166156974140231189579604563356431869913419491758498427988375

noncomputable def p5309 :=
nat_lit 822752278660603021077484591278675252491367932816789931674304512

noncomputable def p5310 :=
nat_lit 28766554442853027962962605951095115906806811860675798551895848154503857846755473

noncomputable def p5311 :=
nat_lit 4172219110007382416880599781416716752402017260144856924160000000000000000000000000000000

noncomputable def p5312 :=
@p5307 p5295 p5237 p3486 p5308
  p5309 p5310 p5311 p5286
  p5269 p5287 p5271

noncomputable def p5313 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p5084
  2 1 0 1 p5244 p3406

noncomputable def p5314 :=
@Neg.neg Real Real.instNeg
  (p5078
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5315 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  (p5001
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5314
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5084
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
            (Enclosure.sfrac false 12 1))))))

noncomputable def p5316 :=
@p5005
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5314
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5084
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))
  10465871295845

noncomputable def p5317 :=
nat_lit 53618675513134374960893407176320669898503892640075

noncomputable def p5318 :=
nat_lit 187072209578355573530071658587684226515959365500928

noncomputable def p5319 :=
nat_lit 5419739298115742627591762897856457485649993211972782323444929594011

noncomputable def p5320 :=
nat_lit 1897305587593738171963468531165161381250990080000000000000000000000000000000

noncomputable def p5321 :=
@p5316 4398046511104 1491 4398046511104 p5317
  p5318 p5319 p5320 p5308
  p5309 p5310 p5311

noncomputable def p5322 :=
nat_lit 380195839043538286837595717144330860575

noncomputable def p5323 :=
@Enclosure.Real.IsNear.subLit_ff_n p5314
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5084
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))
  p5322 p3426

noncomputable def p5324 :=
nat_lit 14498364634965740764621110962599540848219860011

noncomputable def p5325 :=
nat_lit 33465975846025256199512964621926400000000000000000000000

noncomputable def p5326 :=
nat_lit 471648421373557251656276669487889964739633045971275

noncomputable def p5327 :=
nat_lit 4597775272340619610020868386371169672092083950915532080065729594011

noncomputable def p5328 :=
nat_lit 9122744907387564913815603186810320101101043605954617392747792360795374175492012349849600

noncomputable def p5329 :=
@p5323 p5324 p5325 p5326 p5318
  p5327 p5320 p5328 p5317
  p5318 p5319 p5320

noncomputable def p5330 :=
@Enclosure.Real.IsNear.neg
  (p5078
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5002 (Enclosure.sfrac false 1 16)))))

noncomputable def p5331 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5332 :=
@p5331
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5002 (Enclosure.sfrac false 1 16))))
  p5169

noncomputable def p5333 :=
@p5332 p976 p5170 p5171 540180559815
  549755813888 3965195057 28346784153600000000 p5322
  p3426 p5324 p5325

noncomputable def p5334 :=
p5333
  (p5177 d144
    (p5179 (p5181 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p5184 2160722239260 2199023255552 259863023255552
    p3422 540180559815 549755813888 3965195057
    28346784153600000000 (p5211 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5335 :=
@Enclosure.Real.IsNear.mulLit_ff p5084
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  p5244 p3406 p5237

noncomputable def p5336 :=
nat_lit 31167618786939658410393600000000

noncomputable def p5337 :=
@p5005
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5002 (Enclosure.sfrac false 1 16))))
  10465871295845

noncomputable def p5338 :=
@p5337 4398046511104 1491 4398046511104 102158786707
  549755813888 3965195057 28346784153600000000 1069180713415143050332415
  p2602 12338289183202049632663 p5336

noncomputable def p5339 :=
p5338
  (p5095
    (@Enclosure.Real.IsNear.neg p5009 false 10465871295845 4398046511104
      1491 4398046511104 (p5122 (Eq.refl true))))
  (@p5038 408635146828 2199023255552 259863023255552
    p3422 102158786707 549755813888 3965195057
    28346784153600000000 (p5233 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5340 :=
@p5335 p2908 1069180713415143050332415 p2602
  12338289183202049632663 p5336 p5326 p5318
  p5327 p5320
  (@p5246 true p5244 p3406 p5237
    p2908 (p5262 (Eq.refl true)))
  (@p5003 false 1069180713415143050332415 p2602
    12338289183202049632663 p5336
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (p5004 (Eq.refl true) (Eq.refl true)
        (p4782 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5339 (Eq.refl true)))

noncomputable def p5341 :=
p5321
  (p5095
    (@Enclosure.Real.IsNear.neg p5009 false 10465871295845 4398046511104
      1491 4398046511104 (p5122 (Eq.refl true))))
  (p5329
    (@p5330 true p5322 p3426 p5324
      p5325 (p5334 (Eq.refl true)))
    (p5340 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p5342 :=
p5312
  (@p5313 p5237 p2908 p5244
    p5295 p5237 p3486
    (Enclosure.Real.IsNear.const false 2 1)
    (@p5246 true p5244 p3406 p5237
      p2908 (p5262 (Eq.refl true)))
    (Eq.refl true))
  (@p5315 false p5308 p5309 p5310
    p5311
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (p5004 (Eq.refl true) (Eq.refl true)
        (p4782 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5341 (Eq.refl true)))

noncomputable def p5343 :=
nat_lit 90324089528890144696543944817493038797975

noncomputable def p5344 :=
nat_lit 1235438693748667967856720554367150585564588869552632929889073

noncomputable def p5345 :=
@Enclosure.Real.IsNear.mulLit_ff p5086
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  p5343 p3453 p5344

noncomputable def p5346 :=
nat_lit 522905872594144628117390072217600000000000000000000000000000000000000

noncomputable def p5347 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c16)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5348 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    c16)
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p5349 :=
@p5348 p1070 p1071 p1072 115511244639
  274877906944 1696445057 28346784153600000000 p5343
  p3453 p5344 p5346

noncomputable def p5350 :=
p5349 d148
  (@p5013 1848179914224 4398046511104 111178223255552
    p3422 115511244639 274877906944 1696445057
    28346784153600000000
    (p5107 (p5119 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5351 :=
@p5345 p5346 1069180713415143050332415 p2602
  12338289183202049632663 p5336 p5276 p5277
  p5278 p3520
  (@p5347 true p5343 p3453 p5344
    p5346 (p5350 (Eq.refl true)))
  (@p5003 false 1069180713415143050332415 p2602
    12338289183202049632663 p5336
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (p5004 (Eq.refl true) (Eq.refl true)
        (p4782 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5339 (Eq.refl true)))

noncomputable def p5352 :=
p5272
  (p5095
    (@Enclosure.Real.IsNear.neg p5009 false 10465871295845 4398046511104
      1491 4398046511104 (p5122 (Eq.refl true))))
  (p5280
    (p5306 (p5342 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p5351 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p5353 :=
p5243
  (@p5245 p5237 p2908 p5235
    p3406 p5237 p5238
    (Enclosure.Real.IsNear.const false 3 1)
    (@p5246 true p5244 p3406 p5237
      p2908 (p5262 (Eq.refl true)))
    (Eq.refl true))
  (@p5266 false p5239 p5240 p5241
    p5242
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (p5004 (Eq.refl true) (Eq.refl true)
        (p4782 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5352 (Eq.refl true)))

noncomputable def p5354 :=
@p5149 p5134 p3327
  (@p5159 p5144 p5145
    (p5212 (Eq.refl true)) (p5234 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p5353 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p5355 :=
nat_lit 270972268586670434089631834452479116393925

noncomputable def p5356 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p5086)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  p5355

noncomputable def p5357 :=
nat_lit 174301957531381542705796690739200000000000000000000000000000000000000

noncomputable def p5358 :=
@p5356 p3453 p5344 p5357 p5308
  p5309 p5310 p5311 p5135
  p5136 p5137 p5138

noncomputable def p5359 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p5086
  3 1 0 1 p5343 p3453

noncomputable def p5360 :=
p5358
  (@p5359 p5344 p5346 p5355
    p3453 p5344 p5357
    (Enclosure.Real.IsNear.const false 3 1)
    (@p5347 true p5343 p3453 p5344
      p5346 (p5350 (Eq.refl true)))
    (Eq.refl true))
  (@p5315 false p5308 p5309 p5310
    p5311
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (p5004 (Eq.refl true) (Eq.refl true)
        (p4782 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5341 (Eq.refl true)))

noncomputable def p5361 :=
nat_lit 344942413913074574182772081167882929788980165487770692125

noncomputable def p5362 :=
nat_lit 1532495540865888858358347027150309183618739122183602176

noncomputable def p5363 :=
nat_lit 33339975445616842349230547769900963147805616423540139989324133169519936151604181997591

noncomputable def p5364 :=
@Enclosure.Real.IsNear.mulLit_tf p5088
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
      (Enclosure.sfrac false 12 1)))
  p5361 p5362 p5363

noncomputable def p5365 :=
nat_lit 2245863621678193858858272409049670195609600000000000000000000000000000000000000000000000000000

noncomputable def p5366 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c16 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))))

noncomputable def p5367 :=
@p5366 p1059 p1061 p1062 p1063
  498858761927 549755813888 1696445057 28346784153600000000
  p5361 p5362 p5363

noncomputable def p5368 :=
@p5367 p5365 d149
  (@p5249 3990870095416 4398046511104 111178223255552
    p3422 498858761927 549755813888 1696445057
    28346784153600000000
    (p5251 (p5261 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5369 :=
@p5364 p5365 1069180713415143050332415 p2602
  12338289183202049632663 p5336 p5126 p5127
  p5128 p5129 (p5368 (Eq.refl true))
  (@p5003 false 1069180713415143050332415 p2602
    12338289183202049632663 p5336
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (p5004 (Eq.refl true) (Eq.refl true)
        (p4782 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5339 (Eq.refl true)))

noncomputable def p5370 :=
p5094
  (p5095
    (@Enclosure.Real.IsNear.neg p5009 false 10465871295845 4398046511104
      1491 4398046511104 (p5122 (Eq.refl true))))
  (p5131
    (@p5140 p5125 p3327 p5354
      (p5360 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p5369 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p5371 :=
@p5077 p5069
  (@p5089 false p5073 p5074 p5075
    p5076
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1))
      (p5004 (Eq.refl true) (Eq.refl true)
        (p4782 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5370 (Eq.refl true)))

noncomputable def p5372 :=
@p5067 p5068 p5069 1354775085 17179869184
  1 17179869184 p4997 p4973 p4998
  p4975
  (@p5071 p5066 p5068 p5069
    (BSN.correctionLinear_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p4779
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p5070 false p5065 p5066
      p5068 p5069
      (p5371 d150 (Eq.refl true))))

noncomputable def p5373 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p4779) false
  1354775085 17179869184 1 17179869184 1354775085
  17179869184

noncomputable def p5374 :=
@Enclosure.Real.IsNear.inv_image p4779 217857494095 17179869184 41
  17179869184 677387542 677387543 8589934592
  (p4991 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p5375 :=
p5064
  (p5372
    (@p5373 1 17179869184
      (p5374 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p5376 :=
@p4976 p4774
  (@p4978 17179869184
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p4994 (Eq.refl true))
  (p5375 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p5377 :=
@p4781 p4771 p4773 p4774
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    12
    (p4782 (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (p4970 p5376 (Eq.refl true) (Eq.refl true))

theorem d162 : p4772 p4773 p4774 :=
@p4775 p4771 p4773 p4774
  (@Eq.refl Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific Real c2 101038100
        true 5)))
  p5377

noncomputable def p5378 :=
nat_lit
  1456135677440358278010747394496759467691707455303373494154571491359759290740818141721974566508405887599649481802484527843517225732836755207106349450285149166018151358288164767

noncomputable def p5379 :=
Enclosure.Real.IsNear
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  true p5378 p2994

noncomputable def p5380 :=
nat_lit
  15312256043745402007258940457655565638554780168975212901321868368315837004774612485307802394003447198395650121376934799279211437277184635120673749678999280544345683930292326968452526415975343107612110189403358647660636829370229

noncomputable def p5381 :=
nat_lit
  4792571189020741311886311035125287918760385619611651158282486892029549491316084015804595742174356276484613194231160699964594985308830803969378297243605401600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5382 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  true p5378

noncomputable def p5383 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    12)

noncomputable def p5384 :=
@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    c7)

noncomputable def p5385 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  c22
  (p5384
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p5386 :=
Real.sqrt
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    c7)

noncomputable def p5387 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5385
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p5386)))

noncomputable def p5388 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  (p5383 p5387) true p5378

noncomputable def p5389 :=
@BSN.floor_sqrt_eq_dec
  (@OfScientific.ofScientific Real c2 101161500
    true 5)
  101161500 100000 12
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))

noncomputable def p5390 :=
@Enclosure.Real.IsNear.subLit_tf
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    12)

noncomputable def p5391 :=
nat_lit
  62059155832315394013623571393503162467187875713247877986857150249578358492111151472871406881732537754106720544106010150516586139958251378970287714900480677412062585173112735

noncomputable def p5392 :=
nat_lit
  155634249349923694629719009058279166917023757271017248523671415757104670784993689518295134686612715513659690286766065180579106675320371614342891387799280544345683930292326968452526415975343107612110189403358647660636829370229

noncomputable def p5393 :=
nat_lit
  12508110226290287589158071991761584583428504261854741831734263448568225448327939061958747775394760392668692930810036357267815780270366993842558955365844587085059269252451292436248920064

noncomputable def p5394 :=
@p5390 p5387 24208560827 8589934592 217327
  68719476736 p5391 p2994 p5392 p5381
  p5393 p5378

noncomputable def p5395 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.mainSumOfPhase
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    12)

noncomputable def p5396 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    12)

noncomputable def p5397 :=
p5396
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    12)

noncomputable def p5398 :=
@p5395 p5397 true 24208560827 8589934592 217327
  68719476736
  (BSN.main_sum_of_phase_eq
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    12)

noncomputable def p5399 :=
@Enclosure.Real.IsNear.addLit_tt
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    12)

noncomputable def p5400 :=
@p5399
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    12)

noncomputable def p5401 :=
@p5400 193668486616 137438953472 217327 137438953472
  193668486616 137438953472 217327 137438953472
  53235188242018157461504 24208560827 8589934592

noncomputable def p5402 :=
BSN.mainSumRS_step
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  (@OfScientific.ofScientific Real c2 101161500
    true 5)
  Real.cos BSN.quadSignNeg

noncomputable def p5403 :=
p5402 11 12 101161500 100000 286
  137438953472 68719476736 2305843009213693952 false 283677208169223
  3352

noncomputable def p5404 :=
p5403 341522969406 43 39675208392 8 true
  158807471560 203792 true 68409990534 7244019458077122842 1

noncomputable def p5405 :=
p5404 false 120762098559 true true 193668486616 217327
  BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 120762098559 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p5406 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  (@OfScientific.ofScientific Real c2 101161500
    true 5)
  Real.cos Real.cos

noncomputable def p5407 :=
p5406 BSN.quadSignPos BSN.quadSignNeg 9 10 11 101161500
  100000 168 230 137438953472 68719476736

noncomputable def p5408 :=
p5407 2305843009213693952 false 283677208169223 3352
  316464885454 43 43462013224 8 329564216814 43
  41439403656

noncomputable def p5409 :=
p5408 8 true 128172375068 174831 true 194131579570
  true 60518270430 7244019458077122842 1 false

noncomputable def p5410 :=
p5409 21666266031 false false 124328892008 true true
  158807471560 203792 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 168 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 21666266031 137438953472)

noncomputable def p5411 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  (@OfScientific.ofScientific Real c2 101161500
    true 5)
  Real.sin Real.sin

noncomputable def p5412 :=
p5411 BSN.quadSignNeg BSN.quadSignNeg 7 8 9 101161500
  100000 25 101 137438953472 68719476736

noncomputable def p5413 :=
p5412 2305843009213693952 false 283677208169223 3352
  285796269294 43 48592008000 16 301984246446 43
  45812984488

noncomputable def p5414 :=
p5413 8 true 110489851247 142622 true 41369710818
  true 9836368739 7244019458077122842 1 false

noncomputable def p5415 :=
p5414 40747827535 true false 9827973709 true true
  128172375068 174831 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 25 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 40747827535 137438953472)

noncomputable def p5416 :=
p5406 BSN.quadSignPos BSN.quadSignPos 5 6 7 101161500
  100000 160 60 137438953472 68719476736

noncomputable def p5417 :=
p5416 2305843009213693952 false 283677208169223 3352
  246257546308 43 56109217800 8 267443854420 43
  51947041624

noncomputable def p5418 :=
p5417 8 true 181864833153 105767 false 17203937279
  false 173677183793 7244019458077122842 1 false

noncomputable def p5419 :=
p5418 136363606246 false false 41550923152 false true
  110489851247 142622 BSN.abs_quadSignPos
  (BSN.cos_quad_nat0 160 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 136363606246 137438953472)

noncomputable def p5420 :=
p5411 BSN.quadSignNeg BSN.quadSignNeg 3 4 5 101161500
  100000 421 277 137438953472 68719476736

noncomputable def p5421 :=
p5420 2305843009213693952 false 283677208169223 3352
  190530846192 42 68719476728 8 221199462352 42
  61464568544

noncomputable def p5422 :=
p5421 16 true 116842512736 62319 false 44244221042
  false 107370955562 7244019458077122842 1 false

noncomputable def p5423 :=
p5422 43483985594 true false 96777754652 true true
  181864833153 105767 BSN.abs_quadSignNeg
  (BSN.cos_quad_nat1 421 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 43483985594 137438953472)

noncomputable def p5424 :=
BSN.mainSumRS_step2
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  (@OfScientific.ofScientific Real c2 101161500
    true 5)
  Real.sin Real.cos

noncomputable def p5425 :=
p5424 BSN.quadSignPos BSN.quadSignNeg 1 2 3 101161500
  100000 867 606 137438953472 68719476736

noncomputable def p5426 :=
p5425 2305843009213693952 false 283677208169223 3352
  95265423088 42 97184016000 16 150992123216 42
  79350416784

noncomputable def p5427 :=
p5426 16 true 137438322288 3402 false 129858154926
  false 102817859023 7244019458077122842 1 false

noncomputable def p5428 :=
p5427 111381164079 false false 100740520908 true true
  116842512736 62319 BSN.abs_quadSignPos
  (BSN.cos_quad_nat3 867 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 111381164079 137438953472)

noncomputable def p5429 :=
@Enclosure.Real.IsNear.recentre'
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    1)

noncomputable def p5430 :=
@Enclosure.Real.IsNear.of_eq
  (BSN.mainSumRS
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    1)

noncomputable def p5431 :=
@p5430
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5)))
  true 8589895143

noncomputable def p5432 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5)))
  true 17179790286

noncomputable def p5433 :=
@Enclosure.Real.IsNear.cos_image
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 1108114094411)
    (@Nat.cast Real Real.instNatCast 536870912))
  false 1108114094411

noncomputable def p5434 :=
nat_lit 20403102517564421757993976601016685170809587152474613

noncomputable def p5435 :=
nat_lit 9885112292571585599545230035144312241606002475008

noncomputable def p5436 :=
@Enclosure.Real.IsNear.recentre'
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  false p5434 p5435

noncomputable def p5437 :=
nat_lit 13841203200000000000000000

noncomputable def p5438 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101161500 400000)
      (Real.log (Enclosure.sfrac false 40934606329000000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 202323000))))))

noncomputable def p5439 :=
nat_lit 508531439381754579721007764500000000000000000000

noncomputable def p5440 :=
nat_lit 3086628544186352185310191428718005000000000000000000

noncomputable def p5441 :=
@Enclosure.Real.IsNear.of_eq
  (riemannSiegelThetaApproximant 2 0
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (p5438 (Enclosure.sfrac false 101161500 200000))
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 101161500 200000) (Real.log Real.pi)))
    (Enclosure.sfrac true p5439 p5440))
  false

noncomputable def p5442 :=
BSN.riemannSiegelThetaApproximant_two_zero_mk
  (@OfScientific.ofScientific Real c2 101161500
    true 5)
  101161500 100000 40934606329000000 160000000000

noncomputable def p5443 :=
p5442 202323000 400000 200000 p5439
  p5440
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5444 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (p5438 (Enclosure.sfrac false 101161500 200000))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101161500 200000) (Real.log Real.pi)))
  (Enclosure.sfrac true p5439 p5440) 297457135976667499117
  144115188075855872

noncomputable def p5445 :=
nat_lit 918139613290398979109728947045750832686431421861357585000000000000000000

noncomputable def p5446 :=
@p5444 337457950023929239 p5437 p5439
  p5440 0 1 p5445 p5434
  p5435 337457950023929239 p5437

noncomputable def p5447 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (p5438 (Enclosure.sfrac false 101161500 200000))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101161500 200000) (Real.log Real.pi))
  9522542446376258520229 3602879701896396800 255017256503 26400000000000000000

noncomputable def p5448 :=
nat_lit 204410987357057908443779820421120000

noncomputable def p5449 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 101161500 400000)
      (Real.log (Enclosure.sfrac false 40934606329000000 160000000000)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 4)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 1 2) Real.pi)
        (Real.arctan
          (@HDiv.hDiv Real Real Real c4
            (@Nat.cast Real Real.instNatCast 100000)
            (@Nat.cast Real Real.instNatCast 202323000))))))

noncomputable def p5450 :=
@p5449 (Enclosure.sfrac false 101161500 200000)
  2268981204238644048929 720575940379279360 255017256503 26400000000000000000
  101161500 200000 0

noncomputable def p5451 :=
nat_lit 380901697855050340809160000

noncomputable def p5452 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101161500 400000)
    (Real.log (Enclosure.sfrac false 40934606329000000 160000000000)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 4)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 1 2) Real.pi)
      (Real.arctan
        (@HDiv.hDiv Real Real Real c4
          (@Nat.cast Real Real.instNatCast 100000)
          (@Nat.cast Real Real.instNatCast 202323000)))))
  2269264084710928383969

noncomputable def p5453 :=
nat_lit 5109291452959908308994007407517499392

noncomputable def p5454 :=
@p5452 720575940379279360 7667189491 800000000000000000
  884001475888547 2251799813685248 20000033 264000000000000000
  p5453 2268981204238644048929 720575940379279360 255017256503

noncomputable def p5455 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101161500 400000)
  (Real.log (Enclosure.sfrac false 40934606329000000 160000000000)) 101161500
  400000 0 1 56080230243495015 4503599627370496

noncomputable def p5456 :=
nat_lit 30830432620539034388995768320

noncomputable def p5457 :=
@Enclosure.Real.IsNear.recentre'
  (Real.log
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 40934606329000000)
      (@Nat.cast Real Real.instNatCast 160000000000)))
  false p5456 p2333

noncomputable def p5458 :=
BSN.log_rat_reduce_isNear 40934606329000000 160000000000 17 81869212658000000
  41943040000000000 45960307527 68719476736 24973259072661432
  36028797018963968 26400000000 1000000000000000

noncomputable def p5459 :=
nat_lit
  828225522967555179738316268165200685009373753935054860707855208101749533516038451533491852638866885437810601026195046211471985303271151779209025983478644593855311699766358438657935582944282961565249575678210917569412545867731381506718301823237657225000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5460 :=
nat_lit
  30644887754761931951210397751796850892159049957161478526623533340793884635312098269994449324540271415951971935253186023220835770358245297689527681205390362908148976678747311360073940460514725763268148531256382490768335919483880283415987435786279335000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5461 :=
nat_lit
  553719717651345578122504946889731582362736902726066408935174780073858326560588034483576477720137795488250794170601389815072726065338353391072883613371428986384386743469881713907138302658414363438114742844342010469763397013069929795028575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5462 :=
BSN.log_dyadic_bound 19963086329000000 61906126329000000 12 11
  p5459 68719476736 26400000000 p5460 p5461
  45960307527 81869212658000000

noncomputable def p5463 :=
p5462 41943040000000000 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p5464 :=
@BSN.binarySplit_of_base11 (BSN.artanhP 19963086329000000) (BSN.artanhQ 61906126329000000)
  0 11 p5460 p5459 p5461
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5465 :=
p5458 (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)
  (p5463 (p5464 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  BSN.log2_near_15 (Eq.refl true)

noncomputable def p5466 :=
@p5455 1250561 33000000000000000 2269264084710928383969
  720575940379279360 7667189491 800000000000000000
  (Enclosure.Real.IsNear.const false 101161500 400000)
  (BSN.isNear_log_sfrac 40934606329000000 160000000000 56080230243495015
    4503599627370496 1250561 33000000000000000 false
    (@p5457 1000448800000000 p2422 56080230243495015
      4503599627370496 1250561 33000000000000000
      (p5465 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true)))
  (Eq.refl true)

noncomputable def p5467 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 4)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 1 2) Real.pi)
    (Real.arctan
      (@HDiv.hDiv Real Real Real c4
        (@Nat.cast Real Real.instNatCast 100000)
        (@Nat.cast Real Real.instNatCast 202323000))))
  1 4

noncomputable def p5468 :=
@p5467 0 1 884001475888547 562949953421312 20000033
  66000000000000000 884001475888547 2251799813685248 20000033
  264000000000000000 (Enclosure.Real.IsNear.const false 1 4)

noncomputable def p5469 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 2) Real.pi)
  (Real.arctan
    (@HDiv.hDiv Real Real Real c4
      (@Nat.cast Real Real.instNatCast 100000) (@Nat.cast Real Real.instNatCast 202323000)))
  884279719003555 562949953421312 1

noncomputable def p5470 :=
nat_lit 7593514857114083811917824

noncomputable def p5471 :=
@p5469 2000000000000000 4245653 8589934592 1
  3300000000 p5470 884001475888547 562949953421312 20000033
  66000000000000000
  (@p803 1 1000000000000000 884279719003555 562949953421312
    1 2000000000000000 (Enclosure.Real.IsNear.const false 1 2)
    BSN.pi_near_15 (Eq.refl true))

noncomputable def p5472 :=
BSN.arctan_dyadic_bound_f 100000 202323000 1 0 8589934592
  3300000000 0 1 1 0 1

noncomputable def p5473 :=
p5472 1 4245653 (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)
  (@BSN.binarySplit_of_le (BSN.arctanEvenP 100000) (BSN.arctanEvenQ 202323000) 0
    0 (Eq.refl true))
  (@BSN.binarySplit_of_le (BSN.arctanOddP 100000) (BSN.arctanOddQ 202323000) 0 0
    (Eq.refl true))

noncomputable def p5474 :=
p5468
  (p5471
    (p5473 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5475 :=
@p5447 15915787101437157 27487790694400 202323 13743895347200
  p5448 297457135976667499117 144115188075855872 337457950023929239
  p5437
  (@p5450 1 p5451 9522542446376258520229
    3602879701896396800 255017256503 26400000000000000000
    (@p5454 26400000000000000000 p5466 p5474
      (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 101161500 200000) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5476 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101161500 200000) (Real.log Real.pi)
  101161500 200000 0 1 78665238759 68719476736

noncomputable def p5477 :=
p5475
  (@p5476 1 34359738368 15915787101437157 27487790694400
    202323 13743895347200
    (Enclosure.Real.IsNear.const false 101161500 200000) d91
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p5478 :=
@p5433 536870912 105 4294967296 true 17179790286
  17179869184 1 3300000000
  (@p5436 337457950023929239 p5437 1108114094411
    536870912 105 4294967296
    (@p5441 p5434 p5435 337457950023929239
      p5437
      (p5443 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p5446 (p5477 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p5439 p5440)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p5479 :=
nat_lit 121299993243579585147174912

noncomputable def p5480 :=
BSN.cos_reduce1
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 1108114094411)
    (@Nat.cast Real Real.instNatCast 536870912))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p5479)
    (@Nat.cast Real Real.instNatCast p3406))
  226375608064910080 72057594037927936 false

noncomputable def p5481 :=
BSN.sin_reduce_arg_pos_rat_q1 1108114094411 536870912 226375608064910080
  72057594037927936 328 p5479 p3406
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true)

noncomputable def p5482 :=
nat_lit
  1130546374673286162996396792333869391077186970931211897914549855421200945702267683117556018561486987475747169119181968630643946949338309563722420225853882704081300712665281

noncomputable def p5483 :=
nat_lit
  793544806075064486961986893256758746959103824135200675588901710246826865868569080768629419427832425076406622660369289853494103963069866229179926807450678511915839681

noncomputable def p5484 :=
nat_lit
  5645761626034742546737264117587942728383404064653009298897913017578057954662482985339843925067959022744008388578810346855541419871361831150180416630128311403397921399451841

noncomputable def p5485 :=
BSN.sin_dyadic_bound_f 55160850590063 35184372088832 4 3 17179869184
  6606445313 p5482 p3100 p5483 p5484
  p3103

noncomputable def p5486 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 55160850590063) (BSN.sinEvenQ 35184372088832) 0
  3 p5482 p3100 p5483 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5487 :=
p5485 p5483 17179790286 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5486 (Eq.refl true))

noncomputable def p5488 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 55160850590063) (BSN.sinOddQ 35184372088832) 0
  3 p5484 p3103 p5483 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5489 :=
@BSN.sin_arg_round false 17179790286 17179869184 p5479
  p3406 55160850590063 35184372088832 6606445313 6600000000
  (p5487 (p5488 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5490 :=
p5480 17179790286 17179869184 328 1000000000000000
  6600000000 3300000000 p5481 BSN.pi_near_15 p5489
  (Eq.refl true) (Eq.refl true)

noncomputable def p5491 :=
@p5431 8589934592 1370292841 55364812800000000
  (BSN.main_sum_rs_one
    (riemannSiegelThetaApproximant 2 0
      (@OfScientific.ofScientific Real c2 101161500
        true 5))
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  (@p5432 17179869184 350794967296 14173392076800000000
    8589895143 8589934592 1370292841 55364812800000000
    (p5478 (Enclosure.sfrac_false_div 1108114094411 536870912)
      (p5490 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5492 :=
@p5429 true 8589895143 8589934592 1370292841
  55364812800000000 137438322288 137438953472 3402 137438953472
  p5491 (Eq.refl true)

noncomputable def p5493 :=
p5428 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 606 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 100740520908 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true) p5492
  (@p5436 337457950023929239 p5437 283677208169223
    137438953472 3352 137438953472
    (@p5441 p5434 p5435 337457950023929239
      p5437
      (p5443 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p5446 (p5477 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p5439 p5440)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p5494 :=
nat_lit
  1879183304633634701493130033724580209372705780098616945300169602869050031379985503023445165311311063605387222020549929907083904256550700978176

noncomputable def p5495 :=
nat_lit
  22994858184923775090590703974967658547826696534361021531887060284491356065848412873040508696428780878831391764260512414766057247870976

noncomputable def p5496 :=
nat_lit
  9394386060294542203366414201445670877735713237152331142055535927324249348944703778777113721664874955684665898773976271275370109108396883316736

noncomputable def p5497 :=
BSN.sin_dyadic_bound_f 129858154926 137438953472 4 3 137438953472
  68719476736 p5494 p2504 p5495 p5496
  p2507

noncomputable def p5498 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 129858154926) (BSN.sinEvenQ 137438953472) 0
  3 p5494 p2504 p5495 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5499 :=
p5497 p5495 111381164079 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5498 (Eq.refl true))

noncomputable def p5500 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 129858154926) (BSN.sinOddQ 137438953472) 0
  3 p5496 p2507 p5495 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5501 :=
nat_lit
  284026999627121184580445569519068291770854478234664625895654974204648646389146292863301573340514249928903999733190930963486703313583391886401

noncomputable def p5502 :=
nat_lit
  1395798334236004465414923818054226442472436863021450152293339762194703166815810351164297122201335255567136330497538742358826253536321

noncomputable def p5503 :=
nat_lit
  1722883001095746719189405638904411793211321538327338744104197344684770733727403478384934433556119363432255425855937193143337235231737582177345

noncomputable def p5504 :=
BSN.cos_dyadic_bound_f 102817859023 137438953472 4 3 137438953472
  68719476736 p5501 p2457 p5502 p5503
  p2460

noncomputable def p5505 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 102817859023) (BSN.cosEvenQ 137438953472) 0
  3 p5501 p2457 p5502 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5506 :=
p5504 p5502 100740520908 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5505 (Eq.refl true))

noncomputable def p5507 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 102817859023) (BSN.cosOddQ 137438953472) 0
  3 p5503 p2460 p5502 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5508 :=
p5493 d93 d95 d97 d99 d103
  (p5499 (p5500 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p5506 (p5507 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5509 :=
p5423 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 277 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 96777754652 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p5508 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p5436 337457950023929239 p5437 283677208169223
    137438953472 3352 137438953472
    (@p5441 p5434 p5435 337457950023929239
      p5437
      (p5443 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p5446 (p5477 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p5439 p5440)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p5510 :=
nat_lit 4134746621055237989127634060614748662445897483431236719933496044826159510933401664874922240

noncomputable def p5511 :=
nat_lit 14684272221445130046972032759846494917270980520892699395317626543660748032111642460416

noncomputable def p5512 :=
nat_lit 10829074518703931441314203632604635316842722589303824249741087698387442315995428560584622336

noncomputable def p5513 :=
BSN.sin_dyadic_bound_f 44244221042 137438953472 3 2 137438953472
  68719476736 p5510 p2477 p5511 p5512
  p2480

noncomputable def p5514 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 44244221042) (BSN.sinEvenQ 137438953472) 0
  2 p5510 p2477 p5511 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5515 :=
p5513 p5511 43483985594 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5514 (Eq.refl true))

noncomputable def p5516 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 44244221042) (BSN.sinOddQ 137438953472) 0
  2 p5512 p2480 p5511 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5517 :=
nat_lit
  878169909986984691285920669414084642580683796392246455749419383667934551285001241162641328261918184657864357763435315480776648808528267513856

noncomputable def p5518 :=
nat_lit
  2347695774299282660705277958961780543446263495357256060398246804879122508596277934711879839317093926318015736207150700492841155629056

noncomputable def p5519 :=
nat_lit
  4390515239741611299413338526006834874417536193259152957447798182456596765573000101897594174606715267348565644826798881628231184121550952534016

noncomputable def p5520 :=
BSN.sin_dyadic_bound_f 107370955562 137438953472 4 3 137438953472
  68719476736 p5517 p2504 p5518 p5519
  p2507

noncomputable def p5521 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 107370955562) (BSN.sinEvenQ 137438953472) 0
  3 p5517 p2504 p5518 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5522 :=
p5520 p5518 96777754652 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5521 (Eq.refl true))

noncomputable def p5523 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 107370955562) (BSN.sinOddQ 137438953472) 0
  3 p5519 p2507 p5518 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5524 :=
p5509 d105 d107 d109 d111 d103
  (p5515 (p5516 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p5522 (p5523 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5525 :=
p5419 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 (Eq.refl true))
  (BSN.sfrac_eq_quadSignPos_mul false 41550923152 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p5524 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p5436 337457950023929239 p5437 283677208169223
    137438953472 3352 137438953472
    (@p5441 p5434 p5435 337457950023929239
      p5437
      (p5443 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p5446 (p5477 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p5439 p5440)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p5526 :=
nat_lit 87601471678976110813313058379448212193281

noncomputable def p5527 :=
BSN.cos_dyadic_bound_f 17203937279 137438953472 2 1 137438953472
  68719476736 p5526 p2486 p5526 p5526
  p2487

noncomputable def p5528 :=
@BSN.binarySplit_of_base (BSN.cosEvenP 17203937279) (BSN.cosEvenQ 137438953472) 0
  1 p5526 p2486 p5526 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5529 :=
p5527 p5526 136363606246 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5528 (Eq.refl true))

noncomputable def p5530 :=
@BSN.binarySplit_of_base (BSN.cosOddP 17203937279) (BSN.cosOddQ 137438953472) 0
  1 p5526 p2487 p5526 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5531 :=
nat_lit
  2315444298869105096659392471533686453341393508549698620433664516512235441649668441096487209204943438757720417857159098687888638321620851030081

noncomputable def p5532 :=
nat_lit
  753205044652150458931576978967851173768131291799851551268848000069192411301222123218299699295399332409513014938088992931629666383886401

noncomputable def p5533 :=
nat_lit
  14032832498306593208592769097996018034135657642774893930805528128688970381753956743055441892069294155781689867062418068514796471969164439255105

noncomputable def p5534 :=
BSN.cos_dyadic_bound_f 173677183793 137438953472 4 3 137438953472
  68719476736 p5531 p2457 p5532 p5533
  p2460

noncomputable def p5535 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 173677183793) (BSN.cosEvenQ 137438953472) 0
  3 p5531 p2457 p5532 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5536 :=
p5534 p5532 41550923152 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5535 (Eq.refl true))

noncomputable def p5537 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 173677183793) (BSN.cosOddQ 137438953472) 0
  3 p5533 p2460 p5532 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5538 :=
p5525 d113 d115 d117 d119 d103
  (p5529 (p5530 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p5536 (p5537 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5539 :=
p5415 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 101 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 9827973709 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p5538 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p5436 337457950023929239 p5437 283677208169223
    137438953472 3352 137438953472
    (@p5441 p5434 p5435 337457950023929239
      p5437
      (p5443 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p5446 (p5477 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p5439 p5440)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p5540 :=
nat_lit 3160474309733126963775739851412680191992789720032812678034563773233030211415095073289765120

noncomputable def p5541 :=
nat_lit 8579458559543122362777316107628692705416469283866659345153845406716745855904816005376

noncomputable def p5542 :=
nat_lit 8277418825415759930547874161854750056383402401992811705975393918908230155165291822247280896

noncomputable def p5543 :=
BSN.sin_dyadic_bound_f 41369710818 137438953472 3 2 137438953472
  68719476736 p5540 p2477 p5541 p5542
  p2480

noncomputable def p5544 :=
@BSN.binarySplit_of_base2 (BSN.sinEvenP 41369710818) (BSN.sinEvenQ 137438953472) 0
  2 p5540 p2477 p5541 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5545 :=
p5543 p5541 40747827535 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5544 (Eq.refl true))

noncomputable def p5546 :=
@BSN.binarySplit_of_base2 (BSN.sinOddP 41369710818) (BSN.sinOddQ 137438953472) 0
  2 p5542 p2480 p5541 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5547 :=
nat_lit 9361365536335290583875096687240000914641

noncomputable def p5548 :=
BSN.sin_dyadic_bound_f 9836368739 137438953472 2 1 137438953472
  68719476736 p5547 p3178 p5547 p5547
  p3179

noncomputable def p5549 :=
@BSN.binarySplit_of_base (BSN.sinEvenP 9836368739) (BSN.sinEvenQ 137438953472) 0
  1 p5547 p3178 p5547 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5550 :=
p5548 p5547 9827973709 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5549 (Eq.refl true))

noncomputable def p5551 :=
@BSN.binarySplit_of_base (BSN.sinOddP 9836368739) (BSN.sinOddQ 137438953472) 0 1
  p5547 p3179 p5547 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5552 :=
p5539 d121 d123 d125 d127 d103
  (p5545 (p5546 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p5550 (p5551 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5553 :=
p5410 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 (Eq.refl true))
  (BSN.sfrac_not_eq_quadSignNeg_mul false 124328892008 137438953472)
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))
  (Eq.refl true) (Eq.refl true)
  (p5552 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p5436 337457950023929239 p5437 283677208169223
    137438953472 3352 137438953472
    (@p5441 p5434 p5435 337457950023929239
      p5437
      (p5443 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p5446 (p5477 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p5439 p5440)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p5554 :=
nat_lit
  56381849585508069750412364129219419141818363591697410362110784324528068296773351740920768248479417869624940172225278533136227478191586211028342143379837324506485379355523226330181329920000000

noncomputable def p5555 :=
nat_lit
  4069480874503121080769013674672790925022304167133689956085615708629814001001961261694534920198708333576401936517458104558208664207583876830505710894148740457582192010000000000000000

noncomputable def p5556 :=
nat_lit
  574188218245850529921132129758163550950477879908300541467086706925733056565860626806576791257139976755362137828597522191699371295797284391897622152831640913878727428952970176726506333184000000

noncomputable def p5557 :=
BSN.cos_dyadic_bound_f 194131579570 137438953472 5 4 137438953472
  68719476736 p5554 p2495 p5555 p5556
  p2498

noncomputable def p5558 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 194131579570) (BSN.cosEvenQ 137438953472) 0
  4 p5554 p2495 p5555 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5559 :=
p5557 p5555 21666266031 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5558 (Eq.refl true))

noncomputable def p5560 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 194131579570) (BSN.cosOddQ 137438953472) 0
  4 p5556 p2498 p5555 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5561 :=
nat_lit 8040894958251204326138348074280186518891621488652394341273892767463417766223949091760800000

noncomputable def p5562 :=
nat_lit 179925227943571086412197312764939473959067090402753792256733427146714552818960100000000

noncomputable def p5563 :=
nat_lit 24122325024297725836242219828215029677726946331776377516237164835535959869566209355082400000

noncomputable def p5564 :=
BSN.cos_dyadic_bound_f 60518270430 137438953472 3 2 137438953472
  68719476736 p5561 p2466 p5562 p5563
  p2469

noncomputable def p5565 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 60518270430) (BSN.cosEvenQ 137438953472) 0
  2 p5561 p2466 p5562 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5566 :=
p5564 p5562 124328892008 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5565 (Eq.refl true))

noncomputable def p5567 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 60518270430) (BSN.cosOddQ 137438953472) 0
  2 p5563 p2469 p5562 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5568 :=
p5553 d129 d131 d133 d135 d103
  (p5559 (p5560 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (p5566 (p5567 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5569 :=
p5405
  (p5568 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (@p5436 337457950023929239 p5437 283677208169223
    137438953472 3352 137438953472
    (@p5441 p5434 p5435 337457950023929239
      p5437
      (p5443 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p5446 (p5477 (Eq.refl true))
        (Enclosure.Real.IsNear.const true p5439 p5440)
        (Eq.refl true) (Eq.refl true)))
    (Eq.refl true))

noncomputable def p5570 :=
nat_lit 13129331948513552137833626455069928137957491296753537824071810932177594420293189393569259776

noncomputable def p5571 :=
nat_lit 479685115511189810728820786430080592634033263753458457668735225601015649101146734960896

noncomputable def p5572 :=
nat_lit 39387036475309634033879421723636924252687205823733106555300095326081581229581365887237857536

noncomputable def p5573 :=
BSN.cos_dyadic_bound_f 68409990534 137438953472 3 2 137438953472
  68719476736 p5570 p2466 p5571 p5572
  p2469

noncomputable def p5574 :=
@BSN.binarySplit_of_base2 (BSN.cosEvenP 68409990534) (BSN.cosEvenQ 137438953472) 0
  2 p5570 p2466 p5571 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5575 :=
p5573 p5571 120762098559 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5574 (Eq.refl true))

noncomputable def p5576 :=
@BSN.binarySplit_of_base2 (BSN.cosOddP 68409990534) (BSN.cosOddQ 137438953472) 0
  2 p5572 p2469 p5571 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5577 :=
p5569 d137 d139 d103
  (p5575 (p5576 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true) (Eq.refl true)

noncomputable def p5578 :=
@p5394 p2994 p5380 p5381
  (p5398
    (@p5401 217327 68719476736
      (p5577 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (p5577 (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true) (Eq.refl true)))

noncomputable def p5579 :=
@Enclosure.Real.IsNear.mulLit_ff p5385
  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1)))
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Zeta.RiemannSiegel.correctionLinear
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (@Inv.inv Real Real.instInv p5386)))

noncomputable def p5580 :=
nat_lit
  25735040429730510056062811236110122792205801743242565602238855500150408964574176074069707830699197759789709491006541643295037290495090039756881222367220330285066697

noncomputable def p5581 :=
nat_lit
  57586096570152913699974892898380567793532123114264532903689671329431521032595044740083720782129802971518987656109067457577065805510327036019308994315074097345724416

noncomputable def p5582 :=
nat_lit
  193307673526923334333779507911924906844622427824405465943192244059019794758311964479955000792382080645499943904315951617685891852834843097369986497994806684842432037759771330946217559337326397071538449931483972889927

noncomputable def p5583 :=
nat_lit
  1673786152045035727282396180715396040617623000735760838124838270722963902394782291657033752012423801870765115913641883513632341745134025335793254400000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5584 :=
@p5579 2411465255 8589934592 1 8589934592
  p5580 p5581 p5582 p5583
  p5391 p2994 p5392

noncomputable def p5585 :=
@Enclosure.Real.IsNear.mulLit_ff
  c22
  (p5384
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p5586 :=
@p5585 1 1 0 1 2411465255 8589934592
  1 8589934592 2411465255 8589934592 1

noncomputable def p5587 :=
@Enclosure.Real.IsNear.of_eq
  (p5384
    (@Neg.neg Real Real.instNeg
      (@HDiv.hDiv Real Real Real c4
        c38
        c20)))

noncomputable def p5588 :=
BSN.rpow_neg_quarter_mk
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    c7)

noncomputable def p5589 :=
p5588
  (BSN.t_div_two_pi_nonneg
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    101161500 100000
    (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true)))

noncomputable def p5590 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt p5386)) false
  4822930510 17179869184 2 17179869184 2411465255 8589934592

noncomputable def p5591 :=
@Enclosure.Real.IsNear.recentre' (Real.sqrt p5386) false 61196798204
  17179869184 6 17179869184 15299199551 4294967296 3
  8589934592

noncomputable def p5592 :=
@Enclosure.Real.IsNear.sqrt_image
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    c7)

noncomputable def p5593 :=
@Enclosure.Real.IsNear.of_eq
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    c7)

noncomputable def p5594 :=
@p5593
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101161500 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 553203909142269

noncomputable def p5595 :=
@p5594 3435973836800 202323 3435973836800
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    101161500 100000
    (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true)))

noncomputable def p5596 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 101161500 100000)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi))
  101161500 100000 0

noncomputable def p5597 :=
@p5596 1 2734261103 17179869184 1 17179869184
  553203909142269 3435973836800 202323 3435973836800
  (Enclosure.Real.IsNear.const false 101161500 100000) d142

noncomputable def p5598 :=
@p5592 553203909142269 3435973836800 202323 3435973836800
  108995245238 108995245279 8589934592
  (p5595 (p5597 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5599 :=
@Enclosure.Real.IsNear.recentre' p5386 false 217990490517 17179869184
  41 17179869184 217990490517 17179869184 41 17179869184
  (p5598 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p5600 :=
@Enclosure.Real.IsNear.sqrt_image p5386 217990490517 17179869184 41
  17179869184 30598399099 30598399105 8589934592
  (p5599 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p5601 :=
@Enclosure.Real.IsNear.inv_image (Real.sqrt p5386) 15299199551 4294967296
  3 8589934592 2411465254 2411465256 8589934592
  (p5591
    (p5600 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p5602 :=
@p5587 (@Inv.inv Real Real.instInv (Real.sqrt p5386)) false
  2411465255 8589934592 1 8589934592 p5589
  (@p5590 1 8589934592
    (p5601 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5603 :=
@Enclosure.Real.IsNear.addLit_ft_p
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Zeta.RiemannSiegel.correctionLinear
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1)))
    (@Inv.inv Real Real.instInv p5386))
  16513976982455568819

noncomputable def p5604 :=
nat_lit 43234556422756761600000000

noncomputable def p5605 :=
nat_lit
  41201422735657861841655448321378198964632454216318142631965487371825640173367217326186236400620532993449060473394773311540521383670036466358214219904920090744375

noncomputable def p5606 :=
nat_lit
  2130272782577187326626074483284451712656370202510099122603315022957460339710240374373344594946797597371405625683706495811337124125477126266471873994806684842432037759771330946217559337326397071538449931483972889927

noncomputable def p5607 :=
nat_lit
  949455409067613997777368357480431659005018958169081847311813325461515200627813920774156570600033621218352342919958274104389276836651141401475271254885031951243746048152519393048264704

noncomputable def p5608 :=
@p5603 36893488147419103232 4938187658643634861 p5604
  p5605 p5581 p5606 p5583
  p5607 p5580 p5581 p5582

noncomputable def p5609 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5610 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))

noncomputable def p5611 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (p5609
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5612 :=
BSN.cos_two_pi_p_ne_zero_mk
  (@OfScientific.ofScientific Real c2 101161500
    true 5)
  101161500 100000 12
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))

noncomputable def p5613 :=
@Enclosure.Real.IsNear.mulLit_tt
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5614 :=
@p5613
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5610 (Enclosure.sfrac false 1 16))))
  11434635499

noncomputable def p5615 :=
@p5614 4294967296 933 8589934592 1444206681
  8589934592 3990976307 110729625600000000 16513976982455568819
  36893488147419103232 4938187658643634861 p5604

noncomputable def p5616 :=
@Enclosure.Real.IsNear.of_eq
  (@Inv.inv Real Real.instInv
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5617 :=
@Inv.inv Real Real.instInv
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5618 :=
@p5616 (@Neg.neg Real Real.instNeg p5617) true 11434635499
  4294967296 933 8589934592
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5619 :=
@Enclosure.Real.IsNear.inv_image
  (@Neg.neg Real Real.instNeg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5620 :=
@Enclosure.Real.IsNear.neg
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p5621 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p5622 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 74343027487)
    (@Nat.cast Real Real.instNatCast 17179869184))
  false

noncomputable def p5623 :=
nat_lit 10462850965275636145398495

noncomputable def p5624 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  false p5623

noncomputable def p5625 :=
nat_lit 44257167736297200262849463

noncomputable def p5626 :=
nat_lit 2951479051793528258560000000000000

noncomputable def p5627 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
    (Enclosure.sfrac false 12 1))
  884279719003555 140737488355328 1

noncomputable def p5628 :=
@Enclosure.Real.IsNear.subLit_ff_p p5386 (Enclosure.sfrac false 12 1)
  217990490517 17179869184 41 17179869184 12 1 0

noncomputable def p5629 :=
@p5627 500000000000000 11832060309 17179869184 41
  17179869184 p5623 p2602 p5625 p5626
  d141
  (@p5628 1 11832060309 11832060309 17179869184 41
    17179869184 (p5599 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5630 :=
@p5622 74343027487 17179869184 129 8589934592 true
  6452936458 17179869184 1 3300000000
  (@p5624 p2602 p5625 p5626
    74343027487 17179869184 129 8589934592
    (p5629 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 74343027487 17179869184)

noncomputable def p5631 :=
nat_lit 2935752722410306622900404224

noncomputable def p5632 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast 74343027487)
    (@Nat.cast Real Real.instNatCast 17179869184))
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p5631)
    (@Nat.cast Real Real.instNatCast p2333))
  226375608064910080 72057594037927936 false

noncomputable def p5633 :=
BSN.sin_reduce_arg_pos_rat_q2 74343027487 17179869184 226375608064910080
  72057594037927936 0 p5631 p2333 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5634 :=
nat_lit
  142165314098397969408488309847097578287732637962825823389525514399521781991401003969501776912510787650863048175153034240199230588332155218249937393463110866971945837489041

noncomputable def p5635 :=
nat_lit
  27802001404199489382430999783726980452551751610627493375427790217534344890024338610436792083414432758773414484592743553205622117345678067926182484169749442590108561

noncomputable def p5636 :=
nat_lit
  861793672224817793710527466371261656362276535829912274806267296144924800183728056305116106928885587425048983354206777388510575687400716005098456573191596036445895856188305

noncomputable def p5637 :=
BSN.cos_dyadic_bound_f 41719555417931 35184372088832 4 3 17179869184
  6606445313 p5634 p2613 p5635 p5636
  p2616

noncomputable def p5638 :=
@BSN.binarySplit_of_base3 (BSN.cosEvenP 41719555417931) (BSN.cosEvenQ 35184372088832) 0
  3 p5634 p2613 p5635 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5639 :=
p5637 p5635 6452936458 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5638 (Eq.refl true))

noncomputable def p5640 :=
@BSN.binarySplit_of_base3 (BSN.cosOddP 41719555417931) (BSN.cosOddQ 35184372088832) 0
  3 p5636 p2616 p5635 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5641 :=
@BSN.cos_arg_round false 6452936458 17179869184 p5631 p2333
  41719555417931 35184372088832 6606445313 6600000000
  (p5639 (p5640 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5642 :=
p5632 6452936458 17179869184 0 1000000000000000
  6600000000 3300000000 p5633 BSN.pi_near_15 p5641
  (Eq.refl true) (Eq.refl true)

noncomputable def p5643 :=
@p5620 3226468229 8589934592 1696445057 110729625600000000
  (@p5621 6452936458 17179869184 434289934592
    28346784153600000000 3226468229 8589934592 1696445057
    110729625600000000
    (p5630 (p5642 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5644 :=
@p5619 3226468229 8589934592 1696445057 110729625600000000
  22869270065 22869271931 8589934592 p5643 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5645 :=
@Enclosure.Real.IsNear.recentre' p5617 false 45738541996 17179869184
  1866 17179869184 11434635499 4294967296 933 8589934592
  (p5644 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p5646 :=
@Enclosure.Real.IsNear.recentre'
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5610 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p5647 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5610 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14944136303))
    (@Nat.cast Real Real.instNatCast 8589934592))
  true

noncomputable def p5648 :=
nat_lit 72265408915933739565427375332638005

noncomputable def p5649 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5610 (Enclosure.sfrac false 1 16)))
  true p5648

noncomputable def p5650 :=
nat_lit 45190979288276075224350961392231926093

noncomputable def p5651 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (p5610 (Enclosure.sfrac false 1 16)) 884279719003555
  140737488355328 1

noncomputable def p5652 :=
@Enclosure.Real.IsNear.subLit_tf
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1)))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))

noncomputable def p5653 :=
@p5652 (Enclosure.sfrac false 1 16) 63275597130005442375
  295147905179352825856 1674603583563 295147905179352825856 1 16
  0

noncomputable def p5654 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
    (Enclosure.sfrac false 12 1))
  139997651155813175481

noncomputable def p5655 :=
nat_lit 1087066481232979341210550272000

noncomputable def p5656 :=
@p5654 295147905179352825856 970228947019 295147905179352825856
  11832060309 17179869184 41 17179869184 p5655
  63275597130005442375 295147905179352825856 1674603583563

noncomputable def p5657 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
    (Enclosure.sfrac false 12 1))
  11832060309 17179869184 41

noncomputable def p5658 :=
@p5657 17179869184 11832060309 17179869184 41
  17179869184 139997651155813175481 295147905179352825856 970228947019
  295147905179352825856
  (@p5628 1 11832060309 11832060309 17179869184 41
    17179869184 (p5599 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5659 :=
p5658
  (@p5628 1 11832060309 11832060309 17179869184 41
    17179869184 (p5599 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5660 :=
@p5656 295147905179352825856 (p5659 (Eq.refl true))
  (@p5628 1 11832060309 11832060309 17179869184 41
    17179869184 (p5599 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5661 :=
@p5651 500000000000000 81722341203714993991 295147905179352825856
  1674603583563 295147905179352825856 p5648 p2630
  p5650 p2632 d141
  (@p5653 1 1307557459259439903856 81722341203714993991
    295147905179352825856 1674603583563 295147905179352825856
    (p5660 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5662 :=
@p5647 14944136303 8589934592 307 8589934592 true
  1444206681 8589934592 1 3300000000
  (@p5649 p2630 p5650 p2632
    14944136303 8589934592 307 8589934592
    (p5661 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 14944136303 8589934592)

noncomputable def p5663 :=
nat_lit
  7055590915981684532831767494814357833710709720254805768998267910728587679097596561198037714879497771793781815087687805343598145440310723500524538328506016152059222895571201

noncomputable def p5664 :=
nat_lit
  6187755153135331678131850480319172423279188803638821543359508176402992094742010766638604283310563388403157002905374088309168854967310286677549591351623478220632321

noncomputable def p5665 :=
nat_lit
  71706584268539819161610270555182788945367650585757296222976183090371115262312225819384294919872097499511855505537015945236010020502548693919173572805946143207551150711845121

noncomputable def p5666 :=
BSN.cos_dyadic_bound_t 14944136303 8589934592 5 4 8589934592
  3300000000 p5663 p2646 p5664 p5665
  p2649

noncomputable def p5667 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 14944136303) (BSN.cosEvenQ 8589934592) 0
  4 p5663 p2646 p5664 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5668 :=
p5666 p5664 1444206681 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5667 (Eq.refl true))

noncomputable def p5669 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 14944136303) (BSN.cosOddQ 8589934592) 0 4
  p5665 p2649 p5664 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5670 :=
p5662
  (BSN.cos_neg_of_bound 14944136303 8589934592 true 1444206681 8589934592
    1 3300000000
    (p5668 (p5669 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p5671 :=
p5615
  (p5618
    (@Enclosure.Real.IsNear.neg p5617 false 11434635499 4294967296
      933 8589934592 (p5645 (Eq.refl true))))
  (@p5646 1444206681 8589934592 1021689934592
    28346784153600000000 1444206681 8589934592 3990976307
    110729625600000000 (p5670 (Eq.refl true)) (Eq.refl true))

noncomputable def p5672 :=
@p5608 p5583
  (@p5611 false 16513976982455568819 36893488147419103232
    4938187658643634861 p5604
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (p5612 (Eq.refl true) (Eq.refl true)
        (p5389 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5671 (Eq.refl true)))

noncomputable def p5673 :=
nat_lit
  30430567832224037852114850378251784115732622153410094447914512032634711756874287194517505350098505031765524583543179735070595858113644228255850374626625

noncomputable def p5674 :=
nat_lit
  3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608412251521024

noncomputable def p5675 :=
@Enclosure.Real.IsNear.mulLit_tf
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv p5386) p5673 p5674

noncomputable def p5676 :=
nat_lit
  1572724691568492596718674889378611679724030740749952995969007650944693227860538396942416637396279004066341044944809322382287695196937262872476607832722787953500215925138459545394029617285406415533685499057

noncomputable def p5677 :=
nat_lit
  97427176779894840861810148968093332404830900529385593144970379695468809362197195392627836671449698151017371327246183268355225547282841600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5678 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))

noncomputable def p5679 :=
@Enclosure.Real.IsNear.of_eq
  (Zeta.RiemannSiegel.correctionLinear
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@Neg.neg Real Real.instNeg p5678) true p5673

noncomputable def p5680 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 96 1)
      c16))

noncomputable def p5681 :=
nat_lit
  6555732387434283303048684169173587164371574367964536482270934165295625544034828716320003780688721304757861661283207744638430784829793150748775

noncomputable def p5682 :=
nat_lit
  762145642166990290864647761179972242614403843424065222377723867096038022172794340849684107193235344521442121855812163792833978437326241529856

noncomputable def p5683 :=
nat_lit
  3048974230503020703723929091885098631705132868178132056034596572403664891526866637283748763081593180716476334958063140560016719745901499311577106012373417158691788351308018506571080399500686831343

noncomputable def p5684 :=
nat_lit
  199371377452519838642795398462303635743291603094910519372372941065627693264963172290129143685373329244420424844341971360153600000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5685 :=
@p5680 p5681 p5682 p5683 p5684
  4641825815 4398046511104 1 4398046511104 p5673
  p5674 p5676

noncomputable def p5686 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5687 :=
p5686
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5688 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5687
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5689 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5688
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5690 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5691 :=
p5689
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5690
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5692 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5693 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5691
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p5692)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))

noncomputable def p5694 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c16)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5695 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5693
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p5694)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))

noncomputable def p5696 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c16 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))

noncomputable def p5697 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 3 (instOfNatNat 3)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (p5609
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5695
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5696
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
            (Enclosure.sfrac false 12 1))))))

noncomputable def p5698 :=
@p5613
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5695
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5696
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))
  5854533227701

noncomputable def p5699 :=
nat_lit
  1119770292944196886303674257355907822224933626563369747879989608611670934906122344388705271801549706914828534926668875775574431275

noncomputable def p5700 :=
nat_lit
  520741729937584618484998929466919384917476529065408520200947737428123928259494566444876732216050705112369152465636537726574354850291187626281090866445698448908129207696103336588791411

noncomputable def p5701 :=
nat_lit
  90663605739118719904033877565918208230546771617314570618133503133152632137791066402373482417430445477484874956800000000000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5702 :=
@p5698 2199023255552 937 2199023255552 p5699
  p3325 p5700 p5701 p5681
  p5682 p5683 p5684

noncomputable def p5703 :=
@p5616 (@Neg.neg Real Real.instNeg p5617) true 5854533227701
  2199023255552 937 2199023255552
  (BSN.inv_eq_neg_inv_neg
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5704 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c59
    c33)
  false

noncomputable def p5705 :=
nat_lit 2678489840801227058131649795

noncomputable def p5706 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  false p5705

noncomputable def p5707 :=
nat_lit 221291022149305031852339859

noncomputable def p5708 :=
nat_lit 3777893186295716170956800000000000000

noncomputable def p5709 :=
@Enclosure.Real.IsNear.subLit_ff_p p5386 (Enclosure.sfrac false 12 1)
  55805565565217 4398046511104 41 4398046511104 12 1
  0

noncomputable def p5710 :=
@p5593
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 101161500 100000)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)))
  false 141620200704609693

noncomputable def p5711 :=
@p5710 879609302220800 202323 879609302220800
  (BSN.t_div_two_pi_mk
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    101161500 100000
    (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true)))

noncomputable def p5712 :=
@p5596 1 699970842191 4398046511104 1 4398046511104
  141620200704609693 879609302220800 202323 879609302220800
  (Enclosure.Real.IsNear.const false 101161500 100000) d145

noncomputable def p5713 :=
@p5592 141620200704609693 879609302220800 202323
  879609302220800 27902782782588 27902782782629 2199023255552
  (p5711 (p5712 (Eq.refl true))) (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5714 :=
@Enclosure.Real.IsNear.recentre' p5386 false 55805565565217 4398046511104
  41 4398046511104 55805565565217 4398046511104 41
  4398046511104
  (p5713 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p5715 :=
@p5627 500000000000000 3029007431969 4398046511104 41
  4398046511104 p5705 p504 p5707 p5708
  d144
  (@p5709 1 3029007431969 3029007431969 4398046511104
    41 4398046511104 (p5714 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5716 :=
@p5704 19031814991885 4398046511104 259 4398046511104
  true 1651951774935 4398046511104 1 844800000000
  (@p5706 p504 p5707 p5708
    19031814991885 4398046511104 259 4398046511104
    (p5715 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 19031814991885 4398046511104)

noncomputable def p5717 :=
nat_lit 751552690482551567109146542080

noncomputable def p5718 :=
BSN.cos_reduce2
  (@HDiv.hDiv Real Real Real c4
    c59
    c33)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p5717)
    (@Nat.cast Real Real.instNatCast p2704))
  226375608064910080 72057594037927936 false

noncomputable def p5719 :=
BSN.sin_reduce_arg_pos_rat_q2 19031814991885 4398046511104 226375608064910080
  72057594037927936 0 p5717 p2704 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5720 :=
nat_lit
  3238283956193050427024980792401926347189770406143023369860324775873486583162714576931399069501554245142274247770402570495968352355251598659454842787087111293907232920530395772230916763769206591123175806989315427902134082986811751726125000794432944201264969809920000000

noncomputable def p5721 :=
nat_lit
  28659864529570302431069785462562805353159300329449869010831559506885992418340904121795806908178388636518033003342451496914705757958381564943266992028192728170146445715339730307520427577009783471487207349854602430665776964214376786509650984960000000000000000

noncomputable def p5722 :=
nat_lit
  33004611021390172854801586561583540475586623680264205446930745210277128707022623710078886201193046204821008366618467171527633628990701043920925879482231224207083232553996894011205151024166043916958518874606925033630039035379729892505620316492228366951982179549184000000

noncomputable def p5723 :=
BSN.cos_dyadic_bound_f 10680206095266720 9007199254740992 5 4
  4398046511104 1691250000001 p5720 p2708
  p5721 p5722 p2711

noncomputable def p5724 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 10680206095266720) (BSN.cosEvenQ 9007199254740992)
  0 4 p5720 p2708 p5721
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5725 :=
p5723 p5721 1651951774935 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5724 (Eq.refl true))

noncomputable def p5726 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 10680206095266720) (BSN.cosOddQ 9007199254740992) 0
  4 p5722 p2711 p5721 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5727 :=
@BSN.cos_arg_round false 1651951774935 4398046511104 p5717
  p2704 10680206095266720 9007199254740992 1691250000001
  1689600000000
  (p5725 (p5726 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5728 :=
p5718 1651951774935 4398046511104 0 1000000000000000
  1689600000000 844800000000 p5719 BSN.pi_near_15 p5727
  (Eq.refl true) (Eq.refl true)

noncomputable def p5729 :=
@p5620 1651951774935 4398046511104 3405780739
  56693568307200000000
  (@p5621 1651951774935 4398046511104 223201246511104
    p2689 1651951774935 4398046511104 3405780739
    56693568307200000000
    (p5716 (p5728 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5730 :=
@p5619 1651951774935 4398046511104 3405780739
  56693568307200000000 5854533226764 5854533228638 2199023255552
  p5729 (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5731 :=
@Enclosure.Real.IsNear.recentre' p5617 false 11709066455402 4398046511104
  1874 4398046511104 5854533227701 2199023255552 937
  2199023255552
  (p5730 (Eq.refl true) (Eq.refl true) (Eq.refl true))

noncomputable def p5732 :=
nat_lit
  36783378074391183984859214605223256900781115070541199699606556163165282363761403127054820053063849396475523569016123574288351647275

noncomputable def p5733 :=
@Enclosure.Real.IsNear.subLit_tt_n p5695
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5696
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))
  p5732 p3325

noncomputable def p5734 :=
nat_lit
  510831440513288907333221076917078437434414103362431216910407086559924346245322145523373123989507522683823170929643618003809810872957488106589756224263764381008339731856103336588791411

noncomputable def p5735 :=
nat_lit 3050253834010269734910646702417492035659331708481526134606117991400174893763467625

noncomputable def p5736 :=
nat_lit
  15302780552374716806148895732655152186370381334762418223546157240411296622552267288188763302198573277492880693745980931

noncomputable def p5737 :=
nat_lit
  33193098671587876751936585981194306250119457633815588701288753380474307714304476216085569659462310587019691136648521239223267363565833423901796887631282327537278185246557675001339405162344655897269434213990400

noncomputable def p5738 :=
@p5733 p5734 p5701 p5735 p2761
  p5736 p3364 p5737 p5699
  p3325 p5700 p5701

noncomputable def p5739 :=
@Enclosure.Real.IsNear.subLit_tf p5693
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p5694)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))

noncomputable def p5740 :=
nat_lit
  25750841372379855850030614502091895436989871411608905483087282743448405094204776819384879429056979508715742049099986124851085727275

noncomputable def p5741 :=
nat_lit
  475351937738539886608386240695265672050382300603352572225824971372792375364720168269305961540624465705071390318884392520990945501858742563658889383444371911263780937979690510988791411

noncomputable def p5742 :=
nat_lit 9125900467183490157747144246180034764619010011459433838544428548739836813738106863207289270882650691560625

noncomputable def p5743 :=
nat_lit 286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328

noncomputable def p5744 :=
nat_lit
  2276689985031271954205688816356748921407822358745272407430460902983877488444789865003100724878755464717487448206847028520631895431780659882308010248617

noncomputable def p5745 :=
nat_lit
  5817807664993002135136058545459733245667347881251394831268865214065583608118298149912576000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def p5746 :=
nat_lit
  10545328338131965271218699440958831616324373311132784408163298744176114843759788237355293338797506480896771700682600071943399659652203348615678014728403476237975740242367325144242956655278084210137640538047527864829637663311518708531200

noncomputable def p5747 :=
@p5739 p5740 p3325 p5741 p5701
  p5742 p5743 p5744 p5745
  p5746 p5732 p3325

noncomputable def p5748 :=
@Enclosure.Real.IsNear.subLit_ff_n p5691
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 3 1) p5692)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))

noncomputable def p5749 :=
nat_lit 122802074285100779540164280020172167962640521450898374391373527508261577246914846979040332075

noncomputable def p5750 :=
nat_lit 65185151242703554760590262029100101153646988597309960020356494379340201592426774597868716032

noncomputable def p5751 :=
nat_lit
  409715619861824638416172125966495150983894440752932512577661225310522140632264453885648913489342387042966202591359864045367

noncomputable def p5752 :=
nat_lit
  23882118405196465306111515658041880994736934337288366333138126701632082988236800000000000000000000000000000000000000000000000000000

noncomputable def p5753 :=
nat_lit
  26403769192700715309602605000645596429223273895768761336410931301002652849506116707150675451152625020266430483654279693980946028075

noncomputable def p5754 :=
nat_lit
  473796535709537781192443476537595310949218865856940471278635462593946010184407555570741990336970936074931187993300516478045310576193944858684483679804199973471780937979690510988791411

noncomputable def p5755 :=
nat_lit
  1678572489485448872095146600639957381622828649071725817918057633689744056611689283196660329156835878733650785451590715853475126336828415673124623307371642531870477175055497953553658807450364254541035735705931817065172172800

noncomputable def p5756 :=
@p5748 p5749 p5750 p5751 p5752
  p5753 p3325 p5754 p5701
  p5755 p5740 p3325

noncomputable def p5757 :=
@Enclosure.Real.IsNear.subLit_tt_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5688
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5758 :=
@p5757
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5690
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 4 1) Real.pi))
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5759 :=
nat_lit 857001811841183776559110516204983074614636315179188959115320221740105565457373238228848359125

noncomputable def p5760 :=
nat_lit
  91375528105759975163775297184952992436392517458231707395910563232807636406480019789418948261562343355374266591359864045367

noncomputable def p5761 :=
nat_lit 719846208159482111254888625419013785357547926178678175

noncomputable def p5762 :=
nat_lit 47890485652059026823698344598447161988085597568237568

noncomputable def p5763 :=
nat_lit 2554586313383271564796439472906309166894105298798956684940677452320309059

noncomputable def p5764 :=
nat_lit 191647029049872542622572578905571856692019200000000000000000000000000000000000000

noncomputable def p5765 :=
nat_lit
  5881050976593705656330870270535152039688066654843413832346880616626793438040640334980772103051418494292505809798828582860730230866649047210393600

noncomputable def p5766 :=
@p5758 p5759 p5750 p5760 p5752
  p5761 p5762 p5763 p5764
  p5765 p5749 p5750

noncomputable def p5767 :=
nat_lit 395346985515304307690857324971030619013639638199715544809739200755918343215662875

noncomputable def p5768 :=
@Enclosure.Real.IsNear.mulLit_ft p5688
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5610 (Enclosure.sfrac false 1 16))))
  p5767

noncomputable def p5769 :=
nat_lit 1665201234065144010202882478373546104757132776064637533492613561304034180957639893631485270089645586081

noncomputable def p5770 :=
@p5768 p2761 p5769 p5163 2167720618191
  2199023255552 3990976307 28346784153600000000 p5759
  p5750 p5760 p5752

noncomputable def p5771 :=
@Enclosure.Real.IsNear.mulLit_ff p5687
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5772 :=
nat_lit 538665243693968425864640795534393882678753802285129225

noncomputable def p5773 :=
nat_lit 49563951430998979621160830878922975128624283654276405415678360371

noncomputable def p5774 :=
nat_lit 733938174299421780570162435

noncomputable def p5775 :=
nat_lit 1106436221280593680680844511

noncomputable def p5776 :=
@p5771 p5772 p2767 p5773 p5168
  p5774 p976 p5775 p5171 p5767
  p2761 p5769

noncomputable def p5777 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5778 :=
@p5777
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5779 :=
@p5778 p5774 p976 p5775 p5171
  p5774 p976 p5775 p5171 p5772
  p2767 p5773

noncomputable def p5780 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1)))
    (Enclosure.sfrac false 1 1))
  884279719003555

noncomputable def p5781 :=
@p5780 140737488355328 1 500000000000000 829984176417
  2199023255552 41 2199023255552 p5774 p976
  p5775 p5171

noncomputable def p5782 :=
@Enclosure.Real.IsNear.subLit_ff_p
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (Enclosure.sfrac false 1 1) 3029007431969 2199023255552

noncomputable def p5783 :=
@p5782 41 2199023255552 1 1 0 1
  829984176417 829984176417 2199023255552 41 2199023255552

noncomputable def p5784 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1)
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
    (Enclosure.sfrac false 12 1))
  2 1 0 1

noncomputable def p5785 :=
@p5784 3029007431969 4398046511104 41 4398046511104
  3029007431969 2199023255552 41 2199023255552
  (Enclosure.Real.IsNear.const false 2 1)
  (@p5709 1 3029007431969 3029007431969 4398046511104
    41 4398046511104 (p5714 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5786 :=
@p5779 p5168
  (p5781 d144
    (p5783 (p5785 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p5781 d144
    (p5783 (p5785 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p5787 :=
@p5776 p5163 (p5786 (Eq.refl true))
  (p5781 d144
    (p5783 (p5785 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p5788 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5610 (Enclosure.sfrac false 1 16))))
  true

noncomputable def p5789 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5610 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7651397804245))
    c33)
  true

noncomputable def p5790 :=
nat_lit 4735985849187931348429708176505735983005

noncomputable def p5791 :=
@Enclosure.Real.IsNear.recentre'
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5610 (Enclosure.sfrac false 1 16)))
  true p5790

noncomputable def p5792 :=
nat_lit 11568936496321163008303393910012134424373

noncomputable def p5793 :=
nat_lit 5355755364970540094572991

noncomputable def p5794 :=
nat_lit 4146829545355910919866815

noncomputable def p5795 :=
@p5652 (Enclosure.sfrac false 1 16) p5794
  p2793 428698516378403 p2793 1 16 0

noncomputable def p5796 :=
nat_lit 85692085839528641513167856

noncomputable def p5797 :=
nat_lit 9174886022923436163216961

noncomputable def p5798 :=
@Enclosure.Real.IsNear.subLit_ff_n
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1))
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
    (Enclosure.sfrac false 12 1))
  p5797

noncomputable def p5799 :=
nat_lit 18237949214095550547064061031098613760

noncomputable def p5800 :=
@p5798 p2793 248378609423139 p2793
  3029007431969 4398046511104 41 4398046511104 p5799
  p5794 p2793 428698516378403

noncomputable def p5801 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
    (Enclosure.sfrac false 12 1))
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
    (Enclosure.sfrac false 12 1))
  3029007431969 4398046511104 41

noncomputable def p5802 :=
@p5801 4398046511104 3029007431969 4398046511104 41
  4398046511104 p5797 p2793 248378609423139
  p2793
  (@p5709 1 3029007431969 3029007431969 4398046511104
    41 4398046511104 (p5714 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5803 :=
p5802
  (@p5709 1 3029007431969 3029007431969 4398046511104
    41 4398046511104 (p5714 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5804 :=
@p5800 p2793 (p5803 (Eq.refl true))
  (@p5709 1 3029007431969 3029007431969 4398046511104
    41 4398046511104 (p5714 (Eq.refl true))
    (Enclosure.Real.IsNear.const false 12 1) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5805 :=
@p5651 500000000000000 p5793 p2793
  428698516378403 p2793 p5790 p2789
  p5792 p2791 d144
  (@p5795 1 p5796 p5793 p2793
    428698516378403 p2793
    (p5804 (Eq.refl true) (Eq.refl true))
    (Enclosure.Real.IsNear.const false 1 16) (Eq.refl true)
    (Eq.refl true))

noncomputable def p5806 :=
@p5789 7651397804245 4398046511104 307 2199023255552 true
  2167720618191 2199023255552 1 844800000000
  (@p5791 p2789 p5792 p2791
    7651397804245 4398046511104 307 2199023255552
    (p5805 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 7651397804245 4398046511104)

noncomputable def p5807 :=
nat_lit
  533681970195391069216827202602168507393399390731015716638939212868063234109783439856383805218470380726293985523265528203504236259309839643041375620297671096943244254250542893435831908856952391698496064066326895890625

noncomputable def p5808 :=
nat_lit
  137991555957888614927395666654746344875551240188372479148081385557393659507234307793401273954483002403069467016032732040849085388685694705566607663641870621706377435168904507480111730156298633789215087890625

noncomputable def p5809 :=
nat_lit
  4337577028771977439981310923569966268970220900296193596206074283134593392166861135132003058504885137019588417830259903779163507444855349591337445634520851342707074021793225005560996066310991787800627755042378095890625

noncomputable def p5810 :=
BSN.sin_dyadic_bound_f 7651397804245 4398046511104 5 4 2199023255552
  844800000000 p5807 p2808 p5808 p5809
  p2811

noncomputable def p5811 :=
@BSN.binarySplit_of_base4 (BSN.sinEvenP 7651397804245) (BSN.sinEvenQ 4398046511104) 0
  4 p5807 p2808 p5808 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5812 :=
p5810 p5808 2167720618191 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5811 (Eq.refl true))

noncomputable def p5813 :=
@BSN.binarySplit_of_base4 (BSN.sinOddP 7651397804245) (BSN.sinOddQ 4398046511104) 0
  4 p5809 p2811 p5808 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5814 :=
p5806
  (BSN.sin_neg_of_bound 7651397804245 4398046511104 false 2167720618191
    2199023255552 1 844800000000
    (p5812 (p5813 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p5815 :=
p5770 p5787
  (@p5788 2167720618191 2199023255552 261552623255552
    p3422 2167720618191 2199023255552 3990976307
    28346784153600000000 (p5814 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5816 :=
nat_lit 1947019927606424592584092026708248077369275

noncomputable def p5817 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5690
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi))
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5610 (Enclosure.sfrac false 1 16))))
  p5816

noncomputable def p5818 :=
nat_lit 89575691100793825949241353581943763653144543278470411

noncomputable def p5819 :=
@p5817 p2820 p5818 p5216 369716918637
  2199023255552 3990976307 28346784153600000000 p5761
  p5762 p5763 p5764

noncomputable def p5820 :=
nat_lit 2201814522898265341710487305

noncomputable def p5821 :=
nat_lit 3319308663841781042042533533

noncomputable def p5822 :=
@Enclosure.Real.IsNear.mulLit_ff p5690
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  p5820 p976 p5821 p5171

noncomputable def p5823 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5824 :=
@p5823 3 1 0 1 p5774 p976
  p5775 p5171 p5820 p976 p5821

noncomputable def p5825 :=
@p5824 p5171 (Enclosure.Real.IsNear.const false 3 1)
  (p5781 d144
    (p5783 (p5785 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (Eq.refl true)

noncomputable def p5826 :=
@p5822 884279719003555 70368744177664 1 250000000000000
  p5816 p2820 p5818 p5216
  p5825 d146 (Eq.refl true)

noncomputable def p5827 :=
@Enclosure.Real.IsNear.cos_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (p5610 (Enclosure.sfrac false 1 16)))
  (@HDiv.hDiv Real Real Real c4
    (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7651397804245))
    c33)
  true

noncomputable def p5828 :=
@p5827 7651397804245 4398046511104 307 2199023255552 true
  369716918637 2199023255552 1 844800000000
  (@p5791 p2789 p5792 p2791
    7651397804245 4398046511104 307 2199023255552
    (p5805 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_true_div 7651397804245 4398046511104)

noncomputable def p5829 :=
nat_lit
  157344936657350911063881089131069640353371030790627181463370691139883112967820675872647459822642508887116949105295960540442368369385883592941593209525085721487969229572640539510343390488957753318464888679076207890625

noncomputable def p5830 :=
nat_lit
  1599110279158479009842186431302529820133300971120773617299553877151606847648827478651824062973846446455843683356264405845432239686450025914033775675669911063253430536638539984371981403513966513002967165745926511890625

noncomputable def p5831 :=
BSN.cos_dyadic_bound_t 7651397804245 4398046511104 5 4 2199023255552
  844800000000 p5829 p2834 p5808 p5830
  p2836

noncomputable def p5832 :=
@BSN.binarySplit_of_base4 (BSN.cosEvenP 7651397804245) (BSN.cosEvenQ 4398046511104) 0
  4 p5829 p2834 p5808 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5833 :=
p5831 p5808 369716918637 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5832 (Eq.refl true))

noncomputable def p5834 :=
@BSN.binarySplit_of_base4 (BSN.cosOddP 7651397804245) (BSN.cosOddQ 4398046511104) 0
  4 p5830 p2836 p5808 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5835 :=
p5828
  (BSN.cos_neg_of_bound 7651397804245 4398046511104 true 369716918637
    2199023255552 1 844800000000
    (p5833 (p5834 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (Eq.refl true)

noncomputable def p5836 :=
p5819 p5826
  (@p5646 369716918637 2199023255552 261552623255552
    p3422 369716918637 2199023255552 3990976307
    28346784153600000000 (p5835 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5837 :=
nat_lit 5406501244124281869343714995

noncomputable def p5838 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p5692)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  p5837

noncomputable def p5839 :=
nat_lit 91909107184533420924386949399126613

noncomputable def p5840 :=
nat_lit 4883707225887722194010073235727860237256347239627847529733727985131924376864737158707714910375083849385

noncomputable def p5841 :=
nat_lit
  667670531679454255141530304174877178005708318331653891871400114122669896432861353884902967455485828124245423702514804683621467707893763119

noncomputable def p5842 :=
nat_lit
  2234038143357312819892246481456537566336261586400535615207244242201184105517426489566429184000000000000000000000000000000000000000000000000000000

noncomputable def p5843 :=
@p5838 p976 p5839 p2846 p5840
  p2734 p5841 p5842 p5753
  p3325 p5754 p5701

noncomputable def p5844 :=
nat_lit 1802167081374760623114571665

noncomputable def p5845 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p5692
  3 1 0 1 p5844 p976

noncomputable def p5846 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5847 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))
  884279719003555

noncomputable def p5848 :=
@p5847 140737488355328 1 500000000000000 2038005670203
  2199023255552 3405780739 56693568307200000000 p5844
  p976 p5839 p2854

noncomputable def p5849 :=
@Enclosure.Real.IsNear.recentre'
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))
  true

noncomputable def p5850 :=
@Enclosure.Real.IsNear.sin_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (@HDiv.hDiv Real Real Real c4
    c59
    c33)
  false

noncomputable def p5851 :=
@p5850 19031814991885 4398046511104 259 4398046511104
  true 4076011340406 4398046511104 1 844800000000
  (@p5706 p504 p5707 p5708
    19031814991885 4398046511104 259 4398046511104
    (p5715 (Eq.refl true)) (Eq.refl true))
  (Enclosure.sfrac_false_div 19031814991885 4398046511104)

noncomputable def p5852 :=
BSN.sin_reduce2
  (@HDiv.hDiv Real Real Real c4
    c59
    c33)
  (@HDiv.hDiv Real Real Real c4
    (@Nat.cast Real Real.instNatCast p5717)
    (@Nat.cast Real Real.instNatCast p2704))
  226375608064910080 72057594037927936 false

noncomputable def p5853 :=
nat_lit
  29269789752940105683728174317135182371014190326946560715688002656449165818308506997437627106696315685255967443248022776364655933090287637187160982901316200108476904137853771578132131530813105766400000

noncomputable def p5854 :=
nat_lit
  2202701258467166068152331922867628122601416309526229658783924127201442369078639794209102788690637406717319982412778653011314186250716801429027481847418824320610113648233573427183616000000000000

noncomputable def p5855 :=
nat_lit
  146289838296126317635131787542054522537454040780346868839052613245462694464881759870119204195414246500779923109659036276609248431443031396434713479989416726612305242224129661542930687218608504832000000

noncomputable def p5856 :=
BSN.sin_dyadic_bound_f 10680206095266720 9007199254740992 4 3
  4398046511104 1691250000001 p5853 p2863
  p5854 p5855 p2866

noncomputable def p5857 :=
@BSN.binarySplit_of_base3 (BSN.sinEvenP 10680206095266720) (BSN.sinEvenQ 9007199254740992)
  0 3 p5853 p2863 p5854
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p5858 :=
p5856 p5854 4076011340406 (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (p5857 (Eq.refl true))

noncomputable def p5859 :=
@BSN.binarySplit_of_base3 (BSN.sinOddP 10680206095266720) (BSN.sinOddQ 9007199254740992) 0
  3 p5855 p2866 p5854 (Eq.refl true)
  (Eq.refl true) (Eq.refl true)

noncomputable def p5860 :=
@BSN.sin_arg_round false 4076011340406 4398046511104 p5717
  p2704 10680206095266720 9007199254740992 1691250000001
  1689600000000
  (p5858 (p5859 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true) (Eq.refl true) (Eq.refl true))
  (Eq.refl true)

noncomputable def p5861 :=
p5852 4076011340406 4398046511104 0 1000000000000000
  1689600000000 844800000000 p5719 BSN.pi_near_15 p5860
  (Eq.refl true) (Eq.refl true)

noncomputable def p5862 :=
p5848 d144
  (@p5849 4076011340406 4398046511104 223201246511104
    p2689 2038005670203 2199023255552 3405780739
    56693568307200000000
    (p5851 (p5861 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5863 :=
@Neg.neg Real Real.instNeg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5687
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5864 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5863
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5865 :=
@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5864
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p5692)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))

noncomputable def p5866 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 2 (instOfNatNat 2)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (p5609
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5865
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5694
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
            (Enclosure.sfrac false 12 1))))))

noncomputable def p5867 :=
@p5613
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5865
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5694
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))
  5854533227701

noncomputable def p5868 :=
nat_lit 834175336605868285910636880104686744534375469812198287724463364026454701797218515085534885

noncomputable def p5869 :=
nat_lit
  113777007328014864976286531144977918708042634669906035665310937486811520254364107311291752315085281427648301773373870736234163

noncomputable def p5870 :=
@p5867 2199023255552 937 2199023255552 p5868
  p3378 p5869 p3512 p5840
  p2734 p5841 p5842

noncomputable def p5871 :=
nat_lit 2545990026363348061186105728152583865398188805003011566355097333737862205259520532616993115

noncomputable def p5872 :=
@Enclosure.Real.IsNear.subLit_ff_n p5865
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5694
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))
  p5871 p3378

noncomputable def p5873 :=
nat_lit
  105972611652349943416462961891518424555024769628276396760019114196059156717826055383170862891213090222066703235773665936234163

noncomputable def p5874 :=
nat_lit 2796007255471403506515624901867609641801079254325459594867374237375

noncomputable def p5875 :=
nat_lit 421249166674228746791672110734681729275580381602196445017243910144

noncomputable def p5876 :=
nat_lit 500801535658876906051979855813843872106823227466268073805437206052595364441777462242307411561

noncomputable def p5877 :=
nat_lit 65190923593865350263759371584636199256281519689763389440000000000000000000000000000000000000000000000

noncomputable def p5878 :=
nat_lit
  351395665405416277950001156377220818666291849219854302028421426960173721292089986890313694486379611380506738919032777184854363786456715053751897031117373440

noncomputable def p5879 :=
@p5872 p5873 p3512 p5874 p5875
  p5876 p5877 p5878 p5868
  p3378 p5869 p3512

noncomputable def p5880 :=
@Enclosure.Real.IsNear.subLit_ff_p p5864
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) p5692)
    (@iteratedDeriv Real c11 Real
      Real.normedAddCommGroup
      c10
      (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))

noncomputable def p5881 :=
nat_lit 2808263773971749167309527368733817556289003798768330532657400351445

noncomputable def p5882 :=
nat_lit 210624583337114373395836055367340864637790190801098222508621955072

noncomputable def p5883 :=
nat_lit 2237366363571481950600960521719243795079549673101827630001270516753835151353155462049

noncomputable def p5884 :=
nat_lit 842872547476238872097090864932670050990306517200981196800000000000000000000000000000000000000

noncomputable def p5885 :=
nat_lit 4243975142922389120225385811120139996966801250500381308055580117315651882102124281407055525

noncomputable def p5886 :=
nat_lit
  103275891023933841340373454543622060712602492803708273727079302729974863175220382797713468012140512219518540675773665936234163

noncomputable def p5887 :=
nat_lit
  536248088483229024280710205253828876655197635788277471177093735116482568075957649333726632570743327098212050789017046345851483685342735853723312721263329280

noncomputable def p5888 :=
@p5880 p5881 p5882 p5883 p5884
  p5885 p3378 p5886 p3512
  p5887 p5871 p3378

noncomputable def p5889 :=
@Enclosure.Real.IsNear.subLit_ft p5863
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1) Real.pi)
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5890 :=
nat_lit 199153654075382701833044367377820456057451343128005506354355866325

noncomputable def p5891 :=
nat_lit 2238373432263486558763041083953215689804884633740794045194533758202113454059466386147

noncomputable def p5892 :=
nat_lit 2528617642428716616291272594798010152970919551602943590400000000000000000000000000000000000000

noncomputable def p5893 :=
nat_lit 1916871379132150015126669005

noncomputable def p5894 :=
nat_lit 107701027607302576620989667578664869

noncomputable def p5895 :=
nat_lit 434557770834287179610335458513454327191359363552217143962283356867424901591145268097539112960

noncomputable def p5896 :=
@p5889 p5890 p5882 p5891 p5892
  p5893 p982 p5894 p3486 p5895
  p5881 p5882

noncomputable def p5897 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5687
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5898 :=
@Enclosure.Real.IsNear.mulLit_ft p5687
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5610 (Enclosure.sfrac false 1 16))))
  p5772

noncomputable def p5899 :=
@p5898 p2767 p5773 p5168 369716918637
  2199023255552 3990976307 28346784153600000000 p5890
  p5882 p5891 p5892

noncomputable def p5900 :=
p5899 (p5786 (Eq.refl true))
  (@p5646 369716918637 2199023255552 261552623255552
    p3422 369716918637 2199023255552 3990976307
    28346784153600000000 (p5835 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5901 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1) Real.pi)
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5610 (Enclosure.sfrac false 1 16))))
  884279719003555

noncomputable def p5902 :=
@p5901 70368744177664 1 250000000000000 2167720618191
  2199023255552 3990976307 28346784153600000000 p5893
  p982 p5894 p3486

noncomputable def p5903 :=
p5902 d146
  (@p5788 2167720618191 2199023255552 261552623255552
    p3422 2167720618191 2199023255552 3990976307
    28346784153600000000 (p5814 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5904 :=
@p5888 p5873 p3512
  (@p5896 p5883 p5884
    (@p5897 true p5890 p5882 p5891
      p5892 (p5900 (Eq.refl true)))
    (p5903 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p5905 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 2 1) p5692)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  p5844

noncomputable def p5906 :=
nat_lit 2354928789224651551486813334145638446649107993702245515947721685

noncomputable def p5907 :=
nat_lit 144899187452739972707899128827150751057075840706644138736850640944130182243113327

noncomputable def p5908 :=
@p5905 p982 p5839 p2908 p5906
  p2888 p5907 p3552 p5885
  p3378 p5886 p3512

noncomputable def p5909 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 2 1) p5692
  2 1 0 1 p5844 p976

noncomputable def p5910 :=
@Neg.neg Real Real.instNeg
  (p5686
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5911 :=
@Enclosure.Real.IsNear.of_eq
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  (p5609
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5910
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5692
        (Zeta.RiemannSiegel.correction
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
            (Enclosure.sfrac false 12 1))))))

noncomputable def p5912 :=
@p5613
  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5910
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5692
      (Zeta.RiemannSiegel.correction
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))
  5854533227701

noncomputable def p5913 :=
nat_lit 402240229516880176482681072745285661806811493697185

noncomputable def p5914 :=
nat_lit 24423452251081838676723656896898104665239758898106173001540561768179

noncomputable def p5915 :=
@p5912 2199023255552 937 2199023255552 p5913
  p3390 p5914 p3560 p5906
  p2888 p5907 p3552

noncomputable def p5916 :=
nat_lit 1590972912906316490511402466047485855085

noncomputable def p5917 :=
nat_lit 680564733841876926926749214863536422912

noncomputable def p5918 :=
@Enclosure.Real.IsNear.subLit_ff_n p5910
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5692
    (Zeta.RiemannSiegel.correction
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))
  p5916 p5917

noncomputable def p5919 :=
nat_lit 120307399525894252615332778597823725728385594627

noncomputable def p5920 :=
nat_lit 267727806768202049596103716975411200000000000000000000000

noncomputable def p5921 :=
nat_lit 3900826663951176823431528641010349152680498687379105

noncomputable def p5922 :=
nat_lit 21013124364640395323818026332150657849316245506623016098833361768179

noncomputable def p5923 :=
nat_lit 273750514741651044612910088375923339433278990044497947314582690391598728826144768623902720

noncomputable def p5924 :=
@p5918 p5919 p5920 p5921 p3390
  p5922 p3560 p5923 p5913
  p3390 p5914 p3560

noncomputable def p5925 :=
@Enclosure.Real.IsNear.neg
  (p5686
    (Real.sin
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (p5610 (Enclosure.sfrac false 1 16)))))

noncomputable def p5926 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 2 1) Real.pi)
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))
      (Enclosure.sfrac false 1 1)))

noncomputable def p5927 :=
@p5926
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5610 (Enclosure.sfrac false 1 16))))
  p5774

noncomputable def p5928 :=
@p5927 p976 p5775 p5171 2167720618191
  2199023255552 3990976307 28346784153600000000 p5916
  p5917 p5919 p5920

noncomputable def p5929 :=
p5928
  (p5781 d144
    (p5783 (p5785 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (@p5788 2167720618191 2199023255552 261552623255552
    p3422 2167720618191 2199023255552 3990976307
    28346784153600000000 (p5814 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5930 :=
@Enclosure.Real.IsNear.mulLit_ff p5692
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  p5844 p976 p5839

noncomputable def p5931 :=
nat_lit 2164519985003543611563537

noncomputable def p5932 :=
nat_lit 4835703278458516698824704

noncomputable def p5933 :=
@p5613
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (p5610 (Enclosure.sfrac false 1 16))))
  5854533227701

noncomputable def p5934 :=
@p5933 2199023255552 937 2199023255552 369716918637
  2199023255552 3990976307 28346784153600000000 p5931
  p5932 27830934982622330082991 p3576

noncomputable def p5935 :=
p5934
  (p5703
    (@Enclosure.Real.IsNear.neg p5617 false 5854533227701 2199023255552
      937 2199023255552 (p5731 (Eq.refl true))))
  (@p5646 369716918637 2199023255552 261552623255552
    p3422 369716918637 2199023255552 3990976307
    28346784153600000000 (p5835 (Eq.refl true))
    (Eq.refl true))

noncomputable def p5936 :=
@p5930 p2854 p5931 p5932
  27830934982622330082991 p3576 p5921 p3390
  p5922 p3560
  (@p5846 true p5844 p976 p5839
    p2854 (p5862 (Eq.refl true)))
  (@p5611 false p5931 p5932 27830934982622330082991
    p3576
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (p5612 (Eq.refl true) (Eq.refl true)
        (p5389 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5935 (Eq.refl true)))

noncomputable def p5937 :=
p5915
  (p5703
    (@Enclosure.Real.IsNear.neg p5617 false 5854533227701 2199023255552
      937 2199023255552 (p5731 (Eq.refl true))))
  (p5924
    (@p5925 true p5916 p5917 p5919
      p5920 (p5929 (Eq.refl true)))
    (p5936 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p5938 :=
p5908
  (@p5909 p5839 p2854 p5844
    p982 p5839 p2908
    (Enclosure.Real.IsNear.const false 2 1)
    (@p5846 true p5844 p976 p5839
      p2854 (p5862 (Eq.refl true)))
    (Eq.refl true))
  (@p5911 false p5906 p2888 p5907
    p3552
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (p5612 (Eq.refl true) (Eq.refl true)
        (p5389 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5937 (Eq.refl true)))

noncomputable def p5939 :=
nat_lit 1291744717000996442635904949280444572903375

noncomputable def p5940 :=
nat_lit 87112285931760246646623899502532662132736

noncomputable def p5941 :=
nat_lit 2480263790079639174019893891942009661343036605899616941418771

noncomputable def p5942 :=
@Enclosure.Real.IsNear.mulLit_ff p5694
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  p5939 p5940 p5941

noncomputable def p5943 :=
@Enclosure.Real.IsNear.neg
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (Enclosure.sfrac false 4 1)
      c16)
    (Real.cos
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (Enclosure.sfrac false 2 1) Real.pi)
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
          (Enclosure.sfrac false 12 1)))))

noncomputable def p5944 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 4 1)
    c16)
  (Real.cos
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))
  p1068

noncomputable def p5945 :=
@p5944 p1070 p1071 p1072 1651951774935
  4398046511104 3405780739 56693568307200000000 p5939
  p5940 p5941 p2961

noncomputable def p5946 :=
p5945 d148
  (@p5621 1651951774935 4398046511104 223201246511104
    p2689 1651951774935 4398046511104 3405780739
    56693568307200000000
    (p5716 (p5728 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5947 :=
@p5942 p2961 p5931 p5932
  27830934982622330082991 p3576 p5874 p5875
  p5876 p5877
  (@p5943 true p5939 p5940 p5941
    p2961 (p5946 (Eq.refl true)))
  (@p5611 false p5931 p5932 27830934982622330082991
    p3576
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (p5612 (Eq.refl true) (Eq.refl true)
        (p5389 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5935 (Eq.refl true)))

noncomputable def p5948 :=
p5870
  (p5703
    (@Enclosure.Real.IsNear.neg p5617 false 5854533227701 2199023255552
      937 2199023255552 (p5731 (Eq.refl true))))
  (p5879
    (p5904 (p5938 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p5947 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p5949 :=
p5843
  (@p5845 p5839 p2854 p5837
    p976 p5839 p2846
    (Enclosure.Real.IsNear.const false 3 1)
    (@p5846 true p5844 p976 p5839
      p2854 (p5862 (Eq.refl true)))
    (Eq.refl true))
  (@p5866 false p5840 p2734 p5841
    p5842
    (BSN.iteratedDeriv_two_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (p5612 (Eq.refl true) (Eq.refl true)
        (p5389 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5948 (Eq.refl true)))

noncomputable def p5950 :=
@p5756 p5741 p5701
  (@p5766 p5751 p5752
    (p5815 (Eq.refl true)) (p5836 (Eq.refl true))
    (Eq.refl true) (Eq.refl true))
  (p5949 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p5951 :=
nat_lit 3875234151002989327907714847841333718710125

noncomputable def p5952 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 3 1) p5694)
  (@iteratedDeriv Real c11 Real
    Real.normedAddCommGroup
    c8
    (@OfNat.ofNat Nat 1 (instOfNatNat 1)) Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  p5951

noncomputable def p5953 :=
@p5952 p5940 p5941 p2972 p5906
  p2888 p5907 p3552 p5742
  p5743 p5744 p5745

noncomputable def p5954 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 3 1) p5694
  3 1 0 1 p5939 p5940

noncomputable def p5955 :=
p5953
  (@p5954 p5941 p2961 p5951
    p5940 p5941 p2972
    (Enclosure.Real.IsNear.const false 3 1)
    (@p5943 true p5939 p5940 p5941
      p2961 (p5946 (Eq.refl true)))
    (Eq.refl true))
  (@p5911 false p5906 p2888 p5907
    p3552
    (BSN.deriv_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (p5612 (Eq.refl true) (Eq.refl true)
        (p5389 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5937 (Eq.refl true)))

noncomputable def p5956 :=
nat_lit 1409205669221518440914645300915286864802125409314416561625

noncomputable def p5957 :=
nat_lit 66933305303314096992142276609882703934201514684202280922792091758401952148702910479557

noncomputable def p5958 :=
@Enclosure.Real.IsNear.mulLit_tf p5696
  (Zeta.RiemannSiegel.correction
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
      (Enclosure.sfrac false 12 1)))
  p5956 p2977 p5957

noncomputable def p5959 :=
@Enclosure.Real.IsNear.mulLit_ft
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 8 1)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      c16 Real.pi))
  (Real.sin
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (Enclosure.sfrac false 2 1) Real.pi)
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))))

noncomputable def p5960 :=
@p5959 p1059 p1061 p1062 p1063
  2038005670203 2199023255552 3405780739 56693568307200000000
  p5956 p2977 p5957

noncomputable def p5961 :=
@p5960 p2980 d149
  (@p5849 4076011340406 4398046511104 223201246511104
    p2689 2038005670203 2199023255552 3405780739
    56693568307200000000
    (p5851 (p5861 (Eq.refl true) (Eq.refl true))
      (Eq.refl true) (Eq.refl true))
    (Eq.refl true))

noncomputable def p5962 :=
@p5958 p2980 p5931 p5932
  27830934982622330082991 p3576 p5735 p2761
  p5736 p3364 (p5961 (Eq.refl true))
  (@p5611 false p5931 p5932 27830934982622330082991
    p3576
    (BSN.correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (p5612 (Eq.refl true) (Eq.refl true)
        (p5389 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5935 (Eq.refl true)))

noncomputable def p5963 :=
p5702
  (p5703
    (@Enclosure.Real.IsNear.neg p5617 false 5854533227701 2199023255552
      937 2199023255552 (p5731 (Eq.refl true))))
  (p5738
    (@p5747 p5734 p5701 p5950
      (p5955 (Eq.refl true)) (Eq.refl true)
      (Eq.refl true))
    (p5962 (Eq.refl true)) (Eq.refl true) (Eq.refl true))

noncomputable def p5964 :=
@p5685 p5677
  (@p5697 false p5681 p5682 p5683
    p5684
    (BSN.iteratedDeriv_three_correction_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1))
      (p5612 (Eq.refl true) (Eq.refl true)
        (p5389 (Eq.refl true) (Eq.refl true)
          (Eq.refl true))))
    (p5963 (Eq.refl true)))

noncomputable def p5965 :=
@p5675 p5676 p5677 1353948535 17179869184
  1 17179869184 p5605 p5581 p5606
  p5583
  (@p5679 p5674 p5676 p5677
    (BSN.correctionLinear_mk
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) p5386
        (Enclosure.sfrac false 12 1)))
    (@Enclosure.Real.IsNear.neg p5678 false p5673 p5674
      p5676 p5677
      (p5964 d150 (Eq.refl true))))

noncomputable def p5966 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p5386) false
  1353948535 17179869184 1 17179869184 1353948535
  17179869184

noncomputable def p5967 :=
@Enclosure.Real.IsNear.inv_image p5386 217990490517 17179869184 41
  17179869184 676974267 676974268 8589934592
  (p5599 (Eq.refl true)) (Eq.refl true) (Eq.refl true)

noncomputable def p5968 :=
p5672
  (p5965
    (@p5966 1 17179869184
      (p5967 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p5969 :=
@p5584 p5381
  (@p5586 8589934592
    (@p2563 1 0 1
      (BSN.neg_one_pow_even_mk 12 (Eq.refl true))
      (Enclosure.Real.IsNear.const false 1 1))
    p5602 (Eq.refl true))
  (p5968 (Eq.refl true) (Eq.refl true)) (Eq.refl true)

noncomputable def p5970 :=
@p5388 p2994 p5380 p5381
  (BSN.hardyZApproximantRS_eq
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    12
    (p5389 (Eq.refl true) (Eq.refl true) (Eq.refl true)))
  (p5578 p5969 (Eq.refl true) (Eq.refl true))

theorem d163 : p5379 p5380 p5381 :=
@p5382 p2994 p5380 p5381
  (@Eq.refl Real
    (hardyZApproximantRS
      (@OfScientific.ofScientific Real c2 101161500
        true 5)))
  p5970

noncomputable def p5971 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  false 6000234691 549755813888

noncomputable def p5972 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt p4779)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    c7)

noncomputable def p5973 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p5972))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5972
          p5972)
        p5972)))

noncomputable def p5974 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  p5973 false 6000234691

noncomputable def p5975 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific Real c2 101038100
    true 5)
  101038100 100000
  (Enclosure.sfrac_ofScientific_eq 101038100 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p5976 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p5972))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5972
          p5972)
        p5972)))

noncomputable def p5977 :=
@p5976 750029325 68719476736 25 68719476736 91
  549755813888 1 549755813888 412332988258714648576 6000234691
  549755813888

noncomputable def p5978 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv Real Real.instInv p5972) 25 4 0 1
  30001173 17179869184

noncomputable def p5979 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p5972) false 30001173
  17179869184 1 17179869184 30001173 17179869184

noncomputable def p5980 :=
nat_lit 169013475855759504634542759

noncomputable def p5981 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p4779)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101038100
      true 5)
    c7)

noncomputable def p5982 :=
@p5981 61178127213 17179869184 7 17179869184
  2762645467510243 17179869184000 1010381 17179869184000 p5980
  295147905179352825856000 81151735631242521

noncomputable def p5983 :=
@p5982 295147905179352825856000
  (p4983
    (p4992 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p4987 (p4989 (Eq.refl true))) (Eq.refl true)

noncomputable def p5984 :=
@Enclosure.Real.IsNear.inv_image p5972 p5980 295147905179352825856000
  81151735631242521 295147905179352825856000 15000586 15000587
  8589934592 p5983 (Eq.refl true) (Eq.refl true)

noncomputable def p5985 :=
@p5977 201 549755813888
  (@p5978 1 17179869184 750029325 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p5979 1 17179869184
      (p5984 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p5986 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5972
        p5972)
      p5972))
  1

noncomputable def p5987 :=
@p5986 32 0 1 91 17179869184 1
  17179869184 91 549755813888 1 549755813888

noncomputable def p5988 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5972
        p5972)
      p5972))
  false

noncomputable def p5989 :=
nat_lit 4827963743822023877977142732998568743004864449274100818113939078351015834951479

noncomputable def p5990 :=
nat_lit 25711008708143844408671393477458601640355247900524685364822016000000000

noncomputable def p5991 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5972
      p5972)
    p5972)
  p5989 p5990

noncomputable def p5992 :=
nat_lit 6954433110973242841222811873703554976622022520861175353970750819000521

noncomputable def p5993 :=
nat_lit 28565555020845401017449683241713059819907584999332081

noncomputable def p5994 :=
nat_lit 87112285931760246646623899502532662132736000000

noncomputable def p5995 :=
nat_lit 27431473828113576447954972767828630065346319

noncomputable def p5996 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p5972
    p5972)
  p5972 p5993 p5994 p5995

noncomputable def p5997 :=
@Enclosure.Real.IsNear.mulLit_ff p5972 p5972 p5980
  295147905179352825856000 81151735631242521 295147905179352825856000
  p5980 295147905179352825856000 81151735631242521
  295147905179352825856000 p5993

noncomputable def p5998 :=
@p5996 p5994 p5980 295147905179352825856000
  81151735631242521 295147905179352825856000 p5989 p5990
  p5992 p5990
  (@p5997 p5994 p5995 p5994
    p5983 p5983 (Eq.refl true))
  p5983

noncomputable def p5999 :=
@p5991 p5992 p5990 45 46 8589934592
  (p5998 (Eq.refl true)) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p6000 :=
p5987 (Enclosure.Real.IsNear.const false 1 32)
  (@p5988 91 17179869184 1 17179869184 91
    17179869184 1 17179869184 (p5999 (Eq.refl true))
    (Eq.refl true))

theorem d164 : p5971 201 549755813888 :=
@p5974 549755813888 201 549755813888
  (p5975 (Eq.refl true))
  (p5985 (p6000 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p6001 :=
Enclosure.Real.IsNear
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  false 5991086691 549755813888

noncomputable def p6002 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt p5386)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    c7)

noncomputable def p6003 :=
@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p6002))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p6002
          p6002)
        p6002)))

noncomputable def p6004 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  p6003 false 5991086691

noncomputable def p6005 :=
BSN.hardyZErrorBoundRS_mk
  (@OfScientific.ofScientific Real c2 101161500
    true 5)
  101161500 100000
  (Enclosure.sfrac_ofScientific_eq 101161500 5 100000 (Eq.refl true))
  (Eq.refl true)

noncomputable def p6006 :=
@Enclosure.Real.IsNear.addLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 25 4) (@Inv.inv Real Real.instInv p6002))
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (Enclosure.sfrac false 1 32)
    (@Inv.inv Real Real.instInv
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p6002
          p6002)
        p6002)))

noncomputable def p6007 :=
@p6006 748885825 68719476736 25 68719476736 91
  549755813888 1 549755813888 411704342485533720576 5991086691
  549755813888

noncomputable def p6008 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 25 4)
  (@Inv.inv Real Real.instInv p6002) 25 4 0 1
  29955433 17179869184

noncomputable def p6009 :=
@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv p6002) false 29955433
  17179869184 1 17179869184 29955433 17179869184

noncomputable def p6010 :=
nat_lit 8463576998360846679921219

noncomputable def p6011 :=
@Enclosure.Real.IsNear.mulLit_ff (Real.sqrt p5386)
  (@HDiv.hDiv Real Real Real c4
    (@OfScientific.ofScientific Real c2 101161500
      true 5)
    c7)

noncomputable def p6012 :=
@p6011 15299199551 4294967296 3 8589934592
  553203909142269 3435973836800 202323 3435973836800 p6010
  14757395258967641292800 3925185814773861

noncomputable def p6013 :=
@p6012 14757395258967641292800
  (p5591
    (p5600 (Eq.refl true) (Eq.refl true) (Eq.refl true)
      (Eq.refl true))
    (Eq.refl true))
  (p5595 (p5597 (Eq.refl true))) (Eq.refl true)

noncomputable def p6014 :=
@Enclosure.Real.IsNear.inv_image p6002 p6010 14757395258967641292800
  3925185814773861 14757395258967641292800 14977716 14977717
  8589934592 p6013 (Eq.refl true) (Eq.refl true)

noncomputable def p6015 :=
@p6007 201 549755813888
  (@p6008 1 17179869184 748885825 68719476736 25
    68719476736 (Enclosure.Real.IsNear.const false 25 4)
    (@p6009 1 17179869184
      (p6014 (Eq.refl true) (Eq.refl true) (Eq.refl true)
        (Eq.refl true))
      (Eq.refl true))
    (Eq.refl true))

noncomputable def p6016 :=
@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac false 1 32)
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p6002
        p6002)
      p6002))
  1

noncomputable def p6017 :=
@p6016 32 0 1 91 17179869184 1
  17179869184 91 549755813888 1 549755813888

noncomputable def p6018 :=
@Enclosure.Real.IsNear.recentre'
  (@Inv.inv Real Real.instInv
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p6002
        p6002)
      p6002))
  false

noncomputable def p6019 :=
nat_lit 606264095268417322250238126663201505953765780279773664066409189828420746459

noncomputable def p6020 :=
nat_lit 3213876088517980551083924184682325205044405987565585670602752000000

noncomputable def p6021 :=
@Enclosure.Real.IsNear.inv_image
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p6002
      p6002)
    p6002)
  p6019 p6020

noncomputable def p6022 :=
nat_lit 843508328093011666725478833711444074812697637219970140770723765541

noncomputable def p6023 :=
nat_lit 71632135607182799324102005487451290675412046445961

noncomputable def p6024 :=
nat_lit 217780714829400616616559748756331655331840000

noncomputable def p6025 :=
nat_lit 66442224767831741281670520292930129760439

noncomputable def p6026 :=
@Enclosure.Real.IsNear.mulLit_ff
  (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) p6002
    p6002)
  p6002 p6023 p6024 p6025

noncomputable def p6027 :=
@Enclosure.Real.IsNear.mulLit_ff p6002 p6002 p6010
  14757395258967641292800 3925185814773861 14757395258967641292800 p6010
  14757395258967641292800 3925185814773861 14757395258967641292800 p6023

noncomputable def p6028 :=
@p6026 p6024 p6010 14757395258967641292800
  3925185814773861 14757395258967641292800 p6019 p6020
  p6022 p6020
  (@p6027 p6024 p6025 p6024
    p6013 p6013 (Eq.refl true))
  p6013

noncomputable def p6029 :=
@p6021 p6022 p6020 45 46 8589934592
  (p6028 (Eq.refl true)) (Eq.refl true) (Eq.refl true)
  (Eq.refl true) (Eq.refl true) (Eq.refl true)

noncomputable def p6030 :=
p6017 (Enclosure.Real.IsNear.const false 1 32)
  (@p6018 91 17179869184 1 17179869184 91
    17179869184 1 17179869184 (p6029 (Eq.refl true))
    (Eq.refl true))

theorem d165 : p6001 201 549755813888 :=
@p6004 549755813888 201 549755813888
  (p6005 (Eq.refl true))
  (p6015 (p6030 (Eq.refl true)) (Eq.refl true)
    (Eq.refl true))

noncomputable def p6031 :=
@LE.le Real Real.instLE
  c18
  (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d8))

noncomputable def p6032 :=
@OfNat.ofNat Real 1010381
  (@instOfNatAtLeastTwo Real 1010381
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              c3)))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 1010379))

noncomputable def p6033 :=
@OfNat.ofNat Real 1000
  (@instOfNatAtLeastTwo Real 1000
    (@AddMonoidWithOne.toNatCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real
            (@DivisionSemiring.toSemiring Real
              c3)))))
    (Mathlib.Meta.NormNum.instAtLeastTwo 998))

noncomputable def p6034 :=
@LE.le Real Real.instLE
  c18
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6035 :=
@congrArg Real Prop (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d8))
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6036 :=
p6035
  (@LE.le Real Real.instLE
    c17)

noncomputable def p6037 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  c3 1010381 1000
  (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d8)) p6032
  p6033
  (@Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true Real
    c3 101038100
    5 1010381 1000
    (p55
      (p56 p4
        (@p57 1010381 1000
          (p61 (@Eq.refl Nat (Nat.mul 101038100 1))
            (@Eq.refl Nat 100000))))))
  (@Eq.refl Real p6032)

noncomputable def p6038 :=
@congrArg Real Prop
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6039 :=
@p6038
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6040 :=
p6039
  (@LE.le Real Real.instLE
    c17)

noncomputable def p6041 :=
@Mathlib.Meta.NormNum.IsNNRat.to_eq Real
  c3 1010381 1000
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6042 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@HMul.hMul Real Real Real
    c19)
  p6032
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p6033)

noncomputable def p6043 :=
@p6042 1010381 1 1010381 1 1000 1000
  1
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      c3)
    p6032 1010381
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p6032 1010381
      (@Eq.refl Real
        (@OfNat.ofNat Real 1010381
          (@instOfNatAtLeastTwo Real 1010381
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 1010379))))))

noncomputable def p6044 :=
@Mathlib.Meta.NormNum.isNNRat_inv_pos Real
  c3
  (@FloorSemiring.instCharZero Real Real.semiring Real.partialOrder
    c26)
  p6033 999 1
  (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
    (@DivisionSemiring.toSemiring Real
      c3)
    p6033 1000
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p6033 1000
      (@Eq.refl Real
        (@OfNat.ofNat Real 1000
          (@instOfNatAtLeastTwo Real 1000
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p6045 :=
@p6041 p6032 p6033
  (@Mathlib.Meta.NormNum.isNNRat_div Real
    c3 p6032
    p6033 1010381 1000
    (p6043 p6044 (@Eq.refl Nat (Nat.mul 1010381 1))
      (@Eq.refl Nat 1000)))
  (@Eq.refl Real p6032)

noncomputable def p6046 :=
@le_of_not_gt Real Real.linearOrder
  c18
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6047 :=
@LT.lt Real
  (@Preorder.toLT Real (@PartialOrder.toPreorder Real (@LinearOrder.toPartialOrder Real Real.linearOrder)))
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6048 :=
@HMul.hMul Real Real Real
  c19
  c14

noncomputable def p6049 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          c3))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  p6032

noncomputable def p6050 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          c3))))
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6051 :=
@HSub.hSub Real Real Real
  (@instHSub Real
    (@SubNegMonoid.toSub Real
      (@AddGroup.toSubNegMonoid Real
        (@AddGroupWithOne.toAddGroup Real
          (@Ring.toAddGroupWithOne Real
            c32)))))
  p6049
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3))))
    p3705 (p6050 Real.pi))

noncomputable def p6052 :=
@HAdd.hAdd Real Real Real
  c36
  (p6048
    c13)
  p6051

noncomputable def p6053 :=
@HMul.hMul Real Real Real
  c19
  c15

noncomputable def p6054 :=
@Eq.mp
  (@LT.lt Real c29
    (@HAdd.hAdd Real Real Real
      c36
      p6052 (p6053 p3713))
    (@OfNat.ofNat Real 0
      c48))
  (@LT.lt Real c29
    c25
    (@OfNat.ofNat Real 0
      c48))

noncomputable def p6055 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real c0)))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real c0))))
    Real.pi
    c9)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 32000))

noncomputable def p6056 :=
@Mathlib.Tactic.Ring.Common.add_congr Real Real.instCommSemiring p6052
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      100800)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6055
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (p6053 p3713)

noncomputable def p6057 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real c0)))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real c0))))
    Real.pi
    c9)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32000)

noncomputable def p6058 :=
@p6056
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6057
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))

noncomputable def p6059 :=
@Mathlib.Tactic.Ring.Common.add_congr Real Real.instCommSemiring
  (p6048
    c13)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 909581))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p6060 :=
@p6059 p6051
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6055
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      100800)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6055
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p6061 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  c14

noncomputable def p6062 :=
@p6061
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      909581)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Neg.neg Real
    c37
    c23)

noncomputable def p6063 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  c14

noncomputable def p6064 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  c14

noncomputable def p6065 :=
@p6062
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 909581))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p6063 909581
    (@p6064 909581
      (@Eq.refl Real
        (@OfNat.ofNat Real 909581
          (@instOfNatAtLeastTwo Real 909581
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 909579))))))

noncomputable def p6066 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    909581)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 909581))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p6067 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    909581)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 909581))

noncomputable def p6068 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      909581)
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 1)))
  (Int.negOfNat 909581)

noncomputable def p6069 :=
@Mathlib.Meta.NormNum.isInt_mul Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@Ring.toSemiring Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    909581)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 1))

noncomputable def p6070 :=
@p6069 (Int.ofNat 909581) (Int.negOfNat 1) (Int.negOfNat 909581)
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real
            (@Ring.toSemiring Real
              (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))))))))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      909581)
    909581
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      909581))

noncomputable def p6071 :=
@p6067
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 909581))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p6068 (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (p6070
      (@Mathlib.Meta.NormNum.IsInt.of_raw Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 1))
      (@Eq.refl Int (Int.negOfNat 909581))))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      909581))

noncomputable def p6072 :=
@p6066
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 909581))
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p6071
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
          (Int.negOfNat 909581))
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p6073 :=
p6072
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
        (Int.negOfNat 1))
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
        (Int.negOfNat 909581))
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p6074 :=
p6060
  (p6065
    (p3726 p3727
      (p3728
        (@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real p3729 (Int.negOfNat 1)
          (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
          (p3733 (@Eq.refl Int (Int.negOfNat 1))))
        c64))
    p6073)

noncomputable def p6075 :=
@Mathlib.Tactic.Ring.Common.sub_congr Real Real.commRing p6049
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3))))
    p3705 (p6050 Real.pi))

noncomputable def p6076 :=
@p3744 p6032
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p6077 :=
p6076
  (p3746
    (p3747
      (@Nat.cast_one Real
        c5)))
  (@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring p6032 1010381
    (@Mathlib.Meta.NormNum.isNat_ofNat Real
      c5
      p6032 1010381
      (@Eq.refl Real
        (@OfNat.ofNat Real 1010381
          (@instOfNatAtLeastTwo Real 1010381
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 1010379))))))

noncomputable def p6078 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p6079 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1010381)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1010381)

noncomputable def p6080 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381))
  1010381

noncomputable def p6081 :=
@Mathlib.Meta.NormNum.isNat_mul Real c0
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1010381)
  1 1010381

noncomputable def p6082 :=
@p6081 1010381
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1010381)
  (@Eq.refl Nat 1010381)

noncomputable def p6083 :=
@p6079
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p6080
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    p6082)

noncomputable def p6084 :=
p6083
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        1010381)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p6085 :=
@p6078
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  p6084

noncomputable def p6086 :=
p6085
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        1010381)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p6087 :=
p6086
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Nat.rawCast Real
        (@AddCommMonoidWithOne.toAddMonoidWithOne Real
          (@NonAssocSemiring.toAddCommMonoidWithOne Real
            (@Semiring.toNonAssocSemiring Real c0)))
        1010381)
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p6088 :=
@p6075
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6055
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (p6077 p6087)

noncomputable def p6089 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring p3705
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p6050 Real.pi)

noncomputable def p6090 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real c0)))
  (@HPow.hPow Real Nat Real
    (@instHPow Real Nat
      (@NPow.toPow Real
        (@Monoid.toNPow Real
          (@Semiring.toMonoid Real c0))))
    Real.pi
    c9)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)

noncomputable def p6091 :=
@p6089
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6090
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p3762
    (p3746
      (p3747
        (@Nat.cast_one Real
          c5)))
    p3763 p3773)

noncomputable def p6092 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6093 :=
@p6092
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1000)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  Real.pi

noncomputable def p6094 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6095 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6096 :=
@p6093
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3777
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6090
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@p6094 1000
    (@p6095 1000
      (@Eq.refl Real
        (@OfNat.ofNat Real 1000
          (@instOfNatAtLeastTwo Real 1000
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p6097 :=
p6096
  (@Mathlib.Tactic.Ring.Common.atom_pf Real Real.instCommSemiring p3777 Real.pi
    c9
    (@rfl Nat
      (@Nat.rawCast Nat
        (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
          (@NonAssocSemiring.toAddCommMonoidWithOne Nat
            c35))
        1))
    (@Eq.mpr (@Eq Real p3777 p3777)
      (@Eq Real p3777 p3777)
      (@id
        (@Eq Prop (@Eq Real p3777 p3777)
          (@Eq Real p3777 p3777))
        p3782)
      (@Eq.refl Real p3777)))

noncomputable def p6098 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3777
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6090
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p6099 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)
  p3777
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p6090

noncomputable def p6100 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)
  Real.pi

noncomputable def p6101 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1000)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1))
  1000

noncomputable def p6102 :=
@Mathlib.Meta.NormNum.isNat_mul Real c0
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  1000 1

noncomputable def p6103 :=
@p6102 1000
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1)
  (@Eq.refl Nat 1000)

noncomputable def p6104 :=
@p6099
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6090
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p6100
    c9
    (@p6101
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      p6103))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1000))

noncomputable def p6105 :=
@p6098
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6090
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p6104
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p6090
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p6106 :=
p6105
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p3777
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6090
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p6107 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6090
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p6108 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)
  p6090
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p6057

noncomputable def p6109 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32000)
  Real.pi

noncomputable def p6110 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1000))
  32000

noncomputable def p6111 :=
@Mathlib.Meta.NormNum.isNat_mul Real c0
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)
  32 1000

noncomputable def p6112 :=
@p6111 32000
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1000)
  (@Eq.refl Nat 32000)

noncomputable def p6113 :=
@p6108
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p6109
    c9
    (@p6110
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      p6112))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32))

noncomputable def p6114 :=
@p6107
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p6113
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p6057
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p6115 :=
p6114
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6090
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6057
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p6116 :=
@Mathlib.Tactic.Ring.Common.sub_pf Real Real.commRing
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p6117 :=
@Neg.neg Real
  (@NegZeroClass.toNeg Real
    (@SubNegZeroMonoid.toNegZeroClass Real
      (@SubtractionMonoid.toSubNegZeroMonoid Real
        (@SubtractionCommMonoid.toSubtractionMonoid Real
          (@AddCommGroup.toDivisionAddCommMonoid Real
            (@Ring.toAddCommGroup Real
              (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))))))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32000)

noncomputable def p6118 :=
@p3730
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32000)
  (Int.ofNat 32000) (Int.negOfNat 32000) p3731

noncomputable def p6119 :=
p6118
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32000)
    32000
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32000))

noncomputable def p6120 :=
@Mathlib.Tactic.Ring.Common.neg_mul Real Real.commRing Real.pi
  (@Nat.rawCast Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne Nat
        c35))
    1)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32000)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 32000))
  (@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real p6117 (Int.negOfNat 32000)
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (p6119 (@Eq.refl Int (Int.negOfNat 32000))))

noncomputable def p6121 :=
@Mathlib.Tactic.Ring.Common.neg_add Real Real.commRing p6057
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p6055
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p6120 c64

noncomputable def p6122 :=
@p6116
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6055
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6055
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  p6121

noncomputable def p6123 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt Real Real.instCommSemiring
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6055
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6055
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1010381)

noncomputable def p6124 :=
p6122
  (p6123
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p6055
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p6125 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap Real Real.instCommSemiring
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 909581))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1010381)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6055
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Nat.rawCast Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
    100800)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6055
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p6126 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 909581))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381))
  100800
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))

noncomputable def p6127 :=
@Mathlib.Meta.NormNum.isInt_add Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 909581))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1010381)
  (Int.negOfNat 909581) (Int.ofNat 1010381)

noncomputable def p6128 :=
@p6127 (Int.ofNat 100800)
  (@Eq.refl (Real → Real → Real)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 909581))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381)
    1010381
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381))

noncomputable def p6129 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat Real
  (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 909581))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1010381))
  100800 (p6128 (@Eq.refl Int (Int.ofNat 100800)))

noncomputable def p6130 :=
p6074
  (p6088
    (p6091 (p6097 p6106) p6115)
    p6124)
  (p6125 (p6126 p6129)
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p6055
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p6131 :=
@Mathlib.Tactic.Ring.Common.mul_congr Real Real.instCommSemiring
  c15

noncomputable def p6132 :=
@p6131
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1600)
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  p3713

noncomputable def p6133 :=
@p6132
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6057
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p6134 :=
@Mathlib.Tactic.Ring.cast_pos Real Real.instCommSemiring
  c15

noncomputable def p6135 :=
@Mathlib.Meta.NormNum.isNat_ofNat Real
  c5
  c15

noncomputable def p6136 :=
p6133
  (@p6134 1600
    (@p6135 1600
      (@Eq.refl Real
        (@OfNat.ofNat Real 1600
          (@instOfNatAtLeastTwo Real 1600
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 1598))))))

noncomputable def p6137 :=
@Mathlib.Tactic.Ring.Common.add_mul Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1600)
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p3819
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6057
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))

noncomputable def p6138 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1600)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 63))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p3819
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 100800))

noncomputable def p6139 :=
@Mathlib.Meta.NormNum.IsInt.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1600)
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 63)))
  (Int.negOfNat 100800)

noncomputable def p6140 :=
@Mathlib.Meta.NormNum.isInt_mul Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@Ring.toSemiring Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1600)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 63))

noncomputable def p6141 :=
@p6140 (Int.ofNat 1600) (Int.negOfNat 63) (Int.negOfNat 100800)
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real
            (@Ring.toSemiring Real
              (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))))))))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1600)
    1600
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1600))

noncomputable def p6142 :=
@p6138
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6057
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  (@p6139 (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (p6141
      (@Mathlib.Meta.NormNum.IsInt.of_raw Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 63))
      (@Eq.refl Int (Int.negOfNat 100800))))

noncomputable def p6143 :=
@Mathlib.Tactic.Ring.Common.mul_add Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1600)
  p3819
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p6057

noncomputable def p6144 :=
@Mathlib.Tactic.Ring.Common.mul_pf_right Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1600)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32000)
  Real.pi

noncomputable def p6145 :=
@Mathlib.Meta.NormNum.IsNat.to_raw_eq Real
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1600)
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      20))
  32000

noncomputable def p6146 :=
@Mathlib.Meta.NormNum.isNat_mul Real c0
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1600)
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  1600 20

noncomputable def p6147 :=
@p6146 32000
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      (@instHMul Real
        (@Distrib.toMul Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    1600)
  (@Mathlib.Meta.NormNum.IsNat.of_raw Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    20)
  (@Eq.refl Nat 32000)

noncomputable def p6148 :=
@p6143
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (p6144
    c9
    (@p6145
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      p6147))
  (@Mathlib.Tactic.Ring.Common.mul_zero Real Real.instCommSemiring
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      1600))

noncomputable def p6149 :=
p6142
  (p6148
    (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p6057
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p6150 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_lt Real Real.instCommSemiring
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 100800))

noncomputable def p6151 :=
p6149
  (p6150
    (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p6057
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p6152 :=
@p6137
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 100800))
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      p6057
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))))
  p6151

noncomputable def p6153 :=
p6152
  (@Mathlib.Tactic.Ring.Common.zero_mul Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
        (Int.negOfNat 63))
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p3819
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p6154 :=
p6153
  (@Mathlib.Tactic.Ring.Common.add_pf_add_zero Real Real.instCommSemiring
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))
      (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
        (Int.negOfNat 100800))
      (@HAdd.hAdd Real Real Real
        (@instHAdd Real
          (@Distrib.toAdd Real
            (@instDistribOfSemiring Real c0)))
        p6057
        (@OfNat.ofNat Real 0
          (@Zero.toOfNat0 Real
            (@MulZeroClass.toZero Real
              (@instMulZeroClassOfSemiring Real c0)))))))

noncomputable def p6155 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero Real Real.instCommSemiring
  (@Nat.rawCast Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
    100800)
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6055
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 100800))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    p6057
    (@OfNat.ofNat Real 0
      (@Zero.toOfNat0 Real
        (@MulZeroClass.toZero Real
          (@instMulZeroClassOfSemiring Real c0)))))

noncomputable def p6156 :=
@Mathlib.Meta.NormNum.isInt_add Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0))))
  (@Nat.rawCast Real
    (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
      (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
    100800)
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 100800))
  (Int.ofNat 100800) (Int.negOfNat 100800)

noncomputable def p6157 :=
@p6156 (Int.ofNat 0)
  (@Eq.refl (Real → Real → Real)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      100800)
    100800
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      100800))
  (@Mathlib.Meta.NormNum.IsInt.of_raw Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 100800))

noncomputable def p6158 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat Real
  (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Nat.rawCast Real
      (@Mathlib.Meta.NormNum.instAddMonoidWithOne Real
        (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)))
      100800)
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 100800)))
  0 (p6157 (@Eq.refl Int (Int.ofNat 0)))

noncomputable def p6159 :=
@Mathlib.Meta.NormNum.isInt_add Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0))))
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 32000))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32000)
  (Int.negOfNat 32000) (Int.ofNat 32000)

noncomputable def p6160 :=
@p6159 (Int.ofNat 0)
  (@Eq.refl (Real → Real → Real)
    (@HAdd.hAdd Real Real Real
      (@instHAdd Real
        (@Distrib.toAdd Real
          (@instDistribOfSemiring Real c0)))))
  (@Mathlib.Meta.NormNum.IsInt.of_raw Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing)) (Int.negOfNat 32000))
  (@Mathlib.Meta.NormNum.IsNat.to_isInt Real
    (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32000)
    32000
    (@Mathlib.Meta.NormNum.IsNat.of_raw Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32000))

noncomputable def p6161 :=
@Mathlib.Meta.NormNum.IsInt.to_isNat Real
  (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
  (@HAdd.hAdd Real Real Real
    (@instHAdd Real
      (@Distrib.toAdd Real
        (@instDistribOfSemiring Real c0)))
    (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
      (Int.negOfNat 32000))
    (@Nat.rawCast Real
      (@AddCommMonoidWithOne.toAddMonoidWithOne Real
        (@NonAssocSemiring.toAddCommMonoidWithOne Real
          (@Semiring.toNonAssocSemiring Real c0)))
      32000))
  0 (p6160 (@Eq.refl Int (Int.ofNat 0)))

noncomputable def p6162 :=
@Mathlib.Tactic.Ring.Common.add_overlap_pf_zero Real Real.instCommSemiring
  (@Int.rawCast Real (@inferInstance (Ring Real) (@CommRing.toRing Real Real.commRing))
    (Int.negOfNat 32000))
  (@Nat.rawCast Real
    (@AddCommMonoidWithOne.toAddMonoidWithOne Real
      (@NonAssocSemiring.toAddCommMonoidWithOne Real
        (@Semiring.toNonAssocSemiring Real c0)))
    32000)
  Real.pi
  (@Nat.rawCast Nat
    (@AddCommMonoidWithOne.toAddMonoidWithOne Nat
      (@NonAssocSemiring.toAddCommMonoidWithOne Nat
        c35))
    1)
  p6161

noncomputable def p6163 :=
@Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero Real Real.instCommSemiring p6055
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p6057
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  p6162

noncomputable def p6164 :=
@Mathlib.Tactic.Ring.of_eq Real
  (@HAdd.hAdd Real Real Real
    c36
    p6052 (p6053 p3713))
  c25
  (@OfNat.ofNat Real 0
    (@Zero.toOfNat0 Real
      (@MulZeroClass.toZero Real
        (@instMulZeroClassOfSemiring Real c0))))
  (p6058 p6130
    (p6136
      (p3840 (p3842 p3852) p3860)
      p6154)
    (@p6155
      (@OfNat.ofNat Real 0
        (@Zero.toOfNat0 Real
          (@MulZeroClass.toZero Real
            (@instMulZeroClassOfSemiring Real c0))))
      p6158
      (p6163
        (@Mathlib.Tactic.Ring.Common.add_pf_zero_add Real Real.instCommSemiring
          (@OfNat.ofNat Real 0
            (@Zero.toOfNat0 Real
              (@MulZeroClass.toZero Real
                (@instMulZeroClassOfSemiring Real c0))))))))

noncomputable def p6165 :=
@congrArg Real Prop
  (@HAdd.hAdd Real Real Real
    c36
    p6052 (p6053 p3713))
  c25
  (fun (_a : Real) =>
    @LT.lt Real c29 _a
      (@OfNat.ofNat Real 0
        c48))
  (p6164
    (@Mathlib.Tactic.Ring.cast_zero Real Real.instCommSemiring
      c25
      (@Mathlib.Meta.NormNum.isNat_ofNat Real
        c5
        c25 0
        (@Nat.cast_zero Real
          c5))))

noncomputable def p6166 :=
@HAdd.hAdd Real Real Real
  (@instHAdd Real (@Distrib.toAdd Real (@instDistribOfSemiring Real Real.semiring)))
  (@HMul.hMul Real Real Real
    (@instHMul Real
      c50)
    c30
    c13)
  p6051

noncomputable def p6167 :=
@Mathlib.Tactic.Linarith.add_neg Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
  (@HMul.hMul Real Real Real
    (@instHMul Real
      c50)
    c30
    c13)
  p6051

noncomputable def p6168 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (@Neg.neg Real
    c37
    c23)
  c41
  (@neg_neg_of_pos Real Real.instAddCommGroup Real.partialOrder Real.instIsOrderedAddMonoid
    c23
    (@Mathlib.Tactic.Linarith.zero_lt_one Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing))

noncomputable def p6169 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  c41
  0 909581
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c25 0
    (@Nat.cast_zero Real
      c5))

noncomputable def p6170 :=
p6169
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c30
    909581
    (@Eq.refl Real
      (@OfNat.ofNat Real 909581
        (@instOfNatAtLeastTwo Real 909581
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 909579)))))

noncomputable def p6171 :=
@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6172 :=
@HSub.hSub Real Real Real
  c51
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6173 :=
p6171
  (p6172
    c17)

noncomputable def p6174 :=
@Mathlib.Tactic.CancelDenoms.derive_trans Real Real.instMul
  (p6172
    c17)

noncomputable def p6175 :=
@p6174
  (p6172
    c17)

noncomputable def p6176 :=
@p6175
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6177 :=
@congrArg Real (Real → Real)
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6178 :=
@p6177
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6179 :=
@congrFun' Real Real p6172 p6172
  (p6178
    (@HSub.hSub Real Real Real
      c24)
    (p6045 (@Eq.refl Real p6033)))
  c18

noncomputable def p6180 :=
@Mathlib.Tactic.CancelDenoms.sub_subst Real
  c32
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6181 :=
@p6180
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6182 :=
@p6181
  c18
  p6049

noncomputable def p6183 :=
@p6182
  (@HMul.hMul Real Real Real
    (@instHMul Real
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3))))
    p3705 (p6050 Real.pi))

noncomputable def p6184 :=
@Mathlib.Tactic.CancelDenoms.div_subst Real Real.instField
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6185 :=
@p6184
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6186 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3)))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  p6032

noncomputable def p6187 :=
@HDiv.hDiv Real Real Real
  c61
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6188 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  (@Mathlib.Meta.NormNum.instAddMonoidWithOne' Real
    (@DivisionSemiring.toSemiring Real
      c3))
  (p6187 p6033)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  1

noncomputable def p6189 :=
@Mathlib.Meta.NormNum.isNNRat_div Real
  c3
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6190 :=
p6050
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p6033)

noncomputable def p6191 :=
@HMul.hMul Real Real Real
  c19
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6192 :=
p6191
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p6033)

noncomputable def p6193 :=
@Mathlib.Meta.NormNum.isNNRat_mul Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@HMul.hMul Real Real Real
    c19)
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6194 :=
@p6193
  (@Inv.inv Real
    (@InvOneClass.toInv Real
      (@DivInvOneMonoid.toInvOneClass Real
        (@DivisionMonoid.toDivInvOneMonoid Real
          (@GroupWithZero.toDivisionMonoid Real
            (@DivisionSemiring.toGroupWithZero Real
              c3)))))
    p6033)

noncomputable def p6195 :=
@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6196 :=
@p6194 1000 1 1 1 1000 1 1000
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (@p6195 1000
    (@p6095 1000
      (@Eq.refl Real
        (@OfNat.ofNat Real 1000
          (@instOfNatAtLeastTwo Real 1000
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p6197 :=
@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
  (@DivisionSemiring.toSemiring Real
    c3)
  (p6187 p6033) 1
  (@p6189 p6033 1 1
    (@Mathlib.Meta.NormNum.IsNat.to_isNNRat Real
      (@DivisionSemiring.toSemiring Real
        c3)
      p6190 1
      (@Mathlib.Meta.NormNum.IsNNRat.to_isNat Real
        (@DivisionSemiring.toSemiring Real
          c3)
        p6192 1
        (p6196 p6044 (@Eq.refl Nat (Nat.mul 1000 1))
          (@Eq.refl Nat 1000)))))

noncomputable def p6198 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@Distrib.toMul Real
      (@instDistribOfSemiring Real
        (@DivisionSemiring.toSemiring Real
          c3))))
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6199 :=
@Mathlib.Meta.NormNum.isNat_eq_true Real
  c5
  p6198
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6200 :=
@Mathlib.Meta.NormNum.isNat_mul Real Real.semiring
  (@HMul.hMul Real Real Real
    c19)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6201 :=
@p6200 1 1000 1000
  (@Eq.refl (Real → Real → Real)
    (@HMul.hMul Real Real Real
      c19))
  (p3747
    (@Nat.cast_one Real
      c5))
  (@p6095 1000
    (@Eq.refl Real
      (@OfNat.ofNat Real 1000
        (@instOfNatAtLeastTwo Real 1000
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 998)))))
  (@Eq.refl Nat 1000)

noncomputable def p6202 :=
@p6185 p6032 p6033 p6049
  (@rfl Real p6186)
  (p6188 p6197
    (p3747
      (@Nat.cast_one Real
        c5)))
  (@p6199 1000 p6201
    (@p6095 1000
      (@Eq.refl Real
        (@OfNat.ofNat Real 1000
          (@instOfNatAtLeastTwo Real 1000
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p6203 :=
@Mathlib.Tactic.CancelDenoms.mul_subst Real (@Field.toCommRing Real Real.instField)
  (@OfNat.ofNat Real 1
    (@One.toOfNat1 Real
      (@AddMonoidWithOne.toOne Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))))
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6204 :=
@p6203
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6205 :=
@p6204
  c21
  Real.pi p3705 (p6050 Real.pi)

noncomputable def p6206 :=
@HMul.hMul Real Real Real
  (@instHMul Real
    (@inferInstance (Mul Real)
      (@Distrib.toMul Real
        (@instDistribOfSemiring Real
          (@DivisionSemiring.toSemiring Real
            c3)))))
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000
      (@AddMonoidWithOne.toNatCast Real
        (@inferInstance (AddMonoidWithOne Real)
          c1))
      (Mathlib.Meta.NormNum.instAtLeastTwo 998)))

noncomputable def p6207 :=
p6205 (@rfl Real p3930) (@rfl Real (p6206 Real.pi))
  (@p6199 1000 p6201
    (@p6095 1000
      (@Eq.refl Real
        (@OfNat.ofNat Real 1000
          (@instOfNatAtLeastTwo Real 1000
            (@AddMonoidWithOne.toNatCast Real
              c5)
            (Mathlib.Meta.NormNum.instAtLeastTwo 998))))))

noncomputable def p6208 :=
@Eq.mp
  (@LT.lt Real c29
    p6173
    c31)
  (@LT.lt Real c29
    p6051
    c31)
  (@congrArg Real Prop p6173 p6051
    (fun (_a : Real) =>
      @LT.lt Real c29 _a
        c49)
    (@p6176 p6051 p6179
      (p6183 p6202 p6207)))

noncomputable def p6209 :=
@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
  (p6172
    c17)

noncomputable def p6210 :=
@Mathlib.Tactic.Linarith.sub_neg_of_lt Real Real.instRing Real.partialOrder Real.instIsOrderedRing
  (@HDiv.hDiv Real Real Real
    (@instHDiv Real
      (@DivInvMonoid.toDiv Real
        (@GroupWithZero.toDivInvMonoid Real
          (@DivisionSemiring.toGroupWithZero Real
            c3))))
    p6032 p6033)

noncomputable def p6211 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  (@OfNat.ofNat Real 1000
    (@instOfNatAtLeastTwo Real 1000 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 999 (instOfNatNat 999))
        c62)))
  0 1000
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c25 0
    (@Nat.cast_zero Real
      c5))

noncomputable def p6212 :=
p6211
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    (@OfNat.ofNat Real 1000
      (@instOfNatAtLeastTwo Real 1000 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 999 (instOfNatNat 999))
          c62)))
    1000
    (@Eq.refl Real
      (@OfNat.ofNat Real 1000
        (@instOfNatAtLeastTwo Real 1000
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 998)))))

noncomputable def p6213 :=
@Mathlib.Meta.NormNum.isNat_lt_true Real Real.semiring Real.partialOrder Real.instIsOrderedRing
  (@FloorSemiring.instCharZero Real (@Ring.toSemiring Real Real.instRing) Real.partialOrder
    c26)
  c25
  (@OfNat.ofNat Real 1600
    (@instOfNatAtLeastTwo Real 1600 Real.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1599 (instOfNatNat 1599))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 1598 (instOfNatNat 1598))))))
  0 1600
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    c25 0
    (@Nat.cast_zero Real
      c5))

noncomputable def p6214 :=
p6213
  (@Mathlib.Meta.NormNum.isNat_ofNat Real
    c5
    (@OfNat.ofNat Real 1600
      (@instOfNatAtLeastTwo Real 1600 Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 1599 (instOfNatNat 1599))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat 1598 (instOfNatNat 1598))))))
    1600
    (@Eq.refl Real
      (@OfNat.ofNat Real 1600
        (@instOfNatAtLeastTwo Real 1600
          (@AddMonoidWithOne.toNatCast Real
            c5)
          (Mathlib.Meta.NormNum.instAtLeastTwo 1598)))))

noncomputable def p6215 :=
fun
    (a :
      p6047
        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
          (@OfNat.ofNat Real 32
            (@instOfNatAtLeastTwo Real 32 Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
                c63)))
          Real.pi)) =>
  @Mathlib.Tactic.Linarith.lt_irrefl Real Real.instPreorder
    c25
    (p6054 p6165
      (@Mathlib.Tactic.Linarith.add_neg Real Real.semiring Real.partialOrder Real.instIsStrictOrderedRing
        p6166
        (@HMul.hMul Real Real Real
          (@instHMul Real
            c50)
          c39
          p3713)
        (p6167 (p6168 (p6170 (@Eq.refl Bool false)))
          (p6208
            (@p6209
              (@OfNat.ofNat Real 1000
                (@instOfNatAtLeastTwo Real 1000 Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 999 (instOfNatNat 999))
                    c62)))
              (@p6210
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (@OfNat.ofNat Real 32
                    (@instOfNatAtLeastTwo Real 32 Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat 31 (instOfNatNat 31))
                        c63)))
                  Real.pi)
                a)
              (p6212 (@Eq.refl Bool false)))))
        (@Mathlib.Tactic.Linarith.mul_neg Real Real.instRing Real.partialOrder Real.instIsStrictOrderedRing
          p3713
          c39
          p3995 (p6214 (@Eq.refl Bool false)))))

noncomputable def p6216 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal d8)
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  false p4770 p4771

noncomputable def p6217 :=
@Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal d8) p4770
  p4771 p4773 p4774
  (@p6216 p4773 p4774
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101038100
          true 5)))
    d162)

noncomputable def p6218 :=
@Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal d8)
  (hardyZApproximantRS
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  true p5378 p2994

noncomputable def p6219 :=
@Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal d8) p5378
  p2994 p5380 p5381
  (@p6218 p5380 p5381
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101161500
          true 5)))
    d163)

noncomputable def p6220 :=
@Zeta.Certificates.ZIntervalRS.Certificate.mk d8
  (@Eq.mpr p6031 p6034
    (@id (@Eq Prop p6031 p6034)
      (@Eq.trans Prop p6031 p6034 p6034
        (p6036 (p6037 (@Eq.refl Real p6033)))
        (p6040 (p6045 (@Eq.refl Real p6033)))))
    (p6046 p6215))
  (BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal d8)
    (Zeta.Certificates.ZIntervalRS.sndVal d8)
    (p6217 (Eq.refl true) (Eq.refl true) (Eq.refl true))
    (p6219 (Eq.refl true) (Eq.refl true) (Eq.refl true)))

noncomputable def p6221 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal d8)
  (hardyZErrorBoundRS (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d8)))
  false false p4770 p4771 p4773

noncomputable def p6222 :=
@p6221 p4774 6000234691 549755813888 201
  549755813888
  (@p6216 p4773 p4774
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101038100
          true 5)))
    d162)

noncomputable def p6223 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE d8)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101038100
      true 5))
  false 6000234691 549755813888

noncomputable def p6224 :=
p6222
  (@p6223 201 549755813888
    (@Eq.refl Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific Real c2 101038100
          true 5)))
    d164)

noncomputable def p6225 :=
@Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal d8)
  (hardyZErrorBoundRS (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE d8)))
  true false p5378 p2994 p5380

noncomputable def p6226 :=
@p6225 p5381 5991086691 549755813888 201
  549755813888
  (@p6218 p5380 p5381
    (@Eq.refl Real
      (hardyZApproximantRS
        (@OfScientific.ofScientific Real c2 101161500
          true 5)))
    d163)

noncomputable def p6227 :=
@Enclosure.Real.IsNear.of_eq
  (hardyZErrorBoundRS (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE d8)))
  (hardyZErrorBoundRS
    (@OfScientific.ofScientific Real c2 101161500
      true 5))
  false 5991086691 549755813888

noncomputable def p6228 :=
p6226
  (@p6227 201 549755813888
    (@Eq.refl Real
      (hardyZErrorBoundRS
        (@OfScientific.ofScientific Real c2 101161500
          true 5)))
    d165)

theorem d166 : Zeta.Certificates.ZIntervalRS.Certificate d8 :=
p6220
  (p6224 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))
  (p6228 (Eq.refl true) (Eq.refl true) (Eq.refl true)
    (Eq.refl true) (Eq.refl true))

end RHHeight1000.GramZero656

theorem solution : ∃ t ∈ Set.Ioo (1010.38100 : ℝ) (1011.61500 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  exact riemannZeta.exists_zero_of_zIntervalRS_certificate _ RHHeight1000.GramZero656.d166

#print axioms solution
